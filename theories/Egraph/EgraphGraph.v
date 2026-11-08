(** * E-graph state and class operations

    Each allocated identifier owns a node, and a union-find records class equivalence.
    For example, a union rejects an identifier that has no allocated node.
    Builds on: EgraphSyntax and BaseUnionFind. *)

From Stdlib Require Import List BinPos NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphCoreIndex.
Import List.ListNotations Cost.Notations.

Module Egraph.

Definition id := positive.

Inductive enode (K Sort V : Type) : Type :=
  | NVar (s : Sort) (v : V)
  | NApp (s : Sort) (op : K) (children : list id).

Arguments NVar {K Sort V}.
Arguments NApp {K Sort V}.

Inductive just : Type :=
  | JGiven
  | JCongruence (i j : id)
  | JRule (rule : nat) (binding : list (positive * id)).

Record edge : Type := Edge {
  left : id;
  right : id;
  why : just
}.

(** Private runtime data contains parent incidence, repair scheduling and historical signatures. *)
Record kernel_data (K Sort V : Type) : Type := Kernel_data {
  parent_index : EggParent.t;
  pending : EggPending.t;
  snapshots : Map.t id (enode K Sort V);
  reasons : list edge
}.

Arguments parent_index {K Sort V} _.
Arguments pending {K Sort V} _.
Arguments snapshots {K Sort V} _.
Arguments reasons {K Sort V} _.

Definition empty_kernel_c {K Sort V} : Cost.t (kernel_data K Sort V) :=
  let* index := Map.empty_c in
  let* queue := EggPending.empty_c in
  let* snapshots := Map.empty_c in
  Cost.ret (Kernel_data K Sort V index queue snapshots []).

Definition empty_kernel {K Sort V} : kernel_data K Sort V := Cost.value empty_kernel_c.

Record t (K Sort V : Type) : Type := Make {
  uf : UnionFind.t id;
  nodes : Map.t id (enode K Sort V);
  memo : Map.t positive id;
  next : positive;
  private : kernel_data K Sort V
}.

Arguments uf {K Sort V} _.
Arguments nodes {K Sort V} _.
Arguments memo {K Sort V} _.
Arguments next {K Sort V} _.
Arguments private {K Sort V} _.

Definition parents {K Sort V} (g : t K Sort V) := parent_index (private g).
Definition dirty {K Sort V} (g : t K Sort V) := EggPending.entries (pending (private g)).
Definition dirty_flags {K Sort V} (g : t K Sort V) := EggPending.flags (pending (private g)).
Definition edges {K Sort V} (g : t K Sort V) := reasons (private g).
Definition cached {K Sort V} (g : t K Sort V) := snapshots (private g).

Definition id_encoding : encoding id := codec_enc positive_codec.

Definition empty_c {K Sort V} : Cost.t (t K Sort V) :=
  let* forest := UnionFind.make_c in
  let* ns := Map.empty_c in
  let* table := Map.empty_c in
  let* kernel := empty_kernel_c in
  Cost.ret (Make K Sort V forest ns table 1%positive kernel).

Definition empty {K Sort V} : t K Sort V := Cost.value empty_c.

Definition find_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) : Cost.t id :=
  Cost.map fst (UnionFind.find_c id_encoding c (uf g)).

Definition find {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) :=
  Cost.value (find_c a g c).

Definition node_sort {K Sort V} (n : enode K Sort V) : Sort :=
  match n with
  | NVar s _ => s
  | NApp s _ _ => s
  end.

Definition sort_of_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) :
    Cost.t (option Sort) :=
  Cost.map (option_map node_sort) (Map.get_c id_encoding c (nodes g)).

Definition sort_of {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c : id) :=
  Cost.value (sort_of_c a g c).

(** Canonical signatures replace each child by its current class representative. *)
Definition canonical_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (n : enode K Sort V) : Cost.t (enode K Sort V) :=
  match n with
  | NVar s v => Cost.ret (NVar s v)
  | NApp s op cs => Cost.map (NApp s op) (map_c (find_c a g) cs)
  end.

Definition canonical {K Sort V} (a : EggAlg.t K Sort V) g n :=
  Cost.value (canonical_c a g n).

(** Canonicalization retains the constructor and replaces each child by its representative. *)
Theorem canonical_equation {K Sort V} (a : EggAlg.t K Sort V) g n :
  canonical a g n =
    match n with
    | NVar s v => NVar s v
    | NApp s op cs => NApp s op (map (find a g) cs)
    end.
Proof.
  destruct n; [reflexivity|].
  unfold canonical, canonical_c; rewrite Cost.value_map, value_map_c; reflexivity.
Qed.

(** Tags separate variables from applications, including nullary applications. *)
Definition signature_c {K Sort V} (a : EggAlg.t K Sort V) (n : enode K Sort V) :
    Cost.t (list positive) :=
  Cost.step ;;
  let* s := encode_c (EggAlg.sort_enc K Sort V a) (node_sort n) in
  Cost.step ;;
  match n with
  | NVar _ v =>
    let* v := encode_c (EggAlg.var_enc K Sort V a) v in
    Cost.ret [1%positive; s; v]
  | NApp _ op cs =>
    let* op := encode_c (EggAlg.op_enc K Sort V a) op in
    Cost.ret (2%positive :: s :: op :: cs)
  end.

Definition signature {K Sort V} (a : EggAlg.t K Sort V) n :=
  Cost.value (signature_c a n).

(** The public list codec charges serialization of every signature digit. *)
Definition node_code_c {K Sort V} (a : EggAlg.t K Sort V) (n : enode K Sort V) :
    Cost.t positive :=
  let* ps := signature_c a n in
  Cost.step ;;
  encode_c (codec_enc (list_codec positive_codec)) ps.

Definition node_code {K Sort V} (a : EggAlg.t K Sort V) n :=
  Cost.value (node_code_c a n).

Definition child_sorts_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) cs :
    Cost.t (option (list Sort)) :=
  fold_right_c (fun c rest =>
    let* s := sort_of_c a g c in
    Cost.ret
      (match s, rest with
      | Some s, Some ss => Some (s :: ss)
      | _, _ => None
      end)) (Some []) cs.

Definition child_sorts {K Sort V} (a : EggAlg.t K Sort V) g cs :=
  Cost.value (child_sorts_c a g cs).

(** A local shape check rejects unknown children and inconsistent sort annotations. *)
Definition node_valid_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (n : enode K Sort V) : Cost.t bool :=
  match n with
  | NVar s v =>
    Cost.step ;;
    let* declared := EggAlg.var_sort_c a v in
    match declared with
    | None => Cost.ret false
    | Some declared => eqb_c (EggAlg.sort_enc K Sort V a) s declared
    end
  | NApp s op cs =>
    let* sorts := child_sorts_c a g cs in
    match sorts with
    | None => Cost.ret false
    | Some sorts => Cost.step ;; EggAlg.op_shape_c a op sorts s
    end
  end.

Definition node_valid {K Sort V} (a : EggAlg.t K Sort V) g n :=
  Cost.value (node_valid_c a g n).

Definition node_children {K Sort V} (n : enode K Sort V) : list id :=
  match n with
  | NVar _ _ => []
  | NApp _ _ cs => cs
  end.

(** A node is pending when one scheduled losing class retains it in its parent snapshot. *)
Definition pending_node {K Sort V} (g : t K Sort V) i : Prop :=
  exists loser, In loser (dirty g) /\ In i (EggParent.get (parents g) loser).

(** A repair batch temporarily protects its unvisited parents in addition to queued dirty buckets. *)
Definition pending_work {K Sort V} (g : t K Sort V) (work : list id) i : Prop :=
  match work with
  | [] => pending_node g i
  | _ :: _ => pending_node g i \/ In i work
  end.

(** Paths use undirected explanation edges and include the zero-edge reflexive path. *)
Inductive edge_path (es : list edge) : id -> id -> Prop :=
  | path_refl c : edge_path es c c
  | path_step c d e :
      In e es ->
      (left e = c /\ right e = d \/ left e = d /\ right e = c) ->
      forall target, edge_path es d target -> edge_path es c target.

(** Each new explanation edge joins previously disconnected trees. *)
Inductive explanation_forest : list edge -> Prop :=
  | forest_empty : explanation_forest []
  | forest_edge e es :
      explanation_forest es ->
      ~ edge_path es (left e) (right e) ->
      explanation_forest (e :: es).

(** Maintained kernel obligations describe local index, snapshot, queue and memo relationships. *)
Record kernel_inv_on {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (work : list id) : Prop := Kernel_inv {
  (** The parent index has the canonical Base Map representation. *)
  parent_map_wf : Map.wf id_encoding (parents g);
  (** Historical node signatures have the canonical Base Map representation. *)
  snapshot_map_wf : Map.wf id_encoding (cached g);
  (** Scheduling flags agree exactly with the duplicate-free dirty-class queue. *)
  pending_wf : EggPending.wf (pending (private g));
  (** Every stored node has a historical signature snapshot. *)
  snapshot_complete : forall i n, Map.get id_encoding i (nodes g) = Some n ->
    exists old, Map.get id_encoding i (cached g) = Some old;
  (** A snapshot denotes the same current child classes and constructor as its stored node. *)
  snapshot_correct : forall i old, Map.get id_encoding i (cached g) = Some old ->
    exists n, Map.get id_encoding i (nodes g) = Some n /\
      canonical a g old = canonical a g n;
  (** Current child representatives have complete parent buckets. *)
  current_parents : forall i n child,
    Map.get id_encoding i (nodes g) = Some n -> In child (node_children n) ->
    In i (EggParent.get (parents g) (find a g child));
  (** Historical child roots retain their parent incidence until their signatures are repaired. *)
  snapshot_parents : forall i old child,
    Map.get id_encoding i (cached g) = Some old -> In child (node_children old) ->
    In i (EggParent.get (parents g) child);
  (** Every indexed parent identifies an allocated stored node. *)
  indexed_nodes : forall root i, In i (EggParent.get (parents g) root) ->
    exists n, Map.get id_encoding i (nodes g) = Some n;
  (** Every scheduled dirty class has actual parent work to discharge. *)
  pending_nonempty : forall loser, In loser (dirty g) -> EggParent.get (parents g) loser <> [];
  (** Dirty classes stay inside the allocated identifier range. *)
  pending_allocated : forall loser, In loser (dirty g) -> (loser < next g)%positive;
  (** Nodes outside pending buckets have current canonical snapshots. *)
  stable_snapshot : forall i n old, Map.get id_encoding i (nodes g) = Some n ->
    Map.get id_encoding i (cached g) = Some old -> ~ pending_work g work i ->
    old = canonical a g n;
  (** Every memo value owns the historical signature stored at that key. *)
  memo_owner : forall key i, Map.get id_encoding key (memo g) = Some i ->
    exists old, Map.get id_encoding i (cached g) = Some old /\ node_code a old = key;
  (** Every stable node has a canonical memo entry denoting its current class. *)
  stable_memo : forall i n, Map.get id_encoding i (nodes g) = Some n ->
    ~ pending_work g work i -> exists other,
      Map.get id_encoding (node_code a (canonical a g n)) (memo g) = Some other /\
      find a g i = find a g other;
  (** Explanation edges form an undirected forest. *)
  reasons_forest : explanation_forest (edges g);
  (** Every stored explanation edge relates identifiers in the same current UF class. *)
  reasons_correct : forall e, In e (edges g) -> find a g (left e) = find a g (right e)
}.

(** Public maintained validity has no unvisited repair-batch parents outside the dirty queue. *)
Definition kernel_inv {K Sort V} (a : EggAlg.t K Sort V) g : Prop := kernel_inv_on a g [].

Arguments parent_map_wf {K Sort V} a g {work} _.
Arguments snapshot_map_wf {K Sort V} a g {work} _.
Arguments pending_wf {K Sort V} a g {work} _.
Arguments snapshot_complete {K Sort V} a g {work} _ _ _ _.
Arguments snapshot_correct {K Sort V} a g {work} _ _ _ _.
Arguments current_parents {K Sort V} a g {work} _ _ _ _ _ _.
Arguments snapshot_parents {K Sort V} a g {work} _ _ _ _ _ _.
Arguments indexed_nodes {K Sort V} a g {work} _ _ _ _.
Arguments pending_nonempty {K Sort V} a g {work} _ _ _.
Arguments pending_allocated {K Sort V} a g {work} _ _ _.
Arguments stable_snapshot {K Sort V} a g {work} _ _ _ _ _ _ _.
Arguments memo_owner {K Sort V} a g {work} _ _ _ _.
Arguments stable_memo {K Sort V} a g {work} _ _ _ _ _.
Arguments reasons_forest {K Sort V} a g {work} _.
Arguments reasons_correct {K Sort V} a g {work} _ _ _.

Definition allocation_kernel_c {K Sort V} (g : t K Sort V) (n : enode K Sort V) :
    Cost.t (kernel_data K Sort V) :=
  let* index := EggParent.register_c (parents g) (node_children n) (next g) in
  let* snapshots := Map.set_c id_encoding (next g) n (cached g) in
  Cost.ret (Kernel_data K Sort V index (pending (private g)) snapshots (edges g)).

Definition allocation_kernel {K Sort V} (g : t K Sort V) n :=
  Cost.value (allocation_kernel_c g n).

(** Allocation registers each canonical child root and stores the new signature snapshot. *)
Theorem allocation_kernel_equation {K Sort V} (g : t K Sort V) n :
  allocation_kernel g n = Kernel_data K Sort V
    (EggParent.register (parents g) (node_children n) (next g))
    (pending (private g)) (Map.set id_encoding (next g) n (cached g)) (edges g).
Proof.
  reflexivity.
Qed.

(** Allocation registers a fresh singleton and stores its already canonical signature. *)
Definition allocate_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (n : enode K Sort V) (key : positive) : Cost.t (id * t K Sort V) :=
  let c := next g in
  let* forest := UnionFind.union_c id_encoding c c (uf g) in
  let* ns := Map.set_c id_encoding c n (nodes g) in
  let* table := Map.set_c id_encoding key c (memo g) in
  let* kernel := allocation_kernel_c g n in
  Cost.ret (c, Make K Sort V forest ns table (Pos.succ c) kernel).

Definition allocate {K Sort V} (a : EggAlg.t K Sort V) g n key :=
  Cost.value (allocate_c a g n key).

(** Allocation changes only its fresh node, memo key and maintained insertion metadata. *)
Theorem allocate_equation {K Sort V} (a : EggAlg.t K Sort V) g n key :
  allocate a g n key =
    (next g, Make K Sort V
      (UnionFind.union id_encoding (next g) (next g) (uf g))
      (Map.set id_encoding (next g) n (nodes g))
      (Map.set id_encoding key (next g) (memo g))
      (Pos.succ (next g)) (allocation_kernel g n)).
Proof.
  reflexivity.
Qed.

(** Insertion checks sorts before either reusing a memo class or allocating a node. *)
Definition add_node_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (n : enode K Sort V) : Cost.t (option (id * t K Sort V)) :=
  let* valid := node_valid_c a g n in
  if valid then
    let* n' := canonical_c a g n in
    let* key := node_code_c a n' in
    let* hit := Map.get_c id_encoding key (memo g) in
    match hit with
    | Some c =>
      let* root := find_c a g c in
      Cost.ret (Some (root, g))
    | None => Cost.map (@Some _) (allocate_c a g n' key)
    end
  else Cost.ret None.

Definition add_node {K Sort V} (a : EggAlg.t K Sort V) g n :=
  Cost.value (add_node_c a g n).

(** Insertion reuses the memo class on a hit and allocates its canonical node on a miss. *)
Theorem add_node_equation {K Sort V} (a : EggAlg.t K Sort V) g n :
  add_node a g n =
    if node_valid a g n then
      match Map.get id_encoding (node_code a (canonical a g n)) (memo g) with
      | Some c => Some (find a g c, g)
      | None => Some (allocate a g (canonical a g n) (node_code a (canonical a g n)))
      end
    else None.
Proof.
  unfold add_node, add_node_c; rewrite Cost.value_bind.
  fold (node_valid a g n); destruct (node_valid a g n); [|reflexivity].
  rewrite !Cost.value_bind.
  fold (canonical a g n) (node_code a (canonical a g n)).
  fold (Map.get id_encoding (node_code a (canonical a g n)) (memo g)).
  destruct (Map.get _ _ _); reflexivity.
Qed.

(** Term insertion visits children from left to right and threads their allocated graph. *)
Fixpoint add_term_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (e : EggTerm.t K Sort V) : Cost.t (option (id * t K Sort V)) :=
  Cost.step ;;
  match e with
  | EggTerm.Var s v => add_node_c a g (NVar s v)
  | EggTerm.App s op args =>
    let* result := (fix go (args : list (EggTerm.t K Sort V)) (g : t K Sort V) :=
      Cost.step ;;
      match args with
      | [] => Cost.ret (Some ([], g))
      | e :: rest =>
        let* result := add_term_c a g e in
        match result with
        | None => Cost.ret None
        | Some (c, g') =>
          let* result := go rest g' in
          Cost.ret (option_map (fun result => (c :: fst result, snd result)) result)
        end
      end) args g in
    match result with
    | None => Cost.ret None
    | Some (cs, g') => add_node_c a g' (NApp s op cs)
    end
  end.

Definition add_term {K Sort V} (a : EggAlg.t K Sort V) g e :=
  Cost.value (add_term_c a g e).

Definition add_terms_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (args : list (EggTerm.t K Sort V)) : Cost.t (option (list id * t K Sort V)) :=
  (fix go (args : list (EggTerm.t K Sort V)) (g : t K Sort V) :=
    Cost.step ;;
    match args with
    | [] => Cost.ret (Some ([], g))
    | e :: rest =>
      let* result := add_term_c a g e in
      match result with
      | None => Cost.ret None
      | Some (c, g') =>
        let* result := go rest g' in
        Cost.ret (option_map (fun result => (c :: fst result, snd result)) result)
      end
    end) args g.

Definition add_terms {K Sort V} (a : EggAlg.t K Sort V) g args :=
  Cost.value (add_terms_c a g args).

Definition linked_kernel_c {K Sort V} (g : t K Sort V) loser winner reason :
    Cost.t (kernel_data K Sort V) :=
  let* index := EggParent.merge_c (parents g) loser winner in
  let* affected := EggParent.get_c (parents g) loser in
  let* queue :=
    match affected with
    | [] => Cost.ret (pending (private g))
    | _ :: _ => EggPending.push_c loser (pending (private g))
    end in
  Cost.ret (Kernel_data K Sort V index queue (cached g) (Edge loser winner reason :: edges g)).

Definition linked_kernel {K Sort V} (g : t K Sort V) loser winner reason :=
  Cost.value (linked_kernel_c g loser winner reason).

(** A link keeps the loser's parent snapshot and schedules its nonempty bucket once. *)
Theorem linked_kernel_equation {K Sort V} (g : t K Sort V) loser winner reason :
  linked_kernel g loser winner reason = Kernel_data K Sort V
    (EggParent.merge (parents g) loser winner)
    (match EggParent.get (parents g) loser with
    | [] => pending (private g)
    | _ :: _ => EggPending.push loser (pending (private g))
    end) (cached g) (Edge loser winner reason :: edges g).
Proof.
  unfold linked_kernel, linked_kernel_c; rewrite !Cost.value_bind.
  fold (EggParent.get (parents g) loser).
  destruct (EggParent.get (parents g) loser); reflexivity.
Qed.

Definition union_kernel_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (c d : id) (forest : UnionFind.t id) (reason : just) : Cost.t (kernel_data K Sort V) :=
  let* rc := find_c a g c in
  let* rd := find_c a g d in
  let* same := positive_eqb_c rc rd in
  if same then Cost.ret (private g)
  else
    let* found := UnionFind.find_c id_encoding c forest in
    let root := fst found in
    let* left_wins := positive_eqb_c root rc in
    let loser := if left_wins then rd else rc in
    linked_kernel_c g loser root reason.

Definition union_kernel {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    c d forest reason := Cost.value (union_kernel_c a g c d forest reason).

(** Union metadata uses the actual surviving UF root to select the loser and its parent snapshot. *)
Theorem union_kernel_equation {K Sort V} (a : EggAlg.t K Sort V) g c d forest reason :
  union_kernel a g c d forest reason =
    let rc := find a g c in
    let rd := find a g d in
    if Pos.eqb rc rd then private g
    else
      let root := fst (UnionFind.find id_encoding c forest) in
      linked_kernel g (if Pos.eqb root rc then rd else rc) root reason.
Proof.
  unfold union_kernel, union_kernel_c; rewrite !Cost.value_bind.
  fold (find a g c) (find a g d).
  rewrite positive_eqb_equation.
  destruct (Pos.eqb (find a g c) (find a g d)); [reflexivity|].
  rewrite !Cost.value_bind.
  fold (UnionFind.find id_encoding c forest).
  rewrite positive_eqb_equation; reflexivity.
Qed.

Definition merge_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (c d : id) (reason : just) : Cost.t (t K Sort V) :=
  let* forest := UnionFind.union_c id_encoding c d (uf g) in
  let* kernel := union_kernel_c a g c d forest reason in
  Cost.ret (Make K Sort V forest (nodes g) (memo g) (next g) kernel).

Definition merge {K Sort V} (a : EggAlg.t K Sort V) g c d reason :=
  Cost.value (merge_c a g c d reason).

(** The unchecked merge retains stored productions and defers all memo repairs. *)
Theorem merge_equation {K Sort V} (a : EggAlg.t K Sort V) g c d reason :
  merge a g c d reason = Make K Sort V
    (UnionFind.union id_encoding c d (uf g)) (nodes g) (memo g) (next g)
    (union_kernel a g c d (UnionFind.union id_encoding c d (uf g)) reason).
Proof.
  reflexivity.
Qed.

Definition union_j_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (c d : id) (reason : just) :
    Cost.t (option (t K Sort V)) :=
  let* sc := sort_of_c a g c in
  let* sd := sort_of_c a g d in
  match sc, sd with
  | Some sc, Some sd =>
    Cost.step ;;
    let* pc := encode_c (EggAlg.sort_enc K Sort V a) sc in
    Cost.step ;;
    let* pd := encode_c (EggAlg.sort_enc K Sort V a) sd in
    let* cmp := Map.code_compare_c pc pd in
    match cmp with
    | Eq => Cost.map (@Some _) (merge_c a g c d reason)
    | _ => Cost.ret None
    end
  | _, _ => Cost.ret None
  end.

Definition union_j {K Sort V} (a : EggAlg.t K Sort V) g c d reason :=
  Cost.value (union_j_c a g c d reason).

(** Justified union checks allocated sorts before applying the deferred rank-selected merge. *)
Theorem union_j_equation {K Sort V} (a : EggAlg.t K Sort V) g c d reason :
  union_j a g c d reason =
    match sort_of a g c, sort_of a g d with
    | Some sc, Some sd =>
      match Map.code_compare (encode (EggAlg.sort_enc K Sort V a) sc)
        (encode (EggAlg.sort_enc K Sort V a) sd) with
      | Eq => Some (merge a g c d reason)
      | _ => None
      end
    | _, _ => None
    end.
Proof.
  unfold union_j, union_j_c; rewrite !Cost.value_bind.
  fold (sort_of a g c) (sort_of a g d).
  destruct (sort_of a g c) as [sc|], (sort_of a g d) as [sd|]; [|reflexivity..].
  rewrite !Cost.value_bind.
  fold (encode (EggAlg.sort_enc K Sort V a) sc) (encode (EggAlg.sort_enc K Sort V a) sd).
  fold (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) sc)
    (encode (EggAlg.sort_enc K Sort V a) sd)).
  destruct (Map.code_compare _ _); reflexivity.
Qed.

Definition union_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c d : id) :=
  union_j_c a g c d JGiven.

Definition union {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c d : id) :=
  Cost.value (union_c a g c d).

Definition install_c {K Sort V} (g : t K Sort V) i current old_key key :
    Cost.t (t K Sort V) :=
  let* table := Map.remove_c id_encoding old_key (memo g) in
  let* table := Map.set_c id_encoding key i table in
  let* snapshots := Map.set_c id_encoding i current (cached g) in
  Cost.ret (Make K Sort V (uf g) (nodes g) table (next g)
    (Kernel_data K Sort V (parents g) (pending (private g)) snapshots (edges g))).

Definition install {K Sort V} (g : t K Sort V) i current old_key key :=
  Cost.value (install_c g i current old_key key).

(** Installing one signature changes its snapshot and the two selected memo keys alone. *)
Theorem install_equation {K Sort V} (g : t K Sort V) i current old_key key :
  install g i current old_key key = Make K Sort V (uf g) (nodes g)
    (Map.set id_encoding key i (Map.remove id_encoding old_key (memo g))) (next g)
    (Kernel_data K Sort V (parents g) (pending (private g))
      (Map.set id_encoding i current (cached g)) (edges g)).
Proof.
  reflexivity.
Qed.

(** Repair rewrites one historical signature and justifies any collision by its two stored nodes. *)
Definition repair_node_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (i : id) :
    Cost.t (t K Sort V) :=
  let* node := Map.get_c id_encoding i (nodes g) in
  let* old := Map.get_c id_encoding i (cached g) in
  match node, old with
  | Some n, Some historical =>
    let* current := canonical_c a g n in
    let* old_key := node_code_c a historical in
    let* key := node_code_c a current in
    let* collision := Map.get_c id_encoding key (memo g) in
    let* base :=
      match collision with
      | None => Cost.ret g
      | Some other =>
        let* merged := union_j_c a g i other (JCongruence i other) in
        Cost.ret (match merged with Some h => h | None => g end)
      end in
    install_c base i current old_key key
  | _, _ => Cost.ret g
  end.

Definition repair_node {K Sort V} (a : EggAlg.t K Sort V) g i :=
  Cost.value (repair_node_c a g i).

(** Repair observes a collision before deleting its historical key and records the resulting union. *)
Theorem repair_node_equation {K Sort V} (a : EggAlg.t K Sort V) g i :
  repair_node a g i =
    match Map.get id_encoding i (nodes g), Map.get id_encoding i (cached g) with
    | Some n, Some historical =>
      let current := canonical a g n in
      let old_key := node_code a historical in
      let key := node_code a current in
      let base :=
        match Map.get id_encoding key (memo g) with
        | None => g
        | Some other =>
          match union_j a g i other (JCongruence i other) with Some h => h | None => g end
        end in
      install base i current old_key key
    | _, _ => g
    end.
Proof.
  unfold repair_node, repair_node_c; rewrite !Cost.value_bind.
  fold (Map.get id_encoding i (nodes g)) (Map.get id_encoding i (cached g)).
  destruct (Map.get id_encoding i (nodes g)) as [n|],
    (Map.get id_encoding i (cached g)) as [historical|]; [|reflexivity..].
  rewrite !Cost.value_bind.
  fold (canonical a g n) (node_code a historical) (node_code a (canonical a g n)).
  fold (Map.get id_encoding (node_code a (canonical a g n)) (memo g)).
  destruct (Map.get id_encoding (node_code a (canonical a g n)) (memo g)) as [other|];
    [|reflexivity].
  rewrite !Cost.value_bind; fold (union_j a g i other (JCongruence i other)).
  destruct (union_j a g i other (JCongruence i other)); reflexivity.
Qed.

(** A repair batch counts each visited parent in the same fold that performs its update. *)
Definition repair_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (loser : id) :
    Cost.t (t K Sort V * N) :=
  let* affected := EggParent.get_c (parents g) loser in
  fold_left_c (fun result i =>
    let* h := repair_node_c a (fst result) i in
    Cost.ret (h, N.succ (snd result))) affected (g, 0%N).

Definition repair {K Sort V} (a : EggAlg.t K Sort V) g loser :=
  Cost.value (repair_c a g loser).

(** Replacing scheduling data leaves every production, class, memo entry and parent bucket unchanged. *)
Definition with_queue {K Sort V} (g : t K Sort V) queue : t K Sort V :=
  Make K Sort V (uf g) (nodes g) (memo g) (next g)
    (Kernel_data K Sort V (parents g) queue (cached g) (edges g)).

(** A loop step dequeues one dirty class and accumulates that batch's actual parent visits. *)
Definition dirty_step_c {K Sort V} (a : EggAlg.t K Sort V) (state : t K Sort V * N) :
    Cost.t ((t K Sort V * N) + (t K Sort V * N)) :=
  let '(g, visits) := state in
  let* item := EggPending.pop_c (pending (private g)) in
  match item with
  | None => Cost.ret (inr state)
  | Some (loser, queue) =>
    let popped := with_queue g queue in
    let* result := repair_c a popped loser in
    Cost.ret (inl (fst result, N.add visits (snd result)))
  end.

(** A memo scan also detects the first collision between different current classes. *)
Definition scan_step_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (acc : Map.t positive id * option (id * id)) (entry : id * enode K Sort V) :
    Cost.t (Map.t positive id * option (id * id)) :=
  let '(table, collision) := acc in
  let '(c, n) := entry in
  let* n' := canonical_c a g n in
  let* key := node_code_c a n' in
  let* root := find_c a g c in
  let* old := Map.get_c id_encoding key table in
  match old with
  | None =>
    let* table := Map.set_c id_encoding key root table in
    Cost.ret (table, collision)
  | Some other =>
    let* same := positive_eqb_c root other in
    Cost.ret (table,
      match collision with
      | Some collision_pair => Some collision_pair
      | None => if same then None else Some (root, other)
      end)
  end.

Definition scan_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) :=
  let* entries := Map.elements_c (nodes g) in
  let* table := Map.empty_c in
  fold_left_c (scan_step_c a g) entries (table, None).

Definition scan {K Sort V} (a : EggAlg.t K Sort V) g := Cost.value (scan_c a g).

(** Each continuing rebuild step merges a congruent pair found by the charged scan. *)
Definition rebuild_step_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) :
    Cost.t (t K Sort V + t K Sort V) :=
  let* result := scan_c a g in
  let '(table, collision) := result in
  let g' := Make K Sort V (uf g) (nodes g) table (next g) (private g) in
  match collision with
  | None => Cost.ret (inr g')
  | Some (c, d) =>
    let* merged := union_c a g' c d in
    Cost.ret (match merged with Some g'' => inl g'' | None => inr g' end)
  end.

(** Squared node-count fuel bounds the number of unequal identifier pairs. *)
Definition rebuild_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) :
    Cost.t (t K Sort V) :=
  let* count := Map.size_c (nodes g) in
  Cost.step ;;
  let* bound := encode_c (codec_enc nat_codec) count in
  let* result := iterate (rebuild_step_c a) (Pos.mul bound bound) g in
  match result with
  | inr g' => Cost.ret g'
  | inl g' =>
    let* result := scan_c a g' in
    Cost.ret (Make K Sort V (uf g') (nodes g') (fst result) (next g') (private g'))
  end.

Definition rebuild {K Sort V} (a : EggAlg.t K Sort V) g :=
  Cost.value (rebuild_c a g).

Arguments empty {K Sort V} : simpl never.
Arguments empty_c {K Sort V} : simpl never.
Arguments find {K Sort V} _ _ _ : simpl never.
Arguments find_c {K Sort V} _ _ _ : simpl never.
Arguments sort_of {K Sort V} _ _ _ : simpl never.
Arguments sort_of_c {K Sort V} _ _ _ : simpl never.
Arguments add_node {K Sort V} _ _ _ : simpl never.
Arguments add_node_c {K Sort V} _ _ _ : simpl never.
Arguments add_term {K Sort V} _ _ _ : simpl never.
Arguments add_term_c {K Sort V} _ _ _ : simpl never.
Arguments union {K Sort V} _ _ _ _ : simpl never.
Arguments union_c {K Sort V} _ _ _ _ : simpl never.
Arguments rebuild {K Sort V} _ _ : simpl never.
Arguments rebuild_c {K Sort V} _ _ : simpl never.

End Egraph.
