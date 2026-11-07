(** * E-graph state and class operations

    Each allocated identifier owns a node, and a union-find records class equivalence.
    For example, a union rejects an identifier that has no allocated node.
    Builds on: EgraphSyntax and BaseUnionFind. *)

From Stdlib Require Import List BinPos.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax.
Import List.ListNotations Cost.Notations.

Module Egraph.

Definition id := positive.

Inductive enode (K Sort V : Type) : Type :=
  | NVar (s : Sort) (v : V)
  | NApp (s : Sort) (op : K) (children : list id).

Arguments NVar {K Sort V}.
Arguments NApp {K Sort V}.

Record t (K Sort V : Type) : Type := Make {
  uf : UnionFind.t id;
  nodes : Map.t id (enode K Sort V);
  memo : Map.t positive id;
  next : positive
}.

Arguments uf {K Sort V} _.
Arguments nodes {K Sort V} _.
Arguments memo {K Sort V} _.
Arguments next {K Sort V} _.

Definition id_encoding : encoding id := codec_enc positive_codec.

Definition empty_c {K Sort V} : Cost.t (t K Sort V) :=
  let* forest := UnionFind.make_c in
  let* ns := Map.empty_c in
  let* table := Map.empty_c in
  Cost.ret (Make K Sort V forest ns table 1%positive).

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

(** Allocation registers a fresh singleton and stores its already canonical signature. *)
Definition allocate_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V)
    (n : enode K Sort V) (key : positive) : Cost.t (id * t K Sort V) :=
  let c := next g in
  let* forest := UnionFind.union_c id_encoding c c (uf g) in
  let* ns := Map.set_c id_encoding c n (nodes g) in
  let* table := Map.set_c id_encoding key c (memo g) in
  Cost.ret (c, Make K Sort V forest ns table (Pos.succ c)).

Definition allocate {K Sort V} (a : EggAlg.t K Sort V) g n key :=
  Cost.value (allocate_c a g n key).

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

Definition union_c {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c d : id) :
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
    | Eq =>
      let* forest := UnionFind.union_c id_encoding c d (uf g) in
      Cost.ret (Some (Make K Sort V forest (nodes g) (memo g) (next g)))
    | _ => Cost.ret None
    end
  | _, _ => Cost.ret None
  end.

Definition union {K Sort V} (a : EggAlg.t K Sort V) (g : t K Sort V) (c d : id) :=
  Cost.value (union_c a g c d).

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
  let g' := Make K Sort V (uf g) (nodes g) table (next g) in
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
    Cost.ret (Make K Sort V (uf g') (nodes g') (fst result) (next g'))
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
