(** * Fixed plain shared extraction and observations

    Plain computation retains the memo, immutable backpointers and additive tree objectives.
    For example, in a DAG with root 2 applying natural operator 0 to [1; 1] and node 1
    holding variable 0 (both of natural sort 0), both occurrences contribute to size when
    observation succeeds.
    Builds on: the shared representation, plain validation and fixed source data records. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Wellfounded.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditSharedCompare RewriteAuditSharedExtract
  RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Fixpoint rd_plain_pos_succ (p : positive) : positive :=
  match p with
  | xH => xO xH
  | xO rest => xI rest
  | xI rest => xO (rd_plain_pos_succ rest)
  end.

Fixpoint rd_plain_nat_positive (n : nat) : positive :=
  match n with
  | 0 => xH
  | S rest => rd_plain_pos_succ (rd_plain_nat_positive rest)
  end.

Fixpoint rd_plain_pos_add (a b : positive) : positive :=
  match a, b with
  | xH, xH => xO xH
  | xH, xO y => xI y
  | xH, xI y => xO (rd_plain_pos_succ y)
  | xO x, xH => xI x
  | xI x, xH => xO (rd_plain_pos_succ x)
  | xO x, xO y => xO (rd_plain_pos_add x y)
  | xO x, xI y => xI (rd_plain_pos_add x y)
  | xI x, xO y => xI (rd_plain_pos_add x y)
  | xI x, xI y => xO (rd_plain_pos_succ (rd_plain_pos_add x y))
  end.

Definition rd_plain_N_add (a b : N) : N :=
  match a, b with
  | N0, _ => b
  | _, N0 => a
  | Npos x, Npos y => Npos (rd_plain_pos_add x y)
  end.

Fixpoint rd_plain_nat_N (n : nat) : N :=
  match n with
  | 0 => 0%N
  | S rest => rd_plain_N_add 1%N (rd_plain_nat_N rest)
  end.

Fixpoint rd_plain_pos_nat (p : positive) : nat :=
  match p with
  | xH => 1
  | xO rest =>
    let n := rd_plain_pos_nat rest in n + n
  | xI rest =>
    let n := rd_plain_pos_nat rest in S (n + n)
  end.

Definition rd_plain_N_nat (n : N) : nat :=
  match n with
  | N0 => 0
  | Npos p => rd_plain_pos_nat p
  end.

Fixpoint rd_plain_pos_compare (otherwise : comparison) (p q : positive) : comparison :=
  match p, q with
  | xH, xH => otherwise
  | xH, xO _
  | xH, xI _ => Lt
  | xO _, xH
  | xI _, xH => Gt
  | xO a, xO b
  | xI a, xI b => rd_plain_pos_compare otherwise a b
  | xO a, xI b => rd_plain_pos_compare Lt a b
  | xI a, xO b => rd_plain_pos_compare Gt a b
  end.

Definition rd_plain_N_compare (a b : N) : comparison :=
  match a, b with
  | N0, N0 => Eq
  | N0, _ => Lt
  | _, N0 => Gt
  | Npos x, Npos y => rd_plain_pos_compare Eq x y
  end.

Fixpoint rd_plain_headers_compare (xs ys : list positive) : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: rest, y :: tail =>
    match rd_plain_pos_compare Eq x y with
    | Eq => rd_plain_headers_compare rest tail
    | answer => answer
    end
  end.

Definition rd_plain_header {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (node : rw_shared_node K Sort V) : list positive :=
  match node with
  | RWSharedVar _ _ _ ty v => [1%positive; encode ES ty; encode EV v; 1%positive]
  | RWSharedApp _ _ _ ty k children =>
    [2%positive; encode ES ty; encode EK k; encode nat_encoding (length children)]
  end.

Inductive rd_plain_compare_call : Type :=
  | RDPlainRoot (p q : positive) (memo : rw_rd_memo)
  | RDPlainChildren (xs ys : list positive) (memo : rw_rd_memo).

(** This fixed potential-subcall relation covers the literal root, head and tail call shapes. *)
Inductive rd_plain_compare_descend {K Sort V}
    (left right : Map.t positive (rw_shared_node K Sort V)) :
    rd_plain_compare_call -> rd_plain_compare_call -> Prop :=
  | RDPlainDescendChildren : forall p q memo a b,
      Map.get positive_encoding p left = Some a ->
      Map.get positive_encoding q right = Some b ->
      rd_plain_compare_descend left right
        (RDPlainChildren (rw_rd_children a) (rw_rd_children b) memo) (RDPlainRoot p q memo)
  | RDPlainDescendHead : forall x xs y ys memo,
      rd_plain_compare_descend left right (RDPlainRoot x y memo)
        (RDPlainChildren (x :: xs) (y :: ys) memo)
  | RDPlainDescendTail : forall x xs y ys memo middle,
      rd_plain_compare_descend left right (RDPlainChildren xs ys middle)
        (RDPlainChildren (x :: xs) (y :: ys) memo).

(** The contract asks for well-founded comparator subcalls when both stored graphs validate. *)
Definition rw_rd_plain_compare_well_founded_type : Prop :=
  forall K Sort V (left right : rw_shared_tree K Sort V), rw_shared_validate left = true ->
    rw_shared_validate right = true ->
    well_founded (rd_plain_compare_descend (rw_shared_nodes K Sort V left)
      (rw_shared_nodes K Sort V right)).

Definition rd_plain_compare_body {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (left right : Map.t positive (rw_shared_node K Sort V))
    (call : rd_plain_compare_call)
    (recurse : forall child,
      rd_plain_compare_descend left right child call -> comparison * rw_rd_memo) :
    comparison * rw_rd_memo.
Proof.
  destruct call as [p q memo | xs ys memo].
  - destruct (Map.get (pair_encoding positive_encoding positive_encoding) (p, q) memo)
      as [cached |] eqn:Hmemo; [exact (cached, memo) |].
    destruct (Map.get positive_encoding p left) as [a |] eqn:Hleft;
      [|exact (Eq, memo)].
    destruct (Map.get positive_encoding q right) as [b |] eqn:Hright;
      [|exact (Eq, memo)].
    destruct (rd_plain_headers_compare (rd_plain_header EK ES EV a)
      (rd_plain_header EK ES EV b)) as [| |] eqn:Hheaders.
    + destruct (recurse (RDPlainChildren (rw_rd_children a) (rw_rd_children b) memo)
        (RDPlainDescendChildren left right p q memo a b Hleft Hright)) as [answer middle].
      exact (answer, Map.set (pair_encoding positive_encoding positive_encoding)
        (p, q) answer middle).
    + exact (Lt, Map.set (pair_encoding positive_encoding positive_encoding) (p, q) Lt memo).
    + exact (Gt, Map.set (pair_encoding positive_encoding positive_encoding) (p, q) Gt memo).
  - destruct xs as [|x xs]; destruct ys as [|y ys].
    + exact (Eq, memo).
    + exact (Lt, memo).
    + exact (Gt, memo).
    + destruct (recurse (RDPlainRoot x y memo)
        (RDPlainDescendHead left right x xs y ys memo)) as [head middle].
      destruct head.
      * exact (recurse (RDPlainChildren xs ys middle)
          (RDPlainDescendTail left right x xs y ys memo middle)).
      * exact (Lt, middle).
      * exact (Gt, middle).
Defined.

(** Accessibility drives exactly the fixed memo body, with no supplied algorithm operation. *)
Definition rd_plain_compare_execute {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (left right : Map.t positive (rw_shared_node K Sort V))
    (call : rd_plain_compare_call)
    (accessible : Acc (rd_plain_compare_descend left right) call) : comparison * rw_rd_memo :=
  @Fix_F rd_plain_compare_call (rd_plain_compare_descend left right)
    (fun _ => (comparison * rw_rd_memo)%type)
    (rd_plain_compare_body EK ES EV left right) call accessible.

(** The builder validates both trees before comparing them using the well-foundedness witness. *)
Definition rw_shared_compare_builder (Hwf : rw_rd_plain_compare_well_founded_type)
    {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (left right : rw_shared_tree K Sort V) : option bool.
Proof.
  destruct (rw_shared_validate left) eqn:Hleft;
    destruct (rw_shared_validate right) eqn:Hright.
  - pose (call := RDPlainRoot (rw_shared_root K Sort V left)
      (rw_shared_root K Sort V right) Map.empty).
    destruct (rd_plain_compare_execute EK ES EV (rw_shared_nodes K Sort V left)
      (rw_shared_nodes K Sort V right) call (Hwf K Sort V left right Hleft Hright call))
      as [answer memo].
    exact (Some (
      match answer with
      | Gt => false
      | _ => true
      end)).
  - exact None.
  - exact None.
  - exact None.
Defined.

Definition rd_plain_candidate_get {K Sort V} (g : rw_graph K Sort V) (table : rw_rd_table)
    (id : rw_id) : option rw_rd_candidate :=
  match Map.get positive_encoding id (rw_class_roots g) with
  | None => None
  | Some root => Map.get positive_encoding root table
  end.

Fixpoint rd_plain_gather {K Sort V} (g : rw_graph K Sort V) (table : rw_rd_table)
    (ids : list rw_id) : option (list positive * N * N) :=
  match ids with
  | [] => Some ([], 0%N, 0%N)
  | id :: rest =>
    let head := rd_plain_candidate_get g table id in
    let tail := rd_plain_gather g table rest in
    match head, tail with
    | Some candidate, Some (pointers, cost, size) =>
      Some (rw_rd_pointer candidate :: pointers,
        rd_plain_N_add (rw_rd_cost candidate) cost, rd_plain_N_add (rw_rd_size candidate) size)
    | _, _ => None
    end
  end.

Definition rd_plain_allocate {K Sort V} (node : rw_shared_node K Sort V) (cost size : N)
    (store : rw_rd_store K Sort V) : rw_rd_candidate * rw_rd_store K Sort V :=
  let id := rw_rd_next store in
  (RwRdCandidate id cost size, RwRdStore (Map.set positive_encoding id node (rw_rd_nodes store))
    (rd_plain_pos_succ id)).

Definition rd_plain_production {K Sort V} (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V)
    (old : rw_rd_table) (node : rw_node K Sort V) (store : rw_rd_store K Sort V) : option
    rw_rd_candidate * rw_rd_store K Sort V :=
  match node with
  | RWNVar ty v =>
    let '(candidate, next) := rd_plain_allocate (RWSharedVar K Sort V ty v)
      (rd_plain_nat_N (vc v)) 1%N store in (Some candidate, next)
  | RWNApp ty op children =>
    match rd_plain_gather g old children with
    | None => (None, store)
    | Some (pointers, cost, size) =>
      let '(candidate, next) := rd_plain_allocate (RWSharedApp K Sort V ty op pointers)
        (rd_plain_N_add (rd_plain_nat_N (oc op)) cost) (rd_plain_N_add 1%N size) store in
      (Some candidate, next)
    end
  end.

Definition rd_plain_choose (Hwf : rw_rd_plain_compare_well_founded_type) {K Sort V}
    (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (store : rw_rd_store K Sort V)
    (old fresh : rw_rd_candidate) : rw_rd_candidate :=
  match rd_plain_N_compare (rw_rd_cost old) (rw_rd_cost fresh) with
  | Lt => old
  | Gt => fresh
  | Eq =>
    match rd_plain_N_compare (rw_rd_size old) (rw_rd_size fresh) with
    | Lt => old
    | Gt => fresh
    | Eq =>
      match rw_shared_compare_builder Hwf EK ES EV
        (RwSharedTree K Sort V (rw_rd_pointer old) (rw_rd_nodes store))
        (RwSharedTree K Sort V (rw_rd_pointer fresh) (rw_rd_nodes store)) with
      | Some true => old
      | _ => fresh
      end
    end
  end.

Definition rd_plain_insert (Hwf : rw_rd_plain_compare_well_founded_type) {K Sort V}
    (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (store : rw_rd_store K Sort V)
    (root : rw_id) (fresh : rw_rd_candidate) (table : rw_rd_table) : rw_rd_table :=
  let chosen :=
    match Map.get positive_encoding root table with
    | None => fresh
    | Some old => rd_plain_choose Hwf EK ES EV store old fresh
    end in
  Map.set positive_encoding root chosen table.

Fixpoint rd_plain_round (Hwf : rw_rd_plain_compare_well_founded_type) {K Sort V} (EK : encoding K)
    (ES : encoding Sort) (EV : encoding V) (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V)
    (old : rw_rd_table) (entries : list (rw_id * (rw_id * rw_node K Sort V))) (table : rw_rd_table)
    (store : rw_rd_store K Sort V) : rw_rd_table * rw_rd_store K Sort V :=
  match entries with
  | [] => (table, store)
  | (_, (owner, node)) :: rest =>
    let root := Map.get positive_encoding owner (rw_class_roots g) in
    let '(produced, next) := rd_plain_production vc oc g old node store in
    let inserted :=
      match root, produced with
      | Some root, Some fresh => rd_plain_insert Hwf EK ES EV next root fresh table
      | _, _ => table
      end in
    rd_plain_round Hwf EK ES EV vc oc g old rest inserted next
  end.

Fixpoint rd_plain_rounds (Hwf : rw_rd_plain_compare_well_founded_type) {K Sort V} (EK : encoding K)
    (ES : encoding Sort) (EV : encoding V) (vc : V -> nat) (oc : K -> nat) (g : rw_graph K Sort V)
    (entries : list (rw_id * (rw_id * rw_node K Sort V))) (rounds : positive) (table : rw_rd_table)
    (store : rw_rd_store K Sort V) : rw_rd_table * rw_rd_store K Sort V :=
  match rounds with
  | xH => rd_plain_round Hwf EK ES EV vc oc g table entries table store
  | xO p =>
    let '(middle, ms) := rd_plain_rounds Hwf EK ES EV vc oc g entries p table store in
    rd_plain_rounds Hwf EK ES EV vc oc g entries p middle ms
  | xI p =>
    let '(first, fs) := rd_plain_round Hwf EK ES EV vc oc g table entries table store in
    let '(middle, ms) := rd_plain_rounds Hwf EK ES EV vc oc g entries p first fs in
    rd_plain_rounds Hwf EK ES EV vc oc g entries p middle ms
  end.

(** The extractor runs fixed binary DP rounds and retains every allocated backpointer node. *)
Definition rw_shared_extract_builder (Hwf : rw_rd_plain_compare_well_founded_type) {K Sort V}
    (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (vc : V -> nat) (oc : K -> nat)
    (g : rw_graph K Sort V) (root : rw_id) : option (rw_shared_tree K Sort V) :=
  match length (rw_roots g) with
  | 0 => None
  | S count =>
    let '(table, store) := rd_plain_rounds Hwf EK ES EV vc oc g (Map.elements (rw_nodes g))
      (rd_plain_nat_positive count) Map.empty (RwRdStore Map.empty 1%positive) in
    match rd_plain_candidate_get g table root with
    | None => None
    | Some candidate =>
      Some (RwSharedTree K Sort V (rw_rd_pointer candidate) (rw_rd_nodes store))
    end
  end.

Fixpoint rd_plain_shared_gather (table : rw_rd_table) (ids : list positive) : option (N * N) :=
  match ids with
  | [] => Some (0%N, 0%N)
  | id :: rest =>
    let head := Map.get positive_encoding id table in
    let tail := rd_plain_shared_gather table rest in
    match head, tail with
    | Some candidate, Some (cost, size) =>
      Some (rd_plain_N_add (rw_rd_cost candidate) cost, rd_plain_N_add (rw_rd_size candidate) size)
    | _, _ => None
    end
  end.

Definition rd_plain_scalar_node {K Sort V} (vc : V -> nat) (oc : K -> nat) (table : rw_rd_table)
    (id : positive) (node : rw_shared_node K Sort V) : option rw_rd_candidate :=
  match node with
  | RWSharedVar _ _ _ _ v => Some (RwRdCandidate id (rd_plain_nat_N (vc v)) 1%N)
  | RWSharedApp _ _ _ _ op children =>
    match rd_plain_shared_gather table children with
    | None => None
    | Some (cost, size) => Some (RwRdCandidate id
      (rd_plain_N_add (rd_plain_nat_N (oc op)) cost) (rd_plain_N_add 1%N size))
    end
  end.

Fixpoint rd_plain_scalar_pass {K Sort V} (vc : V -> nat) (oc : K -> nat) (old : rw_rd_table)
    (entries : list (positive * rw_shared_node K Sort V)) (table : rw_rd_table) : rw_rd_table :=
  match entries with
  | [] => table
  | (id, node) :: rest =>
    let next :=
      match rd_plain_scalar_node vc oc old id node with
      | None => table
      | Some candidate => Map.set positive_encoding id candidate table
      end in
    rd_plain_scalar_pass vc oc old rest next
  end.

Fixpoint rd_plain_scalar_rounds {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (entries : list (positive * rw_shared_node K Sort V)) (rounds : positive)
    (table : rw_rd_table) : rw_rd_table :=
  match rounds with
  | xH => rd_plain_scalar_pass vc oc table entries table
  | xO p =>
    let middle := rd_plain_scalar_rounds vc oc entries p table in
    rd_plain_scalar_rounds vc oc entries p middle
  | xI p =>
    let first := rd_plain_scalar_pass vc oc table entries table in
    let middle := rd_plain_scalar_rounds vc oc entries p first in
    rd_plain_scalar_rounds vc oc entries p middle
  end.

Definition rd_plain_scalar_observe {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) : option (N * N) :=
  if rw_shared_validate dag then
    let entries := Map.elements (rw_shared_nodes K Sort V dag) in
    match length entries with
    | 0 => None
    | S count =>
      let table := rd_plain_scalar_rounds vc oc entries (rd_plain_nat_positive count) Map.empty in
      option_map (fun candidate => (rw_rd_cost candidate, rw_rd_size candidate))
        (Map.get positive_encoding (rw_shared_root K Sort V dag) table)
    end
  else None.

(** Binary cost sums every occurrence in the expanded tree without unfolding the shared DAG. *)
Definition rw_shared_tree_cost_binary {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) : option N :=
  option_map fst (rd_plain_scalar_observe vc oc dag).

(** Binary size uses the same fixed source pass and retains repeated child occurrences. *)
Definition rw_shared_tree_size_binary {K Sort V} (dag : rw_shared_tree K Sort V) : option N :=
  option_map snd (rd_plain_scalar_observe (fun _ => 0) (fun _ => 0) dag).

(** Unary cost converts the actual binary tree objective only after a successful observation. *)
Definition rw_shared_tree_cost {K Sort V} (vc : V -> nat) (oc : K -> nat)
    (dag : rw_shared_tree K Sort V) : option nat :=
  option_map rd_plain_N_nat (rw_shared_tree_cost_binary vc oc dag).
