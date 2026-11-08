(** * Prepared nested index probing

    Nested probing is the only join strategy. Each listed atom owns a bound-position index.
    For example, R(x,y), S(y,z) probes S's y bucket for each binding from R.
    A second strategy would need its own agreement proof.
    Builds on: DatalogFire, BaseMap and CostList. *)

From Stdlib Require Import List Bool PeanoNat NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire.
Import List.ListNotations Cost.Notations.

Module Join.

(** An index bucket retains row occurrences, including duplicate insertions. *)
Definition index := Map.t tuple (list tuple).

Definition index_get_c (idx : index) key := Map.find_or_c tuple_encoding [] key idx.
Definition index_get idx key := Cost.value (index_get_c idx key).

(** Selection rejects malformed row lengths and keeps exactly the marked positions. *)
Fixpoint select_c {A} (mask : list bool) (xs : list A) : Cost.t (option (list A)) :=
  Cost.step ;;
  match mask, xs with
  | [], [] => Cost.ret (Some [])
  | keep :: rest, x :: tail =>
    let* selected := select_c rest tail in
    Cost.ret (option_map (fun ys => if keep then x :: ys else ys) selected)
  | _, _ => Cost.ret None
  end.

Definition select {A} mask xs := Cost.value (@select_c A mask xs).

Definition bound_term_c (bound : list nat) t :=
  match t with
  | TConst _ => Cost.ret true
  | TVar v => existsb_c (fun w => Cost.ret (Nat.eqb v w)) bound
  end.

Definition bound_term bound t := Cost.value (bound_term_c bound t).

Definition variables_c ts :=
  filter_map_c (fun t =>
    Cost.ret (match t with TVar v => Some v | TConst _ => None end)) ts.

Definition variables ts := Cost.value (variables_c ts).

Record node (P : Type) : Type := Node {
  source : atom P;
  mask : list bool;
  key_terms : list term;
  table : index
}.

Arguments Node {P}.
Arguments source {P}.
Arguments mask {P}.
Arguments key_terms {P}.
Arguments table {P}.

(** Preparation stores the variable order and position mask once per atom occurrence. *)
Definition plan_state P := list (node P).

Definition index_add_c mask row (idx : index) :=
  let* selected := select_c mask row in
  match selected with
  | None => Cost.ret idx
  | Some key =>
    let* old := index_get_c idx key in
    Map.set_c tuple_encoding key (row :: old) idx
  end.

Definition index_add mask row idx := Cost.value (index_add_c mask row idx).

Definition extend_index_c mask rows idx :=
  fold_right_c (index_add_c mask) idx rows.

Definition extend_index mask rows idx := Cost.value (extend_index_c mask rows idx).

Fixpoint prepare_from_c {P} (bound : list nat) (ps : list (atom P))
    (env : P -> Cost.t relation) : Cost.t (plan_state P) :=
  match ps with
  | [] => Cost.ret []
  | a :: rest =>
    Cost.step ;;
    let* positions := map_c (bound_term_c bound) (args a) in
    let* keys := filter_c (bound_term_c bound) (args a) in
    Cost.step ;;
    let* rel := env (pred a) in
    let* rows := FinSet.elements_c (set_raw rel) in
    let* idx := extend_index_c positions rows Map.empty in
    let* vs := variables_c (args a) in
    let* next_bound := app_c vs bound in
    let* tail := prepare_from_c next_bound rest env in
    Cost.ret (Node a positions keys idx :: tail)
  end.

Definition prepare_c {P} (_ : program P) (ps : list (atom P)) env :=
  prepare_from_c [] ps env.
Definition prepare {P} prog ps env := Cost.value (@prepare_c P prog ps env).
Definition prepare_from {P} bound ps env := Cost.value (@prepare_from_c P bound ps env).

(** Each input binding performs one key probe and matches only that bucket's rows. *)
Definition probe_one_c {P} (n : node P) b acc :=
  let* key := instantiate_c b (key_terms n) in
  let* rows := index_get_c (table n) key in
  let* matches := filter_map_c (fun row => bind_terms_c (args (source n)) row b) rows in
  app_c matches acc.

Definition probe_c {P} (n : node P) bs := fold_right_c (probe_one_c n) [] bs.

Definition probe {P} n bs := Cost.value (@probe_c P n bs).

Fixpoint run_from_c {P} (plan : plan_state P) bs : Cost.t (list binding) :=
  match plan with
  | [] => Cost.ret bs
  | n :: rest =>
    Cost.step ;;
    let* next := probe_c n bs in run_from_c rest next
  end.

Definition run_from {P} plan bs := Cost.value (@run_from_c P plan bs).
Definition run_c {P} (plan : plan_state P) := run_from_c plan [[]].
Definition run {P} plan := Cost.value (@run_c P plan).

(** Indexed firing reuses the shared negative tests, head instantiation and relation constructor. *)
Definition fire_c {P} (r : rule P) env (plan : plan_state P) : Cost.t relation :=
  let* bindings := run_c plan in
  let* selected := filter_c (negative_ok_c r env) bindings in
  let* tuples := map_c (fun b => instantiate_c b (args (head r))) selected in
  set_of_list_c tuple_encoding tuples.

Definition fire {P} r env plan := Cost.value (@fire_c P r env plan).

(** Updating scans the supplied atom inventory and inserts only the supplied new rows.
    A reset discards an old frontier index without enumerating its rows. *)
Definition insert_rows_c {P} (reset : P -> Cost.t bool)
    (rows : P -> Cost.t (list tuple)) (plan : plan_state P) :=
  map_c (fun n =>
    Cost.step ;;
    let* clear := reset (pred (source n)) in
    Cost.step ;;
    let* batch := rows (pred (source n)) in
    let* idx := extend_index_c (mask n) batch (if clear then Map.empty else table n) in
    Cost.ret (Node (source n) (mask n) (key_terms n) idx)) plan.

Definition insert_rows {P} reset rows plan := Cost.value (@insert_rows_c P reset rows plan).

(** Work counts listed atom visits, input probes and bucket rows, including failed matches. *)
Fixpoint work_from {P} (plan : plan_state P) (bs : list binding) : N :=
  match plan with
  | [] => 0%N
  | n :: rest =>
    (1 + fold_right (fun b total =>
      1 + N.of_nat (length (index_get (table n)
        (map (inst (binding_value b)) (key_terms n)))) + total)%N 0%N bs +
      work_from rest (probe n bs))%N
  end.

Definition work {P} (plan : plan_state P) := work_from plan [[]].

Arguments prepare_c {P} prog ps env : simpl never.
Arguments run_c {P} plan : simpl never.
Arguments insert_rows_c {P} reset rows plan : simpl never.

End Join.
Import Join.
