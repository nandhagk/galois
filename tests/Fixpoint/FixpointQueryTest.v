(** * Query observations

    Computed examples retain nested continuation charges and ordered traces.
    For example, two asks choose a result using both answers.
    Builds on: FixpointQuery. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Fixpoint Require Import FixpointQuery.
Import List.ListNotations Cost.Notations.

Definition nested_query : Query.t nat nat :=
  Query.Ask 0 (fun n =>
    Cost.tick 2 ;;
    Cost.ret (Query.Side 2 n (Query.Ask 1 (fun m =>
      Cost.tick 3 ;; Cost.ret (Query.Ret (n + m)))))).

Example nested_trace :
  Query.run nested_query (fun x => if Nat.eqb x 0 then 2 else 3) =
    Query.Trace 5 [0; 1] [(2, 2)].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_ticks :
  Cost.ticks (Query.run_c (fun x => Cost.tick 4 ;; Cost.ret x) nested_query) = 21%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example other_answers : Query.eval nested_query (fun _ => 0) = 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example return_boundary :
  (Query.run (@Query.Ret nat bool false) (fun _ => true),
    Cost.ticks (Query.run_c (fun _ : nat => Cost.ret true) (Query.Ret false))) =
    (Query.Trace false [] [], 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example bulk_order :
  Query.run (ask_all [0; 1] (fun values =>
    side_all_c [(2, true); (2, false)] (Query.Ret (forallb (fun b => b) values))))
    (fun x => Nat.eqb x 0) = Query.Trace false [0; 1] [(2, true); (2, false)].
Proof.
  vm_compute; reflexivity.
Qed.

Example imported_bulk_nil {X A} (k : list A -> Cost.t (Query.t X A)) :
  ask_all_c [] k = (Cost.step ;; k []).
Proof.
  apply ask_all_c_nil.
Qed.

Example imported_bulk_cons {X A} x xs (k : list A -> Cost.t (Query.t X A)) :
  ask_all_c (x :: xs) k =
    (Cost.step ;;
      Cost.ret (Query.Ask x (fun a => ask_all_c xs (fun values => k (a :: values))))).
Proof.
  apply ask_all_c_cons.
Qed.

Definition selected_bulk : Query.t nat nat :=
  ask_all [0] (fun values =>
    Cost.tick (if Nat.eqb (hd 0 values) 3 then 7 else 2) ;;
    Cost.ret (Query.Ret (hd 0 values))).

Example selected_nonunit_bulk_continuation :
  (Query.run selected_bulk (fun _ => 3),
    Cost.ticks (Query.run_c (fun _ => Cost.ret 3) selected_bulk)) =
    (Query.Trace 3 [0] [], 12%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example other_nonunit_bulk_continuation :
  (Query.run selected_bulk (fun _ => 4),
    Cost.ticks (Query.run_c (fun _ => Cost.ret 4) selected_bulk)) =
    (Query.Trace 4 [0] [], 7%N).
Proof.
  vm_compute; reflexivity.
Qed.
