(** * Query observations

    Queries resume explicit frames and retain side contribution order.
    For example, two reads select a sum and a side contribution.
    Builds on: Fixpoint.Query. *)

From Stdlib Require Import List Arith Bool.
From Galois.Fixpoint Require Import Query.
Import List.ListNotations.

Inductive frame :=
  | First
  | Second (n : nat).

Definition resume (f : frame) (a : nat) : query nat nat frame :=
  match f with
  | First => Side 2 a (Ask 1 (Second a))
  | Second n => Ret (n + a)
  end.

Definition nested_query : query nat nat frame := Ask 0 First.

(* The old trace was Trace 5 [0; 1] [(2, 2)]. The new result is
   Some (5, [(2, 2)]); the new interface does not expose the read trace. *)
Example nested_result :
  eval_query resume (fun x => if Nat.eqb x 0 then 2 else 3) 3 nested_query =
    Some (5, [(2, 2)]).
Proof.
  vm_compute; reflexivity.
Qed.

Example other_answers :
  eval_query resume (fun _ => 0) 3 nested_query = Some (0, [(2, 0)]).
Proof.
  vm_compute; reflexivity.
Qed.

(* The old trace was Trace false [] []. The new result is Some (false, []);
   the new interface does not expose the read trace. *)
Example return_boundary :
  eval_query (fun (_ : unit) (_ : bool) => Ret false) (fun _ : nat => true)
    1 (Ret false) = Some (false, []).
Proof.
  vm_compute; reflexivity.
Qed.

Definition bulk_resume (f : bool) (a : bool) : query nat bool bool :=
  if f then Ask 1 false else Side 2 true (Side 2 false (Ret false)).

(* The old trace was Trace false [0; 1] [(2, true); (2, false)].
   The new result is Some (false, [(2, true); (2, false)]); read traces are absent. *)
Example bulk_order :
  eval_query bulk_resume (fun x => Nat.eqb x 0) 3 (Ask 0 true) =
    Some (false, [(2, true); (2, false)]).
Proof.
  vm_compute; reflexivity.
Qed.

Example exhausted_query : eval_query resume (fun _ => 0) 1 nested_query = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition selected_resume (_ : unit) (a : nat) : query nat nat unit := Ret a.

(* selected_nonunit_bulk_continuation had Trace 3 [0] [] and 12 ticks.
   The value is retained. eval_query exposes no read trace or callback charge. *)
Example selected_nonunit_bulk_continuation :
  eval_query selected_resume (fun _ => 3) 2 (Ask 0 tt) = Some (3, []).
Proof.
  vm_compute; reflexivity.
Qed.

(* other_nonunit_bulk_continuation had Trace 4 [0] [] and 7 ticks.
   The value is retained. eval_query exposes no read trace or callback charge. *)
Example other_nonunit_bulk_continuation :
  eval_query selected_resume (fun _ => 4) 2 (Ask 0 tt) = Some (4, []).
Proof.
  vm_compute; reflexivity.
Qed.

(* imported_bulk_nil and imported_bulk_cons specified the retired ask_all_c
   constructor equations. Explicit frames replace its stored continuations. *)
