(** * Query observations

    Queries resume explicit frames and retain side contribution order.
    For example, two reads select a sum and a side contribution.

    Groups:
    - Nested: a query that reads twice, and the fuel that it needs.
    - Return: a query that returns at once.
    - Bulk: side contributions and continuations that return values.

    Builds on: Fixpoint.Query. *)

From Stdlib Require Import List Arith Bool.
From Galois.Fixpoint Require Import Query.
Import List.ListNotations.

(** * Fixtures *)

(** The frames of the nested query: the first read, and the second read that keeps its answer. *)
Inductive frame :=
  | First
  | Second (n : nat).

(** * Nested *)

Module NestedTests.

  (** The resume function that the nested query uses. *)
  Definition resume (f : frame) (a : nat) : query nat nat frame :=
    match f with
    | First => Side 2 a (Ask 1 (Second a))
    | Second n => Ret (n + a)
    end.

  (** The query that asks key 0 and then continues with the First frame. *)
  Definition nested_query : query nat nat frame := Ask 0 First.

  (** A nested read returns the sum of its two answers and the side contribution. *)
  Example nested_read_returns_sum :
    eval_query resume (fun x => if Nat.eqb x 0 then 2 else 3) 3 nested_query =
      Some (5, [(2, 2)]).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Answers of zero give a zero sum with a zero side contribution. *)
  Example zero_answers_give_zero_sum :
    eval_query resume (fun _ => 0) 3 nested_query = Some (0, [(2, 0)]).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** With one unit of fuel, the nested query runs out and gives no result. *)
  Example exhausted_fuel_gives_none :
    eval_query resume (fun _ => 0) 1 nested_query = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

End NestedTests.

(** * Return *)

Module ReturnTests.

  (** A query that returns at once has no side contributions. *)
  Example bare_return_has_no_side_contributions :
    eval_query (fun (_ : unit) (_ : bool) => Ret false) (fun _ : nat => true)
      1 (Ret false) = Some (false, []).
  Proof.
    vm_compute; reflexivity.
  Qed.

End ReturnTests.

(** * Bulk *)

Module BulkTests.

  (** The resume function of the bulk query, which writes its side contributions in order. *)
  Definition bulk_resume (f : bool) (a : bool) : query nat bool bool :=
    if f then Ask 1 false else Side 2 true (Side 2 false (Ret false)).

  (** The resume function that returns its unit-typed answer as the value. *)
  Definition selected_resume (_ : unit) (a : nat) : query nat nat unit := Ret a.

  (** Side contributions keep the order in which the bulk query writes them. *)
  Example bulk_side_contributions_keep_order :
    eval_query bulk_resume (fun x => Nat.eqb x 0) 3 (Ask 0 true) =
      Some (false, [(2, true); (2, false)]).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A continuation with a nonunit answer returns that answer as its value. *)
  Example nonunit_continuation_returns_its_value :
    eval_query selected_resume (fun _ => 3) 2 (Ask 0 tt) = Some (3, []).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Another nonunit answer is likewise returned as the value. *)
  Example other_nonunit_continuation_returns_its_value :
    eval_query selected_resume (fun _ => 4) 2 (Ask 0 tt) = Some (4, []).
  Proof.
    vm_compute; reflexivity.
  Qed.

End BulkTests.
