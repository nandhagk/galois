(** * Cost monad examples

    These examples check results, exact tick counts and recursion through a costed query.

    For example, traversing a list of three elements charges three ticks.
    Builds on: Stdlib lists and binary arithmetic, Galois.Cost.CostMonad. *)

From Stdlib.Lists Require Import List.
From Stdlib.NArith Require Import NArith.
From Galois.Cost Require Import CostMonad.

Import List.ListNotations.
Import Cost.Notations.

(** Sequencing uses earlier results and adds charges across nested bindings. *)
Definition chain_c : Cost.t nat :=
  let* x := Cost.lift (fun _ => 2%N) S 3 in
  Cost.step ;;
  let* y := Cost.ret (x + 1) in
  Cost.tick 3 ;;
  Cost.ret (x * y).

Example chain_value : Cost.value chain_c = 20.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example chain_ticks : Cost.ticks chain_c = 6%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Counting a list charges once for each element. *)
Fixpoint length_c {A : Type} (xs : list A) : Cost.t nat :=
  match xs with
  | [] => Cost.ret 0
  | _ :: rest =>
    Cost.step ;;
    let* n := length_c rest in
    Cost.ret (S n)
  end.

Example length_value : Cost.value (length_c [false; true; false]) = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example length_ticks : Cost.ticks (length_c [false; true; false]) = 3%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example empty_length : (Cost.value (length_c ([] : list nat)),
    Cost.ticks (length_c ([] : list nat))) = (0, 0%N).
Proof.
  vm_compute.
  reflexivity.
Qed.

Example singleton_length :
  (Cost.value (length_c [false]), Cost.ticks (length_c [false])) = (1, 1%N).
Proof.
  vm_compute.
  reflexivity.
Qed.

Example bits_one : Cost.ticks (Cost.tick_bits 1) = 1%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example bits_two : Cost.ticks (Cost.tick_bits 2) = 2%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example bits_thirteen : Cost.ticks (Cost.tick_bits 13) = 4%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example zero_charge : (Cost.value (Cost.tick 0), Cost.ticks (Cost.tick 0)) = (tt, 0%N).
Proof.
  vm_compute.
  reflexivity.
Qed.

Example map_result_and_ticks :
  (Cost.value (Cost.map negb (Cost.lift (fun _ => 2%N) negb true)),
    Cost.ticks (Cost.map negb (Cost.lift (fun _ => 2%N) negb true))) = (true, 2%N).
Proof.
  vm_compute.
  reflexivity.
Qed.

Example false_result : Cost.value (Cost.ret false) = false.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example refinement_result :
  proj1_sig (Cost.value (Cost.refine (Cost.ret 3) (P := fun n => n = 3) eq_refl)) = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example refinement_ticks :
  Cost.ticks (Cost.refine (Cost.lift (fun _ => 2%N) S 2)
    (P := fun n => n = 3) eq_refl) = 2%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * First-day query nesting check *)

(** A query asks for a natural number and charges for constructing its next query. *)
Inductive qtree (A : Type) : Type :=
  | QRet (a : A)
  | QAsk (k : nat -> Cost.t (qtree A)).

Arguments QRet {A} a.
Arguments QAsk {A} k.

(** The runner descends structurally through the value projection of a continuation. *)
Fixpoint query_run_c {A : Type} (answer : nat) (q : qtree A) {struct q} : Cost.t A :=
  Cost.step ;;
  match q with
  | QRet a => Cost.ret a
  | QAsk k =>
    Cost.step ;;
    let next := k answer in
    (* Keep the recursive argument as a visible projection for the guard checker. *)
    let result := query_run_c answer (Cost.value next) in
    Cost.bind next (fun _ => result)
  end.

(** Two costed continuations use their answers to select different return values. *)
Definition query_fixture : qtree bool :=
  QAsk (fun n =>
    Cost.tick 2 ;;
    Cost.ret (QAsk (fun m =>
      Cost.tick 3 ;;
      Cost.ret (QRet (Nat.eqb (n + m) 4))))).

Example query_positive :
  (Cost.value (query_run_c 2 query_fixture), Cost.ticks (query_run_c 2 query_fixture)) =
    (true, 10%N).
Proof.
  vm_compute.
  reflexivity.
Qed.

Example query_negative : Cost.value (query_run_c 1 query_fixture) = false.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example query_return :
  (Cost.value (query_run_c 0 (QRet 7)), Cost.ticks (query_run_c 0 (QRet 7))) = (7, 1%N).
Proof.
  vm_compute.
  reflexivity.
Qed.
