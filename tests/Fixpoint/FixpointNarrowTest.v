(** * Simultaneous narrowing clients

    Actual narrowing passes distinguish frozen reads, accepted decrease and rejected candidates.
    For example, lowering a negated read invalidates a previously safe output.
    Builds on: FixpointNarrow and the boolean lattice. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAnalysis FixpointSolver FixpointNarrow.
Import List.ListNotations Cost.Notations.

Module NarrowTest.

Definition lat : lattice bool :=
  of_pure implb false orb orb (fun _ b => b).

Definition accepted : System.t nat nat bool :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then
      Query.Side 2 false (Query.Ret false) else Query.Ask 0 (fun b => Cost.ret (Query.Ret b)))).

Definition rejected : System.t nat nat bool :=
  System.Make [0; 1] (fun c => Cost.ret c)
    (fun c => Cost.ret (if Nat.eqb c 0 then
      Query.Ask 1 (fun b => Cost.ret (Query.Ret (negb b))) else Query.Ret false)).

Definition declarations (S : System.t nat nat bool) : System.static S :=
  System.Static (fun _ => Cost.ret [0; 1]) (fun _ => Cost.ret [2]).

Definition analysis S : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding lat S (declarations S) (Policy.flat nat).

Definition old : assignment nat bool :=
  Map.of_list nat_encoding [(0, true); (1, true); (2, true); (99, true)].

Definition observe m := map (lookup nat_encoding lat m) [0; 1; 2; 99; 100].

Example simultaneous_old_reads :
  observe (Narrow.pass (analysis accepted) old) = [false; true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example two_checked_passes :
  observe (Narrow.checked (analysis accepted) 2 old) = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example broken_candidate_is_discarded :
  check_post lat rejected (lookup nat_encoding lat old) = true /\
  check_post lat rejected (lookup nat_encoding lat (Narrow.pass (analysis rejected) old)) =
    false /\
  Narrow.checked (analysis rejected) 1 old = old.
Proof.
  vm_compute; auto.
Qed.

Example zero_rounds : Narrow.checked (analysis accepted) 0 old = old.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty : System.t nat nat bool :=
  System.Make [] (fun c => Cost.ret c) (fun _ => Cost.ret (Query.Ret false)).

Example empty_keeps_unrelated : Narrow.pass (analysis empty) old = old.
Proof.
  vm_compute; reflexivity.
Qed.

(** This candidate producer checks its output, so its soundness holds for arbitrary analyses. *)
Definition produce_c (a : Analysis.t nat nat bool) (_ : positive) :
    Cost.t (Outcome.t nat bool (assignment nat bool)) :=
  let* safe := check_post_c (Analysis.lat a) (Analysis.system a)
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) old) in
  Cost.ret (if safe then Outcome.Solved old else Outcome.Rejected Reason.Check_failed).

Definition producer : Solver.t nat nat bool := Solver.Make produce_c.

Theorem producer_sound a fuel m :
  Analysis.laws a -> Solver.run producer a fuel = Outcome.Solved m ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros _ Hrun.
  assert (Heq : Solver.run producer a fuel =
    if check_post (Analysis.lat a) (Analysis.system a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) old)
    then Outcome.Solved old else Outcome.Rejected Reason.Check_failed).
  { change (Cost.value (produce_c a fuel) =
      if check_post (Analysis.lat a) (Analysis.system a)
        (lookup (Analysis.key_enc a) (Analysis.lat a) old)
      then Outcome.Solved old else Outcome.Rejected Reason.Check_failed).
    unfold produce_c; rewrite Cost.value_bind.
    rewrite (check_post_c_spec _ _ _ _) by reflexivity; reflexivity. }
  rewrite Heq in Hrun; destruct (check_post _ _ _) eqn:Hcheck; [|discriminate].
  injection Hrun as <-; apply check_post_sound, Hcheck.
Qed.

(** Importing the wrapper's soundness theorem discharges its substantive producer premise. *)
Theorem wrapper_client a fuel m :
  Analysis.laws a -> Solver.run (Narrow.wrap producer) a fuel = Outcome.Solved m ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  apply Narrow.narrow_wrap_sound, producer_sound.
Qed.

Definition policy : Policy.t nat :=
  Policy.Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret false) 0 2.

Definition wrapping S : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding lat S (declarations S) policy.

Example wrapper_lowers :
  match Solver.run (Narrow.wrap producer) (wrapping accepted) 1%positive with
  | Outcome.Solved m => observe m
  | _ => []
  end = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_lat : lattice bool :=
  {| leb_c := fun a b => Cost.step ;; leb_c lat a b;
     join_c := fun a b => Cost.step ;; join_c lat a b;
     widen_c := widen_c lat;
     narrow_c := fun a b => Cost.step ;; narrow_c lat a b;
     bot := false |}.

Definition charged : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding charged_lat accepted (declarations accepted) policy.

Example callbacks_retain_values :
  Narrow.pass charged old = Narrow.pass (wrapping accepted) old.
Proof.
  vm_compute; reflexivity.
Qed.

Example callbacks_add_ticks :
  (Cost.ticks (Narrow.pass_c (wrapping accepted) old) <
    Cost.ticks (Narrow.pass_c charged old))%N.
Proof.
  vm_compute; reflexivity.
Qed.

End NarrowTest.
Import NarrowTest.
