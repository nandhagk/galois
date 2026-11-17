(** * Checked narrowing observations

    Each pass reads the previous assignment and checks the resulting candidate.
    For example, two passes propagate a decrease through a dependent row.

    Groups:
    - [PassTests] Candidates and results of one, two, three and zero narrowing rounds.
    - [DiscardTests] A candidate that fails the checker leaves the old assignment in place.
    - [EmptyTests] A system with no rows keeps the old assignment.
    - [WrapperTests] The certified analysis reports the outcome of its source.

    Builds on: Fixpoint.Narrow and Fixpoint.Check. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Check Narrow Certified.
Import List.ListNotations.

(** * Fixtures *)

Module BoolOps <: WLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition wparam := unit.
  Definition widen (_ : unit) := orb.
  Definition narrow (_ b : bool) := b.
End BoolOps.

(** Rows 1 and 2 ask other keys or write a side contribution, and the frame flag
    inverts the answer that comes back. *)
Module Rows <: SYSTEM_OPS BoolOps.
  Definition prog := bool.
  Definition key := positive.
  Definition row := positive.
  Definition frame := bool.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : bool) := [1; 2]%positive.
  Definition target (_ : bool) (r : positive) := r.
  Definition start (rejected : bool) (r : positive) : query key bool frame :=
    if rejected then
      if Pos.eqb r 1 then Ask 2%positive true else Ret false
    else if Pos.eqb r 1 then Side 3%positive false (Ret false)
    else Ask 1%positive false.
  Definition resume (_ : bool) (invert a : bool) : query key bool frame :=
    Ret (if invert then negb a else a).
  Definition deps (_ : bool) (_ : positive) := [1; 2]%positive.
  Definition sides (_ : bool) (_ : positive) := [3]%positive.
End Rows.
Module C := CheckCode BoolOps Rows.
Module N := NarrowCode BoolOps Rows C.

(** An assignment that binds keys 1, 2, 3 and 100 to their own values, all true. *)
Definition old := PTrieCode.set 1%positive (1%positive, true)
  (PTrieCode.set 2%positive (2%positive, true)
    (PTrieCode.set 3%positive (3%positive, true)
      (PTrieCode.set 100%positive (100%positive, true) PTrieCode.empty))).

(** The Boolean values that an assignment gives keys 1, 2, 3, 100 and 101. *)
Definition observe m := map (C.look m) [1; 2; 3; 100; 101]%positive.

(** * Passes *)

Module PassTests.

  (** A candidate reads the old values of all rows at once. *)
  Example candidate_reads_old_values_at_once :
    observe (N.narrow_candidate false old) = [false; true; false; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Two checked passes propagate a decrease through the dependent row. *)
  Example two_checked_passes_propagate_decrease :
    observe (N.refine false 2 old) = [false; false; false; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Three checked passes give the same values as two in this system. *)
  Example three_checked_passes_keep_decrease :
    observe (N.refine false 3 old) = [false; false; false; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Zero rounds return the old assignment unchanged. *)
  Example zero_rounds_keep_old : N.refine false 0 old = old.
  Proof.
    vm_compute; reflexivity.
  Qed.

End PassTests.

(** * Discard *)

Module DiscardTests.

  (** The old assignment passes the checker when the flag is true. *)
  Example old_assignment_passes_check : C.check true old = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The candidate of a pass with the flag true fails the checker. *)
  Example broken_candidate_fails_check : C.check true (N.narrow_candidate true old) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A pass whose candidate fails the checker returns the old assignment. *)
  Example broken_pass_keeps_old : N.narrow_pass true old = old.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A rejected first pass among three keeps the old assignment. *)
  Example rejected_pass_among_three_keeps_old : N.refine true 3 old = old.
  Proof.
    vm_compute; reflexivity.
  Qed.

End DiscardTests.

(** * Empty *)

Module EmptyTests.

  (** A system with no rows keeps every unrelated binding of the old assignment. *)
  Module EmptyRows <: SYSTEM_OPS BoolOps.
    Definition prog := Rows.prog.
    Definition key := Rows.key.
    Definition row := Rows.row.
    Definition frame := Rows.frame.
    Definition key_code := Rows.key_code.
    Definition key_eqb := Rows.key_eqb.
    Definition target := Rows.target.
    Definition start := Rows.start.
    Definition resume := Rows.resume.
    Definition deps := Rows.deps.
    Definition sides := Rows.sides.
    Definition rows (_ : bool) : list positive := [].
  End EmptyRows.
  Module EC := CheckCode BoolOps EmptyRows.
  Module EN := NarrowCode BoolOps EmptyRows EC.

  (** The candidate of an empty system keeps the old assignment. *)
  Example empty_system_keeps_old : EN.narrow_candidate false old = old.
  Proof.
    vm_compute; reflexivity.
  Qed.

End EmptyTests.

(** * Wrapper *)

(** A policy that narrows for the given number of rounds. *)
Definition pol n : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt n.

(** A source whose run exhausts its fuel and returns the old assignment. *)
Module Exhausted.
  Definition run (_ : bool) (_ : policy unit) (_ : N) := OutOfFuel old.
End Exhausted.

(** A source that rejects its policy. *)
Module RejectedSource.
  Definition run (_ : bool) (_ : policy unit) (_ : N) : outcome (kmap positive bool) :=
    Rejected Bad_policy.
End RejectedSource.

(** A source that returns the old assignment as solved. *)
Module Producer.
  Definition run (_ : bool) (_ : policy unit) (_ : N) := Solved old.
End Producer.

Module ExhaustedA := CertifiedCode BoolOps Rows Exhausted C N.
Module RejectedA := CertifiedCode BoolOps Rows RejectedSource C N.
Module ProducerA := CertifiedCode BoolOps Rows Producer C N.

(** * Wrapper *)

Module WrapperTests.

  (** A source that runs out of fuel makes the wrapper report OutOfFuel. *)
  Example exhausted_source_gives_out_of_fuel :
    ExhaustedA.analyze false (pol 2) 1%N = OutOfFuel old.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A rejected policy makes the wrapper report Bad_policy. *)
  Example rejected_source_gives_bad_policy :
    RejectedA.analyze false (pol 2) 1%N = Rejected Bad_policy.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The wrapper lowers the values that its source returns as solved. *)
  Example producer_result_is_lowered :
    match ProducerA.analyze false (pol 2) 1%N with Solved m => observe m | _ => [] end =
      [false; false; false; true; false].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The wrapper discards a candidate that breaks the checker and returns the old assignment. *)
  Example wrapper_discards_breaking_candidate :
    ProducerA.analyze true (pol 1) 1%N = Solved old.
  Proof.
    vm_compute; reflexivity.
  Qed.

End WrapperTests.
