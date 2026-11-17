(** * Interval narrowing observations

    Narrowing reads frozen interval endpoints and retains unrelated keys.
    For example, the second checked pass restricts the shifted row to one through five.

    Groups:
    - [PassTests] One narrowing pass reads the old endpoints and passes the full check.
    - [WrappedTests] The certified result lowers the endpoints and keeps the checked values.

    Builds on: Fixpoint.Narrow and Fixpoint.Certified. *)

From Stdlib Require Import List Bool ZArith PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Check Narrow Certified.
Import List.ListNotations.

(** * Fixtures *)

(** An interval of integers, or the empty interval None. *)
Definition interval := option (Z * Z).

(** The interval from lower to upper. *)
Definition span (lower upper : Z) : interval := Some (lower, upper).

(** Interval inclusion, where the empty interval lies below every interval. *)
Definition below (a b : interval) :=
  match a, b with
  | None, _ => true
  | Some _, None => false
  | Some (lo, hi), Some (lo', hi') => Z.leb lo' lo && Z.leb hi hi'
  end.

(** The smallest interval that contains both arguments. *)
Definition hull (a b : interval) : interval :=
  match a, b with
  | None, other => other
  | other, None => other
  | Some (lo, hi), Some (lo', hi') => span (Z.min lo lo') (Z.max hi hi')
  end.

(** The interval moved up by one. *)
Definition shift (a : interval) : interval :=
  match a with None => None | Some (lo, hi) => span (lo + 1) (hi + 1) end.

(** Membership of an integer in an interval. *)
Definition contains (a : interval) (z : Z) :=
  match a with None => false | Some (lo, hi) => Z.leb lo z && Z.leb z hi end.

Module IntervalOps <: WLATTICE_OPS.
  Definition t := interval.
  Definition leb := below.
  Definition bot : t := None.
  Definition is_bot (a : t) := match a with None => true | _ => false end.
  Definition join := hull.
  Definition wparam := unit.
  Definition widen (_ : unit) := hull.
  Definition narrow (_ next : t) := next.
End IntervalOps.

(** Row 0 is the constant interval 0 to 4, and row 1 is row 0 moved up by one. *)
Module Rows <: SYSTEM_OPS IntervalOps.
  Definition prog := unit.
  Definition key := nat.
  Definition row := nat.
  Definition frame := unit.
  Definition key_code := NatKeyCode.encode.
  Definition key_eqb := Nat.eqb.
  Definition rows (_ : unit) := [0; 1].
  Definition target (_ : unit) (r : nat) := r.
  Definition start (_ : unit) r : query key interval unit :=
    if Nat.eqb r 0 then Ret (span 0 4) else Ask 0 tt.
  Definition resume (_ : unit) (_ : unit) a : query key interval unit := Ret (shift a).
  Definition deps (_ : unit) r := if Nat.eqb r 0 then [] else [0].
  Definition sides (_ : unit) (_ : nat) : list nat := [].
End Rows.
Module C := CheckCode IntervalOps Rows.
Module R := NarrowCode IntervalOps Rows C.

(** A coarse assignment with wide intervals for keys 0, 1 and 99. *)
Definition old := PTrieCode.set (Rows.key_code 0) (0, span (-10) 10)
  (PTrieCode.set (Rows.key_code 1) (1, span (-20) 20)
    (PTrieCode.set (Rows.key_code 99) (99, span (-7) 9) PTrieCode.empty)).

(** The values that an assignment gives keys 0, 1 and 99. *)
Definition observe m := map (C.look m) [0; 1; 99].

(** A solver that returns the old assignment as solved. *)
Module Coarse.
  Definition run (_ : unit) (_ : policy unit) (_ : N) := Solved old.
End Coarse.
Module A := CertifiedCode IntervalOps Rows Coarse C R.

(** A policy that narrows for two rounds. *)
Definition pol : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 2.

(** The certified result of the coarse solver with one unit of fuel. *)
Definition wrapped := A.analyze tt pol 1%N.

(** * Pass *)

Module PassTests.

  (** The coarse assignment passes the full checker before any narrowing. *)
  Example coarse_input_passes_check : C.check tt old = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** One narrowing pass takes its endpoints from the old assignment. *)
  Example first_pass_reads_old_endpoints :
    observe (R.narrow_candidate tt old) = [span 0 4; span (-9) 11; span (-7) 9].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The candidate of one narrowing pass passes the full checker. *)
  Example first_pass_candidate_passes_check :
    C.check tt (R.narrow_candidate tt old) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End PassTests.

(** * Wrapped *)

Module WrappedTests.

  (** The value of key 1 in the solved result, or None when the result is not solved. *)
  Definition wrapped_value : interval :=
    match wrapped with Solved m => C.look m 1 | _ => None end.

  (** The certified result lowers the endpoints of the solved assignment. *)
  Example wrapped_result_lowers_endpoints :
    match wrapped with Solved m => Some (observe m) | _ => None end =
      Some [span 0 4; span 1 5; span (-7) 9].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The lowered value of key 1 lies below its old value. *)
  Example wrapped_value_is_below_old : below wrapped_value (C.look old 1) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The old value of key 1 does not lie below the lowered value. *)
  Example old_value_is_not_below_wrapped : below (C.look old 1) wrapped_value = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The lowered value of key 1 excludes zero. *)
  Example wrapped_value_excludes_zero : contains wrapped_value 0 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The lowered value of key 1 includes one. *)
  Example wrapped_value_includes_one : contains wrapped_value 1 = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The lowered value of key 1 includes five. *)
  Example wrapped_value_includes_five : contains wrapped_value 5 = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The lowered value of key 1 excludes six. *)
  Example wrapped_value_excludes_six : contains wrapped_value 6 = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The certified result passes the full checker. *)
  Example wrapped_result_passes_check :
    match wrapped with Solved m => C.check tt m | _ => false end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End WrappedTests.
