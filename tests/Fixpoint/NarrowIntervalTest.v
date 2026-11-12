(** * Interval narrowing observations

    Narrowing reads frozen interval endpoints and retains unrelated keys.
    For example, the second checked pass restricts the shifted row to one through five.
    Builds on: Fixpoint.Narrow and Fixpoint.Certified. *)

From Stdlib Require Import List Bool ZArith PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Check Narrow Certified.
Import List.ListNotations.

Definition interval := option (Z * Z).
Definition span (lower upper : Z) : interval := Some (lower, upper).
Definition below (a b : interval) :=
  match a, b with
  | None, _ => true
  | Some _, None => false
  | Some (lo, hi), Some (lo', hi') => Z.leb lo' lo && Z.leb hi hi'
  end.
Definition hull (a b : interval) : interval :=
  match a, b with
  | None, other => other
  | other, None => other
  | Some (lo, hi), Some (lo', hi') => span (Z.min lo lo') (Z.max hi hi')
  end.
Definition shift (a : interval) : interval :=
  match a with None => None | Some (lo, hi) => span (lo + 1) (hi + 1) end.
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
Definition old := PTrieCode.set (Rows.key_code 0) (0, span (-10) 10)
  (PTrieCode.set (Rows.key_code 1) (1, span (-20) 20)
    (PTrieCode.set (Rows.key_code 99) (99, span (-7) 9) PTrieCode.empty)).
Definition observe m := map (C.look m) [0; 1; 99].
Module Coarse.
  Definition run (_ : unit) (_ : policy unit) (_ : N) := Solved old.
End Coarse.
Module A := CertifiedCode IntervalOps Rows Coarse C R.
Definition pol : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 2.
Definition wrapped := A.analyze tt pol 1%N.

Example coarse_input_is_post : C.check tt old = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example first_pass_reads_old_endpoints :
  observe (R.narrow_candidate tt old) = [span 0 4; span (-9) 11; span (-7) 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example first_pass_independent_full_check : C.check tt (R.narrow_candidate tt old) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_endpoint_decrease :
  match wrapped with Solved m => Some (observe m) | _ => None end =
    Some [span 0 4; span 1 5; span (-7) 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_strict_decrease_and_values :
  match wrapped with
  | Solved m =>
    let value := C.look m 1 in
    [below value (C.look old 1); below (C.look old 1) value;
     contains value 0; contains value 1; contains value 5; contains value 6]
  | _ => []
  end = [true; false; false; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_independent_full_check :
  match wrapped with Solved m => C.check tt m | _ => false end = true.
Proof.
  vm_compute; reflexivity.
Qed.
