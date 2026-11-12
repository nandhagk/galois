(** * Worklist widening delays

    A product lattice distinguishes joining from widening at a head.
    For example, delay zero widens the first change.
    Builds on: Fixpoint.Worklist and Fixpoint.Policy. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Base Require Import Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Policy Worklist.
Import List.ListNotations.

Module PairOps <: WLATTICE_OPS.
  Definition t := (bool * bool)%type.
  Definition leb a b := implb (fst a) (fst b) && implb (snd a) (snd b).
  Definition bot := (false, false).
  Definition is_bot a := negb (fst a) && negb (snd a).
  Definition join a b := (fst a || fst b, snd a || snd b).
  Definition wparam := unit.
  Definition widen (_ : unit) (_ _ : t) := (true, true).
  Definition narrow a b := (fst a && fst b, snd a && snd b).
End PairOps.
Module One <: SYSTEM_OPS PairOps.
  Definition prog := unit.
  Definition key := positive.
  Definition row := positive.
  Definition frame := unit.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : unit) := [1]%positive.
  Definition target (_ : unit) (r : positive) := r.
  Definition start (_ : unit) (_ : positive) : query key PairOps.t unit := Ret (true, false).
  Definition resume (_ : unit) (_ : unit) (a : PairOps.t) : query key PairOps.t unit := Ret a.
  Definition deps (_ : unit) (_ : positive) : list positive := [].
  Definition sides (_ : unit) (_ : positive) : list positive := [].
End One.
Module P := PolicyCode PairOps.
Module W := WorklistCode PairOps One P HeapCode.
Definition pol delay : policy unit :=
  Policy unit PTrieCode.empty (PTrieCode.set 1%positive (HeadCfg delay 0) PTrieCode.empty) tt 0.
Definition observe delay :=
  match W.run tt (pol delay) 2%N with
  | Solved m => look_or One.key_code PairOps.bot m 1%positive
  | _ => (false, false)
  end.

Example zero_delay_widens_first_change : observe 0%N = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example positive_delay_joins_first_change : observe 1%N = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.
