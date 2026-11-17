(** * Worklist widening delays

    A product lattice distinguishes joining from widening at a head.
    For example, delay zero widens the first change.

    Groups:
    - [DelayTests] The value at a head after the first change, for each delay.
    - [OutputOrderTests] The stored value and the spent delay after one step.

    Builds on: Fixpoint.Worklist and Fixpoint.Policy. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Base Require Import Trie Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig WorklistSig Policy Worklist.
Import List.ListNotations.

(** * Fixtures *)

(** A pair of Boolean components, ordered and joined componentwise. *)
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

(** A system with one row that returns the pair (true, false). *)
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

(** A policy whose head at key 1 has the given delay. *)
Definition pol delay : policy unit :=
  Policy unit PTrieCode.empty (PTrieCode.set 1%positive (HeadCfg delay 0) PTrieCode.empty) tt 0.

(** The value that the solver stores at key 1 for the given delay. *)
Definition observe delay :=
  match W.run tt (pol delay) 2%N with
  | Solved m => look_or One.key_code PairOps.bot m 1%positive
  | _ => (false, false)
  end.

(** * Delay *)

Module DelayTests.

  (** A head with zero delay widens the first change to the top pair. *)
  Example zero_delay_widens_first_change : observe 0%N = (true, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A head with positive delay joins the first change instead of widening it. *)
  Example positive_delay_joins_first_change : observe 1%N = (true, false).
  Proof.
    vm_compute; reflexivity.
  Qed.

End DelayTests.

(** * Output order *)

(** A system whose row 1 writes a side contribution before its primary output. *)
Module OutputOrder <: SYSTEM_OPS PairOps.
  Definition prog := unit.
  Definition key := positive.
  Definition row := positive.
  Definition frame := unit.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : unit) := [1]%positive.
  Definition target (_ : unit) (r : positive) := r.
  Definition start (_ : unit) (_ : positive) : query key PairOps.t unit :=
    Side 1%positive (true, false) (Ret (true, true)).
  Definition resume (_ : unit) (_ : unit) (a : PairOps.t) : query key PairOps.t unit := Ret a.
  Definition deps (_ : unit) (_ : positive) : list positive := [].
  Definition sides (_ : unit) (_ : positive) := [1; 1]%positive.
End OutputOrder.
Module OW := WorklistCode PairOps OutputOrder P HeapCode.

Module OutputOrderTests.

  (** After one step, the stored value at key 1 is the primary output, not a side one. *)
  Example primary_output_is_stored :
    match OW.step tt (pol 2%N) (OW.prepare tt (pol 2%N)) with
    | inl s => look_or OutputOrder.key_code PairOps.bot (ws_store s) 1%positive
    | inr _ => (false, false)
    end = (true, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A side contribution below the head does not spend the delay, so one change is counted. *)
  Example primary_output_spends_one_change :
    match OW.step tt (pol 2%N) (OW.prepare tt (pol 2%N)) with
    | inl s =>
      match trie_get 1%positive (ws_counters s) with Some n => n | None => 0%N end
    | inr _ => 2%N
    end = 1%N.
  Proof.
    vm_compute; reflexivity.
  Qed.

End OutputOrderTests.
