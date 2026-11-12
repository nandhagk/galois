(** * Worklist ordering and counter observations

    Priority values select row order and widening stops an increasing counter.
    For example, repeated row occurrences consume separate units of fuel.
    Builds on: Fixpoint.Worklist and Fixpoint.WorklistTest. *)

From Stdlib Require Import List Bool Arith PArith NArith.
From Galois.Base Require Import Trie Heap Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig Policy Worklist WorklistSig.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

Definition priority : policy unit := Policy unit
  (PTrieCode.set 3%positive 1%positive
    (PTrieCode.set 2%positive 2%positive
      (PTrieCode.set 1%positive 3%positive PTrieCode.empty)))
  PTrieCode.empty tt 0.

(* target_priority_changes_the_evaluation_order had
   (None, Some [true; true; false; false]) at fuel four.
   The new result is (None, None) because all four row occurrences consume fuel. *)
Example priority_old_fuel :
  (observe (W.run true flat 4%N), observe (W.run true priority 4%N)) =
    (None, None).
Proof.
  vm_compute; reflexivity.
Qed.

(* duplicate_initial_rows_do_not_duplicate_heap_entries had heap size 3.
   The new solver numbers row occurrences, so its initial live count is 4. *)
Example initial_occurrences : length (PTrieCode.elements (ws_live (W.prepare true flat))) = 4.
Proof.
  vm_compute; reflexivity.
Qed.

Example cycle_declared_output_keys :
  flat_map (fun r => Cycle.target true r :: Cycle.sides true r) (Cycle.rows true) =
    [1; 2; 3; 1; 1; 1]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

(* index_repeated_sides retained contributors [0; 2; 0] in IndexedTest.
   Its old readers_of 0 = [1] appears here with keys shifted by one.
   Reader lists use occurrence identifiers in the new solver. *)
Example cycle_reader_occurrences :
  (W.readers (W.prepare true flat) 1%positive,
   W.readers (W.prepare true flat) 2%positive) = ([2], [1; 4])%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Module Chain <: SYSTEM_OPS BoolOps.
  Definition prog := unit.
  Definition key := nat.
  Definition row := nat.
  Definition frame := unit.
  Definition key_code := NatKeyCode.encode.
  Definition key_eqb := Nat.eqb.
  Definition rows (_ : unit) := [0; 1; 2; 3; 4].
  Definition target (_ : unit) (r : nat) := r.
  Definition start (_ : unit) r : query nat bool unit :=
    if Nat.eqb r 0 then Ret true else Ask (Nat.pred r) tt.
  Definition resume (_ : unit) (_ : unit) (a : bool) : query nat bool unit := Ret a.
  Definition deps (_ : unit) r := if Nat.eqb r 0 then [] else [Nat.pred r].
  Definition sides (_ : unit) (_ : nat) : list nat := [].
End Chain.
Module CW := WorklistCode BoolOps Chain P HeapCode.

Example chain_counts_use_prepared_lists :
  (length (Chain.rows tt),
   fold_right Nat.add 0 (map (fun r => length (Chain.deps tt r)) (Chain.rows tt))) = (5, 4).
Proof.
  vm_compute; reflexivity.
Qed.

Example chain_exhausts_before_empty_probe :
  match CW.run tt flat 5%N with
  | OutOfFuel m => map (look_or Chain.key_code false m) [0; 1; 2; 3; 4]
  | _ => []
  end = [true; true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Module CounterOps <: WLATTICE_OPS.
  Definition t := option nat.
  Definition leb (a b : t) :=
    match a, b with
    | Some x, Some y => Nat.leb x y
    | None, Some _ => false
    | _, None => true
    end.
  Definition bot := Some 0.
  Definition is_bot (a : t) := match a with Some n => Nat.eqb n 0 | None => false end.
  Definition join (a b : t) :=
    match a, b with Some x, Some y => Some (Nat.max x y) | _, _ => None end.
  Definition wparam := unit.
  Definition widen (_ : unit) (_ _ : t) : t := None.
  Definition narrow (_ b : t) := b.
End CounterOps.
Module Counter <: SYSTEM_OPS CounterOps.
  Definition prog := unit.
  Definition key := positive.
  Definition row := positive.
  Definition frame := unit.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : unit) := [1]%positive.
  Definition target (_ : unit) (r : positive) := r.
  Definition start (_ : unit) (_ : positive) : query key CounterOps.t unit := Ask 1%positive tt.
  Definition resume (_ : unit) (_ : unit) (a : CounterOps.t) : query key CounterOps.t unit :=
    Ret (match a with Some n => Some (S n) | None => None end).
  Definition deps (_ : unit) (_ : positive) := [1]%positive.
  Definition sides (_ : unit) (_ : positive) : list positive := [].
End Counter.
Module CP := PolicyCode CounterOps.
Module KW := WorklistCode CounterOps Counter CP HeapCode.
Definition counter_policy (selected : bool) : policy unit := Policy unit PTrieCode.empty
  (if selected then PTrieCode.set 1%positive (HeadCfg 2%N 0) PTrieCode.empty
   else PTrieCode.empty) tt 0.

Example delayed_counter_cut_terminates :
  match KW.run tt (counter_policy true) 5%N with
  | Solved m => look_or Counter.key_code CounterOps.bot m 1%positive = None
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example uncut_counter_keeps_growing :
  match KW.run tt (counter_policy false) 8%N with OutOfFuel _ => true | _ => false end = true.
Proof.
  vm_compute; reflexivity.
Qed.
