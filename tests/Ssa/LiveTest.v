(** * Indexed liveness examples

    Reverse searches distinguish uses, kills and cyclic paths before grouping block entries.
    For example, a read of a variable in its own assignment stays live before that assignment.
    Builds on: Ssa.Live and Ssa.Present. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Key Trie.
From Galois.Ssa Require Import Lang LiveSig Present Live.
Import List.ListNotations.
Local Open Scope positive_scope.

Module Ops <: OPS.
  Definition K := unit.
  Definition G := unit.
  Definition C := unit.
  Definition eval (_ : unit) (_ : list unit) : option unit := None.
  Definition test (_ : unit) (_ : list unit) : option bool := None.
  Definition mov := tt.
End Ops.
Module Source.
  Definition t := func positive unit unit.
End Source.
Module View := PresentT Ops UnitKeyT UnitKeyT.
Module L := LiveCode Ops Source View.Q View.R BlockEdge PointEdge PointKey
  View.BC View.C View.U View.SP.

Definition straight : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [(2, tt, [9])] (Return [2]))].

Example follows_use_and_stops_at_definition : L.live_in straight = [(1, [9])].
Proof. vm_compute. reflexivity. Qed.

Definition same_variable : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [(9, tt, [9; 9])] (Return [9]))].

Example use_before_definition_and_duplicate_use : L.live_in same_variable = [(1, [9])].
Proof. vm_compute. reflexivity. Qed.

Definition parameter : Source.t :=
  Func positive unit unit 1 [] [(1, Block positive unit unit [9] [] (Return [9]))].

Example parameter_binding_kills_at_entry : L.live_in parameter = [(1, [])].
Proof. vm_compute. reflexivity. Qed.

Definition cyclic : Source.t :=
  Func positive unit unit 1 [9]
    [(1, Block positive unit unit [] [] (Jump 2 []));
     (2, Block positive unit unit [] [(7, tt, [9])] (Branch tt [7] 2 [] 3 []));
     (3, Block positive unit unit [] [] (Return [7]))].

Example loop_terminates_with_live_predecessors :
  L.live_in cyclic = [(1, [9]); (2, [9]); (3, [7])].
Proof. vm_compute. reflexivity. Qed.

Definition unused_cycle : Source.t :=
  Func positive unit unit 1 [] [(1, Block positive unit unit [] [] (Jump 1 []))].

Example unused_cycle_has_empty_live_row : L.live_in unused_cycle = [(1, [])].
Proof. vm_compute. reflexivity. Qed.

Example one_non_killing_parallel_edge_allows_propagation :
  live_killed (live_kill_add 1 2 [] (live_kill_add 1 2 [9] Empty)) 1 2 9 = false.
Proof. vm_compute. reflexivity. Qed.

Example all_parallel_edges_kill :
  live_killed (live_kill_add 1 2 [9; 8] (live_kill_add 1 2 [9] Empty)) 1 2 9 = true.
Proof. vm_compute. reflexivity. Qed.
