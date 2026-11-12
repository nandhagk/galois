(** * Self-dependent worklist rows

    A row that writes its own input must return to the queue.
    For example, the final empty queue probe consumes one unit of fuel.
    Builds on: Fixpoint.Worklist and Fixpoint.WorklistTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie Heap.
From Galois.Fixpoint Require Import Query SystemSig SolverSig WorklistSig Worklist.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

Module Self <: SYSTEM_OPS BoolOps.
  Definition prog := unit.
  Definition key := positive.
  Definition row := positive.
  Definition frame := unit.
  Definition key_code (x : positive) := x.
  Definition key_eqb := Pos.eqb.
  Definition rows (_ : unit) := [1]%positive.
  Definition target (_ : unit) (r : positive) := r.
  Definition start (_ : unit) (_ : positive) : query key bool unit := Ask 1%positive tt.
  Definition resume (_ : unit) (_ : unit) (_ : bool) : query key bool unit :=
    Side 1%positive true (Ret false).
  Definition deps (_ : unit) (_ : positive) := [1; 1]%positive.
  Definition sides (_ : unit) (_ : positive) := [1; 1]%positive.
End Self.
Module WSelf := WorklistCode BoolOps Self P HeapCode.

Example self_change_requeues_popped_row :
  match WSelf.step tt flat (WSelf.prepare tt flat) with
  | inl s => (trie_get 1%positive (ws_live s), trie_get 1%positive (ws_store s))
  | inr _ => (None, None)
  end = (Some tt, Some (1%positive, true)).
Proof.
  vm_compute; reflexivity.
Qed.

Example final_probe_is_required :
  (match WSelf.run tt flat 2%N with Solved _ => true | _ => false end,
   match WSelf.run tt flat 3%N with Solved _ => true | _ => false end) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

(* self_change_requeues_popped_row had (true, 1, true), including an evaluation
   counter. The new state exposes the queued occurrence and its stored value
   above. worklist_state has no evaluation-count field.
   final_probe_is_required had None at fuel two and Some [true; false; false;
   false] at fuel three. The Boolean solved projections above retain that boundary. *)
