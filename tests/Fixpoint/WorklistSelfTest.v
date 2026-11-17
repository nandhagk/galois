(** * Self-dependent worklist rows

    A row that writes its own input must return to the queue.
    For example, the final empty queue probe consumes one unit of fuel.

    Groups:
    - Fixtures: a system whose only row reads and writes itself.
    - Step: one step of the worklist requeues the popped row.
    - Run: the fuel that the final empty queue probe needs.

    Builds on: Fixpoint.Worklist and Fixpoint.WorklistTest. *)

From Stdlib Require Import List PArith NArith.
From Galois.Base Require Import Trie Heap.
From Galois.Fixpoint Require Import Query SystemSig SolverSig WorklistSig Worklist.
From Galois.Tests.Fixpoint Require Import WorklistTest.
Import List.ListNotations.

(** * Fixtures *)

(** A system whose row 1 writes its own input through a side contribution. *)
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

(** * Step *)

Module StepTests.

  (** A changed self row is queued again, and its new value is stored. *)
  Example self_change_requeues_row :
    match WSelf.step tt flat (WSelf.prepare tt flat) with
    | inl s => trie_get 1%positive (ws_live s)
    | inr _ => None
    end = Some tt.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The step stores the new value of the popped self row. *)
  Example self_change_stores_new_value :
    match WSelf.step tt flat (WSelf.prepare tt flat) with
    | inl s => trie_get 1%positive (ws_store s)
    | inr _ => None
    end = Some (1%positive, true).
  Proof.
    vm_compute; reflexivity.
  Qed.

End StepTests.

(** * Run *)

Module RunTests.

  (** Two units of fuel do not reach a solved result. *)
  Example two_units_are_not_solved :
    match WSelf.run tt flat 2%N with Solved _ => true | _ => false end = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Three units of fuel reach a solved result, because the final probe is paid for. *)
  Example three_units_are_solved :
    match WSelf.run tt flat 3%N with Solved _ => true | _ => false end = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End RunTests.
