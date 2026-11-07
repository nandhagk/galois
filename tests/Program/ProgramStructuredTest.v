(** * A structured source language

    A small language exercises atoms, sequencing and loops with relative jumps.
    For example, break zero inside a loop lowers to jump one inside two labels.
    Builds on: ProgramStructured. *)

From Stdlib Require Import List.
From Galois.Program Require Import ProgramSemantics ProgramSkeleton ProgramSkeletonMachine
  ProgramStructured.
Import List.ListNotations.

Inductive language :=
  | Tick
  | Pair (a b : language)
  | Repeat (body : language)
  | Break (n : nat)
  | Continue (n : nat).

Definition shape (s : language) : Shape language unit unit :=
  match s with
  | Tick => ShAtom tt
  | Pair a b => ShSeq a b
  | Repeat a => ShLoop a
  | Break n => ShBreak n
  | Continue n => ShContinue n
  end.

Fixpoint lower (s : language) : Skeleton.stmt unit unit :=
  match s with
  | Tick => Skeleton.Atom tt
  | Pair a b => Skeleton.Seq (lower a) (lower b)
  | Repeat a => Skeleton.Block (Skeleton.Loop (lower a))
  | Break n => Skeleton.Jump (2 * n + 1)
  | Continue n => Skeleton.Jump (2 * n)
  end.

Definition lowering := Lowering.Make shape lower.

Example lowering_correct : lowering_laws lowering.
Proof.
  constructor; intros []; reflexivity.
Qed.

Definition client : skeleton_client unit unit nat unit :=
  SkeletonClient (fun st => st = 0)
    (fun _ st l st' => l = [tt] /\ st' = S st)
    (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => Some true) (fun _ _ => None) (fun _ _ st st' => st' = st).

Example client_jump_laws : source_jump_laws client.
Proof.
  intros p n st st'; reflexivity.
Qed.

Definition program := Pair Tick (Repeat (Break 0)).

Example source_initial_pair :
  match_state lowering program (Run program [] 0) (Go [] [] 0).
Proof.
  apply match_run, sc_root.
Qed.

Example loop_break_labels : labels_ok 0 (lower program) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_out_of_range_break :
  labels_ok 0 (lower (Repeat (Break 1))) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example boundary_atom : labels_ok 0 (lower Tick) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example source_bisimulation :
  bisimulation (source_machine lowering client program) (source_endings lowering client)
    (skeleton_machine client (lower program)) (skeleton_endings (lower program) client)
    (match_state lowering program).
Proof.
  apply source_skeleton_bisimulation; [exact lowering_correct|exact client_jump_laws].
Qed.

Example invalid_break_still_bisimulates :
  bisimulation (source_machine lowering client (Break 0)) (source_endings lowering client)
    (skeleton_machine client (lower (Break 0))) (skeleton_endings (lower (Break 0)) client)
    (match_state lowering (Break 0)).
Proof.
  apply source_skeleton_bisimulation; [exact lowering_correct|exact client_jump_laws].
Qed.

Definition changing_jump_client : skeleton_client unit unit nat unit :=
  SkeletonClient (fun st => st = 0)
    (fun _ st l st' => l = [] /\ st' = st)
    (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => Some true) (fun _ _ => None) (fun _ _ st st' => st' = S st).

Example rejects_store_changing_jump : ~ source_jump_laws changing_jump_client.
Proof.
  intro Hjump.
  assert (Heffect : jump_effect changing_jump_client [] 0 0 1) by reflexivity.
  discriminate (proj1 (Hjump [] 0 0 1) Heffect).
Qed.
