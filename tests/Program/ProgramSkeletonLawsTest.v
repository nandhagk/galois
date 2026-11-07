(** * Skeleton laws on control fixtures

    Concrete skeletons exercise link laws, loop-head recognition and retained ranks.
    For example, a loop's body entry is a head and the loop's own entry is not.
    Builds on: ProgramSkeletonLaws and ProgramStructuredTest. *)

From Stdlib Require Import List.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSkeleton ProgramSkeletonMachine
  ProgramSkeletonCfg ProgramSkeletonLaws ProgramLink.
From Galois.Tests.Program Require Import ProgramStructuredTest.
Import List.ListNotations.

Definition loop_break : Skeleton.stmt unit unit :=
  Skeleton.Block (Skeleton.Loop (Skeleton.Jump 1)).

Example loop_head_positive : is_loop_head loop_break (PEntry [DBody; DBody]) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_head_negative : is_loop_head loop_break (PEntry [DBody]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_head_boundary : is_loop_head loop_break (PEntry []) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example leaf_cached_exit :
  indexed_point_rank (skeleton_index (Skeleton.Atom tt : Skeleton.stmt unit unit))
    (PExit []) = Some 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example absent_cached_rank :
  indexed_point_rank (skeleton_index loop_break) (PEntry [DFirst]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_link :
  link_laws (skeleton_machine client loop_break) (Cfg.graph (skeleton_cfg loop_break))
    (skeleton_link loop_break client).
Proof.
  apply skeleton_link_laws.
Qed.

Example loop_cycles :
  cycles_cut (Cfg.graph (skeleton_cfg loop_break))
    (fun v => is_loop_head loop_break v = true).
Proof.
  apply skeleton_cuts.
Qed.
