(** * Actual callback occurrences in canonical solver subruns

    These observers select callback bodies from the same index, scheduler and engine captures.
    For example, a scheduler map lookup retains the encoder body for that exact lookup key.
    Builds on: canonical Collections, Graph and Fixpoint source models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs.
From Galois.Fixpoint Require Import FixpointAuditIndex FixpointAuditSchedule
  FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesCompile RulesAuditMaterializePrelude
  RulesAuditMaterializeNaiveCallbacks.
Import List.ListNotations.

(** * Callback frame projections *)

Definition mat_set_callback_frames {P} (event : audit_set_event P mat_frame) : list mat_frame :=
  match event with
  | AuditSetAdd _ _ _ _ encoded _ | AuditSetMem _ _ _ _ encoded _ |
    AuditSetRemove _ _ _ _ encoded _ => encoded
  | AuditSetFold _ _ => []
  end.

Definition mat_index_callback_frames {P}
    (event : fx_index_nested_event P (rconstraint P) mat_frame) : list mat_frame :=
  match event with
  | FxiTarget _ _ body | FxiSides _ _ body | FxiDeps _ _ body => body
  | FxiDistinctBuild _ _ body => flat_map mat_set_callback_frames body
  | FxiRead _ _ _ _ encoded _ | FxiWrite _ _ _ _ _ encoded _ => encoded
  | _ => []
  end.

Definition mat_dep_callback_frames {P}
    (event : fx_dep_event P (rconstraint P) mat_frame) : list mat_frame :=
  match event with
  | FxDepIndexEvent nested => mat_index_callback_frames nested
  | FxDepEncode _ _ body => body
  | _ => []
  end.

Definition mat_dep_map_frames {P A}
    (event : audit_map_event P A (fx_dep_event P (rconstraint P) mat_frame)) : list mat_frame :=
  match event with
  | AuditMapGet _ _ _ _ body _ | AuditMapSet _ _ _ _ _ body _ |
    AuditMapRemove _ _ _ _ body _ => flat_map mat_dep_callback_frames body
  end.

Definition mat_dep_set_frames {P}
    (event : audit_set_event P (fx_dep_event P (rconstraint P) mat_frame)) : list mat_frame :=
  match event with
  | AuditSetAdd _ _ _ _ body _ | AuditSetMem _ _ _ _ body _ |
    AuditSetRemove _ _ _ _ body _ => flat_map mat_dep_callback_frames body
  | AuditSetFold _ _ => []
  end.

Definition mat_prepare_callback_frames {P}
    (event : audit_prepare_source_event P (P * P) (fx_dep_event P (rconstraint P) mat_frame))
    : list mat_frame :=
  match event with
  | PrepareSourceOut _ _ body | PrepareSourceTarget _ _ body =>
      flat_map mat_dep_callback_frames body
  | PrepareSourceMap nested => mat_dep_map_frames nested
  | _ => []
  end.

Definition mat_dfs_callback_frames {P}
    (event : audit_dfs_nested_event P (P * P)
      (audit_graph_callback_capture P (P * P) (fx_dep_event P (rconstraint P) mat_frame)))
    : list mat_frame :=
  flat_map (fun capture =>
    match capture with
    | AuditGraphTargetCapture _ _ _ _ _ body | AuditGraphEncodeCapture _ _ _ _ _ body =>
        flat_map mat_dep_callback_frames body
    end) (snd event).

Definition mat_positions_callback_frames {P}
    (event : audit_rpo_schedule_event P (fx_dep_event P (rconstraint P) mat_frame))
    : list mat_frame :=
  match event with
  | RpoScheduleMap nested => mat_dep_map_frames nested
  | RpoScheduleSet nested => mat_dep_set_frames nested
  | _ => []
  end.

Definition mat_retreat_callback_frames {P}
    (event : audit_rpo_graph_event P (P * P) (fx_dep_event P (rconstraint P) mat_frame))
    : list mat_frame :=
  match event with
  | RpoGraphOut _ _ body | RpoGraphSource _ _ body | RpoGraphTarget _ _ body =>
      flat_map mat_dep_callback_frames body
  | RpoGraphRank nested => mat_dep_map_frames nested
  | RpoGraphSet nested => mat_dep_set_frames nested
  | _ => []
  end.

(** Every selected frame belongs to the one canonical scheduler capture supplied here. *)
Definition mat_rpo_callback_frames {P} (run : fx_rpo_result P (rconstraint P) mat_frame)
    : list mat_frame :=
  flat_map mat_dep_callback_frames (fx_rpo_build_events run) ++
  flat_map mat_prepare_callback_frames (fx_rpo_prepare_events run) ++
  flat_map mat_dfs_callback_frames (fx_rpo_dfs_events run) ++
  flat_map mat_positions_callback_frames (fx_rpo_position_events run) ++
  flat_map mat_retreat_callback_frames (fx_rpo_retreat_events run).

Definition mat_naive_body_callback_frames {P} (event : mat_naive_body_event P) : list mat_frame :=
  match event with
  | MatNaiveLocal local => [local]
  | MatNaiveScheduleQuery nested => mat_positions_callback_frames nested
  end.

Definition mat_naive_bodies_callback_frames {P}
    (bodies : list (list (list (mat_naive_body_event P)))) : list mat_frame :=
  flat_map mat_naive_body_callback_frames (concat (concat bodies)).
