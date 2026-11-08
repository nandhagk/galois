(** * Scoped-frame origins, point paths and checked histories

    These clients keep entry values separate from unavailable sentinels and test ordered folds.
    For example, a failed local precondition excludes a checked history with the same endpoint.
    Builds on: AnalysesSsaPreRename, AnalysesSsaPreFrameStep and AnalysesSsaPreContextTest. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep AnalysesSsaPreOperands.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreFamily AnalysesSsaPreFrameCache
  AnalysesSsaPreFrameInvariant AnalysesSsaPreFrameOrigins AnalysesSsaPreFrameTables AnalysesSsaPreFrameEnd.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest AnalysesSsaPreFrgTest.
Import List.ListNotations.

Example initial_scope_value :
  PreRename.top One.ctx (PreRename.initial_scope One.ctx [tt]) tt =
    PreRename.Frame (PreFrg.Operand (PreFrg.Initial tt) false) true.
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_scope_value :
  PreRename.top One.ctx PreRename.empty_scope tt =
    PreRename.Frame (PreFrg.Operand (PreFrg.Unavailable tt) false) false.
Proof.
  vm_compute; reflexivity.
Qed.

Example internal_projection :
  PreRename.project_edges One.ctx [tt; tt] = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example parallel_projection_order :
  PreRename.project_edges Parallel.ctx [true; false; true] = [true; false; true].
Proof.
  vm_compute; reflexivity.
Qed.

(** The projection theorem preserves the endpoints of the lawful single-block instruction path. *)
Example instruction_path_client :
  path One.bg tt (PreRename.project_edges One.ctx [tt]) tt.
Proof.
  apply (PreRename.project_path One.ctx One.laws false [tt] true).
  - now left.
  - exact (@path_cons bool unit One.pg tt [] true (or_introl eq_refl) (path_nil true)).
Qed.

Definition entry_graph : PreFrg.frg unit unit unit unit :=
  PreFrg.Frg [PreFrg.Unavailable tt; PreFrg.Initial tt]
    Map.empty Map.empty Map.empty Map.empty Map.empty PreFrg.Completed.

(** The initial value is nearest at the actual entry in an inhabited context. *)
Example initial_nearest :
  PreRename.nearest_version One.ctx entry_graph tt false (PreFrg.Initial tt).
Proof.
  split; [now right; left|]; split; [reflexivity|].
  exists false; split; [reflexivity|]; split; [apply dominates_refl|].
  intros other p Hother _ Hpoint _.
  destruct Hother as [<-|[<-|[]]].
  - rewrite PreFrg.version_point_equation in Hpoint; discriminate.
  - rewrite PreFrg.version_point_equation in Hpoint; inversion Hpoint; subst p.
    apply dominates_refl.
Qed.

Example entry_definition_domain :
  forall d, In d (PreFrg.versions entry_graph) -> PreFrg.definition_domain One.ctx d.
Proof.
  intros d [<-|[<-|[]]].
  - apply Pre.family_seed; now left.
  - split; [apply Pre.family_seed; now left|reflexivity].
Qed.

(** Reachable nearest-version uniqueness applies to the entry frame without a point-tree premise. *)
Example initial_nearest_unique :
  forall other, PreRename.nearest_version One.ctx entry_graph tt false other ->
    other = PreFrg.Initial tt.
Proof.
  intros other Hother.
  apply (PreRename.nearest_version_unique One.ctx entry_graph One.laws entry_definition_domain
    tt false other (PreFrg.Initial tt)).
  - apply reachable_entry; now left.
  - exact Hother.
  - exact initial_nearest.
Qed.

(** The entry-frame meaning carries a real nearest definition with no fictitious occurrence. *)
Example initial_frame_meaning :
  PreCoverage.frame_laws One.ctx entry_graph tt false
    (PreRename.Frame (PreFrg.Operand (PreFrg.Initial tt) false) true).
Proof.
  split; [reflexivity|]; split.
  - split; [discriminate|].
    intros [e [Hget _]]; vm_compute in Hget; discriminate.
  - split; [exact initial_nearest|].
    split; [|intros _; reflexivity].
    intros _ e Hlisted; vm_compute in Hlisted |- *; tauto.
Qed.

Definition add (n delta : nat) := n + delta.
Definition small (n delta : nat) := n + delta <= 3.

Example checked_fold_boundary :
  PreFrameStep.fold_enabled add small [1; 2] 0.
Proof.
  vm_compute; repeat split; auto.
Qed.

(** The checked-history theorem applies to the actual ordered fold and its enabled states. *)
Example checked_history_client :
  PreFrameStep.history (PreFrameStep.checked_step add small) 0 [1; 2] 3.
Proof.
  apply (proj2 (PreFrameStep.checked_history_fold add small)).
  split; [exact checked_fold_boundary|reflexivity].
Qed.

Example rejected_checked_fold :
  ~ PreFrameStep.fold_enabled add small [2; 2] 0.
Proof.
  vm_compute; lia.
Qed.

(** The actual ordered diamond model has the internal immediate-dominance boundary
    used by transfer. *)
Example diamond_instruction_immediate :
  forall b, immediately_dominates Diamond.pg (b, Diamond.Body) (b, Diamond.After).
Proof.
  intro b; apply (PreCoverage.internal_immediate Diamond.ctx Diamond.laws
    (e := Diamond.Real b)).
  - apply (PreCoverage.instruction_edge_listed Diamond.ctx Diamond.laws (b := b)).
    + destruct b; vm_compute; tauto.
    + now right; left.
  - reflexivity.
Qed.

(** The supplied checked block tree induces the parent-end to child-entry point boundary. *)
Example diamond_scope_boundary :
  immediately_dominates Diamond.pg (Diamond.Entry, Diamond.After) (Diamond.Left, Diamond.Before).
Proof.
  apply (PreCoverage.block_parent_immediate Diamond.ctx Diamond.laws
    Diamond.Entry Diamond.Left (Diamond.Left, Diamond.Before) 1%positive 2%positive).
  - now left.
  - now right; left.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - reflexivity.
Qed.

(** The computed join phi is nearest at the actual post-parameter definition point. *)
Example diamond_phi_nearest :
  PreRename.nearest_version Diamond.ctx (PreOperands.build_frg Diamond.ctx) tt
    (Diamond.Join, Diamond.Body) (PreFrg.Phi Diamond.Join tt).
Proof.
  apply (PreRename.nearest_at_definition Diamond.ctx _ (PreFrg.Phi Diamond.Join tt)).
  - vm_compute; intuition congruence.
  - reflexivity.
Qed.

(** The actual kill-free diamond supports reuse of that same phi on every return-free path. *)
Example diamond_phi_reusable :
  PreRename.reusable Diamond.ctx (PreOperands.build_frg Diamond.ctx) tt
    (Diamond.Join, Diamond.Body) (PreFrg.Phi Diamond.Join tt).
Proof.
  split; [exact diamond_phi_nearest|].
  exists (Diamond.Join, Diamond.Body); split; [reflexivity|].
  intros es _ _; apply Forall_forall; intros e _; vm_compute; reflexivity.
Qed.

Definition diamond_data := PreFrg.PhiData (PreFamily.universe Diamond.ctx)
  (PreFrg.phi_sites_for Diamond.ctx (PreFamily.universe Diamond.ctx)).

Example diamond_data_actual : PreFrg.phi_sites Diamond.ctx = inr diamond_data.
Proof.
  exact (PreFrg.phi_sites_success Diamond.ctx Diamond.laws).
Qed.

Example diamond_data_laws : PreFrameCache.placement_laws Diamond.ctx diamond_data.
Proof.
  exact (PreFrameCache.placement_from_output Diamond.ctx Diamond.laws _ diamond_data_actual).
Qed.

(** The actual entry cache, rather than a separately supplied scope, establishes source provenance. *)
Example diamond_entry_source_client :
  PreFrameInvariant.scope_source Diamond.ctx diamond_data
    (PreRename.entry_scope (PreRename.prepare Diamond.ctx diamond_data)).
Proof.
  exact (PreFrameInvariant.entry_source Diamond.ctx diamond_data Diamond.laws diamond_data_laws).
Qed.

(** The same invariant survives the real ordered block transfer, with no output-correctness premise. *)
Example diamond_left_transfer_source_client :
  PreFrameInvariant.scope_source Diamond.ctx diamond_data
    (fst (PreRename.block Diamond.ctx (PreRename.prepare Diamond.ctx diamond_data) Diamond.Left
      (PreRename.entry_scope (PreRename.prepare Diamond.ctx diamond_data))
      PreRename.empty_accumulator)).
Proof.
  apply (PreFrameInvariant.block_source Diamond.ctx diamond_data Diamond.laws diamond_data_laws).
  exact diamond_entry_source_client.
Qed.

(** An available unavailable-sentinel frame violates the maintained availability distinction. *)
Example forged_available_rejected :
  ~ PreFrameInvariant.frame_source Diamond.ctx tt
    (PreRename.Frame (PreFrg.Operand (PreFrg.Unavailable tt) false) true).
Proof.
  intros [_ [_ Hnot]]; exact (Hnot eq_refl eq_refl).
Qed.

(** Incoming argument preparation supplies a named translation in the actual source bucket. *)
Example diamond_argument_cache_client :
  exists v id, Pre.translate Diamond.ctx Diamond.LJ tt = Some v /\
    Intern.find (Pre.eu (Pre.keys Diamond.ctx)) v
      (PreFrameCache.names Diamond.ctx diamond_data) = Some id /\
    In (Diamond.Left, PreRename.Argument (Diamond.Join, tt) Diamond.LJ v (Some id))
      (Index.find (Pre.eb (Pre.keys Diamond.ctx)) Diamond.Left
        (PreRename.arguments (PreRename.prepare Diamond.ctx diamond_data))).
Proof.
  apply (PreFrameCache.arguments_total Diamond.ctx diamond_data Diamond.laws diamond_data_laws).
  - apply (PreFrameCache.placement_sites Diamond.ctx diamond_data diamond_data_laws).
    pose proof Diamond.join_phi as Hjoin; rewrite diamond_data_actual in Hjoin.
    exact (proj1 Hjoin).
  - reflexivity.
  - vm_compute; tauto.
  - reflexivity.
Qed.

(** Actual local transfer advances full frame meaning across the singleton's parameter instruction. *)
Example singleton_instruction_frame_client :
  PreCoverage.frame_laws One.ctx entry_graph tt true
    (PreRename.Frame (PreFrg.Operand (PreFrg.Initial tt) false) true).
Proof.
  change (PreCoverage.frame_laws One.ctx entry_graph tt (Graph.target One.pg tt)
    (PreRename.Frame (PreFrg.Operand (PreFrg.Initial tt) (false || false))
      (true && negb (Pre.killed One.ctx tt tt)))).
  apply (PreFrameStep.frame_instruction One.ctx entry_graph One.laws).
  - intros e d Hget; cbn [entry_graph PreFrg.occurrences] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - vm_compute; now left.
  - reflexivity.
  - intros other [<-|[<-|[]]] _; rewrite PreFrg.version_point_equation; discriminate.
  - split; [discriminate|].
    intro Hget; cbn [entry_graph PreFrg.occurrences] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - exact initial_frame_meaning.
Qed.

(** A source block preserves a sibling edge's occurrence and fresh bit through the actual transfer. *)
Example diamond_sibling_table_client :
  let index := PreRename.prepare Diamond.ctx diamond_data in
  let frames := PreRename.entry_scope index in
  let left_output := snd (PreRename.block Diamond.ctx index Diamond.Left frames
    PreRename.empty_accumulator) in
  PreFrameTables.stamp Diamond.ctx (Diamond.Real Diamond.Left)
    (snd (PreRename.block Diamond.ctx index Diamond.Right frames left_output)) =
  PreFrameTables.stamp Diamond.ctx (Diamond.Real Diamond.Left) left_output.
Proof.
  cbn zeta; apply (PreFrameTables.block_other Diamond.ctx Diamond.laws).
  - apply PreFrameEnd.block_wf; apply PreFrameEnd.empty_accumulator_wf.
  - vm_compute; intuition discriminate.
Qed.

(** The actual raw walk accounts for fresh origins in both occurrence and incoming-operand tables. *)
Example diamond_origin_accounting_client :
  PreFrameOrigins.output_origins Diamond.ctx
    (PreRename.stop_output (PreRename.run Diamond.ctx (PreRename.prepare Diamond.ctx diamond_data))).
Proof.
  exact (PreFrameOrigins.run_prepared_origins Diamond.ctx diamond_data).
Qed.

(** Entry initialization establishes full frame meaning relative to the actual final diamond graph. *)
Example diamond_entry_meaning_client :
  PreCoverage.scope_laws Diamond.ctx (PreOperands.build_frg Diamond.ctx)
    (Diamond.Entry, Diamond.Before)
    (PreRename.entry_scope (PreRename.prepare Diamond.ctx diamond_data)).
Proof.
  apply (PreOperands.build_frg_entry_scope_laws Diamond.ctx Diamond.laws
    diamond_data diamond_data_actual Diamond.Entry (Diamond.Entry, Diamond.Before)).
  - now left.
  - reflexivity.
  - reflexivity.
Qed.

(** Every actual driver prefix owns its written table entries through visited source blocks. *)
Example diamond_prefix_table_owners_client :
  forall budget current,
    runs (PreRename.step_c Diamond.ctx (PreRename.prepare Diamond.ctx diamond_data)) budget
      (PreRename.initial (PreRename.prepare Diamond.ctx diamond_data)) (inl current) ->
    PreFrameTables.owned Diamond.ctx current.
Proof.
  intros budget current Hrun.
  exact (PreFrameTables.runs_owned Diamond.ctx Diamond.laws Hrun
    (PreFrameTables.initial_owned Diamond.ctx (PreRename.prepare Diamond.ctx diamond_data))).
Qed.
