(** * Actual scoped graph output and raw failure outcomes

    The diamond selects its left computation and retains an unavailable right incoming operand.
    For example, the join occurrence selects its phi while the two edge identities stay distinct.
    Builds on: AnalysesSsaPreOperands and the lawful diamond fixture. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreOperands
  AnalysesSsaPreFrameInvariant AnalysesSsaPreFrameStep
  AnalysesSsaPreFrameWalk AnalysesSsaPreFrameEdges AnalysesSsaPreFrameWf.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest AnalysesSsaPreFrgTest.
Import List.ListNotations.

Example singleton_completed :
  PreFrg.status (PreOperands.build_frg One.ctx) = PreFrg.Completed.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_completed :
  PreFrg.status (PreOperands.build_frg Diamond.ctx) = PreFrg.Completed.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_phi :
  FinSet.mem (PreFrg.phi_encoding Diamond.ctx) (Diamond.Join, tt)
    (PreFrg.phis (PreOperands.build_frg Diamond.ctx)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_occurrences :
  Map.get Diamond.edge_enc (Diamond.Real Diamond.Left)
    (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) =
      Some (PreFrg.Fresh (Diamond.Real Diamond.Left) tt) /\
  Map.get Diamond.edge_enc (Diamond.Real Diamond.Join)
    (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) =
      Some (PreFrg.Phi Diamond.Join tt).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example diamond_incoming_operands :
  Map.get (PreFrg.link_encoding Diamond.ctx) ((Diamond.Join, tt), Diamond.LJ)
    (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) =
      Some (PreFrg.Operand (PreFrg.Fresh (Diamond.Real Diamond.Left) tt) true) /\
  Map.get (PreFrg.link_encoding Diamond.ctx) ((Diamond.Join, tt), Diamond.RJ)
    (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) =
      Some (PreFrg.Operand (PreFrg.Unavailable tt) false).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example diamond_fresh_flags :
  FinSet.mem Diamond.edge_enc (Diamond.Real Diamond.Left)
    (PreFrg.fresh (PreOperands.build_frg Diamond.ctx)) = true /\
  FinSet.mem Diamond.edge_enc (Diamond.Real Diamond.Join)
    (PreFrg.fresh (PreOperands.build_frg Diamond.ctx)) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example diamond_used_phi_is_safe :
  FinSet.mem (PreFrg.phi_encoding Diamond.ctx) (Diamond.Join, tt)
    (PreFrg.unsafe (PreOperands.build_frg Diamond.ctx)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition diamond_index :=
  match PreFrg.phi_sites Diamond.ctx with
  | inl partial => PreRename.prepare Diamond.ctx (PreFrg.PhiData partial FinSet.empty)
  | inr data => PreRename.prepare Diamond.ctx data
  end.

Definition configure {B BE N E U} (index : PreRename.prepared B BE N E U) roots budget :=
  PreRename.Prepared (PreRename.eligible_family index) (PreRename.phi_keys index)
    (PreRename.entry_scope index) (PreRename.family_ids index) (PreRename.events index)
    (PreRename.exit_points index) (PreRename.phi_definitions index) (PreRename.arguments index)
    (PreRename.children index) (PreRename.parent_pairs index) roots budget.

(** Insufficient actual driver fuel is observable independently of semantic graph claims. *)
Example rename_exhaustion :
  PreRename.stop_status (PreRename.run Diamond.ctx
    (configure diamond_index (PreRename.root_ids diamond_index) 1%positive)) =
      PreFrg.RenameExhausted.
Proof.
  vm_compute; reflexivity.
Qed.

(** A malformed supplied task ID reaches the explicit missing-name outcome. *)
Example missing_block_name :
  PreRename.stop_status (PreRename.run Diamond.ctx
    (configure diamond_index [9%positive] 2%positive)) = PreFrg.MissingBlockName.
Proof.
  vm_compute; reflexivity.
Qed.

Definition malformed_client : Pre.client bool bool bool bool bool unit unit bool bool :=
  Pre.Client Parallel.points Parallel.ssa Parallel.expr
    (Pre.pure_c Parallel.client) (Pre.recomputed_c Parallel.client) [false] [false; true]
    (Pre.shape_c Parallel.client)
    (Cost.lift (fun _ => 1%N) (fun _ => [])) (Pre.eval Parallel.client)
    (Pre.translate_c Parallel.client) (Pre.initial_c Parallel.client)
    (Pre.exit_point_c Parallel.client).
Definition malformed_ctx :=
  Pre.Context malformed_client (Pre.keys Parallel.ctx) Parallel.prepared Parallel.prepared
    (Pre.dom Parallel.ctx).

(** A false shape-capacity client cannot silently turn exhausted discovery
    into completed construction. *)
Example discovery_exhaustion :
  PreFrg.status (PreOperands.build_frg malformed_ctx) = PreFrg.DiscoveryExhausted.
Proof.
  vm_compute; reflexivity.
Qed.

Definition unsafe_client :
    Pre.client Diamond.block Diamond.block_edge (Diamond.block * Diamond.stage) Diamond.edge
      unit unit unit nat unit :=
  Pre.Client Diamond.points Diamond.ssa Diamond.expr
    (Cost.lift (fun _ => 1%N) (fun _ => false)) (Pre.recomputed_c Diamond.client) [tt] []
    (Pre.shape_c Diamond.client) (Pre.operands_c Diamond.client) (Pre.eval Diamond.client)
    (Pre.translate_c Diamond.client) (Pre.initial_c Diamond.client)
    (Pre.exit_point_c Diamond.client).
Definition unsafe_ctx :=
  Pre.Context unsafe_client (Pre.keys Diamond.ctx) Diamond.blocks Diamond.point_graph Diamond.tree.

Example unsafe_laws : Pre.laws unsafe_ctx.
Proof.
  constructor.
  - constructor.
    + exact (Pre.params_nodup Diamond.ctx Diamond.shapes).
    + exact (Pre.occurrences_seeded Diamond.ctx Diamond.shapes).
    + exact (Pre.initials_in_family Diamond.ctx Diamond.shapes).
    + exact (Pre.finite_operands Diamond.ctx Diamond.shapes).
    + exact (Pre.shape_identity Diamond.ctx Diamond.shapes).
    + exact (Pre.shape_arity Diamond.ctx Diamond.shapes).
    + exact (Pre.closed_translation Diamond.ctx Diamond.shapes).
    + exact (Pre.translation_shape Diamond.ctx Diamond.shapes).
    + exact (Pre.translation_operands Diamond.ctx Diamond.shapes).
    + intros be [] [] H; discriminate.
  - destruct Diamond.graphs; constructor; assumption.
  - destruct Diamond.kills; constructor; assumption.
  - destruct Diamond.runtime; constructor; assumption.
Qed.

(** A lawful unsafe-expression client completes
    without making its recomputations eligible versions. *)
Example unsafe_expression_excluded :
  PreFrg.status (PreOperands.build_frg unsafe_ctx) = PreFrg.Completed /\
  PreFrg.versions (PreOperands.build_frg unsafe_ctx) = [] /\
  Map.get Diamond.edge_enc (Diamond.Real Diamond.Left)
    (PreFrg.occurrences (PreOperands.build_frg unsafe_ctx)) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The canonical-output theorem applies to the same actual diamond producer
    and all five indexes. *)
Example diamond_indexes_wf :
  Map.wf Diamond.edge_enc (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) /\
  FinSet.wf Diamond.edge_enc (PreFrg.fresh (PreOperands.build_frg Diamond.ctx)) /\
  FinSet.wf (PreFrg.phi_encoding Diamond.ctx) (PreFrg.phis (PreOperands.build_frg Diamond.ctx)) /\
  Map.wf (PreFrg.link_encoding Diamond.ctx) (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) /\
  FinSet.wf (PreFrg.phi_encoding Diamond.ctx) (PreFrg.unsafe (PreOperands.build_frg Diamond.ctx)).
Proof.
  exact (PreOperands.build_frg_indexes_wf Diamond.ctx).
Qed.

(** Version canonicality is proved for raw outcomes without an assumed graph-correctness result. *)
Example malformed_versions_nodup :
  NoDup (PreFrg.versions (PreOperands.build_frg malformed_ctx)).
Proof.
  exact (PreOperands.build_frg_versions_nodup malformed_ctx).
Qed.

(** The actual general completion theorem applies to the lawful diamond input. *)
Example diamond_completion_client :
  PreFrg.status (PreOperands.build_frg Diamond.ctx) = PreFrg.Completed.
Proof.
  exact (PreOperands.build_frg_completed Diamond.ctx Diamond.laws).
Qed.

Definition bad_parents := Map.of_list positive_encoding [(2, 3); (3, 2); (4, 1)]%positive.
Definition bad_tree := DomCheck.of_parents Diamond.blocks bad_parents.
Definition bad_tree_ctx :=
  Pre.Context Diamond.client (Pre.keys Diamond.ctx) Diamond.blocks Diamond.point_graph bad_tree.

Example rejected_parent_map : DomCheck.check Diamond.blocks bad_parents = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** A checker-rejected supplied tree makes the actual checked graph entry point unavailable. *)
Example rejected_builder : PreOperands.build_frg_checked bad_tree_ctx = None.
Proof.
  vm_compute; reflexivity.
Qed.

(** The checked caller boundary agrees with the same raw graph
    used by downstream semantic proofs. *)
Example accepted_builder_client :
  PreOperands.build_frg_checked Diamond.ctx = Some (PreOperands.build_frg Diamond.ctx).
Proof.
  exact (PreOperands.build_frg_checked_agrees Diamond.ctx Diamond.laws).
Qed.

Definition bad_capacity_client :
    Pre.client Diamond.block Diamond.block_edge (Diamond.block * Diamond.stage) Diamond.edge
      unit unit unit nat unit :=
  Pre.Client Diamond.points Diamond.ssa Diamond.expr
    (Pre.pure_c Diamond.client) (Pre.recomputed_c Diamond.client) [tt] []
    (Pre.shape_c Diamond.client)
    (Cost.lift (fun _ => 1%N) (fun _ => [tt])) (Pre.eval Diamond.client)
    (Pre.translate_c Diamond.client) (Pre.initial_c Diamond.client)
    (Pre.exit_point_c Diamond.client).
Definition bad_capacity_ctx :=
  Pre.Context bad_capacity_client (Pre.keys Diamond.ctx)
    Diamond.blocks Diamond.point_graph Diamond.tree.

(** Valid parents do not turn an exhausted raw expression-family construction
    into successful output. *)
Example checked_exhaustion :
  PreFrg.status (PreOperands.build_frg bad_capacity_ctx) = PreFrg.DiscoveryExhausted /\
  PreOperands.build_frg_checked bad_capacity_ctx = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Omitting a seeded operand from the finite value list violates the unchanged shape laws. *)
Example invalid_value_universe_rejected : ~ Pre.laws bad_capacity_ctx.
Proof.
  intro Hlaw.
  assert (Hfamily : Pre.family bad_capacity_ctx tt) by (apply Pre.family_seed; now left).
  pose proof (Pre.finite_operands bad_capacity_ctx (Pre.shapes bad_capacity_ctx Hlaw)
    tt Hfamily tt (or_introl eq_refl)) as Hbound.
  exact Hbound.
Qed.

(** The constructor-exact theorem excludes an initial version in the lawful diamond. *)
Example diamond_no_initial_client :
  ~ In (PreFrg.Initial tt) (PreFrg.versions (PreOperands.build_frg Diamond.ctx)).
Proof.
  intro Hin.
  destruct (proj1 (PreOperands.build_frg_versions_exact Diamond.ctx Diamond.laws
    (PreFrg.Initial tt)) Hin) as [_ [_ Hinitial]]; discriminate.
Qed.

(** Fresh membership uses the real source edge, recomputation and final fresh flag together. *)
Example diamond_fresh_membership_client :
  In (PreFrg.Fresh (Diamond.Real Diamond.Left) tt)
    (PreFrg.versions (PreOperands.build_frg Diamond.ctx)).
Proof.
  apply (proj2 (PreOperands.build_frg_versions_exact Diamond.ctx Diamond.laws
    (PreFrg.Fresh (Diamond.Real Diamond.Left) tt))).
  split; [vm_compute; tauto|]; split; [reflexivity|exact (proj1 diamond_fresh_flags)].
Qed.

(** Every actual selected occurrence has a source definition, not merely a canonical map key. *)
Example diamond_occurrence_source_client :
  forall e d, Map.get Diamond.edge_enc e
    (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) = Some d ->
      PreFrameInvariant.occurrence_source_at Diamond.ctx e d.
Proof.
  exact (PreOperands.build_frg_occurrence_sources Diamond.ctx Diamond.laws).
Qed.

(** Totality applies to every original diamond recomputation, not just the computed sample reads. *)
Example diamond_occurrence_total_client :
  forall e u, In e (Cfg.edges (Pre.point_cfg Diamond.ctx)) ->
    Pre.recomputed Diamond.ctx e = Some u -> Pre.pure Diamond.ctx u = true ->
      exists d, Map.get Diamond.edge_enc e
        (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) = Some d.
Proof.
  exact (PreOperands.build_frg_occurrence_total Diamond.ctx Diamond.laws).
Qed.

(** Created-list accounting puts every selected occurrence in the actual final version inventory. *)
Example diamond_selected_versions_client :
  forall e d, Map.get Diamond.edge_enc e
    (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) = Some d ->
    In d (PreFrg.versions (PreOperands.build_frg Diamond.ctx)).
Proof.
  exact (PreOperands.build_frg_occurrence_member Diamond.ctx Diamond.laws).
Qed.

(** The same accounting covers incoming selections, including the right-arm unavailable sentinel. *)
Example diamond_operand_versions_client :
  forall key op, Map.get (PreFrg.link_encoding Diamond.ctx) key
    (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) = Some op ->
    In (PreFrg.operand_version op) (PreFrg.versions (PreOperands.build_frg Diamond.ctx)).
Proof.
  exact (PreOperands.build_frg_operand_member Diamond.ctx Diamond.laws).
Qed.

(** Every stored incoming key belongs to a real phi and an actual edge targeting its block. *)
Example diamond_operand_domain_client :
  forall b u be op, Map.get (PreFrg.link_encoding Diamond.ctx) ((b, u), be)
    (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) = Some op ->
    FinSet.mem (PreFrg.phi_encoding Diamond.ctx) (b, u)
      (PreFrg.phis (PreOperands.build_frg Diamond.ctx)) = true /\
    In be (Cfg.edges (Pre.block_cfg Diamond.ctx)) /\ Graph.target Diamond.bg be = b.
Proof.
  exact (PreOperands.build_frg_operand_domain Diamond.ctx Diamond.laws).
Qed.

(** The phi-index theorem recovers the same four-clause source placement from actual output. *)
Example diamond_phi_source_client : PreFrg.phi_needed Diamond.ctx tt Diamond.Join.
Proof.
  exact (proj2 (proj2 (proj1
    (PreOperands.build_frg_phi_exact Diamond.ctx Diamond.laws Diamond.Join tt) diamond_phi))).
Qed.

(** The complete actual diamond driver carries full semantic frame meaning at each processed block. *)
Example diamond_full_frame_history_client :
  exists data labels, PreFrg.phi_sites Diamond.ctx = inr data /\
    let index := PreRename.prepare Diamond.ctx data in
    PreFrameStep.history
      (PreFrameWalk.checked_step Diamond.ctx data (g := PreOperands.build_frg Diamond.ctx))
      (inl (PreRename.initial index)) labels
      (Cost.value (iterate (PreRename.step_c Diamond.ctx index) (PreRename.walk_budget index)
        (PreRename.initial index))).
Proof.
  exact (PreOperands.build_frg_frame_history Diamond.ctx Diamond.laws).
Qed.

(** Parallel incoming edge identities keep their distinct point-edge representatives. *)
Example parallel_point_edge_index :
  Map.get bool_encoding false (PreFrameEdges.point_edge_index Parallel.ctx) = Some false /\
  Map.get bool_encoding true (PreFrameEdges.point_edge_index Parallel.ctx) = Some true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example singleton_no_crossing_edge :
  Map.get unit_encoding tt (PreFrameEdges.point_edge_index One.ctx) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example crossing_callback_charge :
  Cost.ticks (PreFrameEdges.edge_pair_c One.ctx tt) = 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The exact point-edge theorem applies to the original lawful diamond presentation. *)
Example diamond_point_edge_index_client :
  forall be e, Map.get Diamond.be_enc be (PreFrameEdges.point_edge_index Diamond.ctx) =
    Some e <->
    In e (Cfg.edges (Pre.point_cfg Diamond.ctx)) /\
    SsaPoints.block_edge_of Diamond.points e = Some be.
Proof.
  exact (PreFrameEdges.point_edge_index_exact Diamond.ctx Diamond.laws).
Qed.

(** The lawful diamond's full-history occurrence contract requires no semantic-result premise. *)
Example diamond_occurrence_exact_client :
  forall e u, In e (Cfg.edges (Pre.point_cfg Diamond.ctx)) ->
    Pre.recomputed Diamond.ctx e = Some u -> Pre.pure Diamond.ctx u = true ->
    exists d, Map.get (Pre.ee (Pre.keys Diamond.ctx)) e
      (PreFrg.occurrences (PreOperands.build_frg Diamond.ctx)) = Some d /\
      In d (PreFrg.versions (PreOperands.build_frg Diamond.ctx)) /\
      PreFrg.version_expr d = u /\
      (d = PreFrg.Fresh e u \/ PreRename.reusable Diamond.ctx
        (PreOperands.build_frg Diamond.ctx) u (Graph.source (Pre.pg Diamond.ctx) e) d).
Proof.
  exact (PreOperands.build_frg_occurrence_exact Diamond.ctx Diamond.laws).
Qed.

(** The lawful diamond's fresh flags decide the absence of every reusable source definition. *)
Example diamond_fresh_required_client :
  forall e u, In e (Cfg.edges (Pre.point_cfg Diamond.ctx)) ->
    Pre.recomputed Diamond.ctx e = Some u -> Pre.pure Diamond.ctx u = true ->
    (FinSet.mem (Pre.ee (Pre.keys Diamond.ctx)) e
      (PreFrg.fresh (PreOperands.build_frg Diamond.ctx)) = true <->
      ~ exists d, PreRename.reusable Diamond.ctx (PreOperands.build_frg Diamond.ctx)
        u (Graph.source (Pre.pg Diamond.ctx) e) d).
Proof.
  exact (PreOperands.build_frg_fresh_required Diamond.ctx Diamond.laws).
Qed.

(** Incoming selection uses the actual point-edge index and the final graph's reusable versions. *)
Example diamond_operand_selection_client :
  forall b u be op pe v,
    Map.get (PreFrg.link_encoding Diamond.ctx) ((b, u), be)
      (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) = Some op ->
    Map.get (Pre.ebe (Pre.keys Diamond.ctx)) be
      (PreFrameEdges.point_edge_index Diamond.ctx) = Some pe ->
    Pre.translate Diamond.ctx be u = Some v ->
    (PreFrg.operand_version op = PreFrg.Unavailable v <->
      ~ exists d, PreRename.reusable Diamond.ctx (PreOperands.build_frg Diamond.ctx)
        v (Graph.source (Pre.pg Diamond.ctx) pe) d) /\
    (PreFrg.operand_version op <> PreFrg.Unavailable v ->
      PreRename.reusable Diamond.ctx (PreOperands.build_frg Diamond.ctx)
        v (Graph.source (Pre.pg Diamond.ctx) pe) (PreFrg.operand_version op)).
Proof.
  exact (PreOperands.build_frg_operand_selection Diamond.ctx Diamond.laws).
Qed.

(** Incoming real-use bits use the same selected occurrences as the completed producer. *)
Example diamond_operand_real_use_client :
  forall b u be op pe,
    Map.get (PreFrg.link_encoding Diamond.ctx) ((b, u), be)
      (PreFrg.operands (PreOperands.build_frg Diamond.ctx)) = Some op ->
    Map.get (Pre.ebe (Pre.keys Diamond.ctx)) be
      (PreFrameEdges.point_edge_index Diamond.ctx) = Some pe ->
    (PreFrg.real_use op = true <->
      PreCoverage.real_use_at Diamond.ctx (PreOperands.build_frg Diamond.ctx)
        (Graph.source (Pre.pg Diamond.ctx) pe) (PreFrg.operand_version op)).
Proof.
  exact (PreOperands.build_frg_operand_real_use_exact Diamond.ctx Diamond.laws).
Qed.

Definition unused_phi_client :
    Pre.client Diamond.block Diamond.block_edge (Diamond.block * Diamond.stage) Diamond.edge
      unit unit unit nat unit :=
  Pre.Client Diamond.points Diamond.ssa Diamond.expr
    (Pre.pure_c Diamond.client)
    (Cost.lift (fun _ => 1%N)
      (fun e => match e with Diamond.Real Diamond.Left => Some tt | _ => None end))
    [tt] [] (Pre.shape_c Diamond.client) (Pre.operands_c Diamond.client) (Pre.eval Diamond.client)
    (Pre.translate_c Diamond.client) (Pre.initial_c Diamond.client) (Pre.exit_point_c Diamond.client).
Definition unused_phi_ctx :=
  Pre.Context unused_phi_client (Pre.keys Diamond.ctx)
    Diamond.blocks Diamond.point_graph Diamond.tree.

(** Removing the join's recomputation retains every supported expression and graph law. *)
Example unused_phi_laws : Pre.laws unused_phi_ctx.
Proof.
  constructor.
  - constructor.
    + exact (Pre.params_nodup Diamond.ctx Diamond.shapes).
    + intros e [] Hcomputed; now left.
    + exact (Pre.initials_in_family Diamond.ctx Diamond.shapes).
    + exact (Pre.finite_operands Diamond.ctx Diamond.shapes).
    + exact (Pre.shape_identity Diamond.ctx Diamond.shapes).
    + exact (Pre.shape_arity Diamond.ctx Diamond.shapes).
    + exact (Pre.closed_translation Diamond.ctx Diamond.shapes).
    + exact (Pre.translation_shape Diamond.ctx Diamond.shapes).
    + exact (Pre.translation_operands Diamond.ctx Diamond.shapes).
    + exact (Pre.translation_pure Diamond.ctx Diamond.shapes).
  - destruct Diamond.graphs; constructor; assumption.
  - constructor.
    + exact (Pre.kill_operand Diamond.ctx Diamond.kills).
    + exact (Pre.def_home Diamond.ctx Diamond.kills).
    + exact (Pre.cross_no_defs Diamond.ctx Diamond.kills).
    + intros e [] Hcomputed; destruct e as [owner|owner|be]; try destruct owner;
        vm_compute in Hcomputed; try discriminate.
      split; [reflexivity|intros b Hbad; discriminate].
  - destruct Diamond.runtime; constructor; assumption.
Qed.

(** The unused join phi becomes unsafe at its exit while the used-phi control stays safe. *)
Example unused_phi_exit_is_unsafe :
  FinSet.mem (PreFrg.phi_encoding unused_phi_ctx) (Diamond.Join, tt)
    (PreFrg.phis (PreOperands.build_frg unused_phi_ctx)) = true /\
  FinSet.mem (PreFrg.phi_encoding unused_phi_ctx) (Diamond.Join, tt)
    (PreFrg.unsafe (PreOperands.build_frg unused_phi_ctx)) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Module Kill.

Definition definitions e :=
  match e with Diamond.Real Diamond.Right => [tt] | _ => [] end.
Definition vars := Vars.of_pure Diamond.pc unit_encoding (fun _ => []) definitions (fun _ => []).
Definition points :=
  SsaPoints.of_pure vars Diamond.bc (SsaPoints.points_in_block Diamond.points)
    (SsaPoints.instruction_edges Diamond.points) (SsaPoints.parameter_edge Diamond.points)
    (SsaPoints.block_of_point Diamond.points) (SsaPoints.block_edge_of Diamond.points)
    (fun _ => []) (fun _ => []) (fun _ => Some (Diamond.Right, Diamond.Body)).
Definition ssa : Ssa.t Diamond.block Diamond.block_edge unit unit unit :=
  Ssa.of_pure Diamond.bc unit_encoding [tt] (fun _ => Arbitrary) (fun _ => Diamond.Right)
    (fun _ => []) (fun _ => []) (fun _ => []).
Definition expr :=
  Bitvector.of_pure Diamond.pc unit_encoding [tt] Forward
    (fun e => match Diamond.occurrence e with Some u => [u] | None => [] end)
    definitions (fun _ => None).
Definition client :=
  Pre.Client points ssa expr (Pre.pure_c Diamond.client) (Pre.recomputed_c Diamond.client)
    [tt] [tt] (Pre.shape_c Diamond.client) (Cost.lift (fun _ => 1%N) (fun _ => [tt]))
    (Pre.eval Diamond.client) (Pre.translate_c Diamond.client) (Pre.initial_c Diamond.client)
    (Pre.exit_point_c Diamond.client).
Definition ctx :=
  Pre.Context client (Pre.keys Diamond.ctx) Diamond.blocks Diamond.point_graph Diamond.tree.

Example point_laws : ssa_point_laws points.
Proof.
  destruct Diamond.point_laws; constructor; assumption.
Qed.

Example strict_points : reachable_point_ssa points.
Proof.
  constructor.
  - exists (Diamond.Entry, Diamond.Before); reflexivity.
  - intros n [] Hn [Huse|[e [He Huse]]]; vm_compute in Huse; contradiction.
  - intros [b stage] e [] Hn He Hdef; destruct b, stage;
      destruct e as [owner|owner|be]; try destruct owner; try destruct be;
      vm_compute in He, Hdef |- *; intuition congruence.
  - intros [] d e Hhome Hreach He; vm_compute in Hhome; inversion Hhome; subst d.
    destruct e as [owner|owner|be]; try destruct owner; try destruct be;
      vm_compute in He |- *; intuition congruence.
Qed.

Example laws : Pre.laws ctx.
Proof.
  constructor.
  - constructor.
    + intro b; constructor.
    + intros e [] Hcomputed; now left.
    + intros [] H; discriminate.
    + intros [] Hfamily [] Hin; now left.
    + intros [] [] Hfamily Hfamily' Hshape Hoperands; reflexivity.
    + intros [] [] Hfamily Hfamily' Hshape; reflexivity.
    + intros be [] Hbe Hfamily; exists tt; reflexivity.
    + intros be [] [] Hfamily Htranslate; reflexivity.
    + intros be [] [] Hfamily Hbe Htranslate; reflexivity.
    + intros be [] [] Hpure Htranslate; reflexivity.
  - destruct Diamond.graphs; constructor; try assumption.
    + exact point_laws.
    + exact strict_points.
  - constructor.
    + intros e [] He Hfamily Hkill; exists tt; split; [now left|].
      destruct e as [owner|owner|be]; try destruct owner;
        vm_compute in Hkill |- *; intuition congruence.
    + intros e [] He Hdef; destruct e as [owner|owner|be]; try destruct owner;
        vm_compute in Hdef |- *; intuition congruence.
    + intros e be He Hcross; destruct e as [owner|owner|edge]; try destruct owner;
        vm_compute in Hcross |- *; intuition congruence.
    + exact (Pre.real_internal Diamond.ctx Diamond.kills).
  - constructor; intros; reflexivity.
Qed.

(** The right branch has an actual SSA definition supporting its expression-kill callback. *)
Example lawful_kill :
  Pre.killed ctx (Diamond.Real Diamond.Right) tt = true /\
  edge_def (SsaPoints.point_model points) (Diamond.Real Diamond.Right) = [tt] /\
  Ssa.home ssa tt = Diamond.Right.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The killed branch supplies unavailable while the unaltered branch retains its real definition. *)
Example one_branch_kill_arguments :
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, tt), Diamond.LJ)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Fresh (Diamond.Real Diamond.Left) tt) true) /\
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, tt), Diamond.RJ)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Unavailable tt) false).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example aggregate_wf : PreFrameWf.frg_wf ctx (PreOperands.build_frg ctx).
Proof.
  exact (PreOperands.build_frg_wf ctx laws).
Qed.

End Kill.

Module Flow.

Definition edge := (Diamond.block + (Diamond.block + (Diamond.block + positive)))%type.
Definition bind (b : Diamond.block) : edge := inl b.
Definition compute (b : Diamond.block) : edge := inr (inl b).
Definition again (b : Diamond.block) : edge := inr (inr (inl b)).
Definition cross (be : positive) : edge := inr (inr (inr be)).
Definition edge_enc := sum_encoding Diamond.block_enc
  (sum_encoding Diamond.block_enc (sum_encoding Diamond.block_enc positive_encoding)).
Definition point_enc := pair_encoding Diamond.block_enc nat_encoding.
Definition bc (bg : Graph.t Diamond.block positive) := Cfg.Make bg Diamond.block_enc positive_encoding.
Definition pg (bg : Graph.t Diamond.block positive) :=
  Graph.of_pure [(Diamond.Entry, 0%nat)]
    (list_prod (Graph.nodes bg) [0%nat; 1%nat; 2%nat; 3%nat])
    (fun point => let '(b, stage) := point in
      match stage with
      | 0%nat => [bind b]
      | 1%nat => [compute b]
      | 2%nat => [again b]
      | 3%nat => map cross (Graph.out bg b)
      | _ => []
      end)
    (fun e => match e with
      | inl b => (b, 0%nat)
      | inr (inl b) => (b, 1%nat)
      | inr (inr (inl b)) => (b, 2%nat)
      | inr (inr (inr be)) => (Graph.source bg be, 3%nat)
      end)
    (fun e => match e with
      | inl b => (b, 1%nat)
      | inr (inl b) => (b, 2%nat)
      | inr (inr (inl b)) => (b, 3%nat)
      | inr (inr (inr be)) => (Graph.target bg be, 0%nat)
      end).
Definition pc bg := Cfg.Make (pg bg) point_enc edge_enc.
Definition points bg :=
  SsaPoints.of_pure
    (Vars.of_pure (pc bg) unit_encoding (fun _ => []) (fun _ => []) (fun _ => []))
    (bc bg) (fun b => [(b, 0%nat); (b, 1%nat); (b, 2%nat); (b, 3%nat)])
    (fun b => [bind b; compute b; again b]) bind fst
    (fun e => match e with inr (inr (inr be)) => Some be | _ => None end)
    (fun _ => []) (fun _ => []) (fun _ => None).
Definition client bg (occurs : edge -> bool) :
    Pre.client Diamond.block positive (Diamond.block * nat) edge unit unit unit nat unit :=
  Pre.Client (points bg)
    (Ssa.of_pure (bc bg) unit_encoding [] (fun _ => Arbitrary) (fun _ => Diamond.Entry)
      (fun _ => []) (fun _ => []) (fun _ => []))
    (Bitvector.of_pure (pc bg) unit_encoding [tt] Forward (fun _ => []) (fun _ => [])
      (fun _ => None))
    (Pre.pure_c Diamond.client)
    (Cost.lift (fun _ => 1%N) (fun e => if occurs e then Some tt else None))
    [tt] [] (Pre.shape_c Diamond.client) (Pre.operands_c Diamond.client) (Pre.eval Diamond.client)
    (fun _ => Pre.translate_c Diamond.client Diamond.EL)
    (Pre.initial_c Diamond.client) (Cost.lift (fun _ => 1%N) (fun _ => false)).
Definition blocks (bg : Graph.t Diamond.block positive) := Prepared.prepare Diamond.block_enc bg.
Definition context bg parents occurs :=
  Pre.Context (client bg occurs)
    (Pre.Encs Diamond.block_enc positive_encoding point_enc edge_enc unit_encoding unit_encoding)
    (blocks bg) (Prepared.prepare point_enc (pg bg)) (DomCheck.of_parents (blocks bg) parents).
Definition loop_bg :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (fun b => match b with
      | Diamond.Entry => [1%positive]
      | Diamond.Left => [2%positive; 3%positive]
      | Diamond.Right => [4%positive]
      | Diamond.Join => []
      end)
    (fun be => match be with 1%positive => Diamond.Entry | 4%positive => Diamond.Right
      | _ => Diamond.Left end)
    (fun be => match be with 3%positive => Diamond.Right | 4%positive => Diamond.Join
      | _ => Diamond.Left end).
Definition loop_occurs (e : edge) :=
  match e with inr (inl Diamond.Entry) | inr (inl Diamond.Left) => true | _ => false end.
Definition loop_parents := Map.of_list positive_encoding [(2, 1); (3, 2); (4, 3)]%positive.
Definition loop_ctx := context loop_bg loop_parents loop_occurs.

Example loop_tree_accepted : DomCheck.check (blocks loop_bg) loop_parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The original backedge closes a finite phi link and the header computation reuses that phi. *)
Example loop_cyclic_link :
  FinSet.mem (PreFrg.phi_encoding loop_ctx) (Diamond.Left, tt)
    (PreFrg.phis (PreOperands.build_frg loop_ctx)) = true /\
  Map.get (PreFrg.link_encoding loop_ctx) ((Diamond.Left, tt), 2%positive)
    (PreFrg.operands (PreOperands.build_frg loop_ctx)) =
      Some (PreFrg.Operand (PreFrg.Phi Diamond.Left tt) true) /\
  Map.get edge_enc (compute Diamond.Left) (PreFrg.occurrences (PreOperands.build_frg loop_ctx)) =
    Some (PreFrg.Phi Diamond.Left tt) /\
  FinSet.mem edge_enc (compute Diamond.Left) (PreFrg.fresh (PreOperands.build_frg loop_ctx)) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition irreducible_bg :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (fun b => match b with
      | Diamond.Entry => [1%positive; 2%positive]
      | Diamond.Left => [3%positive]
      | Diamond.Right => [4%positive; 5%positive]
      | Diamond.Join => []
      end)
    (fun be => match be with 1%positive | 2%positive => Diamond.Entry
      | 3%positive => Diamond.Left | _ => Diamond.Right end)
    (fun be => match be with 1%positive | 4%positive => Diamond.Left
      | 5%positive => Diamond.Join | _ => Diamond.Right end).
Definition irreducible_parents := Map.of_list positive_encoding [(2, 1); (3, 1); (4, 3)]%positive.
Definition irreducible_ctx := context irreducible_bg irreducible_parents loop_occurs.

Example irreducible_tree_accepted :
  DomCheck.check (blocks irreducible_bg) irreducible_parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The two-entry cycle retains distinct left and right expression phis without unrolling. *)
Example irreducible_phi_sites :
  FinSet.mem (PreFrg.phi_encoding irreducible_ctx) (Diamond.Left, tt)
    (PreFrg.phis (PreOperands.build_frg irreducible_ctx)) = true /\
  FinSet.mem (PreFrg.phi_encoding irreducible_ctx) (Diamond.Right, tt)
    (PreFrg.phis (PreOperands.build_frg irreducible_ctx)) = true /\
  Map.get edge_enc (compute Diamond.Left)
    (PreFrg.occurrences (PreOperands.build_frg irreducible_ctx)) = Some (PreFrg.Phi Diamond.Left tt).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition sequential_ctx := context loop_bg loop_parents (fun e =>
  match e with inr (inl Diamond.Entry) | inr (inr (inl Diamond.Entry)) => true | _ => false end).

(** Two actual instructions in the entry block select the first fresh version. *)
Example sequential_reuse :
  Map.get edge_enc (compute Diamond.Entry)
    (PreFrg.occurrences (PreOperands.build_frg sequential_ctx)) =
      Some (PreFrg.Fresh (compute Diamond.Entry) tt) /\
  Map.get edge_enc (again Diamond.Entry)
    (PreFrg.occurrences (PreOperands.build_frg sequential_ctx)) =
      Some (PreFrg.Fresh (compute Diamond.Entry) tt).
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition entry_loop_bg :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (fun b => match b with Diamond.Entry => [1%positive] | _ => [] end)
    (fun _ => Diamond.Entry) (fun _ => Diamond.Entry).
Definition entry_loop_ctx := context entry_loop_bg Map.empty (fun _ => false).

(** A raw entry self-loop violates the unchanged supported no-incoming-entry law. *)
Example entry_self_loop_rejected : ~ Pre.laws entry_loop_ctx.
Proof.
  intro Hlaw.
  apply (Pre.entry_no_incoming entry_loop_ctx (Pre.graphs entry_loop_ctx Hlaw)
    Diamond.Entry 1%positive).
  - now left.
  - vm_compute; now left.
  - reflexivity.
Qed.

End Flow.

Module Pair.

Definition value := Diamond.block.
Definition expression := (value * value)%type.
Definition expression_enc := pair_encoding Diamond.block_enc Diamond.block_enc.
Definition ab : expression := (Diamond.Entry, Diamond.Left).
Definition ba : expression := (Diamond.Left, Diamond.Entry).
Definition cd : expression := (Diamond.Right, Diamond.Join).
Definition dc : expression := (Diamond.Join, Diamond.Right).
Definition parameters b :=
  match b with
  | Diamond.Entry => [Diamond.Entry; Diamond.Left]
  | Diamond.Join => [Diamond.Right; Diamond.Join]
  | _ => []
  end.
Definition loop_bg :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (fun b => match b with Diamond.Entry => [1%positive] | Diamond.Left => [2%positive]
      | Diamond.Right => [3%positive] | Diamond.Join => [4%positive] end)
    (fun be => match be with 1%positive => Diamond.Entry | 2%positive => Diamond.Left
      | 3%positive => Diamond.Right | _ => Diamond.Join end)
    (fun be => match be with 1%positive => Diamond.Left | 2%positive => Diamond.Right
      | _ => Diamond.Join end).
Definition arguments (be : positive) :=
  match be with 3%positive => [Diamond.Entry; Diamond.Left]
  | 4%positive => [Diamond.Join; Diamond.Right] | _ => [] end.
Definition occurrence (e : Flow.edge) :=
  match e with
  | inr (inl Diamond.Entry) => Some ab
  | inr (inr (inl Diamond.Entry)) => Some ba
  | inr (inl Diamond.Join) => Some cd
  | inr (inr (inl Diamond.Join)) => Some dc
  | _ => None
  end.
Definition operands (u : expression) := [fst u; snd u].
Definition eval (u : expression) (env : value -> option nat) :=
  match env (fst u), env (snd u) with
  | Some x, Some y => Some (10 * x + y)%nat
  | _, _ => None
  end.
Definition defs (e : Flow.edge) :=
  match e with inl b => parameters b | _ => [] end.
Definition rename (bg : Graph.t Diamond.block positive) args be x :=
  match Map.get Diamond.block_enc x (Map.of_list Diamond.block_enc
    (combine (parameters (Graph.target bg be)) (args be))) with
  | Some y => y
  | None => x
  end.
Definition translate bg args be (u : expression) :=
  Some (rename bg args be (fst u), rename bg args be (snd u)).
Definition uses args occurs (e : Flow.edge) :=
  match e with
  | inl _ => []
  | inr (inr (inr be)) => args be
  | _ => match occurs e with Some u => operands u | None => [] end
  end.
Definition client bg args occurs :
    Pre.client Diamond.block positive (Diamond.block * nat) Flow.edge value unit unit nat expression :=
  let vars := Vars.of_pure (Flow.pc bg) Diamond.block_enc (uses args occurs) defs (fun _ => []) in
  let points := SsaPoints.of_pure vars (Flow.bc bg)
    (SsaPoints.points_in_block (Flow.points bg)) (SsaPoints.instruction_edges (Flow.points bg))
    Flow.bind fst (SsaPoints.block_edge_of (Flow.points bg)) parameters args
    (fun v => Some (match v with Diamond.Entry | Diamond.Left => Diamond.Entry
      | _ => Diamond.Join end, 0%nat)) in
  Pre.Client points
    (Ssa.of_pure (Flow.bc bg) Diamond.block_enc
      [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join] (fun _ => Arbitrary)
      (fun v => match v with Diamond.Entry | Diamond.Left => Diamond.Entry
        | _ => Diamond.Join end) parameters args (fun _ => []))
    (Bitvector.of_pure (Flow.pc bg) expression_enc [ab; ba; cd; dc] Forward (fun _ => [])
      (fun e => filter (fun u => existsb (fun x =>
        existsb (eqb Diamond.block_enc x) (defs e)) (operands u)) [ab; ba; cd; dc])
      (fun _ => None))
    (Cost.lift (fun _ => 1%N) (fun _ => true)) (Cost.lift (fun _ => 1%N) occurs)
    [ab; ba; cd; dc] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (Cost.lift (fun _ => 1%N) (fun _ => 1%positive)) (Cost.lift (fun _ => 1%N) operands) eval
    (fun be => Cost.lift (fun _ => 1%N) (translate bg args be))
    (Cost.lift (fun _ => 1%N) (fun _ => false))
    (Cost.lift (fun _ => 1%N) (fun _ => false)).
Definition context bg args occurs :=
  Pre.Context (client bg args occurs)
    (Pre.Encs Diamond.block_enc positive_encoding Flow.point_enc Flow.edge_enc
      Diamond.block_enc expression_enc)
    (Flow.blocks bg) (Prepared.prepare Flow.point_enc (Flow.pg bg))
    (DomCheck.of_parents (Flow.blocks bg)
      (Map.of_list positive_encoding [(2, 1); (3, 2); (4, 3)]%positive)).
Definition ctx := context loop_bg arguments occurrence.

(** The actual translation exchanges both parameters using the same incoming environment. *)
Example simultaneous_exchange :
  Pre.translate ctx 4%positive cd = Some dc /\
  Pre.operands ctx dc = [Diamond.Join; Diamond.Right] /\
  Pre.eval (Pre.input ctx) cd (Pre.phi_env ctx 4%positive
    (fun v => Some (match v with Diamond.Right => 3%nat | Diamond.Join => 7%nat | _ => 0%nat end))) =
      Some 73%nat.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The exchange backedge links the two expression phis and retains the real incoming definitions. *)
Example cyclic_versions :
  FinSet.mem (PreFrg.phi_encoding ctx) (Diamond.Join, cd)
    (PreFrg.phis (PreOperands.build_frg ctx)) = true /\
  FinSet.mem (PreFrg.phi_encoding ctx) (Diamond.Join, dc)
    (PreFrg.phis (PreOperands.build_frg ctx)) = true /\
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, cd), 3%positive)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Fresh (Flow.compute Diamond.Entry) ab) true) /\
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, cd), 4%positive)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Phi Diamond.Join dc) true) /\
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, dc), 4%positive)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Phi Diamond.Join cd) true) /\
  FinSet.mem Flow.edge_enc (Flow.compute Diamond.Join) (PreFrg.fresh (PreOperands.build_frg ctx)) =
    false /\ length (PreFrg.versions (PreOperands.build_frg ctx)) = 8%nat.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition parallel_bg (two : bool) :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (fun b => match b with Diamond.Entry => [1%positive] | Diamond.Left => [2%positive]
      | Diamond.Right => if two then [3%positive; 4%positive] else [3%positive]
      | Diamond.Join => [] end)
    (fun be => match be with 1%positive => Diamond.Entry | 2%positive => Diamond.Left
      | _ => Diamond.Right end)
    (fun be => match be with 1%positive => Diamond.Left | 2%positive => Diamond.Right
      | _ => Diamond.Join end).
Definition parallel_args (be : positive) :=
  match be with 3%positive => [Diamond.Entry; Diamond.Left]
  | 4%positive => [Diamond.Left; Diamond.Entry] | _ => [] end.
Definition parallel_occurs (e : Flow.edge) :=
  match e with inr (inl Diamond.Right) => Some ab
  | inr (inr (inl Diamond.Right)) => Some ba
  | inr (inl Diamond.Join) => Some cd | _ => None end.
Definition parallel_ctx two := context (parallel_bg two) parallel_args parallel_occurs.

(** Parallel incoming identities select distinct predecessor expression versions. *)
Example parallel_distinct_arguments :
  Map.get (PreFrg.link_encoding (parallel_ctx true)) ((Diamond.Join, cd), 3%positive)
    (PreFrg.operands (PreOperands.build_frg (parallel_ctx true))) =
      Some (PreFrg.Operand (PreFrg.Fresh (Flow.compute Diamond.Right) ab) true) /\
  Map.get (PreFrg.link_encoding (parallel_ctx true)) ((Diamond.Join, cd), 4%positive)
    (PreFrg.operands (PreOperands.build_frg (parallel_ctx true))) =
      Some (PreFrg.Operand (PreFrg.Fresh (Flow.again Diamond.Right) ba) true).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A direct parameter phi remains present when the target has one predecessor. *)
Example single_predecessor_parameter_phi :
  FinSet.mem (PreFrg.phi_encoding (parallel_ctx false)) (Diamond.Join, cd)
    (PreFrg.phis (PreOperands.build_frg (parallel_ctx false))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example direct_nonmember :
  ~ exists x, In x (Pre.operands ctx ab) /\ In x (SsaPoints.block_params (Pre.points (Pre.input ctx))
    Diamond.Join).
Proof.
  vm_compute; intros [x [Hoperand Hparameter]]; destruct x; intuition congruence.
Qed.

Example entry_phi_absent :
  map (fun u => FinSet.mem (PreFrg.phi_encoding ctx) (Diamond.Entry, u)
    (PreFrg.phis (PreOperands.build_frg ctx))) [ab; ba; cd; dc] = [false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition boundary_bg :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right] (fun _ => [])
    (Graph.source loop_bg) (Graph.target loop_bg).
Definition boundary_ctx := context boundary_bg arguments occurrence.

Example unlisted_parameter_phi_absent :
  FinSet.mem (PreFrg.phi_encoding boundary_ctx) (Diamond.Join, cd)
    (PreFrg.phis (PreOperands.build_frg boundary_ctx)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example listed_nonmember_phi_absent :
  FinSet.mem (PreFrg.phi_encoding boundary_ctx) (Diamond.Left, ab)
    (PreFrg.phis (PreOperands.build_frg boundary_ctx)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition graph (kind : option bool) :=
  match kind with None => loop_bg | Some two => parallel_bg two end.
Definition args (kind : option bool) :=
  match kind with None => arguments | Some _ => parallel_args end.
Definition occurs (kind : option bool) :=
  match kind with None => occurrence | Some _ => parallel_occurs end.
Definition law_ctx kind := context (graph kind) (args kind) (occurs kind).
Definition model kind := Pre.points (Pre.input (law_ctx kind)).

Example point_graph_wf kind : graph_wf (Flow.pg (graph kind)).
Proof.
  constructor.
  - destruct kind as [[|]|]; vm_compute;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros [b stage] Hentry; vm_compute in Hentry; inversion Hentry as [Heq|[]].
    inversion Heq; subst b stage; destruct kind as [[|]|]; vm_compute; tauto.
  - intros [b stage] e Hout; destruct kind as [[|]|], b;
      destruct stage as [|[|[|[|stage]]]]; vm_compute in Hout |- *; intuition (subst; reflexivity).
  - intros [b stage] e Hnode Hout; destruct kind as [[|]|], b;
      destruct stage as [|[|[|[|stage]]]]; vm_compute in Hout |- *; intuition (subst; tauto).
Qed.

Example block_graph_wf kind : graph_wf (graph kind).
Proof.
  constructor.
  - destruct kind as [[|]|]; vm_compute;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros b Hentry; destruct kind as [[|]|], b; vm_compute in Hentry |- *; intuition congruence.
  - intros b e Hout; destruct kind as [[|]|], b; vm_compute in Hout |- *; intuition (subst; reflexivity).
  - intros b e Hnode Hout; destruct kind as [[|]|], b;
      vm_compute in Hout |- *; intuition (subst; tauto).
Qed.

Example point_laws kind : ssa_point_laws (model kind).
Proof.
  constructor.
  - exact (point_graph_wf kind).
  - intros [b stage]; destruct kind as [[|]|], b; destruct stage as [|[|[|[|stage]]]];
      vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - exact (block_graph_wf kind).
  - intros b; destruct kind as [[|]|], b; vm_compute;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros [b stage]; split.
    + intro Hnode; exists b; destruct kind as [[|]|], b;
        destruct stage as [|[|[|[|stage]]]]; vm_compute in Hnode |- *; intuition congruence.
    + intros [owner [Howner Hpoint]]; destruct kind as [[|]|], b, owner;
        destruct stage as [|[|[|[|stage]]]]; vm_compute in Hpoint |- *; intuition congruence.
  - intros b; vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros b [owner stage] Hb Hpoint; destruct b, owner;
      destruct stage as [|[|[|[|stage]]]]; vm_compute in Hpoint |- *; intuition congruence.
  - intros b Hb; vm_compute; discriminate.
  - intros b Hb.
    change (point_chain (Flow.pg (graph kind))
      [(b, 0%nat); (b, 1%nat); (b, 2%nat); (b, 3%nat)]
      [Flow.bind b; Flow.compute b; Flow.again b]).
    econstructor; [now left|reflexivity|].
    econstructor; [now left|reflexivity|].
    econstructor; [now left|reflexivity|constructor].
  - intros b e Hb Hin; destruct Hin as [<-|[<-|[<-|[]]]]; reflexivity.
  - intros [b stage] e Hnode Hout Hinternal; destruct kind as [[|]|], b;
      destruct stage as [|[|[|[|stage]]]]; vm_compute in Hout, Hinternal |- *;
      intuition (subst; simpl in *; try discriminate; tauto).
  - intros b Hb; reflexivity.
  - intros b x Hb; reflexivity.
  - intros [b stage] e Hnode Hout; destruct kind as [[|]|], b;
      destruct stage as [|[|[|[|stage]]]]; vm_compute in Hout |- *;
      intuition (subst; vm_compute; tauto).
  - intros be Hbe; destruct kind as [[|]|]; vm_compute in Hbe |- *;
      intuition (subst; vm_compute; reflexivity).
  - intros n e be Hnode Hout Hcross x Harg.
    destruct e as [b|[b|[b|edge]]]; cbn in Hcross; try discriminate.
    inversion Hcross; subst edge; exact Harg.
  - intros be Hbe; exists (Graph.source (graph kind) be, 3%nat), (Flow.cross be).
    destruct kind as [[|]|]; vm_compute in Hbe |- *; intuition (subst; vm_compute; tauto).
  - intros e other be He Ho Hcross Hcross'.
    destruct e as [b|[b|[b|edge]]]; destruct other as [owner|[owner|[owner|other]]];
      cbn in Hcross, Hcross'; congruence.
Qed.

Lemma after_reachable kind b :
  reachable (Flow.pg (graph kind)) (b, 0%nat) ->
  reachable (Flow.pg (graph kind)) (b, 3%nat).
Proof.
  intro Hbefore.
  exact (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.again b)
    (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.compute b)
      (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.bind b) Hbefore (or_introl eq_refl))
      (or_introl eq_refl)) (or_introl eq_refl)).
Qed.

Lemma cross_reachable kind be source target :
  Graph.source (graph kind) be = source -> Graph.target (graph kind) be = target ->
  In be (Graph.out (graph kind) source) ->
  reachable (Flow.pg (graph kind)) (source, 0%nat) ->
  reachable (Flow.pg (graph kind)) (target, 0%nat).
Proof.
  intros Hsource Htarget Hout Hbefore.
  assert (Hstart : reachable (Flow.pg (graph kind))
    (Graph.source (Flow.pg (graph kind)) (Flow.cross be))).
  { change (reachable (Flow.pg (graph kind)) (Graph.source (graph kind) be, 3%nat)).
    rewrite Hsource; apply after_reachable; exact Hbefore. }
  assert (Hedge : In (Flow.cross be) (Graph.out (Flow.pg (graph kind))
    (Graph.source (Flow.pg (graph kind)) (Flow.cross be)))).
  { change (In (Flow.cross be) (map Flow.cross (Graph.out (graph kind)
      (Graph.source (graph kind) be)))).
    rewrite Hsource; apply in_map; exact Hout. }
  pose proof (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.cross be) Hstart Hedge) as Hnext.
  change (reachable (Flow.pg (graph kind)) (Graph.target (graph kind) be, 0%nat)) in Hnext.
  rewrite Htarget in Hnext; exact Hnext.
Qed.

Example before_reachable kind : forall b, reachable (Flow.pg (graph kind)) (b, 0%nat).
Proof.
  assert (Hentry : reachable (Flow.pg (graph kind)) (Diamond.Entry, 0%nat)).
  { apply reachable_entry; now left. }
  assert (Hleft : reachable (Flow.pg (graph kind)) (Diamond.Left, 0%nat)).
  { apply (cross_reachable kind 1%positive Diamond.Entry Diamond.Left);
      try (destruct kind as [[|]|]; vm_compute; tauto); exact Hentry. }
  assert (Hright : reachable (Flow.pg (graph kind)) (Diamond.Right, 0%nat)).
  { apply (cross_reachable kind 2%positive Diamond.Left Diamond.Right);
      try (destruct kind as [[|]|]; vm_compute; tauto); exact Hleft. }
  assert (Hjoin : reachable (Flow.pg (graph kind)) (Diamond.Join, 0%nat)).
  { apply (cross_reachable kind 3%positive Diamond.Right Diamond.Join);
      try (destruct kind as [[|]|]; vm_compute; tauto); exact Hright. }
  intros []; assumption.
Qed.

Example points_reachable kind n :
  In n (Graph.nodes (Flow.pg (graph kind))) -> reachable (Flow.pg (graph kind)) n.
Proof.
  intros Hnode; destruct n as [b stage].
  destruct stage as [|[|[|[|stage]]]].
  - apply before_reachable.
  - exact (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.bind b)
      (before_reachable kind b) (or_introl eq_refl)).
  - exact (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.compute b)
      (@reachable_step _ _ (Flow.pg (graph kind)) (Flow.bind b)
        (before_reachable kind b) (or_introl eq_refl)) (or_introl eq_refl)).
  - apply after_reachable, before_reachable.
  - destruct kind as [[|]|], b; vm_compute in Hnode; intuition congruence.
Qed.

Lemma previous_dominates kind b stage :
  (stage < 3)%nat -> dominates (Flow.pg (graph kind)) (b, stage) (b, S stage).
Proof.
  intro Hstage; apply dominates_unique_predecessor.
  - change (~ In (b, S stage) [(Diamond.Entry, 0%nat)]); intros [Hbad|[]]; discriminate.
  - intros e Hout Htarget.
    change (match e with
        | inl block => (block, 1%nat)
        | inr (inl block) => (block, 2%nat)
        | inr (inr (inl block)) => (block, 3%nat)
        | inr (inr (inr edge)) => (Graph.target (graph kind) edge, 0%nat)
        end = (b, S stage)) in Htarget.
    destruct stage as [|[|[|stage]]]; try lia;
      destruct e as [owner|[owner|[owner|be]]];
      cbn in Htarget; inversion Htarget; subst; reflexivity.
Qed.

Lemma first_dominates kind b stage :
  (0 < stage <= 3)%nat -> dominates (Flow.pg (graph kind)) (b, 0%nat) (b, stage).
Proof.
  intro Hstage; destruct stage as [|[|[|[|stage]]]]; try lia.
  - apply previous_dominates; lia.
  - eapply dominates_trans; apply previous_dominates; lia.
  - eapply dominates_trans; [eapply dominates_trans|]; apply previous_dominates; lia.
Qed.

Definition home x :=
  match x with Diamond.Entry | Diamond.Left => Diamond.Entry | _ => Diamond.Join end.

Lemma use_location kind b stage x :
  point_use_at (SsaPoints.point_model (model kind)) (b, stage) x ->
  (home x = Diamond.Entry /\ (b, stage) <> (Diamond.Entry, 0%nat)) \/
    (home x = Diamond.Join /\ b = Diamond.Join /\ (0 < stage <= 3)%nat).
Proof.
  intros [Hexit|[e [Hout Huse]]]; [contradiction|].
  destruct kind as [[|]|], b, x; destruct stage as [|[|[|[|stage]]]];
    vm_compute in Hout, Huse |- *;
    intuition (subst; vm_compute in Huse; intuition (try lia; congruence)).
Qed.

Example strict_points kind : reachable_point_ssa (model kind).
Proof.
  constructor.
  - exists (Diamond.Entry, 0%nat); reflexivity.
  - intros [b stage] x Hreach Huse; exists (home x, 0%nat); split; [destruct x; reflexivity|].
    split; [apply before_reachable|].
    destruct (use_location kind b stage x Huse) as [[Hhome Hne]|[Hhome [-> Hstage]]]; rewrite Hhome.
    + split; [|congruence].
      intros start es Hentry Hpath; change (In start [(Diamond.Entry, 0%nat)]) in Hentry.
      destruct Hentry as [<-|[]]; now left.
    + split; [apply first_dominates; exact Hstage|intro Hbad; inversion Hbad; lia].
  - intros n e x Hreach Hout Hdef.
    pose proof (out_source (point_graph_wf kind) n e Hout) as Hsource.
    destruct e as [b|[b|[b|be]]]; try contradiction.
    assert (Hhome : home x = b) by
      (destruct b, x; vm_compute in Hdef |- *; intuition congruence).
    rewrite <- Hsource; destruct x, b; vm_compute in Hhome |- *; congruence.
  - intros x d e Hdef Hreach Hout.
    change (Some (home x, 0%nat) = Some d) in Hdef; inversion Hdef; subst d.
    change (In e [Flow.bind (home x)]) in Hout; destruct Hout as [<-|[]].
    destruct x; vm_compute; tauto.
Qed.

Example blocks_reachable kind : forall b, reachable (graph kind) b.
Proof.
  assert (Hentry : reachable (graph kind) Diamond.Entry).
  { apply reachable_entry; destruct kind as [[|]|]; now left. }
  assert (Hleft : reachable (graph kind) Diamond.Left).
  { destruct kind as [[|]|];
      exact (@reachable_step _ _ _ 1%positive Hentry (or_introl eq_refl)). }
  assert (Hright : reachable (graph kind) Diamond.Right).
  { destruct kind as [[|]|];
      exact (@reachable_step _ _ _ 2%positive Hleft (or_introl eq_refl)). }
  assert (Hjoin : reachable (graph kind) Diamond.Join).
  { destruct kind as [[|]|];
      exact (@reachable_step _ _ _ 3%positive Hright (or_introl eq_refl)). }
  intros []; assumption.
Qed.

Example blocks_ready kind : Prepared.ready (Pre.blocks (law_ctx kind)).
Proof.
  apply Prepared.prepare_ready; [exact Diamond.block_enc_laws|exact (block_graph_wf kind)|].
  exact (blocks_out_nodup (point_laws kind)).
Qed.

Example points_ready kind : Prepared.ready (Pre.point_graph (law_ctx kind)).
Proof.
  apply Prepared.prepare_ready; [|exact (point_graph_wf kind)|].
  - apply pair_encoding_laws; [exact Diamond.block_enc_laws|exact nat_encoding_laws].
  - exact (points_out_nodup (point_laws kind)).
Qed.

Lemma operand_agrees kind be x :
  Pre.phi_operand (law_ctx kind) be x = rename (graph kind) (args kind) be x.
Proof.
  destruct kind as [[|]|], x; destruct be as [p|p|]; try destruct p as [q|q|];
    try destruct q as [r|r|]; vm_compute; reflexivity.
Qed.

Example shapes kind : Pre.shape_laws (law_ctx kind).
Proof.
  constructor.
  - intros b; destruct b; vm_compute;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros e u Hcomputed; destruct kind as [[|]|]; destruct e as [b|[b|[b|be]]];
      try destruct b; vm_compute in Hcomputed; try discriminate;
      inversion Hcomputed; subst u; vm_compute; tauto.
  - intros u Hfalse; discriminate.
  - intros [x y] Hfamily z Hz; change (In z [x; y]) in Hz.
    destruct Hz as [<-|[<-|[]]]; [destruct x|destruct y]; vm_compute; tauto.
  - intros [x y] [z w] Hfamily Hfamily' Hshape Hoperands.
    change ([x; y] = [z; w]) in Hoperands; inversion Hoperands; reflexivity.
  - intros [x y] [z w] Hfamily Hfamily' Hshape; reflexivity.
  - intros be [x y] Hbe Hfamily; eexists; reflexivity.
  - intros be [x y] v Hfamily Htranslate; reflexivity.
  - intros be [x y] v Hfamily Hbe Htranslate.
    change (Some (rename (graph kind) (args kind) be x, rename (graph kind) (args kind) be y) =
      Some v) in Htranslate.
    inversion Htranslate; subst v.
    change ([rename (graph kind) (args kind) be x; rename (graph kind) (args kind) be y] =
      [Pre.phi_operand (law_ctx kind) be x; Pre.phi_operand (law_ctx kind) be y]).
    rewrite !operand_agrees; reflexivity.
  - intros be u v Hpure Htranslate; reflexivity.
Qed.

Example graphs kind : Pre.graph_laws (law_ctx kind).
Proof.
  constructor.
  - exact Diamond.block_enc_laws.
  - exact positive_encoding_laws.
  - apply pair_encoding_laws; [exact Diamond.block_enc_laws|exact nat_encoding_laws].
  - repeat apply sum_encoding_laws; first [exact Diamond.block_enc_laws|exact positive_encoding_laws].
  - exact Diamond.block_enc_laws.
  - apply pair_encoding_laws; exact Diamond.block_enc_laws.
  - exact (point_laws kind).
  - exact (strict_points kind).
  - reflexivity.
  - reflexivity.
  - apply Prepared.prepare_graph.
  - apply Prepared.prepare_graph.
  - exact (blocks_ready kind).
  - exact (points_ready kind).
  - apply DomCheck.check_sound; [exact (blocks_ready kind)|apply Map.wf_of_list|].
    destruct kind as [[|]|]; vm_compute; reflexivity.
  - intros b Hb; apply blocks_reachable.
  - intros n Hn; apply points_reachable; exact Hn.
  - exists Diamond.Entry, (Diamond.Entry, 0%nat); destruct kind as [[|]|]; repeat split; reflexivity.
  - intros b be Hb Hbe; destruct kind as [[|]|];
      change (In b [Diamond.Entry]) in Hb; destruct Hb as [<-|[]];
      vm_compute in Hbe |- *; intuition (subst; discriminate).
Qed.

Example kills kind : Pre.kill_laws (law_ctx kind).
Proof.
  constructor.
  - intros e u He Hfamily Hkill.
    rewrite Pre.killed_equation in Hkill; apply existsb_exists in Hkill.
    destruct Hkill as [v [Hin Hsame]].
    change (eqb expression_enc u v = true) in Hsame.
    apply (eqb_true_iff _ (pair_encoding_laws _ _ Diamond.block_enc_laws Diamond.block_enc_laws))
      in Hsame; subst v.
    change (In u (filter (fun candidate => existsb (fun x =>
      existsb (eqb Diamond.block_enc x) (defs e)) (operands candidate)) [ab; ba; cd; dc])) in Hin.
    apply filter_In in Hin; destruct Hin as [Hcandidate Htest].
    apply existsb_exists in Htest; destruct Htest as [x [Hx Hdefined]].
    apply existsb_exists in Hdefined; destruct Hdefined as [y [Hy Hsame]].
    apply (eqb_true_iff _ Diamond.block_enc_laws) in Hsame; subst y.
    exists x; auto.
  - intros e x He Hdef; change (In x (defs e)) in Hdef.
    destruct e as [b|[b|[b|be]]]; try contradiction.
    destruct b, x; vm_compute in Hdef |- *; intuition congruence.
  - intros e be He Hcross; destruct e as [b|[b|[b|edge]]]; cbn in Hcross;
      try discriminate; reflexivity.
  - intros e u Hcomputed; destruct kind as [[|]|]; destruct e as [b|[b|[b|be]]];
      try destruct b; vm_compute in Hcomputed; try discriminate.
    all: split; [reflexivity|intros owner Hbad; discriminate].
Qed.

Example runtime kind : Pre.runtime_laws (law_ctx kind).
Proof.
  constructor.
  - intros [x y] first second Hagree.
    change (eval (x, y) first = eval (x, y) second); unfold eval; cbn [fst snd].
    rewrite (Hagree x (or_introl eq_refl)), (Hagree y (or_intror (or_introl eq_refl))); reflexivity.
  - intros be [x y] v env Hbe Hfamily Htranslate.
    change (Some (rename (graph kind) (args kind) be x, rename (graph kind) (args kind) be y) =
      Some v) in Htranslate.
    inversion Htranslate; subst v.
    change (eval (x, y) (Pre.phi_env (law_ctx kind) be env) =
      eval (rename (graph kind) (args kind) be x, rename (graph kind) (args kind) be y) env).
    unfold eval; cbn [fst snd]; rewrite !Pre.phi_env_substitution, !operand_agrees; reflexivity.
Qed.

(** Cyclic exchange, parallel edges and one-predecessor parameters each inhabit the full domain. *)
Example laws kind : Pre.laws (law_ctx kind).
Proof.
  exact (Pre.Laws _ (shapes kind) (graphs kind) (kills kind) (runtime kind)).
Qed.

Example aggregate_wf kind : PreFrameWf.frg_wf (law_ctx kind) (PreOperands.build_frg (law_ctx kind)).
Proof.
  exact (PreOperands.build_frg_wf _ (laws kind)).
Qed.

Example unknown_stage_has_no_outgoing :
  Graph.out (Flow.pg loop_bg) (Diamond.Join, 17%nat) = [].
Proof.
  vm_compute; reflexivity.
Qed.

End Pair.

Module KillCycle.

Definition bg :=
  Graph.of_pure [Diamond.Entry] [Diamond.Entry; Diamond.Left; Diamond.Right; Diamond.Join]
    (fun b => match b with Diamond.Entry => [1%positive] | Diamond.Left => [3%positive]
      | Diamond.Right => [2%positive; 4%positive] | Diamond.Join => [] end)
    (fun be => match be with 1%positive => Diamond.Entry | 3%positive => Diamond.Left
      | _ => Diamond.Right end)
    (fun be => match be with 3%positive => Diamond.Right | 4%positive => Diamond.Join
      | _ => Diamond.Left end).
Definition definitions (e : Flow.edge) :=
  match e with inr (inl Diamond.Left) => [tt] | _ => [] end.
Definition original := Flow.client bg (fun e =>
  match e with inr (inl Diamond.Entry) | inr (inl Diamond.Right) => true | _ => false end).
Definition points :=
  SsaPoints.of_pure
    (Vars.of_pure (Flow.pc bg) unit_encoding (fun _ => []) definitions (fun _ => []))
    (Flow.bc bg) (SsaPoints.points_in_block (Flow.points bg))
    (SsaPoints.instruction_edges (Flow.points bg)) Flow.bind fst
    (SsaPoints.block_edge_of (Flow.points bg)) (fun _ => []) (fun _ => [])
    (fun _ => Some (Diamond.Left, 1%nat)).
Definition client : Pre.client Diamond.block positive (Diamond.block * nat) Flow.edge
    unit unit unit nat unit :=
  Pre.Client points
    (Ssa.of_pure (Flow.bc bg) unit_encoding [tt] (fun _ => Arbitrary) (fun _ => Diamond.Left)
      (fun _ => []) (fun _ => []) (fun _ => []))
    (Bitvector.of_pure (Flow.pc bg) unit_encoding [tt] Forward (fun _ => []) definitions
      (fun _ => None))
    (Pre.pure_c original) (Pre.recomputed_c original) [tt] [tt] (Pre.shape_c original)
    (Cost.lift (fun _ => 1%N) (fun _ => [tt])) (Pre.eval original)
    (Pre.translate_c original) (Pre.initial_c original) (Pre.exit_point_c original).
Definition ctx :=
  Pre.Context client
    (Pre.Encs Diamond.block_enc positive_encoding Flow.point_enc Flow.edge_enc
      unit_encoding unit_encoding)
    (Flow.blocks bg) (Prepared.prepare Flow.point_enc (Flow.pg bg))
    (DomCheck.of_parents (Flow.blocks bg)
      (Map.of_list positive_encoding [(2, 1); (3, 2); (4, 3)]%positive)).

(** A loop kill invalidates the header phi and forces a fresh right-block definition. *)
Example cyclic_kill_requires_fresh :
  Map.get Flow.edge_enc (Flow.compute Diamond.Right) (PreFrg.occurrences (PreOperands.build_frg ctx)) =
    Some (PreFrg.Fresh (Flow.compute Diamond.Right) tt) /\
  FinSet.mem Flow.edge_enc (Flow.compute Diamond.Right) (PreFrg.fresh (PreOperands.build_frg ctx)) =
    true /\
  FinSet.mem (PreFrg.phi_encoding ctx) (Diamond.Left, tt)
    (PreFrg.unsafe (PreOperands.build_frg ctx)) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

End KillCycle.

Example diamond_aggregate_wf : PreFrameWf.frg_wf Diamond.ctx (PreOperands.build_frg Diamond.ctx).
Proof.
  exact (PreOperands.build_frg_wf Diamond.ctx Diamond.laws).
Qed.

Example unused_phi_aggregate_wf : PreFrameWf.frg_wf unused_phi_ctx (PreOperands.build_frg unused_phi_ctx).
Proof.
  exact (PreOperands.build_frg_wf unused_phi_ctx unused_phi_laws).
Qed.

Module InitialKill.

Definition client : Pre.client Diamond.block Diamond.block_edge (Diamond.block * Diamond.stage)
    Diamond.edge unit unit unit nat unit :=
  Pre.Client Kill.points Kill.ssa Kill.expr (Pre.pure_c Kill.client)
    (Cost.lift (fun _ => 1%N) (fun _ => None)) [tt] [tt]
    (Pre.shape_c Kill.client) (Pre.operands_c Kill.client) (Pre.eval Kill.client)
    (Pre.translate_c Kill.client) (Cost.lift (fun _ => 1%N) (fun _ => true))
    (Pre.exit_point_c Kill.client).
Definition ctx :=
  Pre.Context client (Pre.keys Kill.ctx) Diamond.blocks Diamond.point_graph Diamond.tree.

(** This invalidation control has a lawful initially available expression and no join real use. *)
Example laws : Pre.laws ctx.
Proof.
  constructor.
  - constructor.
    + exact (Pre.params_nodup Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + intros e [] Hcomputed; discriminate.
    + intros [] Hinitial; apply Pre.family_seed; now left.
    + exact (Pre.finite_operands Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + exact (Pre.shape_identity Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + exact (Pre.shape_arity Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + exact (Pre.closed_translation Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + exact (Pre.translation_shape Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + exact (Pre.translation_operands Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
    + exact (Pre.translation_pure Kill.ctx (Pre.shapes Kill.ctx Kill.laws)).
  - destruct (Pre.graphs Kill.ctx Kill.laws); constructor; assumption.
  - constructor.
    + exact (Pre.kill_operand Kill.ctx (Pre.kills Kill.ctx Kill.laws)).
    + exact (Pre.def_home Kill.ctx (Pre.kills Kill.ctx Kill.laws)).
    + exact (Pre.cross_no_defs Kill.ctx (Pre.kills Kill.ctx Kill.laws)).
    + intros e [] Hcomputed; discriminate.
  - destruct (Pre.runtime Kill.ctx Kill.laws); constructor; assumption.
Qed.

Example initially_available :
  PreRename.selected (PreRename.top ctx (PreRename.initial_scope ctx [tt]) tt) =
    PreFrg.Operand (PreFrg.Initial tt) false /\
  PreRename.available (PreRename.top ctx (PreRename.initial_scope ctx [tt]) tt) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The unaffected arm retains Initial, the killed arm is unavailable and the unused join is unsafe. *)
Example available_to_unavailable :
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, tt), Diamond.LJ)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Initial tt) false) /\
  Map.get (PreFrg.link_encoding ctx) ((Diamond.Join, tt), Diamond.RJ)
    (PreFrg.operands (PreOperands.build_frg ctx)) =
      Some (PreFrg.Operand (PreFrg.Unavailable tt) false) /\
  Pre.killed ctx (Diamond.Real Diamond.Right) tt = true /\
  Map.get Diamond.edge_enc (Diamond.Real Diamond.Join)
    (PreFrg.occurrences (PreOperands.build_frg ctx)) = None /\
  FinSet.mem (PreFrg.phi_encoding ctx) (Diamond.Join, tt)
    (PreFrg.unsafe (PreOperands.build_frg ctx)) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example aggregate_wf : PreFrameWf.frg_wf ctx (PreOperands.build_frg ctx).
Proof.
  exact (PreOperands.build_frg_wf ctx laws).
Qed.

End InitialKill.
