(** * Actual scoped graph output and raw failure outcomes

    The diamond selects its left computation and retains an unavailable right incoming operand.
    For example, the join occurrence selects its phi while the two edge identities stay distinct.
    Builds on: AnalysesSsaPreOperands and the lawful diamond fixture. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphDomSpec GraphCheckDom.
From Galois.Program Require Import ProgramCfg.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreOperands AnalysesSsaPreFrameInvariant.
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
