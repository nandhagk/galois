(** * Expression definition origins and source identity

    Version points distinguish the entry from completed instruction and parameter edges.
    For example, an unavailable sentinel has no definition point.
    Builds on: AnalysesSsaPreFrg and AnalysesSsaPreContextTest. *)

From Stdlib Require Import List.
From Galois.Base Require Import BaseEncoding.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreFrg.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest.
Import List.ListNotations.

Example version_encoding_client : encoding_laws (PreFrg.version_encoding One.ctx).
Proof.
  exact (PreFrg.version_encoding_laws One.ctx One.laws).
Qed.

Example unavailable_has_no_point :
  PreFrg.version_point One.ctx (PreFrg.Unavailable tt) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example initial_has_entry_point :
  PreFrg.version_point One.ctx (PreFrg.Initial tt) = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_has_target_point :
  PreFrg.version_point One.ctx (PreFrg.Fresh tt tt) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example phi_has_parameter_target :
  PreFrg.version_point One.ctx (PreFrg.Phi tt tt) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example prepared_definition_entry :
  PreFrg.defs One.ctx (PreFrg.definition_index One.ctx [tt]) tt = [tt].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_definition_index :
  PreFrg.defs One.ctx (PreFrg.definition_index One.ctx []) tt = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_definition_values_retained :
  PreFrg.defs Parallel.ctx (PreFrg.definition_index Parallel.ctx [false; false]) false =
    [false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** The prepared bucket denotes the same source relation on the actual inhabited model. *)
Example prepared_definition_client :
  forall b, In b (PreFrg.defs One.ctx (PreFrg.definition_index One.ctx [tt]) tt) <->
    PreFrg.definition_block One.ctx tt b.
Proof.
  apply (PreFrg.defs_exact One.ctx [tt] tt One.laws); now left.
Qed.

(** The static definition identity theorem applies without assuming any built-graph result. *)
Example definition_identity_client :
  forall d other q, PreFrg.definition_domain One.ctx d ->
    PreFrg.definition_domain One.ctx other -> PreFrg.version_expr d = PreFrg.version_expr other ->
    PreFrg.version_point One.ctx d = Some q -> PreFrg.version_point One.ctx other = Some q ->
    d = other.
Proof.
  exact (PreFrg.definition_points_unique One.ctx One.laws).
Qed.

Example distinct_origins :
  @PreFrg.Initial unit unit unit tt <> PreFrg.Unavailable tt.
Proof.
  vm_compute; discriminate.
Qed.
