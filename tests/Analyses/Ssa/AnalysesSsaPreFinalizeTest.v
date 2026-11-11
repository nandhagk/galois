(** * Actual indexed PRE placement fixtures

    These fixtures observe insertions, deletions, selected inputs and explicit driver outcomes.
    For example, the missing diamond arm inserts its translated expression at the crossing edge.
    Builds on: AnalysesSsaPreFinalize and the accepted graph-card presentations. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreOperands AnalysesSsaPreReset AnalysesSsaPreFinalize.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest AnalysesSsaPreFrgTest
  AnalysesSsaPreOperandsTest.
Import List.ListNotations.

Definition diamond_frg := PreOperands.build_frg Diamond.ctx.
Definition diamond_facts := PreReset.solve Diamond.ctx diamond_frg.
Definition diamond_result := PreFinalize.finalize Diamond.ctx diamond_frg diamond_facts.
Definition diamond_plan := PreFinalize.output diamond_result.

(** The actual prepared dominator and point traversal finishes without a missing block or fuel cut. *)
Example diamond_finished : PreFinalize.reason diamond_result = PreFinalize.Finished.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_insertion :
  PreFinalize.inserted Diamond.ctx diamond_plan (Diamond.Cross Diamond.RJ) tt = true /\
  PreFinalize.inserted Diamond.ctx diamond_plan (Diamond.Cross Diamond.LJ) tt = false.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example diamond_deletion :
  PreFinalize.deleted Diamond.ctx diamond_plan (Diamond.Real Diamond.Join) tt = true /\
  PreFinalize.deleted Diamond.ctx diamond_plan (Diamond.Real Diamond.Left) tt = false /\
  Map.get Diamond.edge_enc (Diamond.Real Diamond.Join) (PreFinalize.reload_versions diamond_plan) =
    Some (PreFinalize.Merged (Diamond.Bind Diamond.Join) tt).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example diamond_phi_selection :
  Map.get (PreFinalize.phi_encoding Diamond.ctx)
    ((Diamond.Bind Diamond.Join, Diamond.Cross Diamond.LJ), tt)
    (PreFinalize.phi_versions diamond_plan) =
      Some (PreFinalize.Computed (Diamond.Real Diamond.Left) tt) /\
  Map.get (PreFinalize.phi_encoding Diamond.ctx)
    ((Diamond.Bind Diamond.Join, Diamond.Cross Diamond.RJ), tt)
    (PreFinalize.phi_versions diamond_plan) =
      Some (PreFinalize.Inserted (Diamond.Cross Diamond.RJ) tt).
Proof.
  vm_compute. split; reflexivity.
Qed.

Definition loop_frg := PreOperands.build_frg Flow.loop_ctx.
Definition loop_facts := PreReset.solve Flow.loop_ctx loop_frg.
Definition loop_plan := PreFinalize.place Flow.loop_ctx loop_frg loop_facts.

(** The loop header reload and its backedge retain the original merged definition identity. *)
Example loop_pre_selection :
  Map.get Flow.edge_enc (Flow.compute Diamond.Left) (PreFinalize.reload_versions loop_plan) =
    Some (PreFinalize.Merged (Flow.bind Diamond.Left) tt) /\
  Map.get (PreFinalize.phi_encoding Flow.loop_ctx)
    ((Flow.bind Diamond.Left, Flow.cross 2%positive), tt) (PreFinalize.phi_versions loop_plan) =
    Some (PreFinalize.Merged (Flow.bind Diamond.Left) tt) /\
  Map.get (PreFinalize.phi_encoding Flow.loop_ctx)
    ((Flow.bind Diamond.Left, Flow.cross 1%positive), tt) (PreFinalize.phi_versions loop_plan) =
    Some (PreFinalize.Computed (Flow.compute Diamond.Entry) tt).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition sequential_frg := PreOperands.build_frg Flow.sequential_ctx.
Definition sequential_facts := PreReset.solve Flow.sequential_ctx sequential_frg.
Definition sequential_plan := PreFinalize.place Flow.sequential_ctx sequential_frg sequential_facts.

Example sequential_reload :
  Map.get Flow.edge_enc (Flow.again Diamond.Entry) (PreFinalize.reload_versions sequential_plan) =
    Some (PreFinalize.Computed (Flow.compute Diamond.Entry) tt) /\
  PreFinalize.deleted Flow.sequential_ctx sequential_plan (Flow.compute Diamond.Entry) tt = false /\
  PreFinalize.deleted Flow.sequential_ctx sequential_plan (Flow.again Diamond.Entry) tt = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example unsafe_no_motion :
  let f := PreOperands.build_frg unsafe_ctx in
  PreFinalize.place unsafe_ctx f (PreReset.solve unsafe_ctx f) = PreFinalize.empty_plan.
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_no_motion :
  let f := PreOperands.build_frg One.ctx in
  PreFinalize.place One.ctx f (PreReset.solve One.ctx f) = PreFinalize.empty_plan.
Proof.
  vm_compute. reflexivity.
Qed.

(** Phi evaluation reads from the same old cache even when the predecessor selects a merged slot. *)
Example phi_update_uses_old_selection :
  PreFinalize.phi_update Diamond.ctx diamond_plan (Diamond.Cross Diamond.LJ)
    (Diamond.Bind Diamond.Join)
    (fun v => match v with
      | PreFinalize.Computed (Diamond.Real Diamond.Left) _ => Some 7%nat
      | _ => None
      end)
    (PreFinalize.Merged (Diamond.Bind Diamond.Join) tt) = Some 7%nat.
Proof.
  vm_compute. reflexivity.
Qed.
