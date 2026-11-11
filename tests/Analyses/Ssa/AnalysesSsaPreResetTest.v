(** * Shared PRE reset query regressions

    The actual diamond and raw cyclic indexes distinguish the three reset guards.
    For example, a real-use link stops down-safety and still propagates later resets.
    Builds on: AnalysesSsaPreReset and the graph card's certified fixtures. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreOperands AnalysesSsaPreReset.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest AnalysesSsaPreFrgTest.
Import List.ListNotations.

Definition diamond_frg := PreOperands.build_frg Diamond.ctx.
Definition diamond_facts := PreReset.solve Diamond.ctx diamond_frg.

(** The original missing-arm diamond remains down-safe and can-available with later reset. *)
Example diamond_reset_flags :
  PreReset.flag Diamond.ctx (PreReset.downsafe diamond_facts) (Diamond.Join, tt) = true /\
  PreReset.flag Diamond.ctx (PreReset.can_available diamond_facts) (Diamond.Join, tt) = true /\
  PreReset.flag Diamond.ctx (PreReset.later diamond_facts) (Diamond.Join, tt) = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** The actual diamond supplies the unchanged independent-reset theorem's full domain. *)
Example diamond_resets_exact :
  forall k, FinSet.mem (PreFrg.phi_encoding Diamond.ctx) k (PreFrg.phis diamond_frg) = true ->
    (PreReset.flag Diamond.ctx (PreReset.downsafe diamond_facts) k = true <->
      ~ PreReset.down_unsafe Diamond.ctx diamond_frg k) /\
    (PreReset.flag Diamond.ctx (PreReset.can_available diamond_facts) k = true <->
      ~ PreReset.cannot Diamond.ctx diamond_frg
        (PreReset.flag Diamond.ctx (PreReset.downsafe diamond_facts)) k) /\
    (PreReset.flag Diamond.ctx (PreReset.later diamond_facts) k = true <->
      PreReset.flag Diamond.ctx (PreReset.can_available diamond_facts) k = true /\
      ~ PreReset.later_reset Diamond.ctx diamond_frg
        (PreReset.flag Diamond.ctx (PreReset.can_available diamond_facts)) k).
Proof.
  exact (PreReset.solve_exact Diamond.ctx Diamond.laws).
Qed.

(** The single-block producer has no phi flags to materialise. *)
Example singleton_empty_flags :
  PreReset.solve One.ctx (PreOperands.build_frg One.ctx) =
    PreReset.Facts Map.empty Map.empty Map.empty.
Proof.
  vm_compute. reflexivity.
Qed.

Definition raw_loop (real : bool) :
    PreFrg.frg Diamond.block Diamond.block_edge Diamond.edge unit :=
  PreFrg.Frg [PreFrg.Phi Diamond.Left tt; PreFrg.Phi Diamond.Join tt]
    Map.empty FinSet.empty
    (FinSet.of_list (PreFrg.phi_encoding Diamond.ctx) [(Diamond.Left, tt); (Diamond.Join, tt)])
    (Map.of_list (PreFrg.link_encoding Diamond.ctx)
      [(((Diamond.Join, tt), Diamond.LJ), PreFrg.Operand (PreFrg.Phi Diamond.Left tt) false);
       (((Diamond.Left, tt), Diamond.RJ), PreFrg.Operand (PreFrg.Phi Diamond.Join tt) real)])
    (FinSet.of_list (PreFrg.phi_encoding Diamond.ctx) [(Diamond.Left, tt)])
    PreFrg.Completed.

(** A real-use link stops the reverse query before the other phi. *)
Example real_use_stops_down :
  let facts := PreReset.solve Diamond.ctx (raw_loop true) in
  PreReset.flag Diamond.ctx (PreReset.downsafe facts) (Diamond.Left, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.downsafe facts) (Diamond.Join, tt) = true /\
  PreReset.flag Diamond.ctx (PreReset.later facts) (Diamond.Left, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.later facts) (Diamond.Join, tt) = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Removing the real-use guard propagates down-safety around the finite cycle. *)
Example no_real_use_resets_cycle :
  let facts := PreReset.solve Diamond.ctx (raw_loop false) in
  PreReset.flag Diamond.ctx (PreReset.downsafe facts) (Diamond.Left, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.downsafe facts) (Diamond.Join, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.later facts) (Diamond.Left, tt) = true /\
  PreReset.flag Diamond.ctx (PreReset.later facts) (Diamond.Join, tt) = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition unavailable_chain :
    PreFrg.frg Diamond.block Diamond.block_edge Diamond.edge unit :=
  PreFrg.Frg [PreFrg.Phi Diamond.Left tt; PreFrg.Phi Diamond.Join tt]
    Map.empty FinSet.empty
    (FinSet.of_list (PreFrg.phi_encoding Diamond.ctx) [(Diamond.Left, tt); (Diamond.Join, tt)])
    (Map.of_list (PreFrg.link_encoding Diamond.ctx)
      [(((Diamond.Left, tt), Diamond.RJ), PreFrg.Operand (PreFrg.Unavailable tt) false);
       (((Diamond.Join, tt), Diamond.LJ), PreFrg.Operand (PreFrg.Phi Diamond.Left tt) false)])
    (FinSet.of_list (PreFrg.phi_encoding Diamond.ctx) [(Diamond.Join, tt)])
    PreFrg.Completed.

(** An unavailable non-down-safe input resets its user and the dependent phi. *)
Example unavailable_propagates_cannot :
  let facts := PreReset.solve Diamond.ctx unavailable_chain in
  PreReset.flag Diamond.ctx (PreReset.can_available facts) (Diamond.Left, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.can_available facts) (Diamond.Join, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.later facts) (Diamond.Left, tt) = false /\
  PreReset.flag Diamond.ctx (PreReset.later facts) (Diamond.Join, tt) = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Shared preparation initializes both adjacency orientations for the existing search engine. *)
Example actual_preparation_ready :
  Prepared.ready (PreReset.arcs Diamond.ctx diamond_frg).
Proof.
  apply PreReset.arcs_ready. exact Diamond.laws.
Qed.

(** The nonempty incidence fixture pays a nonzero shared graph-construction charge. *)
Example graph_construction_is_charged :
  (0 <? Cost.ticks (PreReset.arcs_c Diamond.ctx (raw_loop true)))%N = true.
Proof.
  vm_compute. reflexivity.
Qed.
