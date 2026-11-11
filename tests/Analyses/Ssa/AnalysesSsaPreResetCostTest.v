(** * Primitive reset-cost clients

    Importing clients vary the block dictionary's actual callback charge on the nonempty diamond.
    For example, a higher charge changes solve ticks while leaving all reset flags unchanged.
    Builds on: AnalysesSsaPreResetCost and the certified graph-card diamond. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreOperands AnalysesSsaPreReset AnalysesSsaPreResetCost.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest AnalysesSsaPreFrgTest.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module Primitive.

Definition block_encoding charge : encoding Diamond.block :=
  Encoding (fun b => Cost.tick charge ;; encode_c Diamond.block_enc b).

(** The priced dictionary retains the original block identity. *)
Lemma block_value charge b :
  encode (block_encoding charge) b = encode Diamond.block_enc b.
Proof.
  reflexivity.
Qed.

(** The fixture's own adapter charges its supplied price and the original dictionary call. *)
Lemma block_cost charge b :
  Cost.ticks (encode_c (block_encoding charge) b) =
    charge + Cost.ticks (encode_c Diamond.block_enc b).
Proof.
  unfold block_encoding. cbn [encode_c]. rewrite Cost.ticks_bind, Cost.ticks_tick.
  reflexivity.
Qed.

Lemma block_width charge b :
  key_bits (block_encoding charge) b = key_bits Diamond.block_enc b.
Proof.
  change (N.pos (Pos.size (encode (block_encoding charge) b)) =
    N.pos (Pos.size (encode Diamond.block_enc b))).
  now rewrite block_value.
Qed.

Definition context charge :=
  Pre.Context Diamond.client
    (Pre.Encs (block_encoding charge) Diamond.be_enc Diamond.point_enc
      Diamond.edge_enc unit_encoding unit_encoding)
    Diamond.blocks Diamond.point_graph Diamond.tree.
Definition graph := PreOperands.build_frg Diamond.ctx.

Lemma laws charge : Pre.laws (context charge).
Proof.
  destruct Diamond.laws as [Hshape Hgraph Hkill Hruntime].
  constructor.
  - destruct Hshape. constructor; assumption.
  - destruct Hgraph. constructor; try assumption.
    constructor. intros x y Heq.
    apply (encode_injective Diamond.block_enc_laws).
    change (encode (block_encoding charge) x = encode (block_encoding charge) y) in Heq.
    now rewrite !block_value in Heq.
  - destruct Hkill. constructor; assumption.
  - destruct Hruntime. constructor; assumption.
Qed.

Lemma indexes charge :
  FinSet.wf (PreFrg.phi_encoding (context charge)) (PreFrg.phis graph) /\
  Map.wf (PreFrg.link_encoding (context charge)) (PreFrg.operands graph) /\
  FinSet.wf (PreFrg.phi_encoding (context charge)) (PreFrg.unsafe graph).
Proof.
  destruct (PreOperands.build_frg_indexes_wf Diamond.ctx) as [_ [_ [Hphi [Hlinks Hunsafe]]]].
  repeat split; assumption.
Qed.

Lemma source_block_bound b : PreResetCost.key_bound Diamond.block_enc b 4.
Proof.
  destruct b; vm_compute; intuition discriminate.
Qed.

Lemma source_edge_bound be : PreResetCost.key_bound Diamond.be_enc be 4.
Proof.
  destruct be; vm_compute; intuition discriminate.
Qed.

Lemma unit_bound x : PreResetCost.key_bound unit_encoding x 2.
Proof.
  unfold PreResetCost.key_bound.
  rewrite unit_encoding_cost, unit_encoding_bits. reflexivity.
Qed.

Lemma priced_block_bound charge b :
  PreResetCost.key_bound (block_encoding charge) b (charge + 4).
Proof.
  pose proof (source_block_bound b) as Hsource.
  unfold PreResetCost.key_bound in Hsource |- *.
  rewrite block_cost, block_width. lia.
Qed.

Lemma primitives charge :
  PreResetCost.primitive_bounds (context charge) graph (charge + 4).
Proof.
  constructor.
  - intros b [] Hin.
    change (PreResetCost.key_bound (block_encoding charge) b (charge + 4) /\
      PreResetCost.key_bound unit_encoding tt (charge + 4)).
    split; [apply priced_block_bound|].
    pose proof (unit_bound tt). unfold PreResetCost.key_bound in *. lia.
  - intros b [] be Hin.
    change (PreResetCost.key_bound (block_encoding charge) b (charge + 4) /\
      PreResetCost.key_bound unit_encoding tt (charge + 4) /\
      PreResetCost.key_bound Diamond.be_enc be (charge + 4)).
    split; [apply priced_block_bound|]. split.
    + pose proof (unit_bound tt). unfold PreResetCost.key_bound in *. lia.
    + pose proof (source_edge_bound be). unfold PreResetCost.key_bound in *. lia.
Qed.

(** Every owned price is derived for a nonempty actual producer while the encoder charge varies. *)
Example numeric_solve_client charge :
  Cost.ticks (PreReset.solve_c (context charge) graph) <=
    PreResetCost.solve_bound (context charge) graph (charge + 4).
Proof.
  destruct (indexes charge) as [Hphi [Hlinks Hunsafe]].
  apply PreResetCost.solve_cost; [apply laws|exact Hphi|exact Hlinks|exact Hunsafe|apply primitives].
Qed.

(** The uniform importing client changes an actual callback cost across its indexed family. *)
Example uniform_solve_client :
  bigO (fun charge => PreResetCost.solve_bound (context charge) graph (charge + 4))
    (fun charge => Cost.ticks (PreReset.solve_c (context charge) graph)).
Proof.
  apply PreResetCost.solve_bigO.
  - apply laws.
  - apply indexes.
  - apply primitives.
Qed.

Example varied_charge_preserves_flags charge :
  PreReset.solve (context charge) graph = PreReset.solve Diamond.ctx graph.
Proof.
  vm_compute. reflexivity.
Qed.

Example increased_callback_charge_is_retained :
  (Cost.ticks (PreReset.solve_c (context 0) graph) <?
    Cost.ticks (PreReset.solve_c (context 5) graph)) = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** An impossible primitive budget is rejected on an inventoried site of the actual producer. *)
Example zero_budget_rejected :
  ~ PreResetCost.primitive_bounds (context 0) graph 0.
Proof.
  intro Hbudget.
  assert (Hsite : In (inl (Diamond.Join, tt)) (PreReset.node_inventory (context 0) graph)).
  { vm_compute. tauto. }
  destruct (PreResetCost.site_components _ _ _ Hbudget Diamond.Join tt Hsite) as [Hb Hu].
  change (PreResetCost.key_bound unit_encoding tt 0) in Hu.
  unfold PreResetCost.key_bound in Hu.
  rewrite unit_encoding_cost, unit_encoding_bits in Hu. lia.
Qed.

Definition empty_graph : PreFrg.frg Diamond.block Diamond.block_edge Diamond.edge unit :=
  PreFrg.Frg [] Map.empty FinSet.empty FinSet.empty Map.empty FinSet.empty PreFrg.Completed.

Example empty_numeric_client :
  Cost.ticks (PreReset.solve_c Diamond.ctx empty_graph) <=
    PreResetCost.solve_bound Diamond.ctx empty_graph 0.
Proof.
  apply PreResetCost.solve_cost.
  - exact Diamond.laws.
  - apply FinSet.wf_empty.
  - apply Map.wf_empty.
  - apply FinSet.wf_empty.
  - constructor; intros; vm_compute in H; contradiction.
Qed.

End Primitive.
