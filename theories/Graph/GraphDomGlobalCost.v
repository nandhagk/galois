(** * Input-size dominance bounds

    Global phase budgets reduce to vertex/augmented-edge products on primitive width domains.
    For example, repeated entries keep an occurrence term after virtual-root deduplication.
    Builds on: complete actual pipeline bounds and input-derived discovery/edge inventories. *)

From Stdlib Require Import List PArith NArith Arith Lia Ring.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseCode BaseInternCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphSearchSpec
  GraphSearchCost GraphDomVirtual GraphDomSemi GraphDomSize GraphDomLayoutCost GraphDomVirtualCost
  GraphDomPrologueCost GraphDomLtCost GraphDomNcaCost GraphDomOutputCost GraphDomNumberCost
  GraphDomPipelineCost GraphDomBackend GraphDomSemiCost.

Module DomGlobalCost.
Local Open Scope N_scope.

(** Bounds retain augmented edges, raw root multiplicity and primitive callback inventory. *)
Record bounds {V E} (p : Prepared.t V E) (n m r : nat) w : Prop := {
  nodes : (1 + length (Graph.nodes (Prepared.graph p)) <= n)%nat;
  original_edges : (1 + edge_count (Prepared.graph p) <= m)%nat;
  virtual_edges :
    (1 + edge_count (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)) <= m)%nat;
  roots : (length (Graph.entries (Prepared.graph p)) <= r)%nat;
  callbacks : PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) w w w w w;
  allocation_width : N.pos (Pos.size (Pos.of_succ_nat n)) <= w;
  input_fuel_width : N.pos (Pos.size (Pos.of_succ_nat (2 * n + m))) <= w;
  output_fuel_width : N.pos (Pos.size (Pos.of_succ_nat (2 * n + n * n + 1))) <= w
}.
Arguments nodes {V E p n m r w} _.
Arguments original_edges {V E p n m r w} _.
Arguments virtual_edges {V E p n m r w} _.
Arguments roots {V E p n m r w} _.
Arguments callbacks {V E p n m r w} _.
Arguments allocation_width {V E p n m r w} _.
Arguments input_fuel_width {V E p n m r w} _.
Arguments output_fuel_width {V E p n m r w} _.

Definition work (n m r : nat) w := (N.of_nat n * N.of_nat m + N.of_nat r) * (1 + w).
Definition virtual_k := 256 * (1 + InternCost.intern_k + encode_k).
Definition lt_k :=
  4096 * (1 + InternCost.intern_k + encode_k + SearchCost.search_k + TrieCost.trie_k).

Local Lemma bits_monotone_nat a b :
  (a <= b)%nat ->
  N.pos (Pos.size (Pos.of_succ_nat a)) <= N.pos (Pos.size (Pos.of_succ_nat b)).
Proof.
  intro Hab. apply InternCost.bits_monotone, Pos2Nat.inj_le.
  rewrite !SuccNat2Pos.id_succ. lia.
Qed.

Section Global.
Context {V E : Type} (p : Prepared.t V E) (n m r : nat) (w : N).
Local Abbreviation g := (DomVirtual.graph (Prepared.node_enc p) (Prepared.graph p)).
Local Abbreviation q := (DomVirtual.virtual p).
Local Abbreviation count := (DomOutputCost.count p).

Local Lemma virtual_nodes :
  length (Graph.nodes g) = (length (Graph.nodes (Prepared.graph p)) + 1)%nat.
Proof.
  rewrite DomVirtual.graph_equation. cbn [Graph.nodes].
  rewrite length_app, length_map. reflexivity.
Qed.

Local Lemma count_caps :
  Prepared.ready p -> bounds p n m r w -> (count <= n)%nat /\ (count <= m)%nat.
Proof.
  intros Hready Hb.
  pose proof (DomSize.actual_preorder_nodes p Hready) as Hnodes.
  pose proof (DomSize.actual_preorder_edges p Hready) as Hedges.
  pose proof (nodes Hb). pose proof (virtual_edges Hb).
  unfold DomOutputCost.count. split; lia.
Qed.

Local Lemma original_width :
  bounds p n m r w -> DomOutputCost.original_width p <= w.
Proof.
  intro Hb. eapply N.le_trans; [|exact (allocation_width Hb)].
  apply bits_monotone_nat. pose proof (nodes Hb). lia.
Qed.

Local Lemma raw_width :
  bounds p n m r w -> DomLayoutCost.raw_width p <= w.
Proof.
  intro Hb. eapply N.le_trans; [|exact (allocation_width Hb)].
  unfold DomLayoutCost.raw_width, PreparedCost.id_width.
  apply bits_monotone_nat. rewrite virtual_nodes. pose proof (nodes Hb). lia.
Qed.

Local Lemma rank_width :
  Prepared.ready p -> bounds p n m r w -> DomLayoutCost.rank_width p <= w.
Proof.
  intros Hready Hb. eapply N.le_trans; [|exact (allocation_width Hb)].
  unfold DomLayoutCost.rank_width. rewrite positive_encoding_bits.
  apply bits_monotone_nat. exact (proj1 (count_caps Hready Hb)).
Qed.

Local Lemma input_fuel :
  Prepared.ready p -> bounds p n m r w -> N.pos (Pos.size (Prepared.fuel q)) <= w.
Proof.
  intros Hready Hb. eapply N.le_trans; [|exact (input_fuel_width Hb)].
  apply InternCost.bits_monotone, Pos2Nat.inj_le. rewrite SuccNat2Pos.id_succ.
  pose proof (Prepared.fuel_value q (proj2 (proj2 (DomVirtual.virtual_ready p Hready)))) as Hfuel.
  rewrite DomVirtual.prepared_graph, virtual_nodes in Hfuel.
  pose proof (nodes Hb). pose proof (virtual_edges Hb). lia.
Qed.

Local Lemma output_fuel :
  Prepared.ready p -> bounds p n m r w -> DomNumberCost.fuel_width count <= w.
Proof.
  intros Hready Hb. eapply N.le_trans; [|exact (output_fuel_width Hb)].
  apply bits_monotone_nat.
  pose proof (proj1 (count_caps Hready Hb)) as Hcount.
  assert (Hsquare : (count * count <= n * n)%nat) by (apply Nat.mul_le_mono; assumption).
  lia.
Qed.

Local Lemma product_caps :
  Prepared.ready p -> bounds p n m r w ->
  1 <= N.of_nat n * N.of_nat m /\
  N.of_nat n <= N.of_nat n * N.of_nat m /\
  N.of_nat m <= N.of_nat n * N.of_nat m /\
  N.of_nat count <= N.of_nat n * N.of_nat m /\
  N.of_nat count * N.of_nat count <= N.of_nat n * N.of_nat m.
Proof.
  intros Hready Hb.
  pose proof (nodes Hb) as Hn. pose proof (original_edges Hb) as Hm.
  destruct (count_caps Hready Hb) as [Hcn Hcm].
  assert (Hone_n : 1 <= N.of_nat n) by lia.
  assert (Hone_m : 1 <= N.of_nat m) by lia.
  assert (Hn_bound : N.of_nat n <= N.of_nat n * N.of_nat m).
  { replace (N.of_nat n) with (N.of_nat n * 1) at 1 by ring.
    apply N.mul_le_mono; [reflexivity|exact Hone_m]. }
  assert (Hm_bound : N.of_nat m <= N.of_nat n * N.of_nat m).
  { replace (N.of_nat m) with (1 * N.of_nat m) at 1 by ring.
    apply N.mul_le_mono; [exact Hone_n|reflexivity]. }
  split.
  - change (1 * 1 <= N.of_nat n * N.of_nat m). now apply N.mul_le_mono.
  - split; [exact Hn_bound|]. split; [exact Hm_bound|]. split; [lia|].
    apply N.mul_le_mono; lia.
Qed.

Local Lemma output_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomOutputCost.output_bound p <=
    4 * DomOutputCost.output_k * (N.of_nat n * N.of_nat m) * (1 + w).
Proof.
  intros Hready Hb.
  pose proof (DomOutputCost.output_shape p w (original_width Hb)
    (rank_width Hready Hb) (output_fuel Hready Hb)) as Houtput.
  destruct (product_caps Hready Hb) as [Hone [Hn [Hm [Hcount Hsquare]]]].
  assert (Hcells : (1 + N.of_nat count) * (1 + N.of_nat count) <=
    4 * (N.of_nat n * N.of_nat m)).
  { replace ((1 + N.of_nat count) * (1 + N.of_nat count)) with
      (1 + 2 * N.of_nat count + N.of_nat count * N.of_nat count) by ring. lia. }
  eapply N.le_trans; [exact Houtput|].
  replace (DomOutputCost.output_k * (1 + N.of_nat count) * (1 + N.of_nat count) * (1 + w))
    with (DomOutputCost.output_k * ((1 + N.of_nat count) * (1 + N.of_nat count)) * (1 + w)) by ring.
  replace (4 * DomOutputCost.output_k * (N.of_nat n * N.of_nat m) * (1 + w))
    with (DomOutputCost.output_k * (4 * (N.of_nat n * N.of_nat m)) * (1 + w)) by ring.
  apply N.mul_le_mono; [apply N.mul_le_mono; [reflexivity|exact Hcells]|reflexivity].
Qed.

Local Lemma virtual_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomVirtualCost.virtual_bound p w w w w w <= (virtual_k + 8) * work n m r w.
Proof.
  intros Hready Hb.
  destruct (product_caps Hready Hb) as [Hone [Hn [Hm Hrest]]].
  set (nn := N.of_nat n) in *.
  set (mm := N.of_nat m) in *.
  set (rr := N.of_nat r).
  set (unit := 1 + w).
  set (target := work n m r w).
  set (price := 4 + 10 * encode_k).
  assert (Hproduct : nn * mm * unit <= target).
  { unfold target, work. fold nn mm rr unit. apply N.mul_le_mono; [lia|reflexivity]. }
  assert (Hroots : rr * unit <= target).
  { unfold target, work. fold nn mm rr unit. apply N.mul_le_mono; [lia|reflexivity]. }
  assert (Hplain : nn * mm <= target).
  { eapply N.le_trans; [|exact Hproduct].
    replace (nn * mm) with (nn * mm * 1) at 1 by ring.
    apply N.mul_le_mono; [reflexivity|unfold unit; lia]. }
  assert (Htarget : 1 <= target) by lia.
  assert (Hnode_cells : nn * unit <= target).
  { eapply N.le_trans; [|exact Hproduct]. now apply N.mul_le_mono. }
  assert (Hedge_cells : mm * unit <= target).
  { eapply N.le_trans; [|exact Hproduct]. now apply N.mul_le_mono. }
  assert (Hunit : unit <= target).
  { eapply N.le_trans; [|exact Hproduct].
    replace unit with (1 * unit) at 1 by ring. now apply N.mul_le_mono. }
  assert (Hnode_price : DomVirtualCost.node_price w w <= price * unit).
  { unfold DomVirtualCost.node_price, DomVirtualCost.node_width, price, unit.
    replace ((4 + 10 * encode_k) * (1 + w)) with
      (4 * (1 + w) + encode_k * (10 * (1 + w))) by ring.
    apply N.add_le_mono; [lia|]. apply N.mul_le_mono; lia. }
  assert (Hnode_width : DomVirtualCost.node_width w <= 10 * unit).
  { unfold DomVirtualCost.node_width, unit. lia. }
  assert (Hraw : PreparedCost.id_width g <= w) by exact (raw_width Hb).
  assert (Hnv : N.of_nat (length (Graph.nodes g)) <= nn).
  { rewrite virtual_nodes. pose proof (nodes Hb). unfold nn. lia. }
  assert (Hmv : N.of_nat (edge_count g) <= mm).
  { pose proof (virtual_edges Hb). unfold mm. lia. }
  assert (Hmo : N.of_nat (edge_count (Prepared.graph p)) <= mm).
  { pose proof (original_edges Hb). unfold mm. lia. }
  assert (Hno : N.of_nat (length (Graph.nodes (Prepared.graph p))) <= nn).
  { pose proof (nodes Hb). unfold nn. lia. }
  assert (Hro : N.of_nat (length (Graph.entries (Prepared.graph p))) <= rr).
  { pose proof (roots Hb). unfold rr. lia. }
  assert (Hgraph : DomVirtualCost.graph_bound (Prepared.graph p) w w <= 8 * target).
  { unfold DomVirtualCost.graph_bound.
    assert (Hcopy : 2 * N.of_nat (length (Graph.nodes (Prepared.graph p))) <= 2 * target) by lia.
    assert (Hentries : 3 * N.of_nat (length (Graph.entries (Prepared.graph p))) * (1 + w + w) +
      N.of_nat (length (Graph.entries (Prepared.graph p))) <= 6 * target).
    { eapply N.le_trans with (m := rr * (4 + 6 * w)).
      - replace (3 * N.of_nat (length (Graph.entries (Prepared.graph p))) * (1 + w + w) +
          N.of_nat (length (Graph.entries (Prepared.graph p)))) with
          (N.of_nat (length (Graph.entries (Prepared.graph p))) * (4 + 6 * w)) by ring.
        now apply N.mul_le_mono.
      - eapply N.le_trans with (m := 6 * (rr * unit)).
        + replace (6 * (rr * unit)) with (rr * (6 * unit)) by ring.
          apply N.mul_le_mono; [reflexivity|unfold unit; lia].
        + apply N.mul_le_mono; [reflexivity|exact Hroots]. }
    lia. }
  assert (Hprepare : DomVirtualCost.preparation_bound p w w w w w <= virtual_k * target).
  { assert (Hentries : length (Graph.entries g) = 1%nat).
    { rewrite DomVirtual.graph_equation. reflexivity. }
    assert (Hcap : DomVirtualCost.preparation_bound p w w w w w <=
      2 + nn * (20 + InternCost.intern_k + 5 * (price * unit) + 5 * (10 * unit) +
        3 * w + 3 * (1 + w + mm)) +
      mm * (17 + 4 * (price * unit) + 6 * (10 * unit) + (1 + w) + 2 * (1 + w)) +
      (3 + price * unit + 10 * unit)).
    { unfold DomVirtualCost.preparation_bound. fold g.
      rewrite Hentries. cbn [N.of_nat].
      unfold DomVirtualCost.outgoing_price.
      repeat match goal with
      | |- (?a + ?b <= ?c + ?d)%N => apply N.add_le_mono
      | |- (?a * ?b <= ?c * ?d)%N => apply N.mul_le_mono
      | |- _ => first [reflexivity | assumption | lia]
      end. }
    assert (Hnode_coefficient :
      20 + InternCost.intern_k + 5 * (price * unit) + 5 * (10 * unit) +
        3 * w + 3 * (1 + w + mm) <=
      (32 + InternCost.intern_k + 5 * price + 50) * unit + 3 * mm).
    { clear - w mm unit price. unfold unit. nia. }
    assert (Hedge_coefficient :
      17 + 4 * (price * unit) + 6 * (10 * unit) + (1 + w) + 2 * (1 + w) <=
        (23 + 4 * price + 60) * unit).
    { clear - w unit price. unfold unit. nia. }
    assert (Hentry_coefficient : 3 + price * unit + 10 * unit <= (3 + price + 10) * unit).
    { clear - w unit price. unfold unit. nia. }
    assert (Hnode : nn * (20 + InternCost.intern_k + 5 * (price * unit) + 5 * (10 * unit) +
        3 * w + 3 * (1 + w + mm)) <=
      (32 + InternCost.intern_k + 5 * price + 50) * target + 3 * target).
    { eapply N.le_trans; [apply N.mul_le_mono; [reflexivity|exact Hnode_coefficient]|].
      replace (nn * ((32 + InternCost.intern_k + 5 * price + 50) * unit + 3 * mm)) with
        ((32 + InternCost.intern_k + 5 * price + 50) * (nn * unit) + 3 * (nn * mm)) by ring.
      apply N.add_le_mono; apply N.mul_le_mono; try reflexivity; assumption. }
    assert (Hedge : mm * (17 + 4 * (price * unit) + 6 * (10 * unit) + (1 + w) + 2 * (1 + w)) <=
      (23 + 4 * price + 60) * target).
    { eapply N.le_trans; [apply N.mul_le_mono; [reflexivity|exact Hedge_coefficient]|].
      replace (mm * ((23 + 4 * price + 60) * unit)) with
        ((23 + 4 * price + 60) * (mm * unit)) by ring.
      now apply N.mul_le_mono. }
    assert (Hentry : 3 + price * unit + 10 * unit <= (3 + price + 10) * target).
    { eapply N.le_trans; [exact Hentry_coefficient|]. now apply N.mul_le_mono. }
    assert (Htwo : 2 <= 2 * target) by lia.
    eapply N.le_trans; [exact Hcap|].
    eapply N.le_trans.
    - apply N.add_le_mono; [|exact Hentry].
      apply N.add_le_mono; [|exact Hedge].
      apply N.add_le_mono; [exact Htwo|exact Hnode].
    - replace (2 * target + ((32 + InternCost.intern_k + 5 * price + 50) * target + 3 * target) +
        (23 + 4 * price + 60) * target + (3 + price + 10) * target) with
        ((183 + InternCost.intern_k + 10 * price) * target) by ring.
      apply N.mul_le_mono; [unfold virtual_k, price; lia|reflexivity]. }
  unfold DomVirtualCost.virtual_bound.
  replace ((virtual_k + 8) * target) with (8 * target + virtual_k * target) by ring.
  now apply N.add_le_mono.
Qed.

Local Lemma product_work :
  N.of_nat n * N.of_nat m * (1 + w) <= work n m r w.
Proof.
  unfold work. apply N.mul_le_mono; [lia|reflexivity].
Qed.

Local Lemma rank_value :
  N.pos (DomSemiCost.rank_limit p) = N.of_nat count + 1.
Proof.
  change (N.pos (Pos.of_succ_nat count) = N.of_nat count + 1).
  rewrite <- (N2Nat.id (N.pos (Pos.of_succ_nat count))).
  cbn [N.to_nat]. rewrite SuccNat2Pos.id_succ, Nat2N.inj_succ. lia.
Qed.

Local Lemma layout_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomLayoutCost.layout_bound p w w <= 24 * (N.of_nat n * N.of_nat m) * (1 + w).
Proof.
  intros Hready Hb.
  destruct (product_caps Hready Hb) as [Hone [Hn [Hm [Hcount Hsquare]]]].
  destruct (count_caps Hready Hb) as [Hcn Hcm].
  pose proof (raw_width Hb) as Hraw.
  pose proof (rank_width Hready Hb) as Hrank.
  set (c := N.of_nat count) in *.
  set (edges := N.of_nat (edge_count g)).
  set (product := N.of_nat n * N.of_nat m) in *.
  set (unit := 1 + w).
  assert (Hedge_count : edges <= N.of_nat m) by (pose proof (virtual_edges Hb); unfold edges; lia).
  assert (Hmass : c * edges <= product).
  { unfold product. apply N.mul_le_mono; [unfold c; lia|exact Hedge_count]. }
  change (c * (1 + (20 + 6 * DomLayoutCost.raw_width p + 4 * DomLayoutCost.rank_width p +
    w + w + edges * (3 + DomLayoutCost.raw_width p))) <= 24 * product * unit).
  assert (Hbase : 1 + (20 + 6 * DomLayoutCost.raw_width p + 4 * DomLayoutCost.rank_width p + w + w)
    <= 21 * unit) by (unfold unit; lia).
  assert (Hrow : edges * (3 + DomLayoutCost.raw_width p) <= edges * (3 * unit)).
  { apply N.mul_le_mono; [reflexivity|unfold unit; lia]. }
  eapply N.le_trans with (m := c * (21 * unit + edges * (3 * unit))).
  - apply N.mul_le_mono; [reflexivity|]. lia.
  - replace (c * (21 * unit + edges * (3 * unit))) with
      (21 * c * unit + 3 * (c * edges) * unit) by ring.
    replace (24 * product * unit) with (21 * product * unit + 3 * product * unit) by ring.
    apply N.add_le_mono; apply N.mul_le_mono; try reflexivity; now apply N.mul_le_mono.
Qed.

Local Lemma settlement_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomPrologueCost.settlement_bound p <= 80 * (N.of_nat n * N.of_nat m) * (1 + w).
Proof.
  intros Hready Hb.
  destruct (product_caps Hready Hb) as [Hone [Hn [Hm [Hcount Hsquare]]]].
  destruct (count_caps Hready Hb) as [Hcn Hcm].
  pose proof (rank_width Hready Hb) as Hrank.
  set (c := N.of_nat count) in *.
  set (edges := N.of_nat (edge_count g)).
  set (product := N.of_nat n * N.of_nat m) in *.
  set (unit := 1 + w).
  assert (Hedge_count : edges <= N.of_nat m) by (pose proof (virtual_edges Hb); unfold edges; lia).
  assert (Hedge_product : edges <= product) by lia.
  assert (Hlinks : edges * (c + 1) <= 2 * product).
  { assert (Hpair : edges * c <= product).
    { unfold product. rewrite N.mul_comm. apply N.mul_le_mono; [unfold c; lia|exact Hedge_count]. }
    replace (edges * (c + 1)) with (edges * c + edges) by ring. lia. }
  change (c * (13 + 6 * DomLayoutCost.rank_width p) +
    edges * (5 + 2 * DomLayoutCost.rank_width p +
      N.pos (DomSemiCost.rank_limit p) * (20 + 11 * DomLayoutCost.rank_width p)) <=
        80 * product * unit).
  rewrite rank_value. fold c.
  replace (c * (13 + 6 * DomLayoutCost.rank_width p) +
    edges * (5 + 2 * DomLayoutCost.rank_width p +
      (c + 1) * (20 + 11 * DomLayoutCost.rank_width p))) with
    (c * (13 + 6 * DomLayoutCost.rank_width p) +
      edges * (5 + 2 * DomLayoutCost.rank_width p) +
      (edges * (c + 1)) * (20 + 11 * DomLayoutCost.rank_width p)) by ring.
  eapply N.le_trans with (m := c * (13 * unit) + edges * (5 * unit) +
    (edges * (c + 1)) * (31 * unit)).
  - apply N.add_le_mono; [apply N.add_le_mono|];
      apply N.mul_le_mono; try reflexivity; unfold unit; lia.
  - replace (80 * product * unit) with
      (product * (13 * unit) + product * (5 * unit) + (2 * product) * (31 * unit)) by ring.
    apply N.add_le_mono; [apply N.add_le_mono|]; apply N.mul_le_mono; try reflexivity; assumption.
Qed.

Local Lemma search_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomPrologueCost.search_bound p <=
    7 * SearchCost.search_k * (N.of_nat n * N.of_nat m) * (1 + w).
Proof.
  intros Hready Hb.
  destruct (product_caps Hready Hb) as [Hone [Hn [Hm Hrest]]].
  pose proof (raw_width Hb) as Hraw.
  pose proof (input_fuel Hready Hb) as Hfuel.
  set (product := N.of_nat n * N.of_nat m) in *.
  set (unit := 1 + w).
  assert (Hnodes : N.of_nat (length (Graph.nodes g)) <= N.of_nat n).
  { rewrite virtual_nodes. pose proof (nodes Hb). lia. }
  assert (Hedges : N.of_nat (edge_count g) <= N.of_nat m) by (pose proof (virtual_edges Hb); lia).
  assert (Hinventory :
    N.of_nat (length (Graph.nodes g)) + N.of_nat (edge_count g) + 1 <= 3 * product) by lia.
  assert (Hunit : unit <= product * unit).
  { replace unit with (1 * unit) at 1 by ring. now apply N.mul_le_mono. }
  unfold DomPrologueCost.search_bound, SearchCost.search_size.
  rewrite (DomSize.virtual_entries p Hready), DomVirtual.prepared_graph.
  cbn [length]. change (SearchCost.search_k *
    ((N.of_nat (length (Graph.nodes g)) + N.of_nat (edge_count g) + 1) *
      (1 + DomLayoutCost.raw_width p + 1) + N.pos (Pos.size (Prepared.fuel q))) <=
    7 * SearchCost.search_k * product * unit).
  replace (7 * SearchCost.search_k * product * unit) with
    (SearchCost.search_k * ((3 * product) * (2 * unit) + product * unit)) by ring.
  apply N.mul_le_mono; [reflexivity|]. apply N.add_le_mono.
  - apply N.mul_le_mono; [exact Hinventory|unfold unit; lia].
  - unfold unit in Hunit. lia.
Qed.

Local Lemma finish_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomLtCost.finish_bound p <= 128 * (N.of_nat n * N.of_nat m) * (1 + w) /\
    16 * DomNcaCost.actual_work p <= 128 * (N.of_nat n * N.of_nat m) * (1 + w).
Proof.
  intros Hready Hb.
  destruct (product_caps Hready Hb) as [Hone [Hn [Hm [Hcount Hsquare]]]].
  pose proof (rank_width Hready Hb) as Hrank.
  set (c := N.of_nat count) in *.
  set (product := N.of_nat n * N.of_nat m) in *.
  set (unit := 1 + w).
  assert (Hcurve : c * (c + 1) <= 2 * product).
  { replace (c * (c + 1)) with (c * c + c) by ring. lia. }
  split.
  - unfold DomLtCost.finish_bound, DomSemiCost.eval_bound. cbn zeta.
    change (c * (33 + 16 * DomLayoutCost.rank_width p +
      N.pos (DomSemiCost.rank_limit p) * (20 + 11 * DomLayoutCost.rank_width p)) <=
        128 * product * unit).
    rewrite rank_value. fold c.
    replace (c * (33 + 16 * DomLayoutCost.rank_width p +
      (c + 1) * (20 + 11 * DomLayoutCost.rank_width p))) with
      (c * (33 + 16 * DomLayoutCost.rank_width p) +
        (c * (c + 1)) * (20 + 11 * DomLayoutCost.rank_width p)) by ring.
    eapply N.le_trans with (m := product * (33 * unit) + (2 * product) * (31 * unit)).
    + apply N.add_le_mono; apply N.mul_le_mono; try assumption; unfold unit; lia.
    + replace (product * (33 * unit) + (2 * product) * (31 * unit)) with
        (95 * product * unit) by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; lia|reflexivity].
  - unfold DomNcaCost.actual_work, DomNcaCost.width. cbn zeta.
    rewrite <- positive_encoding_bits.
    change (16 * (c * (1 + c) * (1 + DomLayoutCost.rank_width p)) <= 128 * product * unit).
    replace (16 * (c * (1 + c) * (1 + DomLayoutCost.rank_width p))) with
      (16 * (c * (c + 1)) * (1 + DomLayoutCost.rank_width p)) by ring.
    eapply N.le_trans with (m := (16 * (2 * product)) * unit).
    + apply N.mul_le_mono; [now apply N.mul_le_mono|unfold unit; lia].
    + replace (16 * (2 * product)) with (32 * product) by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono; lia|reflexivity].
Qed.

Local Lemma prologue_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomPrologueCost.prologue_bound p w w w w w <=
    (virtual_k + 112 + 7 * SearchCost.search_k) * work n m r w.
Proof.
  intros Hready Hb.
  pose proof (virtual_shape Hready Hb) as Hvirtual.
  pose proof (search_shape Hready Hb) as Hsearch.
  pose proof (layout_shape Hready Hb) as Hlayout.
  pose proof (settlement_shape Hready Hb) as Hsettle.
  assert (Hsearch_work : 7 * SearchCost.search_k * (N.of_nat n * N.of_nat m) * (1 + w) <=
    (7 * SearchCost.search_k) * work n m r w).
  { replace (7 * SearchCost.search_k * (N.of_nat n * N.of_nat m) * (1 + w)) with
      ((7 * SearchCost.search_k) * (N.of_nat n * N.of_nat m * (1 + w))) by ring.
    apply N.mul_le_mono; [reflexivity|apply product_work]. }
  assert (Hlayout_work : 24 * (N.of_nat n * N.of_nat m) * (1 + w) <= 24 * work n m r w).
  { replace (24 * (N.of_nat n * N.of_nat m) * (1 + w)) with
      (24 * (N.of_nat n * N.of_nat m * (1 + w))) by ring.
    apply N.mul_le_mono; [reflexivity|apply product_work]. }
  assert (Hsettle_work : 80 * (N.of_nat n * N.of_nat m) * (1 + w) <= 80 * work n m r w).
  { replace (80 * (N.of_nat n * N.of_nat m) * (1 + w)) with
      (80 * (N.of_nat n * N.of_nat m * (1 + w))) by ring.
    apply N.mul_le_mono; [reflexivity|apply product_work]. }
  unfold DomPrologueCost.prologue_bound.
  eapply N.le_trans.
  - apply N.add_le_mono; [|eapply N.le_trans; [exact Hsettle|exact Hsettle_work]].
    apply N.add_le_mono; [|eapply N.le_trans; [exact Hlayout|exact Hlayout_work]].
    apply N.add_le_mono; [exact Hvirtual|eapply N.le_trans; [exact Hsearch|exact Hsearch_work]].
  - ring_simplify. lia.
Qed.

Local Lemma total_shape :
  Prepared.ready p -> bounds p n m r w ->
  DomPipelineCost.lt_bound p w w w w w <= lt_k * work n m r w /\
    DomPipelineCost.nca_bound p w w w w w <= lt_k * work n m r w.
Proof.
  intros Hready Hb.
  pose proof (prologue_shape Hready Hb) as Hprologue.
  pose proof (output_shape Hready Hb) as Houtput.
  destruct (finish_shape Hready Hb) as [Hlt Hnca].
  assert (Hone_work : 1 <= work n m r w).
  { destruct (product_caps Hready Hb) as [Hone Hrest].
    eapply N.le_trans; [|apply product_work].
    eapply N.le_trans; [exact Hone|].
    replace (N.of_nat n * N.of_nat m) with (N.of_nat n * N.of_nat m * 1) at 1 by ring.
    apply N.mul_le_mono; [reflexivity|lia]. }
  assert (Hfinish_work : 128 * (N.of_nat n * N.of_nat m) * (1 + w) <= 128 * work n m r w).
  { replace (128 * (N.of_nat n * N.of_nat m) * (1 + w)) with
      (128 * (N.of_nat n * N.of_nat m * (1 + w))) by ring.
    apply N.mul_le_mono; [reflexivity|apply product_work]. }
  assert (Houtput_work : 4 * DomOutputCost.output_k * (N.of_nat n * N.of_nat m) * (1 + w) <=
    (4 * DomOutputCost.output_k) * work n m r w).
  { replace (4 * DomOutputCost.output_k * (N.of_nat n * N.of_nat m) * (1 + w)) with
      ((4 * DomOutputCost.output_k) * (N.of_nat n * N.of_nat m * (1 + w))) by ring.
    apply N.mul_le_mono; [reflexivity|apply product_work]. }
  assert (Hcoefficient :
    virtual_k + 241 + 7 * SearchCost.search_k + 4 * DomOutputCost.output_k <= lt_k).
  { unfold virtual_k, lt_k, DomOutputCost.output_k, DomNumberCost.number_k. lia. }
  assert (Haggregate :
    (virtual_k + 112 + 7 * SearchCost.search_k) * work n m r w +
      work n m r w + 128 * work n m r w + (4 * DomOutputCost.output_k) * work n m r w <=
        lt_k * work n m r w).
  { replace ((virtual_k + 112 + 7 * SearchCost.search_k) * work n m r w +
      work n m r w + 128 * work n m r w + (4 * DomOutputCost.output_k) * work n m r w) with
      ((virtual_k + 241 + 7 * SearchCost.search_k + 4 * DomOutputCost.output_k) *
        work n m r w) by ring.
    now apply N.mul_le_mono. }
  split.
  - unfold DomPipelineCost.lt_bound. eapply N.le_trans; [|exact Haggregate].
    apply N.add_le_mono; [|eapply N.le_trans; [exact Houtput|exact Houtput_work]].
    apply N.add_le_mono; [|eapply N.le_trans; [exact Hlt|exact Hfinish_work]].
    now apply N.add_le_mono.
  - unfold DomPipelineCost.nca_bound. eapply N.le_trans; [|exact Haggregate].
    apply N.add_le_mono; [|eapply N.le_trans; [exact Houtput|exact Houtput_work]].
    apply N.add_le_mono; [|eapply N.le_trans; [exact Hnca|exact Hfinish_work]].
    now apply N.add_le_mono.
Qed.

(** Complete LT trees satisfy the augmented-edge/vertex bound including roots and primitives. *)
Theorem lt_cost :
  Prepared.ready p -> bounds p n m r w ->
  Cost.ticks (DomBackend.compute_c DomBackend.lt p) <= lt_k * work n m r w.
Proof.
  intros Hready Hb.
  eapply N.le_trans; [exact (DomPipelineCost.lt_cost p w w w w w Hready (callbacks Hb))|].
  exact (proj1 (total_shape Hready Hb)).
Qed.

(** Complete NCA trees satisfy the product bound including their actual quadratic walk. *)
Theorem semi_nca_cost :
  Prepared.ready p -> bounds p n m r w ->
  Cost.ticks (DomBackend.compute_c DomBackend.semi_nca p) <= lt_k * work n m r w.
Proof.
  intros Hready Hb.
  eapply N.le_trans; [exact (DomPipelineCost.semi_nca_cost p w w w w w Hready (callbacks Hb))|].
  exact (proj2 (total_shape Hready Hb)).
Qed.

End Global.

(** The complete LT contract lifts to every family in the explicit primitive/data domain. *)
Theorem lt_bigO {X V E} (p : X -> Prepared.t V E) (n m r : X -> nat) (w : X -> N) :
  (forall x, Prepared.ready (p x)) -> (forall x, bounds (p x) (n x) (m x) (r x) (w x)) ->
  bigO (fun x => work (n x) (m x) (r x) (w x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.lt (p x))).
Proof.
  intros Hready Hb. exists lt_k. intro x.
  eapply N.le_trans; [exact (lt_cost (p x) (n x) (m x) (r x) (w x) (Hready x) (Hb x))|].
  apply N.mul_le_mono; [reflexivity|lia].
Qed.

(** The complete NCA family contract includes its shared prologue and actual annotation. *)
Theorem semi_nca_bigO {X V E} (p : X -> Prepared.t V E) (n m r : X -> nat) (w : X -> N) :
  (forall x, Prepared.ready (p x)) -> (forall x, bounds (p x) (n x) (m x) (r x) (w x)) ->
  bigO (fun x => work (n x) (m x) (r x) (w x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (p x))).
Proof.
  intros Hready Hb. exists lt_k. intro x.
  eapply N.le_trans; [exact (semi_nca_cost (p x) (n x) (m x) (r x) (w x) (Hready x) (Hb x))|].
  apply N.mul_le_mono; [reflexivity|lia].
Qed.

End DomGlobalCost.
