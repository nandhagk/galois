(** * Discharged full-pipeline cost clients

    Nonempty producer runs discharge primitive contracts and all finite input widths.
    For example, both complete tree bounds hold for every binary-natural encoder price.
    Builds on: GraphDomGlobalCost, public DomCost contracts and GraphFixtures. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphFixtures
  GraphDomCost GraphDomGlobalCost GraphDomBackend GraphDomVirtualCost GraphDomLayoutCost
  GraphDomPrologueCost GraphDomLtCost GraphDomOutputCost GraphDomInputCost GraphDomSize
  GraphDomVirtual.
Import List.ListNotations Cost.Notations.

Local Lemma callbacks_from_nodes {V E} (p : Prepared.t V E) w :
  Prepared.ready p ->
  (forall v, In v (Graph.nodes (Prepared.graph p)) ->
    (Cost.ticks (encode_c (Prepared.node_enc p) v) <= w)%N /\
      (key_bits (Prepared.node_enc p) v <= w)%N) ->
  (forall v, In v (Graph.nodes (Prepared.graph p)) ->
    (Cost.ticks (Graph.out_c (Prepared.graph p) v) <= w)%N) ->
  (forall e, In e (Prepared.all_edges (Prepared.graph p)) ->
    (Cost.ticks (Graph.source_c (Prepared.graph p) e) <= w)%N /\
      (Cost.ticks (Graph.target_c (Prepared.graph p) e) <= w)%N) ->
  PreparedCost.prepare_bounds (Prepared.node_enc p) (Prepared.graph p) w w w w w.
Proof.
  intros Hready Hkeys Hout Hedge. pose proof (proj1 Hready) as Hwf.
  constructor.
  - exact Hkeys.
  - intros v Hv. apply Hkeys. exact (entries_in Hwf v Hv).
  - exact Hout.
  - intros e He. destruct (Hedge e He) as [Hsource_cost Htarget_cost].
    unfold Prepared.all_edges in He. apply in_flat_map in He. destruct He as [v [Hv He]].
    assert (Hsource : In (Graph.source (Prepared.graph p) e) (Graph.nodes (Prepared.graph p))).
    { rewrite (out_source Hwf v e He). exact Hv. }
    pose proof (out_target_in Hwf v e Hv He) as Htarget.
    destruct (Hkeys _ Hsource) as [Hsource_key Hsource_width].
    destruct (Hkeys _ Htarget) as [Htarget_key Htarget_width].
    repeat split; assumption.
Qed.

Definition weighted_encoding extra :=
  Encoding (fun v : nat => Cost.tick extra ;; encode_c nat_encoding v).

Definition weighted_line extra :=
  Prepared.prepare (weighted_encoding extra) (Prepared.graph Fixtures.Line.prepared).

Example weighted_line_ready extra : Prepared.ready (weighted_line extra).
Proof.
  unfold weighted_line. apply Prepared.prepare_ready.
  - constructor. intros v u Hcode.
    apply (encode_injective nat_encoding_laws).
    exact Hcode.
  - exact (proj1 Fixtures.Line.fixture_ready).
  - exact (proj1 (proj2 Fixtures.Line.fixture_ready)).
Qed.

Local Lemma weighted_encoder_cost extra v :
  Cost.ticks (encode_c (Prepared.node_enc (weighted_line extra)) v) = (extra + 1)%N.
Proof.
  change (Cost.ticks (Cost.tick extra ;; encode_c nat_encoding v) = (extra + 1)%N).
  autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma weighted_encoder_bits extra v :
  key_bits (Prepared.node_enc (weighted_line extra)) v = key_bits nat_encoding v.
Proof.
  reflexivity.
Qed.

Example weighted_callbacks extra :
  PreparedCost.prepare_bounds (Prepared.node_enc (weighted_line extra))
    (Prepared.graph (weighted_line extra))
    (extra + 8)%N (extra + 8)%N (extra + 8)%N (extra + 8)%N (extra + 8)%N.
Proof.
  apply callbacks_from_nodes.
  - exact (weighted_line_ready extra).
  - intros v Hv. split.
    + rewrite weighted_encoder_cost. lia.
    + rewrite weighted_encoder_bits.
      assert (Hsmall : (key_bits nat_encoding v <= 8)%N).
      { change (In v [1; 2; 3; 4]%nat) in Hv. cbn [In] in Hv.
        destruct Hv as [Hcase|[Hcase|[Hcase|[Hcase|Hfalse]]]]; [| | | |contradiction];
          subst v; vm_compute; intuition discriminate. }
      lia.
  - intros v Hv. change (1 <= extra + 8)%N. lia.
  - intros edge He. change (1 <= extra + 8 /\ 1 <= extra + 8)%N. split; lia.
Qed.

Example weighted_bounds extra : DomGlobalCost.bounds (weighted_line extra) 5 5 1 (extra + 8)%N.
Proof.
  constructor.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - exact (weighted_callbacks extra).
  - change (3 <= extra + 8)%N. lia.
  - change (5 <= extra + 8)%N. lia.
  - change (6 <= extra + 8)%N. lia.
Qed.

Example complete_weighted_lt_bound extra :
  (Cost.ticks (DomBackend.compute_c DomBackend.lt (weighted_line extra)) <=
    DomCost.lt_k * DomGlobalCost.work 5 5 1 (extra + 8))%N.
Proof.
  apply DomCost.lt_cost.
  - exact (weighted_line_ready extra).
  - exact (weighted_bounds extra).
Qed.

Example complete_weighted_nca_bound extra :
  (Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (weighted_line extra)) <=
    DomCost.lt_k * DomGlobalCost.work 5 5 1 (extra + 8))%N.
Proof.
  apply DomCost.semi_nca_cost.
  - exact (weighted_line_ready extra).
  - exact (weighted_bounds extra).
Qed.

Example varying_nonempty_lt_family :
  bigO (fun extra : N => DomGlobalCost.work 5 5 1 (extra + 8))
    (fun extra => Cost.ticks (DomBackend.compute_c DomBackend.lt (weighted_line extra))).
Proof.
  apply DomCost.lt_bigO.
  - exact weighted_line_ready.
  - exact weighted_bounds.
Qed.

Example varying_nonempty_nca_family :
  bigO (fun extra : N => DomGlobalCost.work 5 5 1 (extra + 8))
    (fun extra => Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (weighted_line extra))).
Proof.
  apply DomCost.semi_nca_bigO.
  - exact weighted_line_ready.
  - exact weighted_bounds.
Qed.

(** Discharge fixture callbacks by node cases and their unit-price graph dictionaries. *)
Local Ltac unit_callbacks fixture_ready :=
  apply callbacks_from_nodes;
  [ exact fixture_ready
  | intros v Hv; split;
    [ change (1 <= 8)%N; lia
    | vm_compute in Hv; intuition subst; vm_compute; intuition discriminate ]
  | intros v Hv; change (1 <= 8)%N; lia
  | intros edge He; change (1 <= 8 /\ 1 <= 8)%N; split; lia ].

Example diamond_bounds : DomGlobalCost.bounds Fixtures.Diamond.prepared 5 6 1 8%N.
Proof.
  constructor; try solve [vm_compute; lia | vm_compute; intuition discriminate].
  unit_callbacks Fixtures.Diamond.fixture_ready.
Qed.

Example two_entry_bounds : DomGlobalCost.bounds Fixtures.TwoEntry.prepared 5 6 2 8%N.
Proof.
  constructor; try solve [vm_compute; lia | vm_compute; intuition discriminate].
  unit_callbacks Fixtures.TwoEntry.fixture_ready.
Qed.

Example unreachable_bounds : DomGlobalCost.bounds Fixtures.Unreachable.prepared 6 6 1 8%N.
Proof.
  constructor; try solve [vm_compute; lia | vm_compute; intuition discriminate].
  unit_callbacks Fixtures.Unreachable.fixture_ready.
Qed.

Example empty_bounds : DomGlobalCost.bounds Fixtures.Empty.prepared 1 1 0 8%N.
Proof.
  constructor; try solve [vm_compute; lia | vm_compute; intuition discriminate].
  unit_callbacks Fixtures.Empty.fixture_ready.
Qed.

Example full_multi_entry_lt_bound :
  (Cost.ticks (DomBackend.compute_c DomBackend.lt Fixtures.TwoEntry.prepared) <=
    DomCost.lt_k * DomGlobalCost.work 5 6 2 8)%N.
Proof.
  apply DomCost.lt_cost.
  - exact Fixtures.TwoEntry.fixture_ready.
  - exact two_entry_bounds.
Qed.

Example full_unreachable_nca_bound :
  (Cost.ticks (DomBackend.compute_c DomBackend.semi_nca Fixtures.Unreachable.prepared) <=
    DomCost.lt_k * DomGlobalCost.work 6 6 1 8)%N.
Proof.
  apply DomCost.semi_nca_cost.
  - exact Fixtures.Unreachable.fixture_ready.
  - exact unreachable_bounds.
Qed.

Example full_empty_lt_bound :
  (Cost.ticks (DomBackend.compute_c DomBackend.lt Fixtures.Empty.prepared) <=
    DomCost.lt_k * DomGlobalCost.work 1 1 0 8)%N.
Proof.
  apply DomCost.lt_cost.
  - exact Fixtures.Empty.fixture_ready.
  - exact empty_bounds.
Qed.

Example original_input_widths extra : DomInputCost.bounds (weighted_line extra) (extra + 8)%N.
Proof.
  constructor.
  - exact (weighted_callbacks extra).
  - change (3 <= extra + 8)%N. lia.
  - change (5 <= extra + 8)%N. lia.
  - change (6 <= extra + 8)%N. lia.
Qed.

Example input_only_nonempty_lt_family :
  bigO (fun extra : N => DomGlobalCost.work
    (DomInputCost.nodes (weighted_line extra))
    (DomInputCost.augmented_edges (weighted_line extra))
    (DomInputCost.roots (weighted_line extra)) (extra + 8))
    (fun extra => Cost.ticks (DomBackend.compute_c DomBackend.lt (weighted_line extra))).
Proof.
  apply DomInputCost.lt_bigO.
  - exact weighted_line_ready.
  - exact original_input_widths.
Qed.

Example input_only_nonempty_nca_bound extra :
  (Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (weighted_line extra)) <=
    DomGlobalCost.lt_k * DomGlobalCost.work
      (DomInputCost.nodes (weighted_line extra))
      (DomInputCost.augmented_edges (weighted_line extra))
      (DomInputCost.roots (weighted_line extra)) (extra + 8))%N.
Proof.
  apply DomInputCost.semi_nca_cost.
  - exact (weighted_line_ready extra).
  - exact (original_input_widths extra).
Qed.

Example multi_entry_augmented_budget_from_input :
  (edge_count (DomVirtual.graph (Prepared.node_enc Fixtures.TwoEntry.prepared)
    (Prepared.graph Fixtures.TwoEntry.prepared)) <=
    edge_count (Prepared.graph Fixtures.TwoEntry.prepared) +
      length (Graph.entries (Prepared.graph Fixtures.TwoEntry.prepared)))%nat.
Proof.
  apply DomSize.virtual_edges_bound.
  exact (Prepared.encoding_valid _ (proj2 (proj2 Fixtures.TwoEntry.fixture_ready))).
Qed.
