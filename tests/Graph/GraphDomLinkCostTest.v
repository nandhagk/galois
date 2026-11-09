(** * Finite link-eval and shared-settlement cost clients

    Actual linked data and real graph prologues discharge the primitive finite-rank duties.
    For example, a two-link query excludes its root while retaining varying callback charges.
    Builds on: GraphDomLinkCost, GraphDomSemiCost and GraphFixtures. *)

From Stdlib Require Import List PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseInternCost.
From Galois.Graph Require Import GraphFixtures GraphDomLink GraphDomLinkCost GraphDomSemi
  GraphDomSemiCost.
Import Cost.Notations.

Definition linked_chain :=
  Cost.value (DomLink.link_c (Cost.value (DomLink.link_c DomLink.empty 4 3)) 3 2).

Definition scores :=
  Map.set positive_encoding 4%positive 3%positive
    (Map.set positive_encoding 3%positive 1%positive Map.empty).

Example linked_chain_bounded : DomLinkCost.bounded 4 linked_chain.
Proof.
  apply DomLinkCost.link_bounded.
  - apply DomLinkCost.link_bounded.
    + apply DomLinkCost.empty_bounded.
    + reflexivity.
    + vm_compute. intuition discriminate.
  - vm_compute. intuition discriminate.
  - vm_compute. intuition discriminate.
Qed.

Example scores_bounded : DomLinkCost.values_bounded 4 scores.
Proof.
  apply DomLinkCost.values_set.
  - apply DomLinkCost.values_set.
    + split; [apply Map.wf_empty|].
      intros v a Hget. rewrite Map.get_empty in Hget. discriminate.
    + vm_compute. intuition discriminate.
  - vm_compute. intuition discriminate.
Qed.

Example actual_linked_query_value :
  snd (Cost.value (DomLink.eval_c (DomLink.identity_value_c scores) linked_chain 4)) =
    3%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_linked_query_numeric_bound :
  (Cost.ticks (DomLink.eval_c (DomLink.identity_value_c scores) linked_chain 4%positive) <=
    N.pos 4%positive * (20 + 11 * key_bits positive_encoding 4%positive))%N.
Proof.
  apply DomLinkCost.eval_identity_cost.
  - exact scores_bounded.
  - exact linked_chain_bounded.
  - reflexivity.
Qed.

Definition expensive_score extra v :=
  Cost.tick extra ;; DomLink.identity_value_c scores v.

Example varying_score_callbacks_have_finite_prices extra :
  DomLinkCost.score_bounds 4 (expensive_score extra)
    (extra + 2 + key_bits positive_encoding 4%positive)%N (key_bits positive_encoding 4%positive).
Proof.
  intros v Hv. split.
  - unfold expensive_score. rewrite Cost.ticks_bind, Cost.ticks_tick, DomLinkCost.identity_cost.
    pose proof (InternCost.bits_monotone v 4 Hv) as Hwidth.
    change (key_bits positive_encoding v <= key_bits positive_encoding 4%positive)%N in Hwidth.
    lia.
  - change (key_bits positive_encoding (DomLink.identity_value scores v) <=
      key_bits positive_encoding 4%positive)%N.
    apply InternCost.bits_monotone.
    exact (DomLinkCost.identity_bounded 4 scores v scores_bounded Hv).
Qed.

Example varying_nonempty_compression_bound extra :
  (Cost.ticks (DomLink.compress_c (expensive_score extra) linked_chain 4%positive) <=
    N.pos 4%positive * DomLinkCost.compress_k (key_bits positive_encoding 4%positive)
      (extra + 2 + key_bits positive_encoding 4%positive) (key_bits positive_encoding 4%positive))%N.
Proof.
  apply DomLinkCost.compress_cost.
  - exact linked_chain_bounded.
  - exact (varying_score_callbacks_have_finite_prices extra).
  - reflexivity.
Qed.

Example actual_line_shared_settlement_bound :
  let shared := DomSemi.compute Fixtures.Line.prepared in
  DomSemiCost.state_bounded (DomSemiCost.rank_limit Fixtures.Line.prepared) (DomSemi.settled shared) /\
  (Cost.ticks (fold_left_c (DomSemi.settle_c (DomSemi.ranked shared))
    (DomSemi.reverse_order (DomSemi.ranked shared)) DomSemi.initial) <=
    DomSemiCost.settlement_bound (DomSemiCost.rank_limit Fixtures.Line.prepared)
      (DomSemi.ranked shared) (DomSemi.reverse_order (DomSemi.ranked shared)))%N.
Proof.
  apply DomSemiCost.actual_settlement_cost. exact Fixtures.Line.fixture_ready.
Qed.

Example actual_diamond_shared_settlement_bound :
  let shared := DomSemi.compute Fixtures.Diamond.prepared in
  DomSemiCost.state_bounded (DomSemiCost.rank_limit Fixtures.Diamond.prepared)
    (DomSemi.settled shared) /\
  (Cost.ticks (fold_left_c (DomSemi.settle_c (DomSemi.ranked shared))
    (DomSemi.reverse_order (DomSemi.ranked shared)) DomSemi.initial) <=
    DomSemiCost.settlement_bound (DomSemiCost.rank_limit Fixtures.Diamond.prepared)
      (DomSemi.ranked shared) (DomSemi.reverse_order (DomSemi.ranked shared)))%N.
Proof.
  apply DomSemiCost.actual_settlement_cost. exact Fixtures.Diamond.fixture_ready.
Qed.
