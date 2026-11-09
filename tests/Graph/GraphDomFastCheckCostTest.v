(** * Primitive fast-checker cost clients

    Actual nonempty inputs discharge all finite-data duties and retain varying encoder prices.
    For example, arbitrarily increasing the encoder charge changes the family bound explicitly.
    Builds on: GraphDomFastCheckCost and the line fixture. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseMapCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphReach
  GraphDomCheckBound GraphDomFiniteView GraphDomFiniteCost GraphDomFastCheck GraphDomFastCheckCost.
Import List.ListNotations Cost.Notations.

Definition charged_line (extra : N) :=
  Prepared.prepare (Encoding (fun v : nat => Cost.tick extra ;; encode_c nat_encoding v))
    (Prepared.graph Fixtures.Line.prepared).

Local Lemma listed_names extra v :
  In v (Graph.nodes (Prepared.graph (charged_line extra))) ->
    v = 1%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat.
Proof.
  change (In v [1; 2; 3; 4]%nat ->
    v = 1%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat).
  cbn [In]. intuition congruence.
Qed.

Local Lemma listed_ids extra i :
  In i (Reach.universe (charged_line extra)) ->
    i = 1%positive \/ i = 2%positive \/ i = 3%positive \/ i = 4%positive.
Proof.
  intro Hi. vm_compute in Hi. intuition congruence.
Qed.

Local Lemma encoder_cost extra v :
  Cost.ticks (encode_c (Prepared.node_enc (charged_line extra)) v) = (extra + 1)%N.
Proof.
  change (Cost.ticks (Cost.tick extra ;; encode_c nat_encoding v) = (extra + 1)%N).
  autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma encoder_bits extra v :
  key_bits (Prepared.node_enc (charged_line extra)) v = key_bits nat_encoding v.
Proof.
  reflexivity.
Qed.

(** The callback family inhabits every primitive and finite graph/root/width duty without a cost premise. *)
Example charged_line_bounds extra :
  DomFiniteCost.bounds (charged_line extra) (Prepared.entry_ids (charged_line extra))
    4 3 1 (extra + 1)%N 4%N 4%N.
Proof.
  constructor.
  - vm_compute. lia.
  - vm_compute. lia.
  - intros v Hv. split; [rewrite encoder_cost; reflexivity|].
    rewrite encoder_bits.
    destruct (listed_names extra v Hv) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst v;
      vm_compute; intuition discriminate.
  - intros i Hi.
    destruct (listed_ids extra i Hi) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst i;
      vm_compute; intuition discriminate.
  - intros i Hi. vm_compute in Hi. destruct Hi as [<-|Hfalse];
      [vm_compute; intuition discriminate|contradiction].
  - intros u ev Hu Hev.
    destruct (listed_ids extra u Hu) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst u;
      vm_compute in Hev;
      try contradiction;
      (destruct Hev as [<-|Hfalse]; [vm_compute; intuition discriminate|contradiction]).
  - intros u Hu.
    destruct (listed_ids extra u Hu) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst u;
      vm_compute; lia.
  - vm_compute. lia.
  - vm_compute. intuition discriminate.
Qed.

Example charged_line_fuel_width extra :
  (N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared (charged_line extra) (Prepared.entry_ids (charged_line extra))))) <=
    4)%N.
Proof.
  vm_compute. intuition discriminate.
Qed.

Example line_stored_width :
  DomCheckBound.stored_width Fixtures.Line.parents 3%N.
Proof.
  intros vu Hin. vm_compute in Hin.
  destruct Hin as [<-|[<-|[<-|Hfalse]]]; [| | |contradiction];
    vm_compute; intuition discriminate.
Qed.

Example all_callback_prices_have_a_closed_numeric_bound extra :
  (Cost.ticks (DomFastCheck.check_c (charged_line extra) Fixtures.Line.parents) <=
    DomFastCheckCost.checker_bound 4 3 1 3 (extra + 1) 4 4 3 4 4)%N.
Proof.
  apply DomFastCheckCost.check_cost.
  - exact (charged_line_bounds extra).
  - exact (charged_line_fuel_width extra).
  - exact Fixtures.Line.parents_wf.
  - vm_compute. lia.
  - vm_compute. intuition discriminate.
  - exact line_stored_width.
Qed.

Example varying_nonempty_callback_family :
  bigO (fun extra : N => DomFastCheckCost.checker_bound 4 3 1 3 (extra + 1) 4 4 3 4 4)
    (fun extra => Cost.ticks (DomFastCheck.check_c (charged_line extra) Fixtures.Line.parents)).
Proof.
  apply DomFastCheckCost.check_bigO.
  - intro extra. exact (charged_line_bounds extra).
  - intro extra. exact (charged_line_fuel_width extra).
  - intros _. exact Fixtures.Line.parents_wf.
  - intros _. vm_compute. lia.
  - intros _. vm_compute. intuition discriminate.
  - intros _. exact line_stored_width.
Qed.

Example actual_nonempty_table_upper_bound :
  (Cost.ticks (DomFastCheck.check_c (charged_line 0) Fixtures.Line.parents) <=
    DomFastCheckCost.table_k * (1 + N.of_nat 4) * (1 + N.of_nat 4 + N.of_nat 3) * (1 + 4))%N.
Proof.
  apply DomFastCheckCost.check_table_cost with (r := 1%nat) (ek := 1%N) (bk := 4%N).
  - exact (charged_line_bounds 0).
  - exact (charged_line_fuel_width 0).
  - exact Fixtures.Line.parents_wf.
  - vm_compute. lia.
  - intros vu Hvu. pose proof (line_stored_width vu Hvu) as [Hchild Hparent].
    split; lia.
  - lia.
  - lia.
  - reflexivity.
Qed.

Example excessive_callback_prices_stay_outside_the_restricted_table_domain :
  forall extra : N, (4 < extra)%N ->
  ~ (extra + 1 <= 4)%N.
Proof.
  intros extra Hlarge Hsmall. lia.
Qed.
