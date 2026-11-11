(** * Complete families with independently repriced graph callbacks

    A lawful nonempty line retains arbitrary outgoing, source and target prices independently.
    For example, both checked branches satisfy the complete bounds for every triple of charges.
    Builds on: GraphDomInputCost, GraphDomCheckedCost and the hand-written line fixture. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphPreparedCost GraphFixtures
  GraphDomSpec GraphCheckDom GraphDomBackend GraphDomInputCost GraphDomGlobalCost
  GraphDomFiniteView GraphDomFiniteCost GraphDomCheckedCost GraphDomFastCheck GraphReach.
From Galois.Tests.Graph Require Import GraphDomCheckedCostTest.
Import List.ListNotations Cost.Notations.

Module CallbackCost.

Record prices := Prices {
  outgoing : N;
  source : N;
  target : N
}.

Definition budget k := (8 + outgoing k + source k + target k)%N.

Definition graph k :=
  let original := Prepared.graph Fixtures.Line.prepared in
  Graph.Make (Graph.entries original) (Graph.nodes original)
    (fun v => Cost.tick (outgoing k) ;; Graph.out_c original v)
    (fun e => Cost.tick (source k) ;; Graph.source_c original e)
    (fun e => Cost.tick (target k) ;; Graph.target_c original e).

Definition prepared k := Prepared.prepare nat_encoding (graph k).

Local Lemma out_value k v :
  Graph.out (graph k) v = Graph.out (Prepared.graph Fixtures.Line.prepared) v.
Proof.
  unfold graph. rewrite Graph.make_out. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma source_value k e :
  Graph.source (graph k) e = Graph.source (Prepared.graph Fixtures.Line.prepared) e.
Proof.
  unfold graph. rewrite Graph.make_source. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma target_value k e :
  Graph.target (graph k) e = Graph.target (Prepared.graph Fixtures.Line.prepared) e.
Proof.
  unfold graph. rewrite Graph.make_target. autorewrite with galois_cost. reflexivity.
Qed.

Example ready k : Prepared.ready (prepared k).
Proof.
  unfold prepared. apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - pose proof (proj1 Fixtures.Line.fixture_ready) as Hwf. constructor.
    + exact (nodes_nodup Hwf).
    + exact (entries_in Hwf).
    + intros v e He. rewrite source_value. apply (out_source Hwf v e).
      now rewrite <- out_value with (k := k).
    + intros v e Hv He. rewrite target_value. apply (out_target_in Hwf v e Hv).
      now rewrite <- out_value with (k := k).
  - intro v. rewrite out_value.
    exact (proj1 (proj2 Fixtures.Line.fixture_ready) v).
Qed.

Example outgoing_price k v : Cost.ticks (Graph.out_c (graph k) v) = (outgoing k + 1)%N.
Proof.
  unfold graph. cbn [Graph.out_c].
  rewrite Cost.ticks_bind, Cost.ticks_tick.
  change (outgoing k + Cost.ticks (Graph.out_c
    (Fixtures.graph [1]%nat [1; 2; 3; 4]%nat [(1, 2); (2, 3); (3, 4)]%nat) v) =
    outgoing k + 1)%N.
  unfold Fixtures.graph. now rewrite Graph.of_pure_out_cost.
Qed.

Example source_price k e : Cost.ticks (Graph.source_c (graph k) e) = (source k + 1)%N.
Proof.
  unfold graph. cbn [Graph.source_c].
  rewrite Cost.ticks_bind, Cost.ticks_tick.
  pose proof (Graph.of_pure_endpoint_cost [1]%nat [1; 2; 3; 4]%nat
    (fun v => filter (fun edge => Nat.eqb (fst edge) v) [(1, 2); (2, 3); (3, 4)]%nat)
    fst snd e) as [Hsource Htarget].
  apply f_equal. exact Hsource.
Qed.

Example target_price k e : Cost.ticks (Graph.target_c (graph k) e) = (target k + 1)%N.
Proof.
  unfold graph. cbn [Graph.target_c].
  rewrite Cost.ticks_bind, Cost.ticks_tick.
  pose proof (Graph.of_pure_endpoint_cost [1]%nat [1; 2; 3; 4]%nat
    (fun v => filter (fun edge => Nat.eqb (fst edge) v) [(1, 2); (2, 3); (3, 4)]%nat)
    fst snd e) as [Hsource Htarget].
  apply f_equal. exact Htarget.
Qed.

Local Lemma encoder_bounds v :
  In v [1; 2; 3; 4]%nat ->
  (Cost.ticks (encode_c nat_encoding v) <= 4)%N /\ (key_bits nat_encoding v <= 4)%N.
Proof.
  intro Hv. assert (Hwidth : (key_bits nat_encoding v <= 4)%N).
  { cbn [In] in Hv. destruct Hv as [<-|[<-|[<-|[<-|Hfalse]]]];
      [| | | |contradiction]; vm_compute; intuition discriminate. }
  pose proof (encode_cost_bound nat_encoding_cost_laws v). split; lia.
Qed.

Example primitive_bounds k :
  PreparedCost.prepare_bounds nat_encoding (graph k)
    (budget k) (budget k) (budget k) (budget k) (budget k).
Proof.
  constructor.
  - intros v Hv. destruct (encoder_bounds v Hv). unfold budget. split; lia.
  - intros v Hv. change (In v [1]%nat) in Hv. destruct Hv as [<-|Hfalse]; [|contradiction].
    destruct (encoder_bounds 1%nat (or_introl eq_refl)). unfold budget. split; lia.
  - intros v Hv. rewrite outgoing_price. unfold budget. lia.
  - intros e He. rewrite source_price, target_price, source_value, target_value.
    pose proof (proj1 (ready k)) as Hwf.
    unfold prepared in Hwf. rewrite Prepared.prepare_graph in Hwf.
    assert (Hsource : In (Graph.source (graph k) e) [1; 2; 3; 4]%nat).
    { unfold Prepared.all_edges in He. apply in_flat_map in He.
      destruct He as [v [Hv He]]. rewrite (out_source Hwf v e He). exact Hv. }
    assert (Htarget : In (Graph.target (graph k) e) [1; 2; 3; 4]%nat).
    { unfold Prepared.all_edges in He. apply in_flat_map in He.
      destruct He as [v [Hv He]]. exact (out_target_in Hwf v e Hv He). }
    rewrite source_value in Hsource. rewrite target_value in Htarget.
    destruct (encoder_bounds _ Hsource). destruct (encoder_bounds _ Htarget).
    unfold budget. repeat split; lia.
Qed.

Example input_bounds k : DomInputCost.bounds (prepared k) (budget k).
Proof.
  constructor.
  - exact (primitive_bounds k).
  - change (3 <= budget k)%N. unfold budget. lia.
  - change (5 <= budget k)%N. unfold budget. lia.
  - change (6 <= budget k)%N. unfold budget. lia.
Qed.

Example global_bounds k : DomGlobalCost.bounds (prepared k) 5 5 1 (budget k).
Proof.
  exact (DomInputCost.global_bounds (prepared k) (budget k) (ready k) (input_bounds k)).
Qed.

Local Lemma universe_ids k i :
  In i (Reach.universe (prepared k)) ->
  i = 1%positive \/ i = 2%positive \/ i = 3%positive \/ i = 4%positive.
Proof.
  intro Hi. vm_compute in Hi. intuition congruence.
Qed.

Local Lemma finite_small k :
  DomFiniteCost.bounds (prepared k) (Prepared.entry_ids (prepared k)) 5 5 1 4%N 4%N 4%N.
Proof.
  constructor.
  - vm_compute. lia.
  - vm_compute. lia.
  - intros v Hv. exact (encoder_bounds v Hv).
  - intros i Hi.
    destruct (universe_ids k i Hi) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst i;
      vm_compute; intuition discriminate.
  - intros i Hi. vm_compute in Hi. destruct Hi as [<-|Hfalse];
      [vm_compute; intuition discriminate|contradiction].
  - intros u ev Hu Hev.
    destruct (universe_ids k u Hu) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst u;
      vm_compute in Hev;
      try contradiction;
      (destruct Hev as [<-|Hfalse]; [vm_compute; intuition discriminate|contradiction]).
  - intros u Hu.
    destruct (universe_ids k u Hu) as [Hcase|[Hcase|[Hcase|Hcase]]]; subst u; vm_compute; lia.
  - vm_compute. lia.
  - vm_compute. intuition discriminate.
Qed.

Example finite_bounds k :
  DomFiniteCost.bounds (prepared k) (Prepared.entry_ids (prepared k))
    5 5 1 (budget k) (budget k) (budget k).
Proof.
  pose proof (finite_small k) as Hb. assert (Hbudget : (4 <= budget k)%N) by (unfold budget; lia).
  constructor.
  - exact (DomFiniteCost.input_nodes Hb).
  - exact (DomFiniteCost.input_roots Hb).
  - intros v Hv. destruct (DomFiniteCost.input_keys Hb v Hv). split; lia.
  - intros v Hv. pose proof (DomFiniteCost.universe_width Hb v Hv). lia.
  - intros v Hv. pose proof (DomFiniteCost.root_width Hb v Hv). lia.
  - intros u ev Hu Hev. pose proof (DomFiniteCost.row_width Hb u ev Hu Hev). lia.
  - intros u Hu. exact (DomFiniteCost.row_length Hb u Hu).
  - exact (DomFiniteCost.graph_edges Hb).
  - pose proof (DomFiniteCost.dense_width Hb). lia.
Qed.

Example normalized_fuel k :
  (N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared (prepared k) (Prepared.entry_ids (prepared k))))) <= budget k)%N.
Proof.
  assert (Hfuel : (N.pos (Pos.size (Prepared.fuel
    (DomFiniteView.prepared (prepared k) (Prepared.entry_ids (prepared k))))) <= 4)%N).
  { vm_compute. intuition discriminate. }
  unfold budget. lia.
Qed.

Example complete_lt_family :
  bigO (fun k : prices => DomGlobalCost.work 5 5 1 (budget k))
    (fun k => Cost.ticks (DomBackend.compute_c DomBackend.lt (prepared k))).
Proof.
  apply DomGlobalCost.lt_bigO; [exact ready|exact global_bounds].
Qed.

Example complete_nca_family :
  bigO (fun k : prices => DomGlobalCost.work 5 5 1 (budget k))
    (fun k => Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (prepared k))).
Proof.
  apply DomGlobalCost.semi_nca_bigO; [exact ready|exact global_bounds].
Qed.

Example complete_checked_lt_family :
  bigO (fun x : bool * prices => DomCheckedCost.wrapper_bound 5 5 1 3 (budget (snd x)) 3 4)
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.lt
      (prepared (snd x)) (selected_candidate (fst x)))).
Proof.
  apply DomCheckedCost.lt_bigO.
  - intro x. exact (ready (snd x)).
  - intro x. exact (global_bounds (snd x)).
  - intro x. exact (finite_bounds (snd x)).
  - intro x. exact (normalized_fuel (snd x)).
  - intro x. exact (selected_storage (fst x)).
  - intro x. exact (selected_size (fst x)).
  - intro x. exact (selected_skeleton (fst x)).
  - intro x. exact (selected_width (fst x)).
Qed.

Example complete_checked_nca_family :
  bigO (fun x : bool * prices => DomCheckedCost.wrapper_bound 5 5 1 3 (budget (snd x)) 3 4)
    (fun x => Cost.ticks (DomBackend.compute_checked_c DomBackend.semi_nca
      (prepared (snd x)) (selected_candidate (fst x)))).
Proof.
  apply DomCheckedCost.semi_nca_bigO.
  - intro x. exact (ready (snd x)).
  - intro x. exact (global_bounds (snd x)).
  - intro x. exact (finite_bounds (snd x)).
  - intro x. exact (normalized_fuel (snd x)).
  - intro x. exact (selected_storage (fst x)).
  - intro x. exact (selected_size (fst x)).
  - intro x. exact (selected_skeleton (fst x)).
  - intro x. exact (selected_width (fst x)).
Qed.

Example selected_decision k accepted :
  DomCheck.check (prepared k) (Dom.idom (selected_candidate accepted)) = accepted.
Proof.
  destruct accepted; vm_compute; reflexivity.
Qed.

Example accepted_branch k backend :
  DomBackend.compute_checked_c backend (prepared k) (selected_candidate true) =
    (DomFastCheck.check_c (prepared k) Fixtures.Line.parents ;;
      DomBackend.checked_candidate_c (prepared k) Fixtures.Line.parents).
Proof.
  apply DomBackend.compute_checked_accepted. exact (selected_decision k true).
Qed.

Example rejected_fallback k backend :
  DomBackend.compute_checked_c backend (prepared k) (selected_candidate false) =
    (DomFastCheck.check_c (prepared k) (Dom.idom (selected_candidate false)) ;;
      DomBackend.compute_c backend (prepared k)).
Proof.
  apply DomBackend.compute_checked_rejected. exact (selected_decision k false).
Qed.

End CallbackCost.
Import CallbackCost.
