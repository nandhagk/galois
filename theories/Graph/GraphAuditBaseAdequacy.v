(** * Graph audit base adequacy

    Relates counted graph helpers to their source operations and cost bounds.
    For example, a tail-recursive reversal records one frame per input element.
    Builds on: GraphAuditBase and the collection audit adequacy lemmas. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditTrie
  CollectionsAuditMap CollectionsAuditMapAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
Import List.ListNotations.

(** * Generic counted traversals *)

(** Counted folds return the ordinary fold results. *)
Theorem audit_fold_holds : audit_fold_statement.
Proof.
  split.
  - intros A S C step f xs; induction xs as [|a rest IH]; intros initial Hstep.
    + reflexivity.
    + cbn [audit_fold_left fold_left].
      destruct (step initial a) as [next body] eqn:Hcall.
      pose proof (Hstep initial a) as Hvalue; rewrite Hcall in Hvalue; cbn in Hvalue; subst next.
      specialize (IH (f initial a) Hstep).
      destruct (audit_fold_left step rest (f initial a)); exact IH.
  - intros A S C step f xs; induction xs as [|a rest IH]; intros initial Hstep.
    + reflexivity.
    + cbn [audit_fold_right fold_right].
      specialize (IH initial Hstep).
      destruct (audit_fold_right step rest initial) as [middle events]; cbn in IH; subst middle.
      specialize (Hstep a (fold_right f initial rest)).
      destruct (step a (fold_right f initial rest)) as [result body]; exact Hstep.
Qed.

(** Counted list combinators return their standard results. *)
Theorem audit_list_map_filter_exists_holds : audit_list_map_filter_exists_statement.
Proof.
  repeat split.
  - intros A B C step f xs; induction xs as [|a rest IH]; intro Hstep; [reflexivity|].
    cbn [audit_map map].
    specialize (Hstep a) as Hcall.
    destruct (step a) as [value body]; cbn in Hcall; subst value.
    specialize (IH Hstep); destruct (audit_map step rest) as [later events]; cbn in IH.
    now rewrite IH.
  - intros A C step f xs; induction xs as [|a rest IH]; intro Hstep; [reflexivity|].
    cbn [audit_filter filter].
    specialize (Hstep a) as Hcall.
    destruct (step a) as [keep body]; cbn in Hcall; subst keep.
    specialize (IH Hstep); destruct (audit_filter step rest) as [later events]; cbn in IH.
    now rewrite IH.
  - intros A C step f xs; induction xs as [|a rest IH]; intro Hstep; [reflexivity|].
    cbn [audit_existsb_strict existsb].
    specialize (Hstep a) as Hcall.
    destruct (step a) as [here body]; cbn in Hcall; subst here.
    specialize (IH Hstep); destruct (audit_existsb_strict step rest) as [later events]; cbn in IH.
    now rewrite IH.
Qed.

(** Tail-recursive counted reversal captures its source run and exact work. *)
Theorem audit_graph_reverse_fast_counted_holds : audit_graph_reverse_fast_counted_statement.
Proof.
  intros A xs; induction xs as [|x rest IH]; intro acc.
  - cbn [audit_graph_reverse_fast_counted audit_graph_reverse_fast_work rev_append rev].
    repeat split; constructor.
  - cbn [audit_graph_reverse_fast_counted].
    specialize (IH (x :: acc)).
    destruct (audit_graph_reverse_fast_counted rest (x :: acc)) as [result work].
    destruct IH as [Hrun [Happend [Hrev Hwork]]].
    repeat split.
    + constructor; exact Hrun.
    + cbn [rev_append]; exact Happend.
    + cbn [rev]; rewrite Hrev, <- app_assoc; reflexivity.
    + rewrite Hwork; unfold audit_graph_reverse_fast_work; cbn [length]; lia.
Qed.

(** Tail-recursive reversal admits the run returned by the counted traversal. *)
Theorem audit_graph_reverse_fast_run_holds : audit_graph_reverse_fast_run_statement.
Proof.
  intros A xs acc.
  pose proof (audit_graph_reverse_fast_counted_holds A xs acc) as Hcounted.
  destruct (audit_graph_reverse_fast_counted xs acc) as [result work].
  exists result, work; exact Hcounted.
Qed.

(** Naive reversal admits its exact run and a quadratic bound. *)
Theorem audit_graph_reverse_run_holds : audit_graph_reverse_run_statement.
Proof.
  intros A xs; induction xs as [|x rest IH].
  - exists [], 1; split; [apply GraphReverseNil|].
    cbn [rev audit_graph_reverse_work]; repeat split; lia.
  - destruct IH as [result [work [Hrun [Hresult [Hwork Hbound]]]]].
    exists (result ++ [x]), (3 + length result + work).
    repeat split.
    + constructor; exact Hrun.
    + cbn [rev]; now rewrite Hresult.
    + cbn [length audit_graph_reverse_work]; rewrite Hresult, length_rev, Hwork; reflexivity.
    + rewrite Hresult, length_rev; cbn [length]; nia.
Qed.

Lemma audit_comb_call_count_app C (left right : list (audit_comb_event C)) :
  audit_comb_call_count (left ++ right) =
    audit_comb_call_count left + audit_comb_call_count right.
Proof.
  unfold audit_comb_call_count.
  induction left as [|event rest IH]; cbn; [reflexivity|].
  destruct event as [site|body]; [destruct site|]; cbn; rewrite IH; lia.
Qed.

Lemma audit_comb_call_count_bodies C (events : list C) :
  audit_comb_call_count (map AuditCombBody events) = 0.
Proof.
  induction events as [|event rest IH]; cbn [audit_comb_call_count]; auto.
Qed.

(** Positive iteration records exactly one call per source iteration. *)
Theorem audit_pos_iter_holds : audit_pos_iter_statement.
Proof.
  intros A C step f x fuel Hstep; revert x.
  induction fuel as [rest IH|rest IH|]; intro x.
  - cbn [audit_pos_iter Pos.iter].
    specialize (IH x) as Hfirst.
    destruct (audit_pos_iter step x rest) as [middle first].
    destruct Hfirst as [Hmiddle Hfirst].
    specialize (IH middle) as Hsecond.
    destruct (audit_pos_iter step middle rest) as [last second].
    destruct Hsecond as [Hlast Hsecond].
    pose proof (Hstep last) as Hvalue.
    destruct (step last) as [result events]; cbn in Hvalue; subst result.
    split.
    + now rewrite Hlast, Hmiddle.
    + change (audit_comb_call_count (first ++ second ++
        AuditCombCase 0 :: map AuditCombBody events) = Pos.to_nat rest~1).
      repeat rewrite audit_comb_call_count_app.
      change (audit_comb_call_count first + (audit_comb_call_count second +
        S (audit_comb_call_count (map AuditCombBody events))) = Pos.to_nat rest~1).
      rewrite audit_comb_call_count_bodies, Pos2Nat.inj_xI; lia.
  - cbn [audit_pos_iter Pos.iter].
    specialize (IH x) as Hfirst.
    destruct (audit_pos_iter step x rest) as [middle first].
    destruct Hfirst as [Hmiddle Hfirst].
    specialize (IH middle) as Hsecond.
    destruct (audit_pos_iter step middle rest) as [result second].
    destruct Hsecond as [Hresult Hsecond].
    split.
    + now rewrite Hresult, Hmiddle.
    + change (audit_comb_call_count (first ++ second) = Pos.to_nat rest~0).
      rewrite audit_comb_call_count_app, Pos2Nat.inj_xO; lia.
  - cbn [audit_pos_iter Pos.iter].
    pose proof (Hstep x) as Hvalue.
    destruct (step x) as [result events]; cbn in Hvalue; split; [exact Hvalue|].
    change (S (audit_comb_call_count (map AuditCombBody events)) = 1).
    rewrite audit_comb_call_count_bodies; reflexivity.
Qed.

(** Binary-natural iteration records its exact number of calls. *)
Theorem audit_n_iter_holds : audit_n_iter_statement.
Proof.
  intros A C step f x [|fuel] Hstep.
  - split; reflexivity.
  - cbn [audit_n_iter N.iter].
    pose proof (audit_pos_iter_holds A C step f x fuel Hstep) as Hiter.
    destruct (audit_pos_iter step x fuel) as [result events].
    cbn [audit_comb_call_count]; exact Hiter.
Qed.

(** * Preparation executions and event charges *)

Lemma audit_out_execution_exists V E (EV : encoding V) (g : Graph.t V E) nodes initial :
  exists events, audit_graph_prepare_out_execution EV g nodes initial
    (fold_right (fun v m => Map.set EV v (Graph.out g v) m) initial nodes) events.
Proof.
  induction nodes as [|v rest IH].
  - exists []; constructor.
  - destruct IH as [events Hrun].
    eexists; cbn [fold_right]; constructor; exact Hrun.
Qed.

Lemma audit_edges_execution_exists V E (EV : encoding V) (g : Graph.t V E) edges initial :
  exists events, audit_graph_prepare_edges_execution EV g edges initial
    (fold_right (index_edge EV g) initial edges) events.
Proof.
  induction edges as [|edge rest IH].
  - exists []; constructor.
  - destruct IH as [events Hrun].
    eexists; cbn [fold_right]; constructor; exact Hrun.
Qed.

Lemma audit_in_execution_exists V E (EV : encoding V) (g : Graph.t V E) nodes initial :
  exists events, audit_graph_prepare_in_execution EV g nodes initial
    (fold_right (fun v m => fold_right (index_edge EV g) m (Graph.out g v)) initial nodes) events.
Proof.
  induction nodes as [|v rest IH].
  - exists []; constructor.
  - destruct IH as [events Hrun].
    destruct (audit_edges_execution_exists V E EV g (Graph.out g v)
      (fold_right (fun v m => fold_right (index_edge EV g) m (Graph.out g v)) initial rest))
      as [edge_events Hedges].
    eexists; cbn [fold_right]; econstructor; eassumption.
Qed.

(** Every graph preparation has a run yielding the actual prepared graph. *)
Theorem audit_graph_prepare_execution_exists_holds :
  audit_graph_prepare_execution_exists_statement.
Proof.
  intros V E EV g.
  destruct (audit_out_execution_exists V E EV g (Graph.nodes g) Map.empty) as [out_events Hout].
  destruct (audit_in_execution_exists V E EV g (Graph.nodes g) Map.empty) as [in_events Hin].
  exists (prepare EV g), (out_events ++ in_events ++
    map (fun v => AuditPrepareOutCall v (Graph.out g v)) (rev (Graph.nodes g))).
  split; [|reflexivity].
  unfold prepare; constructor; assumption.
Qed.

Definition audit_event_sum {V E} (weight : audit_graph_prepare_call V E -> nat)
    (events : list (audit_graph_prepare_call V E)) : nat :=
  fold_right (fun event total => weight event + total) 0 events.

Lemma audit_event_sum_app V E (weight : audit_graph_prepare_call V E -> nat) left right :
  audit_event_sum weight (left ++ right) =
    audit_event_sum weight left + audit_event_sum weight right.
Proof.
  unfold audit_event_sum; induction left as [|event rest IH]; cbn; lia.
Qed.

Lemma audit_out_execution_weight V E (EV : encoding V) (g : Graph.t V E) nodes initial result
    events (weight : audit_graph_prepare_call V E -> nat) :
  (forall v, weight (AuditPrepareOutCall v (Graph.out g v)) = 0) ->
  audit_graph_prepare_out_execution EV g nodes initial result events ->
  audit_event_sum weight events =
    fold_right (fun v total => weight (AuditPrepareEncodeCall AuditGraphOutSet v (encode EV v)) +
      total) 0 nodes.
Proof.
  intros Hout Hrun; induction Hrun as [m|v rest initial middle events Hrun IH].
  - reflexivity.
  - rewrite audit_event_sum_app, IH; cbn [audit_event_sum fold_right]. rewrite Hout; lia.
Qed.

Lemma audit_edges_execution_weight V E (EV : encoding V) (g : Graph.t V E) edges initial result
    events (weight : audit_graph_prepare_call V E -> nat) :
  (forall e, weight (AuditPrepareTargetCall e (Graph.target g e)) = 0) ->
  audit_graph_prepare_edges_execution EV g edges initial result events ->
  audit_event_sum weight events =
    fold_right (fun e total =>
      weight (AuditPrepareEncodeCall AuditGraphIncomingGet (Graph.target g e)
        (encode EV (Graph.target g e))) +
      weight (AuditPrepareEncodeCall AuditGraphIncomingSet (Graph.target g e)
        (encode EV (Graph.target g e))) + total) 0 edges.
Proof.
  intros Htarget Hrun; induction Hrun as [m|edge rest initial middle events Hrun IH].
  - reflexivity.
  - rewrite audit_event_sum_app, IH; cbn [audit_event_sum fold_right]. rewrite Htarget; lia.
Qed.

Lemma audit_in_execution_weight V E (EV : encoding V) (g : Graph.t V E) nodes initial result
    events (weight : audit_graph_prepare_call V E -> nat) :
  (forall v, weight (AuditPrepareOutCall v (Graph.out g v)) = 0) ->
  (forall e, weight (AuditPrepareTargetCall e (Graph.target g e)) = 0) ->
  audit_graph_prepare_in_execution EV g nodes initial result events ->
  audit_event_sum weight events =
    fold_right (fun v total =>
      fold_right (fun e subtotal =>
        weight (AuditPrepareEncodeCall AuditGraphIncomingGet (Graph.target g e)
          (encode EV (Graph.target g e))) +
        weight (AuditPrepareEncodeCall AuditGraphIncomingSet (Graph.target g e)
          (encode EV (Graph.target g e))) + subtotal) total (Graph.out g v)) 0 nodes.
Proof.
  intros Hout Htarget Hrun.
  induction Hrun as [m|v rest initial middle final tail_events edge_events Hrun IH Hedges].
  - reflexivity.
  - rewrite !audit_event_sum_app, IH.
    rewrite (audit_edges_execution_weight V E EV g _ _ _ _ weight Htarget Hedges).
    cbn [audit_event_sum fold_right]; rewrite Hout.
    generalize (Graph.out g v); intro edges.
    induction edges as [|edge remaining IHedges]; cbn [fold_right] in *; lia.
Qed.

Lemma audit_fold_weight_offset A (first second : A -> nat) xs offset :
  fold_right (fun x total => first x + (second x + total)) offset xs =
    fold_right (fun x total => first x + (second x + total)) 0 xs + offset.
Proof.
  induction xs as [|x rest IH]; cbn; lia.
Qed.

Lemma audit_execution_weight V E (EV : encoding V) (g : Graph.t V E) result events
    (weight : audit_graph_prepare_call V E -> nat) :
  (forall v, weight (AuditPrepareOutCall v (Graph.out g v)) = 0) ->
  (forall e, weight (AuditPrepareTargetCall e (Graph.target g e)) = 0) ->
  audit_graph_prepare_execution EV g result events ->
  audit_event_sum weight events =
    fold_right (fun v total =>
      weight (AuditPrepareEncodeCall AuditGraphOutSet v (encode EV v)) +
      fold_right (fun e subtotal =>
        weight (AuditPrepareEncodeCall AuditGraphIncomingGet (Graph.target g e)
          (encode EV (Graph.target g e))) +
        weight (AuditPrepareEncodeCall AuditGraphIncomingSet (Graph.target g e)
          (encode EV (Graph.target g e))) + subtotal) total (Graph.out g v)) 0 (Graph.nodes g).
Proof.
  intros Hout Htarget Hrun; inversion Hrun as [out incoming out_events in_events Houts Hins]; subst.
  rewrite !audit_event_sum_app.
  rewrite (audit_out_execution_weight V E EV g _ _ _ _ weight Hout Houts).
  rewrite (audit_in_execution_weight V E EV g _ _ _ _ weight Hout Htarget Hins).
  assert (Hzero : audit_event_sum weight
    (map (fun v => AuditPrepareOutCall v (Graph.out g v)) (rev (Graph.nodes g))) = 0).
  { generalize (rev (Graph.nodes g)); intro nodes.
    unfold audit_event_sum; induction nodes as [|v rest IH]; cbn; rewrite ?Hout; lia. }
  rewrite Hzero.
  generalize (Graph.nodes g); intro nodes.
  induction nodes as [|v rest IH]; cbn [fold_right] in *; [lia|].
  rewrite <- IH.
  generalize (Graph.out g v); intro edges.
  induction edges as [|edge remaining IHedges]; cbn [fold_right] in *; lia.
Qed.

(** Map event charges equal the sum derived from the graph inputs. *)
Theorem audit_graph_prepare_map_model_holds : audit_graph_prepare_map_model_statement.
Proof.
  intros V E EV g result events Hrun.
  pose proof (audit_execution_weight V E EV g result events audit_graph_prepare_map_model_event
    (fun _ => eq_refl) (fun _ => eq_refl) Hrun) as Hweight.
  exact Hweight.
Qed.

(** Encoder event charges equal the sum derived from the graph inputs. *)
Theorem audit_graph_prepare_emission_holds : audit_graph_prepare_emission_statement.
Proof.
  intros V E EV g result events Hrun.
  pose proof (audit_execution_weight V E EV g result events audit_graph_prepare_emission_event
    (fun _ => eq_refl) (fun _ => eq_refl) Hrun) as Hweight.
  cbn [audit_graph_prepare_emission_event] in Hweight.
  change (audit_event_sum audit_graph_prepare_emission_event events =
    audit_graph_prepare_emission_expected EV g).
  rewrite Hweight; unfold audit_graph_prepare_emission_expected.
  assert (Hfold : forall edges base,
    fold_right (fun e total =>
      CollectionsAuditCost.audit_encoding_weight
        (CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e))) +
      CollectionsAuditCost.audit_encoding_weight
        (CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e))) + total)
      base edges =
    fold_right (fun e total =>
      2 * CollectionsAuditCost.audit_encoding_weight
        (CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e))) + total)
      base edges).
  { induction edges as [|edge remaining IHedges]; intro base; cbn; [reflexivity|].
    rewrite IHedges; unfold CollectionsAuditCost.audit_encoding_weight; cbn; lia. }
  generalize (Graph.nodes g); intro nodes; induction nodes as [|v rest IH].
  - reflexivity.
  - cbn [fold_right] in *; rewrite IH, Hfold; reflexivity.
Qed.

Lemma audit_out_counted_run V E (EV : encoding V) (g : Graph.t V E) nodes initial :
  let '(result, events) := audit_graph_prepare_out_counted EV g nodes initial in
  audit_graph_prepare_out_execution EV g nodes initial result events /\
  result = fold_right (fun v m => Map.set EV v (Graph.out g v) m) initial nodes /\
  length events = 2 * length nodes.
Proof.
  induction nodes as [|v rest IH]; cbn [audit_graph_prepare_out_counted].
  - repeat split; constructor.
  - destruct (audit_graph_prepare_out_counted EV g rest initial) as [middle events].
    destruct IH as [Hrun [Hresult Hlength]].
    split; [constructor; exact Hrun|].
    split.
    + cbn [fold_right]; rewrite <- Hresult; reflexivity.
    + rewrite length_app; cbn [length]; lia.
Qed.

Lemma audit_edges_counted_run V E (EV : encoding V) (g : Graph.t V E) edges initial :
  let '(result, events) := audit_graph_prepare_edges_counted EV g edges initial in
  audit_graph_prepare_edges_execution EV g edges initial result events /\
  result = fold_right (index_edge EV g) initial edges /\
  length events = 4 * length edges.
Proof.
  induction edges as [|edge rest IH]; cbn [audit_graph_prepare_edges_counted].
  - repeat split; constructor.
  - destruct (audit_graph_prepare_edges_counted EV g rest initial) as [middle events].
    destruct IH as [Hrun [Hresult Hlength]].
    split.
    + constructor; exact Hrun.
    + split.
      * cbn [fold_right]; rewrite <- Hresult; reflexivity.
      * rewrite length_app; cbn [length]; lia.
Qed.

Lemma audit_in_counted_run V E (EV : encoding V) (g : Graph.t V E) nodes initial :
  let '(result, events) := audit_graph_prepare_in_counted EV g nodes initial in
  audit_graph_prepare_in_execution EV g nodes initial result events /\
  result = fold_right (fun v m => fold_right (index_edge EV g) m (Graph.out g v)) initial nodes /\
  length events = length nodes +
    4 * fold_right (fun v total => length (Graph.out g v) + total) 0 nodes.
Proof.
  induction nodes as [|v rest IH]; cbn [audit_graph_prepare_in_counted].
  - repeat split; constructor.
  - destruct (audit_graph_prepare_in_counted EV g rest initial) as [middle events].
    destruct IH as [Hrun [Hresult Hlength]].
    pose proof (audit_edges_counted_run V E EV g (Graph.out g v) middle) as Hedges.
    destruct (audit_graph_prepare_edges_counted EV g (Graph.out g v) middle) as [final edge_events].
    destruct Hedges as [Hedge_run [Hedge_result Hedge_length]].
    split.
    + econstructor; eassumption.
    + split.
      * cbn [fold_right]; rewrite <- Hresult; exact Hedge_result.
      * rewrite !length_app; cbn [length fold_right]; lia.
Qed.

Lemma audit_edge_count_counted_run V E (g : Graph.t V E) nodes :
  let '(count, events) := audit_graph_edge_count_counted g nodes in
  count = fold_right (fun v total => length (Graph.out g v) + total) 0 nodes /\
  events = map (fun v => AuditPrepareOutCall v (Graph.out g v)) (rev nodes) /\
  length events = length nodes.
Proof.
  induction nodes as [|v rest IH]; cbn [audit_graph_edge_count_counted].
  - repeat split; reflexivity.
  - destruct (audit_graph_edge_count_counted g rest) as [count events].
    destruct IH as [Hcount [Hevents Hlength]].
    split; [cbn [fold_right]; now rewrite Hcount|].
    split.
    + cbn [rev]; rewrite map_app, <- Hevents; reflexivity.
    + rewrite length_app; cbn [length]; lia.
Qed.

Lemma audit_prepare_counted_run V E (EV : encoding V) (g : Graph.t V E) :
  let '(result, events) := audit_graph_prepare_counted EV g in
  audit_graph_prepare_execution EV g result events /\
  result = prepare EV g /\
  length events = audit_graph_prepare_callback_count g.
Proof.
  unfold audit_graph_prepare_counted.
  pose proof (audit_out_counted_run V E EV g (Graph.nodes g) Map.empty) as Hout.
  pose proof (audit_in_counted_run V E EV g (Graph.nodes g) Map.empty) as Hin.
  pose proof (audit_edge_count_counted_run V E g (Graph.nodes g)) as Hedges.
  destruct (audit_graph_prepare_out_counted EV g (Graph.nodes g) Map.empty) as [out out_events].
  destruct (audit_graph_prepare_in_counted EV g (Graph.nodes g) Map.empty) as [incoming in_events].
  destruct (audit_graph_edge_count_counted g (Graph.nodes g)) as [count edge_events].
  destruct Hout as [Hout [Hout_result Hout_length]].
  destruct Hin as [Hin [Hin_result Hin_length]].
  destruct Hedges as [Hcount [Hedge_events Hedge_length]].
  subst edge_events count.
  split.
  - constructor; assumption.
  - split.
    + unfold prepare; now rewrite Hout_result, Hin_result.
    + rewrite !length_app, length_map, length_rev.
      unfold audit_graph_prepare_callback_count; lia.
Qed.

Lemma audit_max_fold_member A (width : A -> nat) xs value :
  In value xs -> width value <= fold_right (fun x total => Nat.max (width x) total) 0 xs.
Proof.
  induction xs as [|x rest IH]; cbn; [contradiction|].
  intros [Heq|Hin].
  - subst value; apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma audit_nested_max_base A (width : A -> nat) xs base :
  base <= fold_right (fun x total => Nat.max (width x) total) base xs.
Proof.
  induction xs as [|x rest IH]; cbn; [lia|].
  eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
Qed.

Lemma audit_input_width_node V E (EV : encoding V) (g : Graph.t V E) v :
  In v (Graph.nodes g) ->
  CollectionsAuditCost.audit_key_bits_weight (encode EV v) <= audit_graph_prepare_input_width EV g.
Proof.
  unfold audit_graph_prepare_input_width.
  generalize (Graph.nodes g); intro nodes; induction nodes as [|node rest IH]; cbn;
    [contradiction|].
  intros [Heq|Hin].
  - subst node; apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|].
    eapply Nat.le_trans; [apply audit_nested_max_base|apply Nat.le_max_r].
Qed.

Lemma audit_input_width_edge V E (EV : encoding V) (g : Graph.t V E) v e :
  In v (Graph.nodes g) -> In e (Graph.out g v) ->
  CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <=
    audit_graph_prepare_input_width EV g.
Proof.
  unfold audit_graph_prepare_input_width.
  generalize (Graph.nodes g); intro nodes; induction nodes as [|node rest IH]; cbn;
    [contradiction|].
  intros [Heq|Hin] Hedge.
  - subst node; eapply Nat.le_trans; [|apply Nat.le_max_r].
    generalize (Graph.out g v), Hedge; intros edges Hin.
    induction edges as [|edge remaining IHedges]; cbn in *; [contradiction|].
    destruct Hin as [Heq|Hin].
    + subst edge; apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IHedges; exact Hin|apply Nat.le_max_r].
  - eapply Nat.le_trans; [apply IH; eassumption|].
    eapply Nat.le_trans; [apply audit_nested_max_base|apply Nat.le_max_r].
Qed.

Lemma audit_nested_sum_bound V E (g : Graph.t V E) (node_cost : V -> nat) (edge_cost : E -> nat)
    nodes limit :
  (forall v, In v nodes -> node_cost v <= limit) ->
  (forall v e, In v nodes -> In e (Graph.out g v) -> edge_cost e <= limit) ->
  fold_right (fun v total => node_cost v +
    fold_right (fun e subtotal => edge_cost e + subtotal) total (Graph.out g v)) 0 nodes <=
  (length nodes + fold_right (fun v total => length (Graph.out g v) + total) 0 nodes) * limit.
Proof.
  intros Hnodes Hedges; induction nodes as [|v rest IH]; cbn [fold_right length]; [lia|].
  assert (Hnode : node_cost v <= limit) by (apply Hnodes; now left).
  assert (Hrest :
    fold_right (fun v total => node_cost v +
      fold_right (fun e subtotal => edge_cost e + subtotal) total (Graph.out g v)) 0 rest <=
    (length rest + fold_right (fun v total => length (Graph.out g v) + total) 0 rest) * limit).
  { apply IH.
    - intros u Hin; apply Hnodes; now right.
    - intros u e Hin Hedge; apply Hedges with u; [now right|exact Hedge]. }
  assert (Hedge_bound : forall edges base,
    (forall e, In e edges -> edge_cost e <= limit) ->
    fold_right (fun e subtotal => edge_cost e + subtotal) base edges <=
      length edges * limit + base).
  { induction edges as [|e remaining IHedges]; intros base Hbound; cbn [fold_right length].
    - lia.
    - assert (He : edge_cost e <= limit) by (apply Hbound; now left).
      specialize (IHedges base); assert (Htail : forall x, In x remaining -> edge_cost x <= limit).
      { intros x Hin; apply Hbound; now right. }
      specialize (IHedges Htail); nia. }
  specialize (Hedge_bound (Graph.out g v)
    (fold_right (fun v total => node_cost v +
      fold_right (fun e subtotal => edge_cost e + subtotal) total (Graph.out g v)) 0 rest)).
  assert (Hall : forall e, In e (Graph.out g v) -> edge_cost e <= limit).
  { intros e Hin; apply Hedges with v; [now left|exact Hin]. }
  specialize (Hedge_bound Hall); nia.
Qed.

Lemma audit_prepare_map_input_bound V E (EV : encoding V) (g : Graph.t V E) :
  audit_graph_prepare_map_model_expected EV g <=
  (length (Graph.nodes g) + edge_count g) * (2 + 3 * audit_graph_prepare_input_width EV g).
Proof.
  unfold audit_graph_prepare_map_model_expected, edge_count.
  apply audit_nested_sum_bound.
  - intros v Hin; pose proof (audit_input_width_node V E EV g v Hin) as Hwidth.
    unfold CollectionsAuditCost.audit_set_weight; lia.
  - intros v e Hin Hedge; pose proof (audit_input_width_edge V E EV g v e Hin Hedge) as Hwidth.
    unfold CollectionsAuditCost.audit_set_weight, CollectionsAuditCost.audit_get_weight; lia.
Qed.

Lemma audit_prepare_emission_input_bound V E (EV : encoding V) (g : Graph.t V E) :
  audit_graph_prepare_emission_expected EV g <=
  (length (Graph.nodes g) + edge_count g) * (2 + 2 * audit_graph_prepare_input_width EV g).
Proof.
  unfold audit_graph_prepare_emission_expected, edge_count.
  apply audit_nested_sum_bound.
  - intros v Hin; pose proof (audit_input_width_node V E EV g v Hin) as Hwidth.
    unfold CollectionsAuditCost.audit_encoding_weight; lia.
  - intros v e Hin Hedge; pose proof (audit_input_width_edge V E EV g v e Hin Hedge) as Hwidth.
    unfold CollectionsAuditCost.audit_encoding_weight; lia.
Qed.

(** Counted preparation preserves its run, callbacks, and input-derived work budget. *)
Theorem audit_graph_prepare_model_holds : audit_graph_prepare_model_statement.
Proof.
  intros V E EV g.
  pose proof (audit_prepare_counted_run V E EV g) as Hrun.
  destruct (audit_graph_prepare_counted EV g) as [result events].
  destruct Hrun as [Hrun [Hresult Hlength]].
  repeat split; try assumption.
  rewrite (audit_graph_prepare_map_model_holds V E EV g result events Hrun).
  rewrite (audit_graph_prepare_emission_holds V E EV g result events Hrun).
  pose proof (audit_prepare_map_input_bound V E EV g) as Hmap.
  pose proof (audit_prepare_emission_input_bound V E EV g) as Hemission.
  unfold audit_graph_prepare_input_budget.
  unfold edge_count in *; nia.
Qed.

(** * Full and nested preparation *)

Lemma audit_nested_out_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) nodes initial :
  audit_prepare_callbacks_erase EV g cb ->
  let '(result, events) := audit_prepare_nested_out g cb nodes initial in
  (result, map fst events) = audit_graph_full_out EV g nodes initial.
Proof.
  intros [Hout [Htarget Hencode]].
  induction nodes as [|v rest IH]; cbn [audit_prepare_nested_out audit_graph_full_out].
  - reflexivity.
  - destruct (audit_prepare_nested_out g cb rest initial) as [middle events].
    destruct (audit_graph_full_out EV g rest initial) as [original trace].
    cbn in IH; inversion IH; subst original trace.
    pose proof (Hout v) as Houtv; pose proof (Hencode v) as Hcode.
    destruct (audit_prepare_out_model cb v) as [outgoing body].
    destruct (audit_prepare_encode_model cb v) as [code encode_body].
    cbn in Houtv, Hcode; subst outgoing code.
    cbn; rewrite map_app; reflexivity.
Qed.

Lemma audit_nested_edges_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) edges initial :
  audit_prepare_callbacks_erase EV g cb ->
  let '(result, events) := audit_prepare_nested_edges g cb edges initial in
  (result, map fst events) = audit_graph_full_edges EV g edges initial.
Proof.
  intros [Hout [Htarget Hencode]].
  induction edges as [|edge rest IH]; cbn [audit_prepare_nested_edges audit_graph_full_edges].
  - reflexivity.
  - destruct (audit_prepare_nested_edges g cb rest initial) as [middle events].
    destruct (audit_graph_full_edges EV g rest initial) as [original trace].
    cbn in IH; inversion IH; subst original trace.
    pose proof (Htarget edge) as Htarget_edge.
    destruct (audit_prepare_target_model cb edge) as [target target_body].
    cbn in Htarget_edge; subst target.
    pose proof (Hencode (Graph.target g edge)) as Hcode.
    destruct (audit_prepare_encode_model cb (Graph.target g edge)) as [code encode_body].
    cbn in Hcode; subst code.
    cbn; rewrite map_app; reflexivity.
Qed.

Lemma audit_nested_in_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) nodes initial :
  audit_prepare_callbacks_erase EV g cb ->
  let '(result, events) := audit_prepare_nested_in g cb nodes initial in
  (result, map fst events) = audit_graph_full_in EV g nodes initial.
Proof.
  intro Hcallbacks; destruct Hcallbacks as [Hout [Htarget Hencode]].
  induction nodes as [|v rest IH]; cbn [audit_prepare_nested_in audit_graph_full_in].
  - reflexivity.
  - destruct (audit_prepare_nested_in g cb rest initial) as [middle events].
    destruct (audit_graph_full_in EV g rest initial) as [original trace].
    cbn in IH; inversion IH; subst original trace.
    pose proof (Hout v) as Houtv.
    destruct (audit_prepare_out_model cb v) as [outgoing body].
    cbn in Houtv; subst outgoing.
    pose proof (audit_nested_edges_erases V E B EV g cb (Graph.out g v) middle
      (conj Hout (conj Htarget Hencode))) as Hedges.
    destruct (audit_prepare_nested_edges g cb (Graph.out g v) middle) as [final edge_events].
    destruct (audit_graph_full_edges EV g (Graph.out g v) middle) as [orig_final edge_trace].
    cbn in Hedges; inversion Hedges; subst orig_final edge_trace.
    cbn; rewrite !map_app; reflexivity.
Qed.

Lemma audit_nested_count_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) nodes :
  audit_prepare_callbacks_erase EV g cb ->
  let '(result, events) := audit_prepare_nested_edge_count g cb nodes in
  (result, map fst events) = audit_graph_full_edge_count g nodes.
Proof.
  intros [Hout [Htarget Hencode]].
  induction nodes as [|v rest IH];
    cbn [audit_prepare_nested_edge_count audit_graph_full_edge_count].
  - reflexivity.
  - destruct (audit_prepare_nested_edge_count g cb rest) as [count events].
    destruct (audit_graph_full_edge_count g rest) as [orig_count trace].
    cbn in IH; inversion IH; subst orig_count trace.
    pose proof (Hout v) as Houtv.
    destruct (audit_prepare_out_model cb v) as [outgoing body].
    cbn in Houtv; subst outgoing.
    cbn; rewrite map_app; reflexivity.
Qed.

Lemma audit_nested_prepare_erases V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) :
  audit_prepare_callbacks_erase EV g cb ->
  let '(result, events) := audit_graph_prepare_nested_counted EV g cb in
  (result, map fst events) = audit_graph_prepare_full_counted EV g.
Proof.
  intro Hcallbacks.
  pose proof (audit_nested_out_erases V E B EV g cb (Graph.nodes g) Map.empty Hcallbacks) as Hout.
  pose proof (audit_nested_in_erases V E B EV g cb (Graph.nodes g) Map.empty Hcallbacks) as Hin.
  pose proof (audit_nested_count_erases V E B EV g cb (Graph.nodes g) Hcallbacks) as Hcount.
  unfold audit_graph_prepare_nested_counted, audit_graph_prepare_full_counted.
  destruct (audit_prepare_nested_out g cb (Graph.nodes g) Map.empty) as [out out_events].
  destruct (audit_graph_full_out EV g (Graph.nodes g) Map.empty) as [orig_out orig_out_events].
  destruct (audit_prepare_nested_in g cb (Graph.nodes g) Map.empty) as [incoming in_events].
  destruct (audit_graph_full_in EV g (Graph.nodes g) Map.empty) as [orig_in orig_in_events].
  destruct (audit_prepare_nested_edge_count g cb (Graph.nodes g)) as [count edge_events].
  destruct (audit_graph_full_edge_count g (Graph.nodes g)) as [orig_count orig_edge_events].
  cbn in Hout, Hin, Hcount; inversion Hout; inversion Hin; inversion Hcount; subst.
  cbn; repeat rewrite map_app; cbn; rewrite ?map_app; reflexivity.
Qed.

Definition audit_full_event_bounded {V E} (width size : nat) (event : audit_graph_full_call V E)
    : Prop := audit_graph_full_event_work event <= 70 + 3 * width + 2 * size.

Lemma audit_full_out_bound V E (EV : encoding V) (g : Graph.t V E) nodes initial width size :
  (forall v, In v nodes ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV v) <= width) ->
  let '(result, events) := audit_graph_full_out EV g nodes initial in
  result = fold_right (fun v m => Map.set EV v (Graph.out g v) m) initial nodes /\
  length events = 1 + 3 * length nodes /\
  Forall (audit_full_event_bounded width size) events.
Proof.
  intro Hwidth; induction nodes as [|v rest IH]; cbn [audit_graph_full_out].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor;
      [unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia|constructor].
  - assert (Hrest : forall u, In u rest ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV u) <= width).
    { intros u Hin; apply Hwidth; now right. }
    specialize (IH Hrest).
    destruct (audit_graph_full_out EV g rest initial) as [middle events].
    destruct IH as [Hresult [Hlength Hbound]].
    split; [cbn [fold_right]; now rewrite <- Hresult|].
    split; [cbn [length]; rewrite length_app; cbn [length]; lia|].
    constructor.
    + unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      assert (Hv : CollectionsAuditCost.audit_key_bits_weight (encode EV v) <= width)
        by (apply Hwidth; now left).
      constructor.
      * unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia.
      * constructor.
        -- unfold audit_full_event_bounded, audit_graph_full_event_work,
             audit_graph_prepare_map_model_event, audit_graph_prepare_emission_event,
             CollectionsAuditCost.audit_set_weight, CollectionsAuditCost.audit_encoding_weight;
             cbn; lia.
        -- constructor.
Qed.

Lemma audit_full_edges_bound V E (EV : encoding V) (g : Graph.t V E) edges initial width size :
  (forall e, In e edges ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width) ->
  let '(result, events) := audit_graph_full_edges EV g edges initial in
  result = fold_right (index_edge EV g) initial edges /\
  length events = 1 + 6 * length edges /\
  Forall (audit_full_event_bounded width size) events.
Proof.
  intro Hwidth; induction edges as [|edge rest IH]; cbn [audit_graph_full_edges].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor;
      [unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia|constructor].
  - assert (Hrest : forall e, In e rest ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
    { intros e Hin; apply Hwidth; now right. }
    specialize (IH Hrest).
    destruct (audit_graph_full_edges EV g rest initial) as [middle events].
    destruct IH as [Hresult [Hlength Hbound]].
    split; [cbn [fold_right]; now rewrite <- Hresult|].
    split; [cbn [length]; rewrite length_app; cbn [length]; lia|].
    constructor.
    + unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      assert (Hedge : CollectionsAuditCost.audit_key_bits_weight
        (encode EV (Graph.target g edge)) <= width) by (apply Hwidth; now left).
      destruct (Map.code_get (encode EV (Graph.target g edge)) middle).
      all: repeat (constructor; [unfold audit_full_event_bounded, audit_graph_full_event_work,
        audit_graph_prepare_map_model_event, audit_graph_prepare_emission_event,
        CollectionsAuditCost.audit_get_weight, CollectionsAuditCost.audit_set_weight,
        CollectionsAuditCost.audit_encoding_weight; cbn; lia|]); constructor.
Qed.

Lemma audit_full_in_bound V E (EV : encoding V) (g : Graph.t V E) nodes initial width size :
  (forall v e, In v nodes -> In e (Graph.out g v) ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width) ->
  let '(result, events) := audit_graph_full_in EV g nodes initial in
  result = fold_right (fun v m => fold_right (index_edge EV g) m (Graph.out g v)) initial nodes /\
  length events = 1 + 3 * length nodes +
    6 * fold_right (fun v total => length (Graph.out g v) + total) 0 nodes /\
  Forall (audit_full_event_bounded width size) events.
Proof.
  intro Hwidth; induction nodes as [|v rest IH]; cbn [audit_graph_full_in].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor;
      [unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia|constructor].
  - assert (Hrest : forall u e, In u rest -> In e (Graph.out g u) ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
    { intros u e Hin Hedge; apply Hwidth with u; [now right|exact Hedge]. }
    specialize (IH Hrest).
    destruct (audit_graph_full_in EV g rest initial) as [middle events].
    destruct IH as [Hresult [Hlength Hbound]].
    assert (Hedge_width : forall e, In e (Graph.out g v) ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
    { intros e Hin; apply Hwidth with v; [now left|exact Hin]. }
    pose proof (audit_full_edges_bound V E EV g (Graph.out g v) middle width size Hedge_width)
      as Hedges.
    destruct (audit_graph_full_edges EV g (Graph.out g v) middle) as [final edge_events].
    destruct Hedges as [Hedge_result [Hedge_length Hedge_bound]].
    split; [cbn [fold_right]; rewrite <- Hresult; exact Hedge_result|].
    split; [cbn [length]; rewrite !length_app; cbn [length fold_right]; lia|].
    constructor.
    + unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      constructor.
      * unfold audit_full_event_bounded, audit_graph_full_event_work,
          audit_graph_prepare_map_model_event, audit_graph_prepare_emission_event; cbn; lia.
      * exact Hedge_bound.
Qed.

Lemma audit_full_count_bound V E (g : Graph.t V E) nodes width size :
  (forall v, In v nodes -> length (Graph.out g v) <= size) ->
  let '(result, events) := audit_graph_full_edge_count g nodes in
  result = fold_right (fun v total => length (Graph.out g v) + total) 0 nodes /\
  length events = 1 + 3 * length nodes /\
  Forall (audit_full_event_bounded width size) events.
Proof.
  intro Hsize; induction nodes as [|v rest IH]; cbn [audit_graph_full_edge_count].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor;
      [unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia|constructor].
  - assert (Hrest : forall u, In u rest -> length (Graph.out g u) <= size).
    { intros u Hin; apply Hsize; now right. }
    specialize (IH Hrest).
    destruct (audit_graph_full_edge_count g rest) as [count events].
    destruct IH as [Hcount [Hlength Hbound]].
    split; [cbn [fold_right]; now rewrite Hcount|].
    split; [cbn [length]; rewrite length_app; cbn [length]; lia|].
    constructor.
    + unfold audit_full_event_bounded, audit_graph_full_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      assert (Hv : length (Graph.out g v) <= size) by (apply Hsize; now left).
      repeat (constructor; [unfold audit_full_event_bounded, audit_graph_full_event_work,
        audit_graph_prepare_map_model_event, audit_graph_prepare_emission_event; cbn; lia|]).
      constructor.
Qed.

Lemma audit_edge_count_member V E (g : Graph.t V E) nodes v :
  In v nodes -> length (Graph.out g v) <=
    fold_right (fun u total => length (Graph.out g u) + total) 0 nodes.
Proof.
  induction nodes as [|u rest IH]; cbn; [contradiction|].
  intros [Heq|Hin]; [subst u; lia|specialize (IH Hin); lia].
Qed.

Definition audit_full_sum {V E} (events : list (audit_graph_full_call V E)) : nat :=
  fold_right (fun event total => audit_graph_full_event_work event + total) 0 events.

Lemma audit_full_sum_app V E (left right : list (audit_graph_full_call V E)) :
  audit_full_sum (left ++ right) = audit_full_sum left + audit_full_sum right.
Proof.
  unfold audit_full_sum; induction left as [|event rest IH]; cbn in *; lia.
Qed.

Lemma audit_full_sum_bound V E width size (events : list (audit_graph_full_call V E)) :
  Forall (audit_full_event_bounded width size) events ->
  audit_full_sum events <= length events * (70 + 3 * width + 2 * size).
Proof.
  intro Hbound; induction Hbound as [|event rest Hevent Hrest IH].
  - reflexivity.
  - unfold audit_full_event_bounded in Hevent; unfold audit_full_sum in *; cbn in *; nia.
Qed.

(** Full preparation preserves its result and obeys the published event and work budgets. *)
Theorem audit_graph_prepare_full_correct : audit_graph_prepare_full_statement.
Proof.
  intros V E EV g.
  set (width := audit_graph_prepare_input_width EV g).
  set (nodes := length (Graph.nodes g)).
  set (edges := edge_count g).
  set (size := nodes + edges).
  assert (Hnode_width : forall v, In v (Graph.nodes g) ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV v) <= width).
  { intros v Hin; apply audit_input_width_node; exact Hin. }
  assert (Hedge_width : forall v e, In v (Graph.nodes g) -> In e (Graph.out g v) ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
  { intros v e Hin Hedge; eapply audit_input_width_edge; eassumption. }
  assert (Hsize : forall v, In v (Graph.nodes g) -> length (Graph.out g v) <= size).
  { intros v Hin; pose proof (audit_edge_count_member V E g (Graph.nodes g) v Hin) as Hmember.
    unfold size, edges, edge_count in *; lia. }
  pose proof (audit_full_out_bound V E EV g (Graph.nodes g) Map.empty width size Hnode_width)
    as Hout.
  pose proof (audit_full_in_bound V E EV g (Graph.nodes g) Map.empty width size Hedge_width)
    as Hin.
  pose proof (audit_full_count_bound V E g (Graph.nodes g) width size Hsize) as Hcount.
  unfold audit_graph_prepare_full_counted.
  destruct (audit_graph_full_out EV g (Graph.nodes g) Map.empty) as [out out_events].
  destruct (audit_graph_full_in EV g (Graph.nodes g) Map.empty) as [incoming in_events].
  destruct (audit_graph_full_edge_count g (Graph.nodes g)) as [count edge_events].
  destruct Hout as [Hout [Hout_length Hout_bound]].
  destruct Hin as [Hin [Hin_length Hin_bound]].
  destruct Hcount as [Hcount [Hcount_length Hcount_bound]].
  change (count = edges) in Hcount; subst count.
  set (prefix := out_events ++ in_events ++
    [AuditGraphFullNodesLength (Graph.nodes g) nodes] ++ edge_events).
  set (amount := 2 * nodes + edges + 1).
  set (fuel_event := @AuditGraphFullFuel V E nodes edges (Pos.of_succ_nat amount)).
  assert (Htrace : out_events ++ in_events ++
    [AuditGraphFullNodesLength (Graph.nodes g) nodes] ++ edge_events ++ [fuel_event] =
    prefix ++ [fuel_event]).
  { unfold prefix; repeat rewrite app_assoc; reflexivity. }
  fold nodes; fold amount; fold fuel_event.
  rewrite Htrace.
  change (Prepared out incoming (Pos.of_succ_nat amount) = prepare EV g /\
    length (prefix ++ [fuel_event]) <= audit_graph_prepare_full_event_bound g /\
    audit_graph_prepare_full_work (prefix ++ [fuel_event]) <= audit_graph_prepare_full_budget EV g).
  split.
  - unfold prepare; rewrite Hout, Hin; reflexivity.
  - assert (Hprefix_length : length prefix = 4 + 9 * nodes + 6 * edges).
    { unfold prefix; rewrite !length_app; cbn [length].
      unfold nodes, edges, edge_count in *; lia. }
    assert (Hprefix_bound : Forall (audit_full_event_bounded width size) prefix).
    { unfold prefix; apply Forall_app; split; [exact Hout_bound|].
      apply Forall_app; split; [exact Hin_bound|].
      constructor.
      - unfold audit_full_event_bounded, audit_graph_full_event_work; cbn.
        unfold nodes, size; lia.
      - exact Hcount_bound. }
    pose proof (audit_full_sum_bound V E width size prefix Hprefix_bound) as Hsum.
    set (bound := audit_graph_prepare_full_event_bound g).
    assert (Hbound : bound = 8 + 12 * nodes + 8 * edges) by reflexivity.
    assert (Hlength : length (prefix ++ [fuel_event]) <= bound).
    { rewrite length_app; cbn [length]; lia. }
    split; [exact Hlength|].
    unfold audit_graph_prepare_full_work, audit_graph_prepare_full_budget.
    change (64 * S (length (prefix ++ [fuel_event])) * S (length (prefix ++ [fuel_event])) +
      audit_full_sum (prefix ++ [fuel_event]) <=
      128 * S bound * S bound + bound * (128 + 3 * width) +
      64 * S amount * S amount + amount * CollectionsAuditCost.audit_key_bits_weight
        (Pos.of_succ_nat amount)).
    rewrite audit_full_sum_app.
    unfold audit_full_sum at 2; cbn [fold_right].
    unfold fuel_event, audit_graph_full_event_work,
      CollectionsAuditCost.audit_unary_conversion_weight.
    fold amount; unfold size in Hsum.
    rewrite length_app; cbn [length].
    assert (Hsmall : S (length prefix) <= bound) by lia.
    assert (Hsize_bound : nodes + edges <= bound) by lia.
    assert (Hamount : 1 <= amount) by (unfold amount; lia).
    clear - Hsmall Hsize_bound Hsum Hamount.
    clearbody width nodes edges amount bound prefix.
    assert (Hsquare : S (S (length prefix)) * S (S (length prefix)) <=
      S bound * S bound) by nia.
    assert (Hsum_bound : audit_full_sum prefix <=
      bound * (70 + 3 * width + 2 * bound)).
    { eapply Nat.le_trans; [exact Hsum|].
      apply Nat.mul_le_mono; lia. }
    assert (Hbudget : 64 * (S bound * S bound) +
      bound * (70 + 3 * width + 2 * bound) <=
      128 * (S bound * S bound) + bound * (128 + 3 * width)) by (clear; nia).
    assert (Hfuel_bound : 64 + 32 * (S amount * S amount) + S amount <=
      64 * (S amount * S amount)) by (clear - Hamount; nia).
    nia.
Qed.

(** Nested callback preparation erases to the bounded full preparation trace. *)
Theorem audit_graph_prepare_nested_correct : audit_graph_prepare_nested_statement.
Proof.
  intros V E B EV g cb Hcallbacks.
  pose proof (audit_nested_prepare_erases V E B EV g cb Hcallbacks) as Herases.
  pose proof (audit_graph_prepare_full_correct V E EV g) as Hfull.
  destruct (audit_graph_prepare_nested_counted EV g cb) as [result events].
  destruct (audit_graph_prepare_full_counted EV g) as [original trace].
  cbn in Herases; inversion Herases; subst original trace.
  destruct Hfull as [Hresult [Hlength Hwork]].
  repeat split; try assumption.
  - rewrite length_map in Hlength; exact Hlength.
Qed.

(** * Source events and callback receipts *)

Definition audit_source_receipt {V E B} (cb : audit_prepare_callback_model V E B)
    (event : audit_prepare_source_event V E B) : Prop :=
  match event with
  | PrepareSourceOut v outgoing body => audit_prepare_out_model cb v = (outgoing, body)
  | PrepareSourceTarget e target body => audit_prepare_target_model cb e = (target, body)
  | PrepareSourceMap (AuditMapGet key code _ _ body _) =>
      audit_prepare_encode_model cb key = (code, body)
  | PrepareSourceMap (AuditMapSet key _ code _ _ body _) =>
      audit_prepare_encode_model cb key = (code, body)
  | PrepareSourceMap (AuditMapRemove key code _ _ body _) =>
      audit_prepare_encode_model cb key = (code, body)
  | PrepareSourceCase _
  | PrepareSourceLength _
  | PrepareSourceFuel _ _ _ => True
  end.

Definition audit_source_bounded {V E B} (weight : B -> nat) width size
    (event : audit_prepare_source_event V E B) : Prop :=
  audit_prepare_source_event_work weight event <=
    audit_prepare_source_body_event_work weight event + (70 + 16 * width + 2 * size).

Lemma audit_source_map_get V E B (EV : encoding V) (cb : audit_prepare_callback_model V E B)
    (weight : B -> nat) key (input : Map.t V (list E)) width size :
  fst (audit_prepare_encode_model cb key) = encode EV key ->
  CollectionsAuditCost.audit_key_bits_weight (encode EV key) <= width ->
  let '(result, events) := audit_map_get (audit_prepare_encode_model cb) key input in
  result = Map.get EV key input /\
  length events = 1 /\
  Forall (fun event => audit_source_receipt cb (PrepareSourceMap event) /\
    audit_source_bounded weight width size (PrepareSourceMap event)) events.
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_get_erases V (list E) B (audit_prepare_encode_model cb) EV key input
    Hencode) as Herase.
  pose proof (audit_map_get_source_work_bound V (list E) B (audit_prepare_encode_model cb)
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in *.
  destruct (audit_prepare_encode_model cb key) as [code body] eqn:Hcall.
  destruct (audit_map_code_get code input) as [result trace].
  cbn [fst snd] in Hencode, Herase, Hwork; subst code.
  split; [exact Herase|]; split; [reflexivity|].
  constructor; [|constructor]; split.
  - unfold audit_source_receipt; exact Hcall.
  - unfold audit_source_bounded, audit_prepare_source_event_work,
      audit_prepare_source_body_event_work; cbn [audit_map_source_work] in *.
    unfold CollectionsAuditCost.audit_key_bits_weight in Hwidth; lia.
Qed.

Lemma audit_source_map_set V E B (EV : encoding V) (cb : audit_prepare_callback_model V E B)
    (weight : B -> nat) key value (input : Map.t V (list E)) width size :
  fst (audit_prepare_encode_model cb key) = encode EV key ->
  CollectionsAuditCost.audit_key_bits_weight (encode EV key) <= width ->
  let '(result, events) := audit_map_set (audit_prepare_encode_model cb) key value input in
  result = Map.set EV key value input /\
  length events = 1 /\
  Forall (fun event => audit_source_receipt cb (PrepareSourceMap event) /\
    audit_source_bounded weight width size (PrepareSourceMap event)) events.
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_set_erases V (list E) B (audit_prepare_encode_model cb) EV key value input
    Hencode) as Herase.
  pose proof (audit_map_set_source_work_bound V (list E) B (audit_prepare_encode_model cb)
    (fun body => fold_right (fun item n => weight item + n) 0 body) key value input) as Hwork.
  unfold audit_map_set in *.
  destruct (audit_prepare_encode_model cb key) as [code body] eqn:Hcall.
  destruct (audit_trie_set code (key, value) input) as [result trace].
  cbn [fst snd] in Hencode, Herase, Hwork; subst code.
  split; [exact Herase|]; split; [reflexivity|].
  constructor; [|constructor]; split.
  - unfold audit_source_receipt; exact Hcall.
  - unfold audit_source_bounded, audit_prepare_source_event_work,
      audit_prepare_source_body_event_work; cbn [audit_map_source_work] in *.
    unfold CollectionsAuditCost.audit_key_bits_weight in Hwidth; lia.
Qed.

Lemma audit_source_out_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (weight : B -> nat) nodes initial width size :
  audit_prepare_callbacks_erase EV g cb ->
  (forall v, In v nodes ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV v) <= width) ->
  let '(result, events) := audit_prepare_source_out cb nodes initial in
  result = fold_right (fun v m => Map.set EV v (Graph.out g v) m) initial nodes /\
  length events = 1 + 3 * length nodes /\
  Forall (fun event => audit_source_receipt cb event /\
    audit_source_bounded weight width size event) events.
Proof.
  intros Hcallbacks Hwidth; destruct Hcallbacks as [Hout [Htarget Hencode]].
  induction nodes as [|v rest IH]; cbn [audit_prepare_source_out].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor; [|constructor]; split; [exact I|].
    unfold audit_source_bounded, audit_prepare_source_event_work,
      audit_prepare_source_body_event_work; cbn; lia.
  - assert (Hrest : forall u, In u rest ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV u) <= width).
    { intros u Hin; apply Hwidth; now right. }
    specialize (IH Hrest).
    destruct (audit_prepare_source_out cb rest initial) as [middle events].
    destruct IH as [Hresult [Hlength Hbound]].
    pose proof (Hout v) as Houtv.
    destruct (audit_prepare_out_model cb v) as [outgoing body] eqn:Hcall.
    cbn in Houtv; subst outgoing.
    pose proof (audit_source_map_set V E B EV cb weight v (Graph.out g v) middle width size
      (Hencode v) (Hwidth v (or_introl eq_refl))) as Hmap.
    destruct (audit_map_set (audit_prepare_encode_model cb) v (Graph.out g v) middle)
      as [final writes].
    destruct Hmap as [Hmap_result [Hmap_length Hmap_bound]].
    split; [cbn [fold_right]; rewrite <- Hresult; exact Hmap_result|].
    split; [cbn [length]; rewrite !length_app, length_map; cbn [length]; lia|].
    constructor.
    + split; [exact I|].
      unfold audit_source_bounded, audit_prepare_source_event_work,
        audit_prepare_source_body_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      constructor.
      * split; [exact Hcall|].
        unfold audit_source_bounded, audit_prepare_source_event_work,
          audit_prepare_source_body_event_work; cbn; lia.
      * apply Forall_map; exact Hmap_bound.
Qed.

Lemma audit_source_edges_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (weight : B -> nat) edges initial width size :
  audit_prepare_callbacks_erase EV g cb ->
  (forall e, In e edges ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width) ->
  let '(result, events) := audit_prepare_source_edges cb edges initial in
  result = fold_right (index_edge EV g) initial edges /\
  length events = 1 + 6 * length edges /\
  Forall (fun event => audit_source_receipt cb event /\
    audit_source_bounded weight width size event) events.
Proof.
  intros Hcallbacks Hwidth; destruct Hcallbacks as [Hout [Htarget Hencode]].
  induction edges as [|edge rest IH]; cbn [audit_prepare_source_edges].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor; [|constructor]; split; [exact I|].
    unfold audit_source_bounded, audit_prepare_source_event_work,
      audit_prepare_source_body_event_work; cbn; lia.
  - assert (Hrest : forall e, In e rest ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
    { intros e Hin; apply Hwidth; now right. }
    specialize (IH Hrest).
    destruct (audit_prepare_source_edges cb rest initial) as [middle events].
    destruct IH as [Hresult [Hlength Hbound]].
    pose proof (Htarget edge) as Htarget_edge.
    destruct (audit_prepare_target_model cb edge) as [target body] eqn:Hcall.
    cbn in Htarget_edge; subst target.
    assert (Hedge_width : CollectionsAuditCost.audit_key_bits_weight
      (encode EV (Graph.target g edge)) <= width) by (apply Hwidth; now left).
    pose proof (audit_source_map_get V E B EV cb weight (Graph.target g edge) middle width size
      (Hencode _) Hedge_width) as Hget.
    destruct (audit_map_get (audit_prepare_encode_model cb) (Graph.target g edge) middle)
      as [found reads].
    destruct Hget as [Hfound [Hreads_length Hreads_bound]].
    pose proof (audit_source_map_set V E B EV cb weight (Graph.target g edge)
      (edge ::
        match found with
        | Some xs => xs
        | None => []
        end) middle width size (Hencode _) Hedge_width) as Hset.
    destruct (audit_map_set (audit_prepare_encode_model cb) (Graph.target g edge)
      (edge ::
        match found with
        | Some xs => xs
        | None => []
        end) middle) as [final writes].
    destruct Hset as [Hfinal [Hwrites_length Hwrites_bound]].
    split.
    + cbn [fold_right]; rewrite <- Hresult, Hfinal, Hfound; reflexivity.
    + split.
      * cbn [length]; rewrite !length_app, !length_map; cbn [length]; lia.
      * constructor.
        -- split; [exact I|].
           unfold audit_source_bounded, audit_prepare_source_event_work,
             audit_prepare_source_body_event_work; cbn; lia.
        -- apply Forall_app; split; [exact Hbound|].
           constructor; [|constructor].
           ++ split; [exact Hcall|].
              unfold audit_source_bounded, audit_prepare_source_event_work,
                audit_prepare_source_body_event_work; cbn; lia.
           ++ split; [exact Hcall|].
              unfold audit_source_bounded, audit_prepare_source_event_work,
                audit_prepare_source_body_event_work; cbn; lia.
           ++ apply Forall_app; split; [apply Forall_map; exact Hreads_bound|].
              constructor.
              ** split; [exact I|].
                 unfold audit_source_bounded, audit_prepare_source_event_work,
                   audit_prepare_source_body_event_work; destruct found; cbn; lia.
              ** apply Forall_map; exact Hwrites_bound.
Qed.

Lemma audit_source_in_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (weight : B -> nat) nodes initial width size :
  audit_prepare_callbacks_erase EV g cb ->
  (forall v e, In v nodes -> In e (Graph.out g v) ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width) ->
  let '(result, events) := audit_prepare_source_in cb nodes initial in
  result = fold_right (fun v m => fold_right (index_edge EV g) m (Graph.out g v)) initial nodes /\
  length events = 1 + 3 * length nodes +
    6 * fold_right (fun v total => length (Graph.out g v) + total) 0 nodes /\
  Forall (fun event => audit_source_receipt cb event /\
    audit_source_bounded weight width size event) events.
Proof.
  intros Hcallbacks Hwidth; destruct Hcallbacks as [Hout [Htarget Hencode]].
  induction nodes as [|v rest IH]; cbn [audit_prepare_source_in].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor; [|constructor]; split; [exact I|].
    unfold audit_source_bounded, audit_prepare_source_event_work,
      audit_prepare_source_body_event_work; cbn; lia.
  - assert (Hrest : forall u e, In u rest -> In e (Graph.out g u) ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
    { intros u e Hin Hedge; apply Hwidth with u; [now right|exact Hedge]. }
    specialize (IH Hrest).
    destruct (audit_prepare_source_in cb rest initial) as [middle events].
    destruct IH as [Hresult [Hlength Hbound]].
    pose proof (Hout v) as Houtv.
    destruct (audit_prepare_out_model cb v) as [outgoing body] eqn:Hcall.
    cbn in Houtv; subst outgoing.
    assert (Hedge_width : forall e, In e (Graph.out g v) ->
      CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
    { intros e Hin; apply Hwidth with v; [now left|exact Hin]. }
    pose proof (audit_source_edges_bound V E B EV g cb weight (Graph.out g v) middle width size
      (conj Hout (conj Htarget Hencode)) Hedge_width) as Hedges.
    destruct (audit_prepare_source_edges cb (Graph.out g v) middle) as [final edge_events].
    destruct Hedges as [Hedge_result [Hedge_length Hedge_bound]].
    split; [cbn [fold_right]; rewrite <- Hresult; exact Hedge_result|].
    split; [cbn [length]; rewrite !length_app; cbn [length fold_right]; lia|].
    constructor.
    + split; [exact I|].
      unfold audit_source_bounded, audit_prepare_source_event_work,
        audit_prepare_source_body_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      constructor; [|exact Hedge_bound]; split; [exact Hcall|].
      unfold audit_source_bounded, audit_prepare_source_event_work,
        audit_prepare_source_body_event_work; cbn; lia.
Qed.

Lemma audit_source_count_bound V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (weight : B -> nat) nodes width size :
  audit_prepare_callbacks_erase EV g cb ->
  (forall v, In v nodes -> length (Graph.out g v) <= size) ->
  let '(result, events) := audit_prepare_source_edge_count cb nodes in
  result = fold_right (fun v total => length (Graph.out g v) + total) 0 nodes /\
  length events = 1 + 3 * length nodes /\
  Forall (fun event => audit_source_receipt cb event /\
    audit_source_bounded weight width size event) events.
Proof.
  intros Hcallbacks Hsize; destruct Hcallbacks as [Hout [Htarget Hencode]].
  induction nodes as [|v rest IH]; cbn [audit_prepare_source_edge_count].
  - split; [reflexivity|]; split; [reflexivity|].
    constructor; [|constructor]; split; [exact I|].
    unfold audit_source_bounded, audit_prepare_source_event_work,
      audit_prepare_source_body_event_work; cbn; lia.
  - assert (Hrest : forall u, In u rest -> length (Graph.out g u) <= size).
    { intros u Hin; apply Hsize; now right. }
    specialize (IH Hrest).
    destruct (audit_prepare_source_edge_count cb rest) as [count events].
    destruct IH as [Hcount [Hlength Hbound]].
    pose proof (Hout v) as Houtv.
    destruct (audit_prepare_out_model cb v) as [outgoing body] eqn:Hcall.
    cbn in Houtv; subst outgoing.
    split; [cbn [fold_right]; now rewrite Hcount|].
    split; [cbn [length]; rewrite length_app; cbn [length]; lia|].
    constructor.
    + split; [exact I|].
      unfold audit_source_bounded, audit_prepare_source_event_work,
        audit_prepare_source_body_event_work; cbn; lia.
    + apply Forall_app; split; [exact Hbound|].
      assert (Hv : length (Graph.out g v) <= size) by (apply Hsize; now left).
      constructor.
      * split; [exact Hcall|].
        unfold audit_source_bounded, audit_prepare_source_event_work,
          audit_prepare_source_body_event_work; cbn; lia.
      * constructor; [|constructor]; split; [exact I|].
        unfold audit_source_bounded, audit_prepare_source_event_work,
          audit_prepare_source_body_event_work; cbn; lia.
Qed.

Lemma audit_source_work_app V E B (weight : B -> nat)
    (left right : list (audit_prepare_source_event V E B)) :
  audit_prepare_source_work weight (left ++ right) =
    audit_prepare_source_work weight left + audit_prepare_source_work weight right.
Proof.
  unfold audit_prepare_source_work; induction left as [|event rest IH]; cbn in *; lia.
Qed.

Lemma audit_source_body_work_app V E B (weight : B -> nat)
    (left right : list (audit_prepare_source_event V E B)) :
  audit_prepare_source_body_work weight (left ++ right) =
    audit_prepare_source_body_work weight left + audit_prepare_source_body_work weight right.
Proof.
  unfold audit_prepare_source_body_work; induction left as [|event rest IH]; cbn in *; lia.
Qed.

Lemma audit_source_sum_bound V E B (cb : audit_prepare_callback_model V E B) weight width size
    (events : list (audit_prepare_source_event V E B)) :
  Forall (fun event => audit_source_receipt cb event /\
    audit_source_bounded weight width size event) events ->
  audit_prepare_source_work weight events <= audit_prepare_source_body_work weight events +
    length events * (70 + 16 * width + 2 * size).
Proof.
  intro Hbound; induction Hbound as [|event rest [_ Hevent] Hrest IH].
  - reflexivity.
  - unfold audit_source_bounded in Hevent.
    unfold audit_prepare_source_work, audit_prepare_source_body_work in *; cbn in *; nia.
Qed.

Lemma audit_prepare_source_with_receipts V E B (EV : encoding V) (g : Graph.t V E)
    (cb : audit_prepare_callback_model V E B) (weight : B -> nat) :
  audit_prepare_callbacks_erase EV g cb ->
  let '(result, events) := audit_prepare_source_counted EV g cb in
  result = prepare EV g /\ length events <= audit_graph_prepare_full_event_bound g /\
  audit_prepare_source_work weight events <= audit_prepare_source_budget EV g +
    audit_prepare_source_body_work weight events /\
  Forall (audit_source_receipt cb) events.
Proof.
  intro Hcallbacks.
  set (width := audit_graph_prepare_input_width EV g).
  set (nodes := length (Graph.nodes g)).
  set (edges := edge_count g).
  set (size := nodes + edges).
  assert (Hnode_width : forall v, In v (Graph.nodes g) ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV v) <= width).
  { intros v Hin; apply audit_input_width_node; exact Hin. }
  assert (Hedge_width : forall v e, In v (Graph.nodes g) -> In e (Graph.out g v) ->
    CollectionsAuditCost.audit_key_bits_weight (encode EV (Graph.target g e)) <= width).
  { intros v e Hin Hedge; eapply audit_input_width_edge; eassumption. }
  assert (Hsize : forall v, In v (Graph.nodes g) -> length (Graph.out g v) <= size).
  { intros v Hin; pose proof (audit_edge_count_member V E g (Graph.nodes g) v Hin) as Hmember.
    unfold size, edges, edge_count in *; lia. }
  pose proof (audit_source_out_bound V E B EV g cb weight (Graph.nodes g) Map.empty width size
    Hcallbacks Hnode_width) as Hout.
  pose proof (audit_source_in_bound V E B EV g cb weight (Graph.nodes g) Map.empty width size
    Hcallbacks Hedge_width) as Hin.
  pose proof (audit_source_count_bound V E B EV g cb weight (Graph.nodes g) width size
    Hcallbacks Hsize) as Hcount.
  unfold audit_prepare_source_counted.
  destruct (audit_prepare_source_out cb (Graph.nodes g) Map.empty) as [out out_events].
  destruct (audit_prepare_source_in cb (Graph.nodes g) Map.empty) as [incoming in_events].
  destruct (audit_prepare_source_edge_count cb (Graph.nodes g)) as [count edge_events].
  destruct Hout as [Hout [Hout_length Hout_bound]].
  destruct Hin as [Hin [Hin_length Hin_bound]].
  destruct Hcount as [Hcount [Hcount_length Hcount_bound]].
  change (count = edges) in Hcount; subst count.
  set (prefix := out_events ++ in_events ++ [PrepareSourceLength nodes] ++ edge_events).
  set (amount := 2 * nodes + edges + 1).
  set (fuel_event := @PrepareSourceFuel V E B nodes edges (Pos.of_succ_nat amount)).
  assert (Htrace : out_events ++ in_events ++ [PrepareSourceLength nodes] ++ edge_events ++
    [fuel_event] = prefix ++ [fuel_event]).
  { unfold prefix; repeat rewrite app_assoc; reflexivity. }
  fold nodes; fold amount; fold fuel_event; rewrite Htrace.
  change (Prepared out incoming (Pos.of_succ_nat amount) = prepare EV g /\
    length (prefix ++ [fuel_event]) <= audit_graph_prepare_full_event_bound g /\
    audit_prepare_source_work weight (prefix ++ [fuel_event]) <= audit_prepare_source_budget EV g +
      audit_prepare_source_body_work weight (prefix ++ [fuel_event]) /\
    Forall (audit_source_receipt cb) (prefix ++ [fuel_event])).
  split; [unfold prepare; now rewrite Hout, Hin|].
  assert (Hprefix_length : length prefix = 4 + 9 * nodes + 6 * edges).
  { unfold prefix; rewrite !length_app; cbn [length].
    unfold nodes, edges, edge_count in *; lia. }
  assert (Hprefix_bound : Forall (fun event => audit_source_receipt cb event /\
    audit_source_bounded weight width size event) prefix).
  { unfold prefix; apply Forall_app; split; [exact Hout_bound|].
    apply Forall_app; split; [exact Hin_bound|].
    constructor.
    - split; [exact I|].
      unfold audit_source_bounded, audit_prepare_source_event_work,
        audit_prepare_source_body_event_work; cbn; unfold nodes, size; lia.
    - exact Hcount_bound. }
  pose proof (audit_source_sum_bound V E B cb weight width size prefix Hprefix_bound) as Hsum.
  set (bound := audit_graph_prepare_full_event_bound g).
  assert (Hbound : bound = 8 + 12 * nodes + 8 * edges) by reflexivity.
  assert (Hlength : length (prefix ++ [fuel_event]) <= bound).
  { rewrite length_app; cbn [length]; lia. }
  split; [exact Hlength|].
  split.
  - unfold audit_prepare_source_budget.
    change (audit_prepare_source_work weight (prefix ++ [fuel_event]) <=
      1024 * S bound * S bound + bound * (512 + 64 * width) +
      64 * S amount * S amount + amount * Pos.size_nat (Pos.of_succ_nat amount) +
      audit_prepare_source_body_work weight (prefix ++ [fuel_event])).
    rewrite audit_source_work_app, audit_source_body_work_app.
    unfold audit_prepare_source_work at 2; unfold audit_prepare_source_body_work at 2.
    unfold fuel_event, audit_prepare_source_event_work, audit_prepare_source_body_event_work,
      CollectionsAuditCost.audit_unary_conversion_weight; cbn [fold_right].
    fold amount; unfold size in Hsum.
    assert (Hsmall : length prefix <= bound) by lia.
    assert (Hsize_bound : nodes + edges <= bound) by lia.
    assert (Hamount : 1 <= amount) by (unfold amount; lia).
    clear - Hsmall Hsize_bound Hsum Hamount.
    clearbody width nodes edges amount bound prefix.
    assert (Hsum_bound : audit_prepare_source_work weight prefix <=
      audit_prepare_source_body_work weight prefix + bound * (70 + 16 * width + 2 * bound)).
    { assert (Hproduct : length prefix * (70 + 16 * width + 2 * (nodes + edges)) <=
        bound * (70 + 16 * width + 2 * bound)) by (apply Nat.mul_le_mono; lia).
      lia. }
    assert (Hbudget : bound * (70 + 16 * width + 2 * bound) <=
      1024 * S bound * S bound + bound * (512 + 64 * width)) by (clear; nia).
    assert (Hfuel_bound : 64 + 32 * (S amount * S amount) + S amount <=
      64 * (S amount * S amount)) by (clear - Hamount; nia).
    nia.
  - apply Forall_app; split.
    + eapply Forall_impl; [|exact Hprefix_bound]. intros event [Hreceipt _]; exact Hreceipt.
    + constructor; [exact I|constructor].
Qed.

(** Source preparation preserves its result and bounds its captured internal work. *)
Theorem audit_prepare_source_correct : audit_prepare_source_statement.
Proof.
  intros V E B EV g cb weight Hcallbacks.
  pose proof (audit_prepare_source_with_receipts V E B EV g cb weight Hcallbacks) as Hrun.
  destruct (audit_prepare_source_counted EV g cb) as [result events].
  destruct Hrun as [Hresult [Hlength [Hwork Hreceipts]]].
  repeat split; assumption.
Qed.

Lemma audit_source_receipt_body_bound V E B (cb : audit_prepare_callback_model V E B)
    (weight : B -> nat) encode_source out_source target_source encode_budget out_budget
    target_budget (event : audit_prepare_source_event V E B) :
  audit_graph_external_callback_adapter (audit_prepare_encode_model cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_prepare_out_model cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_prepare_target_model cb) weight target_source
    target_budget ->
  audit_source_receipt cb event ->
  audit_prepare_source_body_event_work weight event <=
    audit_prepare_source_event_budget encode_budget out_budget target_budget event.
Proof.
  intros Hencode Hout Htarget Hreceipt.
  destruct event as [site|v outgoing body|e target body|map_event|amount|nodes edges fuel];
    cbn [audit_prepare_source_body_event_work audit_prepare_source_event_budget
      audit_source_receipt] in *; try lia.
  - destruct (audit_graph_external_callback_source _ _ _ _ Hout v outgoing body Hreceipt)
      as [_ Hbound].
    exact Hbound.
  - destruct (audit_graph_external_callback_source _ _ _ _ Htarget e target body Hreceipt)
      as [_ Hbound].
    exact Hbound.
  - destruct map_event as [key code input output body trace |
      key value code input output body trace | key code input output body trace];
      cbn [audit_source_receipt audit_prepare_source_body_event_work
        audit_prepare_source_event_budget] in *;
      destruct (audit_graph_external_callback_source _ _ _ _ Hencode key code body Hreceipt)
        as [_ Hbound];
      exact Hbound.
Qed.

Lemma audit_source_receipts_body_bound V E B (cb : audit_prepare_callback_model V E B)
    (weight : B -> nat) encode_source out_source target_source encode_budget out_budget
    target_budget (events : list (audit_prepare_source_event V E B)) :
  audit_graph_external_callback_adapter (audit_prepare_encode_model cb) weight encode_source
    encode_budget ->
  audit_graph_external_callback_adapter (audit_prepare_out_model cb) weight out_source out_budget ->
  audit_graph_external_callback_adapter (audit_prepare_target_model cb) weight target_source
    target_budget ->
  Forall (audit_source_receipt cb) events ->
  audit_prepare_source_body_work weight events <=
    fold_right (fun event n => audit_prepare_source_event_budget encode_budget out_budget
      target_budget event + n) 0 events.
Proof.
  intros Hencode Hout Htarget Hreceipts.
  induction Hreceipts as [|event rest Hreceipt Hrest IH].
  - reflexivity.
  - pose proof (audit_source_receipt_body_bound V E B cb weight encode_source out_source
      target_source encode_budget out_budget target_budget event Hencode Hout Htarget Hreceipt)
      as Hbound.
    unfold audit_prepare_source_body_work in *; cbn in *; lia.
Qed.

(** External callback budgets bound the work recorded at the same source calls. *)
Theorem audit_prepare_source_adapted_holds : audit_prepare_source_adapted_statement.
Proof.
  intros V E B EV g cb weight encode_source out_source target_source encode_budget out_budget
    target_budget Hcallbacks Hencode Hout Htarget.
  pose proof (audit_prepare_source_with_receipts V E B EV g cb weight Hcallbacks) as Hrun.
  destruct (audit_prepare_source_counted EV g cb) as [result events].
  destruct Hrun as [Hresult [Hlength [Hwork Hreceipts]]].
  split; [exact Hresult|].
  pose proof (audit_source_receipts_body_bound V E B cb weight encode_source out_source
    target_source encode_budget out_budget target_budget events Hencode Hout Htarget Hreceipts)
    as Hbody.
  lia.
Qed.

(** Preparation and its map primitives satisfy the combined source contract. *)
Theorem audit_prepare_source_contract_holds : audit_prepare_source_contract_statement.
Proof.
  repeat split.
  - exact audit_prepare_source_correct.
  - exact audit_prepare_source_adapted_holds.
  - exact audit_map_get_source_work_bound.
  - exact audit_map_set_source_work_bound.
Qed.
