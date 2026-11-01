(** * Semi-NCA audit adequacy

    These proofs connect the recorded ancestor walks and producer receipts to their source.
    For example, a missing parent ends a walk with the current vertex and its lookup receipt.
    Builds on: GraphAuditSemiNca and GraphAuditSemiDominatorsAdequacy. *)

From Stdlib Require Import List Arith PArith Lia Wf_nat PeanoNat ZArith Ring.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsAuditCost CollectionsAuditMap CollectionsAuditCompare
  CollectionsAuditMapAdequacy CollectionsAuditCompareAdequacy.
From Galois.Graph Require Import GraphCore GraphDfs GraphSemiDominators GraphSemiNca
  GraphAuditDfsAdequacy GraphAuditSemiDominators GraphAuditSemiDominatorsAdequacy
  GraphAuditSemiNca.
Import List.ListNotations.

(** * Receipt determinism *)

(** An ancestor walk fixes both its returned vertex and its complete receipt. *)
Theorem audit_nca_walk_unique : audit_nca_walk_unique_statement.
Proof.
  intros V E EV r limit parents v x y ex ey Hfirst.
  revert y ey.
  induction Hfirst; intros y ey Hsecond; inversion Hsecond; subst; try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = Some ?a, Hright : ?f = Some ?b |- _ =>
      assert (a = b) by congruence; subst b; clear Hright
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try congruence.
  all: try
    match goal with
    | IH : forall _ _, audit_nca_walk_run _ _ _ _ _ _ _ -> _,
      Hrun : audit_nca_walk_run _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hevents]; subst
    end.
  all: split; reflexivity.
Qed.

(** Source walks retain the actual comparison and encoder receipts uniquely. *)
Lemma audit_nca_source_walk_unique V E B enc (r : dfs_result V E) limit parents v x ex y ey :
  audit_nca_source_walk_run (B := B) enc r limit parents v x ex ->
  audit_nca_source_walk_run enc r limit parents v y ey -> x = y /\ ex = ey.
Proof.
  intro Hfirst; revert y ey.
  induction Hfirst; intros y ey Hsecond; inversion Hsecond; subst; try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try congruence.
  all: try
    match goal with
    | IH : forall _ _, audit_nca_source_walk_run _ _ _ _ _ _ _ -> _,
      Hrun : audit_nca_source_walk_run _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hevents]; subst
    end.
  all: split; reflexivity.
Qed.

(** Every source walk has the vertex returned by the underlying well-founded walk. *)
Lemma audit_nca_walk_exists V E (EV : encoding V) (r : dfs_result V E) limit parents v :
  exists events, audit_nca_walk_run EV r limit parents v
    (nca_walk EV (semi_rank EV r) limit parents v) events.
Proof.
  pattern v; apply (well_founded_induction
    (well_founded_ltof V (fun x => Pos.to_nat (semi_rank EV r x)))); clear v.
  intros v IH.
  destruct (audit_semi_rank_counted EV r v) as [rank events] eqn:Hrank.
  pose proof (audit_semi_rank_counted_erases V E EV r v) as Hrank_value.
  rewrite Hrank in Hrank_value; cbn in Hrank_value; subst rank.
  rewrite nca_walk_unfold; unfold nca_walk_body.
  destruct (Pos.leb (semi_rank EV r v) limit) eqn:Hthreshold.
  - exists (events ++ [AuditSemiLe (semi_rank EV r v) limit true; AuditSemiCase 20]).
    apply AuditNcaThreshold; assumption.
  - destruct (Map.get EV v parents) as [a|] eqn:Hparent.
    + destruct (audit_semi_rank_counted EV r a) as [ra ea] eqn:Ha.
      pose proof (audit_semi_rank_counted_erases V E EV r a) as Ha_value.
      rewrite Ha in Ha_value; cbn in Ha_value; subst ra.
      destruct (semi_rank_less (semi_rank EV r a) (semi_rank EV r v)) as [Hlt|Hnot].
      * assert (Hcompare : Pos.ltb (semi_rank EV r a) (semi_rank EV r v) = true).
        { apply Pos.ltb_lt; apply Pos2Nat.inj_lt; exact Hlt. }
        destruct (IH a Hlt) as [inner Hinner].
        exists (events ++ [AuditSemiLe (semi_rank EV r v) limit false; AuditSemiCase 21;
          AuditSemiGet v parents (Some a)] ++ ea ++ events ++
          [AuditSemiLess (semi_rank EV r a) (semi_rank EV r v) true; AuditSemiCase 24] ++ inner).
        eapply AuditNcaRecur; eassumption.
      * assert (Hcompare : Pos.ltb (semi_rank EV r a) (semi_rank EV r v) = false).
        { apply Pos.ltb_ge; apply Pos2Nat.inj_le; lia. }
        exists (events ++ [AuditSemiLe (semi_rank EV r v) limit false; AuditSemiCase 21;
          AuditSemiGet v parents (Some a)] ++ ea ++ events ++
          [AuditSemiLess (semi_rank EV r a) (semi_rank EV r v) false; AuditSemiCase 23]).
        eapply AuditNcaStop; eassumption.
    + exists (events ++ [AuditSemiLe (semi_rank EV r v) limit false; AuditSemiCase 21;
        AuditSemiGet v parents None; AuditSemiCase 22]).
      eapply AuditNcaNoParent; eassumption.
Qed.

(** A single forward step has one successor and one receipt. *)
Lemma audit_nca_step_unique V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis initial v first first_events second second_events :
  audit_nca_step_run EV g r semis initial v first first_events ->
  audit_nca_step_run EV g r semis initial v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst; try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = Some ?a, Hright : ?f = Some ?b |- _ =>
      assert (a = b) by congruence; subst b; clear Hright
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try solve [split; reflexivity].
  all:
    match goal with
    | Hleft : audit_nca_walk_run _ _ _ _ _ _ _, Hright : audit_nca_walk_run _ _ _ _ _ _ _ |- _ =>
      destruct (audit_nca_walk_unique _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; subst
    end.
  all: split; reflexivity.
Qed.

(** Folding deterministic steps preserves the selected map and the entire receipt. *)
Lemma audit_nca_steps_unique V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis vertices initial first first_events second second_events :
  audit_nca_steps_run EV g r semis vertices initial first first_events ->
  audit_nca_steps_run EV g r semis vertices initial second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intro Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_nca_step_run _ _ _ _ _ _ _ _,
      Hright : audit_nca_step_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_nca_step_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_nca_steps_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_nca_steps_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** The full forward pass has one result and one abstract receipt. *)
Theorem audit_nca_compute_unique : audit_nca_compute_unique_statement.
Proof.
  intros V E EV g r semis first second first_events second_events Hfirst Hsecond.
  exact (audit_nca_steps_unique _ _ _ _ _ _ _ _ _ _ _ _ Hfirst Hsecond).
Qed.

(** A source step fixes the callback bodies, selected vertex and successor map. *)
Lemma audit_nca_source_step_unique V E B enc source (r : dfs_result V E) semis
    initial v first first_events second second_events :
  audit_nca_source_step_run (B := B) enc source r semis initial v first first_events ->
  audit_nca_source_step_run enc source r semis initial v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst; try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try congruence.
  all: try solve [split; reflexivity].
  all:
    match goal with
    | Hleft : audit_nca_source_walk_run _ _ _ _ _ _ _,
      Hright : audit_nca_source_walk_run _ _ _ _ _ _ _ |- _ =>
      destruct (audit_nca_source_walk_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; subst
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: split; reflexivity.
Qed.

(** A sequence of source steps fixes its final map and callback receipt. *)
Lemma audit_nca_source_steps_unique V E B enc source (r : dfs_result V E) semis
    vertices initial first first_events second second_events :
  audit_nca_source_steps_run (B := B) enc source r semis vertices initial first first_events ->
  audit_nca_source_steps_run enc source r semis vertices initial second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intro Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_nca_source_step_run _ _ _ _ _ _ _ _,
      Hright : audit_nca_source_step_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_nca_source_step_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_nca_source_steps_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_nca_source_steps_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** The source pass has a unique selected map and same-run callback receipt. *)
Theorem audit_nca_source_unique_holds : audit_nca_source_unique_statement.
Proof.
  intros V E B enc source r semis first first_events second second_events Hfirst Hsecond.
  exact (audit_nca_source_steps_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hfirst Hsecond).
Qed.

(** Every recursive walk step consumes a strictly smaller positive rank. *)
Lemma audit_nca_walk_count V E (EV : encoding V) (r : dfs_result V E)
    limit parents v result events :
  audit_nca_walk_run EV r limit parents v result events ->
  length events <= 12 * S (Pos.to_nat (semi_rank EV r v)).
Proof.
  intro Hrun; induction Hrun.
  all: repeat rewrite length_app; cbn [length].
  all: repeat
    match goal with
    | H : audit_semi_rank_counted _ _ ?vertex = (?rank, ?receipt) |- _ =>
      let Hlength := fresh "Hlength" in
      let Hvalue := fresh "Hvalue" in
      pose proof (audit_semi_rank_counted_length V E EV r vertex) as Hlength;
      pose proof (audit_semi_rank_counted_erases V E EV r vertex) as Hvalue;
      rewrite H in Hlength, Hvalue; cbn in Hlength, Hvalue; clear H
    end.
  all: try lia.
  match goal with
  | Hcompare : Pos.ltb _ _ = true |- _ =>
    apply Pos.ltb_lt in Hcompare; apply Pos2Nat.inj_lt in Hcompare
  end.
  subst; lia.
Qed.

(** Rank lookup receipts are safe whenever their actual lookup key fits the width. *)
Lemma audit_nca_rank_safe V E (EV : encoding V) (r : dfs_result V E) width v :
  Pos.size_nat (encode EV v) <= width ->
  Forall (audit_semi_call_safe V EV width) (snd (audit_semi_rank_counted EV r v)).
Proof.
  intro Hwidth; rewrite audit_semi_rank_counted_details; cbn [audit_semi_call_safe].
  constructor; [exact Hwidth|constructor].
Qed.

(** Walk receipts only use the starting vertex, stored parents, and discovery ranks. *)
Lemma audit_nca_walk_safe V E (EV : encoding V) (r : dfs_result V E) limit parents
    v result events width :
  audit_nca_walk_run EV r limit parents v result events ->
  Pos.size_nat (encode EV v) <= width ->
  (forall x, In x (map snd (Map.elements parents)) -> Pos.size_nat (encode EV x) <= width) ->
  (forall x, Pos.size_nat (semi_rank EV r x) <= width) ->
  Pos.size_nat limit <= width -> Forall (audit_semi_call_safe V EV width) events.
Proof.
  intro Hrun; induction Hrun as
    [v rank events Hrank Hthreshold
    |v rank events Hrank Hthreshold Hparent
    |v rank events a ra rv ea ev Hrank Hthreshold Hparent Hrank_a Hcurrent Hcompare
    |v rank events a ra rv ea ev result inner Hrank Hthreshold Hparent Hrank_a Hcurrent Hcompare
      Hrun IH]; intros Hv Hparents Hranks Hlimit.
  all: repeat
    match goal with
    | |- Forall _ (_ ++ _) => apply Forall_app; split
    end.
  all: try solve [
    pose proof (audit_nca_rank_safe V E EV r width v Hv) as Hsafe;
    rewrite Hrank in Hsafe; exact Hsafe].
  all: try solve [
    cbn [audit_semi_call_safe]; repeat constructor; auto;
    pose proof (audit_semi_rank_counted_erases V E EV r v) as Hvalue;
    rewrite Hrank in Hvalue; cbn in Hvalue; subst; auto].
  all: try solve [
    pose proof (audit_nca_rank_safe V E EV r width a) as Hsafe;
    assert (Ha : Pos.size_nat (encode EV a) <= width)
      by (apply Hparents; eapply audit_semi_value_member; eassumption);
    specialize (Hsafe Ha); rewrite Hrank_a in Hsafe; exact Hsafe].
  all: try solve [
    pose proof (audit_nca_rank_safe V E EV r width v Hv) as Hsafe;
    rewrite Hcurrent in Hsafe; exact Hsafe].
  all: try solve [
    cbn [audit_semi_call_safe]; repeat constructor; auto;
    pose proof (audit_semi_rank_counted_erases V E EV r a) as Ha;
    pose proof (audit_semi_rank_counted_erases V E EV r v) as Hval;
    rewrite Hrank_a in Ha; rewrite Hcurrent in Hval; cbn in Ha, Hval; subst; auto].
  all: apply IH; auto; apply Hparents; eapply audit_semi_value_member; eassumption.
Qed.

(** The original walk width contains the starting vertex and every stored parent value. *)
Lemma audit_nca_walk_vertex_width V E (EV : encoding V) (r : dfs_result V E) limit parents start x :
  x = start \/ In x (map snd (Map.elements parents)) ->
  Pos.size_nat (encode EV x) <= audit_nca_walk_width EV r limit parents start.
Proof.
  intro Hmember; unfold audit_nca_walk_width, audit_key_bits_weight.
  eapply Nat.le_trans; [|eapply Nat.le_trans; [apply Nat.le_max_l|apply Nat.le_max_r]].
  apply (audit_dfs_width_member (fun node : V => Pos.size_nat (encode EV node))).
  destruct Hmember as [->|Hin]; [left; reflexivity|].
  right; apply in_or_app; right; apply in_or_app; left; exact Hin.
Qed.

(** Discovery ranks, including the default one, fit the original walk width. *)
Lemma audit_nca_walk_rank_width V E (EV : encoding V) (r : dfs_result V E) limit parents start x :
  Pos.size_nat (semi_rank EV r x) <= audit_nca_walk_width EV r limit parents start.
Proof.
  pose proof (audit_semi_rank_width V E EV r x) as Hrank.
  pose proof (audit_nca_walk_vertex_width V E EV r limit parents start start (or_introl eq_refl))
    as Hstart.
  assert (Hpositive : 1 <= Pos.size_nat (encode EV start)).
  { destruct (encode EV start); cbn [Pos.size_nat]; lia. }
  eapply Nat.le_trans; [exact Hrank|].
  apply Nat.max_lub; [lia|].
  unfold audit_nca_walk_width, audit_key_bits_weight.
  eapply Nat.le_trans; [apply Nat.le_max_r|apply Nat.le_max_r].
Qed.

(** The walk's actual receipt meets the input rank and key-width budget. *)
Theorem audit_nca_walk_correct : audit_nca_walk_statement.
Proof.
  intros V E EV r limit parents v.
  destruct (audit_nca_walk_exists V E EV r limit parents v) as [events Hrun].
  exists (nca_walk EV (semi_rank EV r) limit parents v), events.
  split; [exact Hrun|]; split; [reflexivity|].
  pose proof (audit_nca_walk_count V E EV r limit parents v _ _ Hrun) as Hcount.
  split; [exact Hcount|].
  set (width := audit_nca_walk_width EV r limit parents v).
  assert (Hsafe : Forall (audit_semi_call_safe V EV width) events).
  { eapply audit_nca_walk_safe; [exact Hrun| | | |].
    - apply audit_nca_walk_vertex_width; left; reflexivity.
    - intros x Hin; apply audit_nca_walk_vertex_width; right; exact Hin.
    - apply audit_nca_walk_rank_width.
    - unfold width, audit_nca_walk_width, audit_key_bits_weight; apply Nat.le_max_l. }
  pose proof (audit_semi_calls_work_safe V EV width events Hsafe) as Hwork.
  unfold audit_semi_compress_work, audit_nca_walk_budget, audit_nca_walk_event_bound in *.
  fold width; nia.
Qed.

(** A walk returns either its starting vertex or a value from its original parent map. *)
Lemma audit_nca_walk_result_in V E (EV : encoding V) (r : dfs_result V E) limit parents
    v result events :
  audit_nca_walk_run EV r limit parents v result events ->
  result = v \/ In result (map snd (Map.elements parents)).
Proof.
  intro Hrun; induction Hrun; try (left; reflexivity).
  destruct IHHrun as [Heq|Hin]; [subst result; right; eapply audit_semi_value_member; eassumption|
    right; exact Hin].
Qed.

(** Each forward step has a receipt for the source operation's exact successor. *)
Lemma audit_nca_step_exists V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis initial v :
  exists events, audit_nca_step_run EV g r semis initial v (nca_step EV g r semis initial v) events.
Proof.
  unfold nca_step; destruct (Map.get EV v (tree_edge r)) as [edge|] eqn:Htree.
  - destruct (audit_semi_value_counted EV semis v) as [value values] eqn:Hvalue.
    pose proof (audit_semi_value_counted_details V EV semis v) as [Hvalue_eq _].
    rewrite Hvalue in Hvalue_eq; cbn in Hvalue_eq; subst value.
    destruct (audit_semi_rank_counted EV r (semi_value EV semis v)) as [rank ranks] eqn:Hrank.
    pose proof (audit_semi_rank_counted_erases V E EV r (semi_value EV semis v)) as Hrank_eq.
    rewrite Hrank in Hrank_eq; cbn in Hrank_eq; subst rank.
    destruct (audit_nca_walk_exists V E EV r (semi_rank EV r (semi_value EV semis v)) initial
      (Graph.source g edge)) as [walk Hwalk].
    eexists; eapply AuditNcaStepNode; eauto.
  - exists [AuditNcaTreeGet v (tree_edge r) None; AuditNcaCase 0].
    apply AuditNcaStepRoot; exact Htree.
Qed.

(** The sequence receipt follows the same left fold as the source producer. *)
Lemma audit_nca_steps_exists V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis vertices initial :
  exists events, audit_nca_steps_run EV g r semis vertices initial
    (fold_left (nca_step EV g r semis) vertices initial) events.
Proof.
  revert initial; induction vertices as [|v rest IH]; intro initial; cbn [fold_left].
  - exists [AuditNcaCase 2]; constructor.
  - destruct (audit_nca_step_exists V E EV g r semis initial v) as [here Hstep].
    destruct (IH (nca_step EV g r semis initial v)) as [later Hrest].
    exists (AuditNcaCase 3 :: here ++ later); econstructor; eassumption.
Qed.

(** * Forward-pass input envelope *)

(** These vertices cover all source keys and values that the forward pass can select. *)
Definition audit_nca_input_vertex V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis (v : V) : Prop :=
  In v (preorder r ++ map fst (Map.elements semis) ++ map snd (Map.elements semis) ++
    map fst (Map.elements (tree_edge r)) ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++
    map fst (Map.elements (pre_num r))).

(** Every vertex in the original input envelope fits the producer width. *)
Lemma audit_nca_input_vertex_width V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis v :
  audit_nca_input_vertex V E EV g r semis v ->
  Pos.size_nat (encode EV v) <= audit_nca_compute_width EV g r semis.
Proof.
  intro Hin; unfold audit_nca_input_vertex in Hin.
  unfold audit_nca_compute_width, audit_key_bits_weight.
  eapply Nat.le_trans; [|apply Nat.le_max_l].
  apply (audit_dfs_width_member (fun node : V => Pos.size_nat (encode EV node))); exact Hin.
Qed.

(** The source of any recorded tree edge belongs to the original input envelope. *)
Lemma audit_nca_tree_source_in V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis v edge :
  Map.get EV v (tree_edge r) = Some edge ->
  audit_nca_input_vertex V E EV g r semis (Graph.source g edge).
Proof.
  intro Hget; apply audit_semi_value_member in Hget.
  unfold audit_nca_input_vertex; do 4 (apply in_or_app; right).
  apply in_or_app; left; apply in_map; exact Hget.
Qed.

(** An input vertex ensures the producer width also covers the default rank. *)
Lemma audit_nca_input_rank_width V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis witness x :
  audit_nca_input_vertex V E EV g r semis witness ->
  Pos.size_nat (semi_rank EV r x) <= audit_nca_compute_width EV g r semis.
Proof.
  intro Hwitness.
  pose proof (audit_semi_rank_width V E EV r x) as Hrank.
  pose proof (audit_nca_input_vertex_width V E EV g r semis witness Hwitness) as Hwidth.
  assert (Hpositive : 1 <= Pos.size_nat (encode EV witness)).
  { destruct (encode EV witness); cbn [Pos.size_nat]; lia. }
  eapply Nat.le_trans; [exact Hrank|].
  apply Nat.max_lub; [lia|].
  unfold audit_nca_compute_width, audit_key_bits_weight; apply Nat.le_max_r.
Qed.

(** Each outer receipt either uses an enveloped key or contains a safe inner event. *)
Definition audit_nca_call_safe V E (EV : encoding V) width (event : audit_nca_call V E) : Prop :=
  match event with
  | AuditNcaTreeGet v _ _ => Pos.size_nat (encode EV v) <= width
  | AuditNcaInner inner => audit_semi_call_safe V EV width inner
  | AuditNcaCase _
  | AuditNcaSource _ _ => True
  end.

(** The input-width allowance bounds each abstract outer event. *)
Lemma audit_nca_call_work_safe V E (EV : encoding V) width event :
  audit_nca_call_safe V E EV width event -> audit_nca_event_work EV event <= 132 + 3 * width.
Proof.
  destruct event; cbn [audit_nca_call_safe]; intro Hsafe;
    unfold audit_nca_event_work, audit_encoding_weight, audit_get_weight, audit_key_bits_weight;
    cbn.
  - lia.
  - lia.
  - lia.
  - change (64 + audit_semi_call_work EV event <= 132 + 3 * width).
    pose proof (audit_semi_call_work_safe V EV width event Hsafe); lia.
Qed.

(** Summing width-safe events preserves the actual receipt length. *)
Lemma audit_nca_calls_work_safe V E (EV : encoding V) width events :
  Forall (audit_nca_call_safe V E EV width) events ->
  fold_right (fun event total => audit_nca_event_work EV event + total) 0 events <=
    length events * (132 + 3 * width).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; cbn [length fold_right].
  - reflexivity.
  - pose proof (audit_nca_call_work_safe V E EV width event Hevent); lia.
Qed.

(** Each forward step preserves the input envelope and charges its actual walk receipt.
    The selected parent, intermediate map and receipt share the same walk derivation, so the
    envelope, count and width arguments stay together at this boundary. *)
Lemma audit_nca_step_in_input V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis initial v result events :
  audit_nca_step_run EV g r semis initial v result events ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) initial ->
  audit_nca_input_vertex V E EV g r semis v ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) result /\
  length events <= 12 * S (audit_semi_compute_rank_bound r) + 8 /\
  Forall (audit_nca_call_safe V E EV (audit_nca_compute_width EV g r semis)) events.
Proof.
  intros Hrun Henvelope Hv.
  pose proof (audit_nca_input_vertex_width V E EV g r semis v Hv) as Hvwidth.
  inversion Hrun as [m node Htree |m node edge value values limit ranks source selected walk
    Htree Hvalue Hrank Hsource Hwalk]; subst.
  - split; [exact Henvelope|]; split; [cbn; lia|].
    repeat constructor; cbn [audit_nca_call_safe]; auto.
  - assert (Hsource_in : audit_nca_input_vertex V E EV g r semis (Graph.source g edge)).
    { eapply audit_nca_tree_source_in; exact Htree. }
    assert (Hselected : audit_nca_input_vertex V E EV g r semis selected).
    { destruct (audit_nca_walk_result_in V E EV r limit initial (Graph.source g edge) selected walk
        Hwalk) as [Heq|Hin]; [subst; exact Hsource_in|].
      apply in_map_iff in Hin; destruct Hin as [[key val] [Heq Hin]]; cbn in Heq; subst val.
      exact (proj2 (audit_semi_map_envelope_elements V EV _ initial key selected Henvelope Hin)). }
    pose proof (audit_nca_walk_count V E EV r limit initial (Graph.source g edge) selected walk
      Hwalk) as Hcount.
    pose proof (audit_semi_rank_in_producer V E EV r (Graph.source g edge)) as Hrank_bound.
    change (Pos.to_nat (semi_rank EV r (Graph.source g edge)) <= audit_semi_compute_rank_bound r)
      in Hrank_bound.
    pose proof (audit_semi_value_counted_details V EV semis v) as [_ Hvalues].
    pose proof (audit_semi_rank_counted_length V E EV r value) as Hranks.
    rewrite Hvalue in Hvalues; cbn in Hvalues; subst values.
    rewrite Hrank in Hranks; cbn in Hranks.
    assert (Hlimit : Pos.size_nat limit <= audit_nca_compute_width EV g r semis).
    { pose proof (audit_semi_rank_counted_erases V E EV r value) as Hlimit.
      rewrite Hrank in Hlimit; cbn in Hlimit; subst limit.
      apply audit_nca_input_rank_width with (witness := v); exact Hv. }
    assert (Hwalk_safe : Forall (audit_semi_call_safe V EV (audit_nca_compute_width EV g r semis))
      walk).
    { eapply audit_nca_walk_safe; [exact Hwalk| | | |exact Hlimit].
      - apply audit_nca_input_vertex_width; exact Hsource_in.
      - intros x Hin; apply in_map_iff in Hin; destruct Hin as [[key val] [Heq Hin]].
        cbn in Heq; subst val; apply audit_nca_input_vertex_width.
        exact (proj2 (audit_semi_map_envelope_elements V EV _ initial key x Henvelope Hin)).
      - intro x; apply audit_nca_input_rank_width with (witness := v); exact Hv. }
    assert (Hrank_safe : Forall (audit_semi_call_safe V EV (audit_nca_compute_width EV g r semis))
      ranks).
    { pose proof (audit_nca_rank_safe V E EV r (audit_nca_compute_width EV g r semis) value)
        as Hsafe.
      assert (Hvalue_in : audit_nca_input_vertex V E EV g r semis value).
      { pose proof (audit_semi_value_counted_details V EV semis v) as [Hvalue_eq _].
        rewrite Hvalue in Hvalue_eq; cbn in Hvalue_eq; subst value.
        unfold semi_value; destruct (Map.get EV v semis) as [found|] eqn:Hget; [|exact Hv].
        unfold audit_nca_input_vertex; apply in_or_app; right; apply in_or_app; right.
        apply in_or_app; left; eapply audit_semi_value_member; exact Hget. }
      specialize (Hsafe (audit_nca_input_vertex_width V E EV g r semis value Hvalue_in)).
      rewrite Hrank in Hsafe; exact Hsafe. }
    split.
    + apply audit_semi_map_envelope_set; assumption.
    + split.
      * repeat rewrite length_app; repeat rewrite length_map; cbn [length]; lia.
      * repeat rewrite Forall_app; repeat split; cbn [map].
        -- repeat constructor; cbn [audit_nca_call_safe]; auto.
        -- repeat constructor; cbn [audit_nca_call_safe audit_semi_call_safe]; auto.
        -- apply Forall_map; exact Hrank_safe.
        -- repeat constructor; cbn [audit_nca_call_safe]; auto.
        -- apply Forall_map; exact Hwalk_safe.
        -- repeat constructor; cbn [audit_nca_call_safe audit_semi_call_safe]; auto.
Qed.

(** Folding steps retains the original envelope and accumulates their receipt bounds. *)
Lemma audit_nca_steps_in_input V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis vertices initial result events :
  audit_nca_steps_run EV g r semis vertices initial result events ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) initial ->
  (forall v, In v vertices -> audit_nca_input_vertex V E EV g r semis v) ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) result /\
  length events <= length vertices * (12 * S (audit_semi_compute_rank_bound r) + 9) + 1 /\
  Forall (audit_nca_call_safe V E EV (audit_nca_compute_width EV g r semis)) events.
Proof.
  intro Hrun; induction Hrun as [m|v rest initial middle result here later Hstep Hrest IH];
    intros Henvelope Hvertices.
  - split; [exact Henvelope|]; split; [cbn; lia|].
    repeat constructor; exact I.
  - destruct (audit_nca_step_in_input V E EV g r semis initial v middle here Hstep Henvelope
      (Hvertices v (or_introl eq_refl))) as [Hmiddle [Hhere Hsafe_here]].
    destruct (IH Hmiddle (fun x Hin => Hvertices x (or_intror Hin)))
      as [Hresult [Hlater Hsafe_later]].
    split; [exact Hresult|]; split.
    + cbn [length]; rewrite length_app; nia.
    + constructor; [exact I|]; apply Forall_app; split; assumption.
Qed.

(** The forward pass returns its source map within the original rank and width budget. *)
Theorem audit_nca_compute_correct : audit_nca_compute_statement.
Proof.
  intros V E EV g r semis.
  destruct (audit_nca_steps_exists V E EV g r semis (preorder r) Map.empty) as [events Hrun].
  exists (nca_compute EV g r semis), events; split; [exact Hrun|]; split; [reflexivity|].
  assert (Hinitial : audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis)
    Map.empty) by apply audit_semi_map_envelope_empty.
  assert (Hvertices : forall v, In v (preorder r) -> audit_nca_input_vertex V E EV g r semis v).
  { intros v Hin; unfold audit_nca_input_vertex; apply in_or_app; left; exact Hin. }
  destruct (audit_nca_steps_in_input V E EV g r semis (preorder r) Map.empty _ _ Hrun
    Hinitial Hvertices) as [_ [Hcount Hsafe]].
  assert (Hbound : length events <= audit_nca_compute_event_bound r).
  { unfold audit_nca_compute_event_bound; nia. }
  split; [exact Hbound|].
  pose proof (audit_nca_calls_work_safe V E EV (audit_nca_compute_width EV g r semis) events Hsafe)
    as Hwork.
  unfold audit_nca_compute_work, audit_nca_compute_budget; nia.
Qed.

(** * Callback-preserving source execution *)

(** The nested walk captures the actual callbacks and returns the ordinary walk result. *)
Lemma audit_nca_source_walk_exists V E B (EV : encoding V) enc (r : dfs_result V E)
    limit parents v :
  (forall x, fst (enc x) = encode EV x) ->
  exists events, audit_nca_source_walk_run (B := B) enc r limit parents v
    (nca_walk EV (semi_rank EV r) limit parents v) events.
Proof.
  intro Hencode; pattern v; apply (well_founded_induction
    (well_founded_ltof V (fun x => Pos.to_nat (semi_rank EV r x)))); clear v.
  intros v IH.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r v (Hencode v)) as Hrank_value.
  destruct (audit_semi_nested_rank enc r v) as [rank events] eqn:Hrank.
  cbn in Hrank_value; subst rank.
  pose proof (proj1 (proj2 (audit_positive_order (semi_rank EV r v) limit))) as Hthreshold_value.
  destruct (audit_positive_leb (semi_rank EV r v) limit) as [threshold cmp] eqn:Hthreshold.
  cbn in Hthreshold_value.
  rewrite nca_walk_unfold; unfold nca_walk_body; rewrite <- Hthreshold_value.
  destruct threshold.
  - eexists; eapply NcaSourceThreshold; eassumption.
  - pose proof (audit_map_get_erases V V B enc EV v parents (Hencode v)) as Hparent_value.
    destruct (audit_map_get enc v parents) as [parent reads] eqn:Hparent.
    cbn in Hparent_value; rewrite <- Hparent_value; destruct parent as [a|].
    + pose proof (audit_semi_nested_rank_erases V E B EV enc r a (Hencode a)) as Ha_value.
      destruct (audit_semi_nested_rank enc r a) as [ra ea] eqn:Ha; cbn in Ha_value; subst ra.
      pose proof (proj1 (audit_positive_order (semi_rank EV r a) (semi_rank EV r v))) as Hlt_value.
      destruct (audit_positive_ltb (semi_rank EV r a) (semi_rank EV r v)) as [less cmp2] eqn:Hlt.
      cbn in Hlt_value; destruct less.
      * assert (Hdecrease : Pos.to_nat (semi_rank EV r a) < Pos.to_nat (semi_rank EV r v)).
        { apply Pos2Nat.inj_lt, Pos.ltb_lt; symmetry; exact Hlt_value. }
        destruct (semi_rank_less (semi_rank EV r a) (semi_rank EV r v)) as [Hproof|Hnot];
          [|contradiction].
        destruct (IH a Hdecrease) as [inner Hinner].
        eexists; eapply NcaSourceRecur; eassumption.
      * destruct (semi_rank_less (semi_rank EV r a) (semi_rank EV r v)) as [Hproof|Hnot].
        { apply Pos2Nat.inj_lt, Pos.ltb_lt in Hproof; congruence. }
        eexists; eapply NcaSourceStop; eassumption.
    + eexists; eapply NcaSourceNoParent; eassumption.
Qed.

(** Each nested step captures the actual source, encoder, and map-update receipts. *)
Lemma audit_nca_source_step_exists V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis initial v :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_nca_source_step_run (B := B) enc source r semis initial v
    (nca_step EV g r semis initial v) events.
Proof.
  intros Hencode Hsource.
  pose proof (audit_map_get_erases V E B enc EV v (tree_edge r) (Hencode v)) as Htree_value.
  destruct (audit_map_get enc v (tree_edge r)) as [edge reads] eqn:Htree; cbn in Htree_value.
  unfold nca_step; rewrite <- Htree_value; destruct edge as [edge|].
  - pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Hvalue_eq.
    destruct (audit_map_get enc v semis) as [value values] eqn:Hvalue; cbn in Hvalue_eq.
    assert (Hselected :
      (match value with
      Some x => x
      | None => v
      end) = semi_value EV semis v).
    { unfold semi_value; rewrite <- Hvalue_eq; destruct value; reflexivity. }
    pose proof (audit_semi_nested_rank_erases V E B EV enc r
      (match value with
      Some x => x
      | None => v
      end) (Hencode _)) as Hrank_value.
    destruct (audit_semi_nested_rank enc r
      (match value with
      Some x => x
      | None => v
      end))
      as [limit ranks] eqn:Hrank; cbn in Hrank_value; rewrite Hselected in Hrank_value; subst limit.
    destruct (source edge) as [origin body] eqn:Horigin.
    specialize (Hsource edge); rewrite Horigin in Hsource; cbn in Hsource; subst origin.
    destruct (audit_nca_source_walk_exists V E B EV enc r (semi_rank EV r (semi_value EV semis v))
      initial (Graph.source g edge) Hencode) as [walk Hwalk].
    pose proof (audit_map_set_erases V V B enc EV v
      (nca_walk EV (semi_rank EV r) (semi_rank EV r (semi_value EV semis v)) initial
        (Graph.source g edge)) initial (Hencode v)) as Hset_value.
    destruct (audit_map_set enc v
      (nca_walk EV (semi_rank EV r) (semi_rank EV r (semi_value EV semis v)) initial
        (Graph.source g edge)) initial) as [output writes] eqn:Hset.
    cbn in Hset_value; subst output.
    eexists; eapply NcaSourceNode; eassumption.
  - eexists; eapply NcaSourceRoot; exact Htree.
Qed.

(** The source receipt follows the same fold as the uninstrumented producer. *)
Lemma audit_nca_source_steps_exists V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis vertices initial :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_nca_source_steps_run (B := B) enc source r semis vertices initial
    (fold_left (nca_step EV g r semis) vertices initial) events.
Proof.
  intros Hencode Hsource; revert initial.
  induction vertices as [|v rest IH]; intro initial; cbn [fold_left].
  - exists [NcaSourceCase 2]; constructor.
  - destruct (audit_nca_source_step_exists V E B EV g enc source r semis initial v Hencode Hsource)
      as [here Hstep].
    destruct (IH (nca_step EV g r semis initial v)) as [later Hrest].
    exists (NcaSourceCase 3 :: here ++ later); econstructor; eassumption.
Qed.

(** A nested walk's event count decreases with the same discovery rank as the source. *)
Lemma audit_nca_source_walk_count V E B (EV : encoding V) enc (r : dfs_result V E)
    limit parents v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_nca_source_walk_run (B := B) enc r limit parents v result events ->
  length events <= 12 * S (Pos.to_nat (semi_rank EV r v)).
Proof.
  intros Hencode Hrun; induction Hrun.
  all: repeat rewrite length_app; repeat rewrite length_map; cbn [length].
  all: repeat
    match goal with
    | H : audit_semi_nested_rank _ _ ?vertex = (?rank, ?receipt) |- _ =>
      let Hlength := fresh "Hlength" in
      let Hvalue := fresh "Hvalue" in
      pose proof (proj1 (audit_semi_nested_reads_length V E B enc r
        (@semi_links_empty V) vertex)) as Hlength;
      pose proof (audit_semi_nested_rank_erases V E B EV enc r vertex (Hencode vertex)) as Hvalue;
      rewrite H in Hlength, Hvalue; cbn in Hlength, Hvalue; clear H
    | H : audit_map_get _ ?key ?input = (?value, ?receipt) |- _ =>
      let Hlength := fresh "Hlength" in
      pose proof (audit_semi_map_get_length V V B enc key input) as Hlength;
      rewrite H in Hlength; cbn in Hlength; clear H
    end.
  all: try lia.
  match goal with
  | Hcompare : audit_positive_ltb ?left ?right = (true, _) |- _ =>
    pose proof (proj1 (audit_positive_order left right)) as Hlt;
    rewrite Hcompare in Hlt; cbn in Hlt; symmetry in Hlt;
    apply Pos.ltb_lt in Hlt; apply Pos2Nat.inj_lt in Hlt
  end.
  subst; lia.
Qed.

(** A nested walk returns its start or a parent value from the original map. *)
Lemma audit_nca_source_walk_result_in V E B (EV : encoding V) enc (r : dfs_result V E)
    limit parents v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_nca_source_walk_run (B := B) enc r limit parents v result events ->
  result = v \/ In result (map snd (Map.elements parents)).
Proof.
  intros Hencode Hrun; induction Hrun as
    [v rank events cmp Hrank Hthreshold
    |v rank events cmp reads Hrank Hthreshold Hparent
    |v rank events cmp a reads ra rv ea ev cmp2 Hrank Hthreshold Hparent Hrank_a Hcurrent Hcompare
    |v rank events cmp a reads ra rv ea ev cmp2 result inner Hrank Hthreshold Hparent Hrank_a
      Hcurrent Hcompare Hrun IH]; try (left; reflexivity).
  destruct IH as [Heq|Hin]; [subst result|right; exact Hin].
  right; apply (audit_semi_value_member V V EV parents v a).
  pose proof (audit_map_get_erases V V B enc EV v parents (Hencode v)) as Herase.
  rewrite Hparent in Herase; symmetry; exact Herase.
Qed.

(** A recorded rank is bounded by the corresponding source rank. *)
Lemma audit_nca_nested_recorded_rank_width V E B (EV : encoding V) enc (r : dfs_result V E)
    width v rank events :
  fst (enc v) = encode EV v -> audit_semi_nested_rank (B := B) enc r v = (rank, events) ->
  Pos.size_nat (semi_rank EV r v) <= width -> Pos.size_nat rank <= width.
Proof.
  intros Hencode Hrank Hwidth.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r v Hencode) as Herase.
  rewrite Hrank in Herase; cbn in Herase; now rewrite Herase.
Qed.

(** Nested walk events retain their actual bodies while their operands stay within width. *)
Lemma audit_nca_source_walk_safe V E B (EV : encoding V) enc (r : dfs_result V E)
    limit parents v result events weight width :
  (forall x, fst (enc x) = encode EV x) ->
  audit_nca_source_walk_run (B := B) enc r limit parents v result events ->
  Pos.size_nat (encode EV v) <= width ->
  (forall x, In x (map snd (Map.elements parents)) -> Pos.size_nat (encode EV x) <= width) ->
  (forall x, Pos.size_nat (semi_rank EV r x) <= width) ->
  Pos.size_nat limit <= width ->
  Forall (audit_semi_nested_event_safe V B weight width) events.
Proof.
  intros Hencode Hrun; induction Hrun as
    [v rank events cmp Hrank Hthreshold
    |v rank events cmp reads Hrank Hthreshold Hparent
    |v rank events cmp a reads ra rv ea ev cmp2 Hrank Hthreshold Hparent Hrank_a Hcurrent Hcompare
    |v rank events cmp a reads ra rv ea ev cmp2 result inner Hrank Hthreshold Hparent Hrank_a
      Hcurrent Hcompare Hrun IH]; intros Hv Hparents Hranks Hlimit.
  all: repeat
    match goal with
    | |- Forall _ (_ ++ _) => apply Forall_app; split
    end.
  all: try solve [
    pose proof (audit_semi_nested_rank_safe V E B EV enc weight width r v (Hencode v) Hv) as Hsafe;
    rewrite Hrank in Hsafe; exact Hsafe].
  all: try solve [
    pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v parents (Hencode v) Hv)
      as Hsafe; rewrite Hparent in Hsafe; exact Hsafe].
  all: try solve [
    assert (Ha : Pos.size_nat (encode EV a) <= width) by
      (apply Hparents; apply (audit_semi_value_member V V EV parents v a);
       pose proof (audit_map_get_erases V V B enc EV v parents (Hencode v)) as Herase;
       rewrite Hparent in Herase; symmetry; exact Herase);
    pose proof (audit_semi_nested_rank_safe V E B EV enc weight width r a (Hencode a) Ha) as Hsafe;
    rewrite Hrank_a in Hsafe; exact Hsafe].
  all: try solve [
    pose proof (audit_semi_nested_rank_safe V E B EV enc weight width r v (Hencode v) Hv) as Hsafe;
    rewrite Hcurrent in Hsafe; exact Hsafe].
  all: try solve [constructor; [apply audit_semi_nested_case_safe|constructor]].
  all: try solve [
    constructor; [|constructor; [apply audit_semi_nested_case_safe|constructor]];
    eapply audit_semi_nested_compare_safe;
    [eapply audit_nca_nested_recorded_rank_width; eauto
    |first [assumption|eapply audit_nca_nested_recorded_rank_width; eauto]
    |eauto]].
  all: apply IH; auto; apply Hparents; apply (audit_semi_value_member V V EV parents v a);
    pose proof (audit_map_get_erases V V B enc EV v parents (Hencode v)) as Herase;
    rewrite Hparent in Herase; symmetry; exact Herase.
Qed.

(** * Source work accounting *)

(** The source allowance charges a callback body in the same event that carries it. *)
Definition audit_nca_source_event_safe V E B (weight : B -> nat) width
    (event : audit_nca_source_event V E B) : Prop :=
  audit_nca_source_event_work weight event <=
    133 + 16 * width + audit_nca_source_event_body weight event.

(** A nested event remains safe when wrapped as an NCA source event. *)
Lemma audit_nca_source_inner_safe V E B (weight : B -> nat) width events :
  Forall (audit_semi_nested_event_safe V B weight width) events ->
  Forall (audit_nca_source_event_safe V E B weight width) (map NcaSourceInner events).
Proof.
  intro Hsafe; apply Forall_map; eapply Forall_impl; [|exact Hsafe].
  intros event Hevent; unfold audit_nca_source_event_safe, audit_nca_source_event_work,
    audit_nca_source_event_body, audit_semi_nested_event_safe in *; cbn in *; lia.
Qed.

(** A tree lookup charges the actual encoding body and trie traversal. *)
Lemma audit_nca_source_tree_safe V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V E) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_nca_source_event_safe V E B weight width)
    (map NcaSourceTree (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_get_source_work_bound V E B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in *; destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trace].
  cbn [fst snd] in Hencode, Hwork; subst code.
  cbn [snd map]; constructor; [|constructor].
  unfold audit_nca_source_event_safe, audit_nca_source_event_work, audit_nca_source_event_body.
  cbn [audit_map_source_work] in *; lia.
Qed.

(** Case markers and captured source bodies need no additional operand allowance. *)
Lemma audit_nca_source_case_safe V E B (weight : B -> nat) width site :
  audit_nca_source_event_safe V E B weight width (NcaSourceCase site).
Proof.
  unfold audit_nca_source_event_safe, audit_nca_source_event_work, audit_nca_source_event_body.
  cbn; lia.
Qed.

(** A callback source body is charged exactly where the source edge is observed. *)
Lemma audit_nca_source_callback_safe V E B (weight : B -> nat) width edge vertex body :
  audit_nca_source_event_safe V E B weight width (NcaSourceSource edge vertex body).
Proof.
  unfold audit_nca_source_event_safe, audit_nca_source_event_work, audit_nca_source_event_body.
  cbn; lia.
Qed.

(** Summing safe events retains each actual callback-body charge. *)
Lemma audit_nca_source_safe_work V E B (weight : B -> nat) width events :
  Forall (audit_nca_source_event_safe V E B weight width) events ->
  audit_nca_source_work weight events <=
    length events * (133 + 16 * width) + audit_nca_source_body_work weight events.
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - unfold audit_nca_source_work, audit_nca_source_body_work in *.
    cbn [fold_right length] in *; unfold audit_nca_source_event_safe in Hevent; lia.
Qed.

(** A nested step preserves the input envelope and bounds the receipts it actually emitted.
    The read, walk, write and their callback bodies share witnesses from this one derivation;
    the envelope, count and safety arguments therefore stay together at this boundary. *)
Lemma audit_nca_source_step_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis initial v result events weight :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  audit_nca_source_step_run (B := B) enc source r semis initial v result events ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) initial ->
  audit_nca_input_vertex V E EV g r semis v ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) result /\
  length events <= 12 * S (audit_semi_producer_input_rank r) + 8 /\
  Forall (audit_nca_source_event_safe V E B weight (audit_nca_compute_width EV g r semis)) events.
Proof.
  intros Hencode Hsource Hrun Henvelope Hv.
  pose proof (audit_nca_input_vertex_width V E EV g r semis v Hv) as Hvwidth.
  inversion Hrun as [m node reads Htree |m node edge reads value values limit ranks origin body
    selected walk output writes Htree Hvalue Hrank Horigin Hwalk Hset]; subst.
  - pose proof (audit_semi_map_get_length V E B enc v (tree_edge r)) as Hlength.
    rewrite Htree in Hlength; cbn in Hlength.
    pose proof (audit_nca_source_tree_safe V E B EV enc weight _ v (tree_edge r)
      (Hencode v) Hvwidth) as Hsafe.
    rewrite Htree in Hsafe; cbn in Hsafe.
    split; [exact Henvelope|]; split; [rewrite length_app, length_map; cbn; lia|].
    apply Forall_app; split; [exact Hsafe|].
    constructor; [apply audit_nca_source_case_safe|constructor].
  - pose proof (audit_map_get_erases V E B enc EV v (tree_edge r) (Hencode v)) as Htree_value.
    rewrite Htree in Htree_value; cbn in Htree_value; symmetry in Htree_value.
    pose proof (Hsource edge) as Horigin_value; rewrite Horigin in Horigin_value;
      cbn in Horigin_value; subst origin.
    assert (Hsource_in : audit_nca_input_vertex V E EV g r semis (Graph.source g edge)).
    { eapply audit_nca_tree_source_in; exact Htree_value. }
    assert (Hselected : audit_nca_input_vertex V E EV g r semis selected).
    { destruct (audit_nca_source_walk_result_in V E B EV enc r limit initial (Graph.source g edge)
        selected walk Hencode Hwalk) as [Heq|Hin]; [subst; exact Hsource_in|].
      apply in_map_iff in Hin; destruct Hin as [[key val] [Heq Hin]]; cbn in Heq; subst val.
      exact (proj2 (audit_semi_map_envelope_elements V EV _ initial key selected Henvelope Hin)). }
    pose proof (audit_map_set_erases V V B enc EV v selected initial (Hencode v)) as Houtput.
    rewrite Hset in Houtput; cbn in Houtput; subst result.
    pose proof (audit_nca_source_walk_count V E B EV enc r limit initial (Graph.source g edge)
      selected walk Hencode Hwalk) as Hcount.
    pose proof (audit_semi_rank_in_producer V E EV r (Graph.source g edge)) as Hrank_bound.
    pose proof (audit_semi_map_get_length V E B enc v (tree_edge r)) as Hreads.
    pose proof (audit_semi_map_get_length V V B enc v semis) as Hvalues.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r (@semi_links_empty V)
      (match value with
      Some x => x
      | None => v
      end))) as Hranks.
    pose proof (audit_semi_map_set_length V V B enc v selected initial) as Hwrites.
    rewrite Htree in Hreads; rewrite Hvalue in Hvalues; rewrite Hrank in Hranks;
      rewrite Hset in Hwrites; cbn in Hreads, Hvalues, Hranks, Hwrites.
    assert (Hlimit : Pos.size_nat limit <= audit_nca_compute_width EV g r semis).
    { eapply audit_nca_nested_recorded_rank_width; [apply Hencode|exact Hrank|].
      apply audit_nca_input_rank_width with (witness := v); exact Hv. }
    assert (Hwalk_safe : Forall (audit_semi_nested_event_safe V B weight
      (audit_nca_compute_width EV g r semis)) walk).
    { eapply audit_nca_source_walk_safe; [exact Hencode|exact Hwalk| | | |exact Hlimit].
      - apply audit_nca_input_vertex_width; exact Hsource_in.
      - intros x Hin; apply in_map_iff in Hin; destruct Hin as [[key val] [Heq Hin]].
        cbn in Heq; subst val; apply audit_nca_input_vertex_width.
        exact (proj2 (audit_semi_map_envelope_elements V EV _ initial key x Henvelope Hin)).
      - intro x; apply audit_nca_input_rank_width with (witness := v); exact Hv. }
    assert (Hvalue_in : audit_nca_input_vertex V E EV g r semis
      (match value with
      Some x => x
      | None => v
      end)).
    { pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Hget.
      rewrite Hvalue in Hget; cbn in Hget; destruct value as [found|]; [|exact Hv].
      unfold audit_nca_input_vertex; apply in_or_app; right; apply in_or_app; right.
      apply in_or_app; left; eapply audit_semi_value_member; symmetry; exact Hget. }
    pose proof (audit_nca_input_vertex_width V E EV g r semis _ Hvalue_in) as Hvaluewidth.
    assert (Hsafe_tree := audit_nca_source_tree_safe V E B EV enc weight _ v (tree_edge r)
      (Hencode v) Hvwidth).
    assert (Hsafe_values := audit_semi_nested_vertex_get_safe V B EV enc weight _ v semis
      (Hencode v) Hvwidth).
    assert (Hsafe_ranks := audit_semi_nested_rank_safe V E B EV enc weight _ r
      (match value with
      Some x => x
      | None => v
      end) (Hencode _) Hvaluewidth).
    assert (Hsafe_writes := audit_semi_nested_vertex_set_safe V B EV enc weight _ v selected initial
      (Hencode v) Hvwidth).
    rewrite Htree in Hsafe_tree; rewrite Hvalue in Hsafe_values; rewrite Hrank in Hsafe_ranks;
      rewrite Hset in Hsafe_writes; cbn in Hsafe_tree, Hsafe_values, Hsafe_ranks, Hsafe_writes.
    split.
    + apply audit_semi_map_envelope_set; assumption.
    + split.
      * repeat rewrite length_app; repeat rewrite length_map; cbn [length]; lia.
      * repeat rewrite Forall_app; repeat split.
        -- exact Hsafe_tree.
        -- constructor; [apply audit_nca_source_case_safe|constructor].
        -- rewrite <- map_map; apply audit_nca_source_inner_safe; exact Hsafe_values.
        -- apply audit_nca_source_inner_safe; exact Hsafe_ranks.
        -- constructor; [apply audit_nca_source_callback_safe|constructor].
        -- apply audit_nca_source_inner_safe; exact Hwalk_safe.
        -- rewrite <- map_map; apply audit_nca_source_inner_safe; exact Hsafe_writes.
Qed.

(** A sequence of nested steps accumulates its same-run body and event allowances. *)
Lemma audit_nca_source_steps_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis vertices initial result events weight :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  audit_nca_source_steps_run (B := B) enc source r semis vertices initial result events ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) initial ->
  (forall v, In v vertices -> audit_nca_input_vertex V E EV g r semis v) ->
  audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis) result /\
  length events <= length vertices * (12 * S (audit_semi_producer_input_rank r) + 9) + 1 /\
  Forall (audit_nca_source_event_safe V E B weight (audit_nca_compute_width EV g r semis)) events.
Proof.
  intros Hencode Hsource Hrun.
  induction Hrun as [m|v rest initial middle result here later Hstep Hrest IH];
    intros Henvelope Hvertices.
  - split; [exact Henvelope|]; split; [cbn; lia|].
    constructor; [apply audit_nca_source_case_safe|constructor].
  - destruct (audit_nca_source_step_in_input V E B EV g enc source r semis initial v middle here
      weight Hencode Hsource Hstep Henvelope (Hvertices v (or_introl eq_refl)))
      as [Hmiddle [Hhere Hsafe_here]].
    destruct (IH Hmiddle (fun x Hin => Hvertices x (or_intror Hin)))
      as [Hresult [Hlater Hsafe_later]].
    split; [exact Hresult|]; split.
    + cbn [length]; rewrite length_app; nia.
    + constructor; [apply audit_nca_source_case_safe|].
      apply Forall_app; split; assumption.
Qed.

(** The quadratic envelope absorbs the width-safe event costs and retains body charges. *)
Lemma audit_nca_source_work_arithmetic count bound width work body :
  count <= bound -> work <= count * (133 + 16 * width) + body ->
  work <= 512 * S bound * S bound + bound * (512 + 64 * width) + body.
Proof.
  intros Hcount Hwork; nia.
Qed.

(** The source pass returns its original map and charges the callbacks from that same run. *)
Theorem audit_nca_source_holds : audit_nca_source_statement.
Proof.
  intros V E B EV g r semis enc source weight Hencode Hsource.
  destruct (audit_nca_source_steps_exists V E B EV g enc source r semis (preorder r) Map.empty
    Hencode Hsource) as [events Hrun].
  exists (nca_compute EV g r semis), events; split; [exact Hrun|]; split; [reflexivity|].
  assert (Hinitial : audit_semi_map_envelope V EV (audit_nca_input_vertex V E EV g r semis)
    Map.empty) by apply audit_semi_map_envelope_empty.
  assert (Hvertices : forall v, In v (preorder r) -> audit_nca_input_vertex V E EV g r semis v).
  { intros v Hin; unfold audit_nca_input_vertex; apply in_or_app; left; exact Hin. }
  destruct (audit_nca_source_steps_in_input V E B EV g enc source r semis (preorder r) Map.empty
    _ _ weight Hencode Hsource Hrun Hinitial Hvertices) as [_ [Hcount Hsafe]].
  pose proof (audit_nca_source_safe_work V E B weight (audit_nca_compute_width EV g r semis)
    events Hsafe) as Hwork.
  assert (Hbound : length events <=
    64 * S (length (preorder r)) * S (audit_semi_producer_input_rank r)) by nia.
  unfold audit_nca_source_input_bound.
  change (audit_nca_source_work weight events <=
    512 * S (64 * S (length (preorder r)) * S (audit_semi_producer_input_rank r)) *
      S (64 * S (length (preorder r)) * S (audit_semi_producer_input_rank r)) +
    (64 * S (length (preorder r)) * S (audit_semi_producer_input_rank r)) *
      (512 + 64 * audit_nca_compute_width EV g r semis) +
    audit_nca_source_body_work weight events).
  eapply audit_nca_source_work_arithmetic; eassumption.
Qed.
