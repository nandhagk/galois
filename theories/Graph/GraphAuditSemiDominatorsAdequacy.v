(** * Semidominator audit adequacy

    These proofs connect semidominator audit runs to the source traversal and its costs.
    For example, a root query records the missing shortcut and terminates immediately.
    Builds on: GraphAuditSemiDominators, GraphAuditDfsAdequacy, GraphAuditVirtualAdequacy,
    CollectionsAuditMapAdequacy and CollectionsAuditCompareAdequacy. *)

From Stdlib Require Import List Arith PArith Lia Wf_nat PeanoNat ZArith Ring.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsFinSet
  CollectionsAuditCost CollectionsAuditMap
  CollectionsAuditCompare
  CollectionsAuditMapAdequacy CollectionsAuditCompareAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators
  GraphAuditSemiDominators GraphDominance GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditBaseAdequacy GraphAuditDfsAdequacy GraphAuditVirtualAdequacy.
Import List.ListNotations.

(** * Determinism of receipts *)

(** Compression has one result and one receipt for each input. *)
Theorem audit_semi_compress_unique : audit_semi_compress_unique_statement.
Proof.
  intros V E EV r semis st v result1 events1 result2 events2 Hfirst.
  revert result2 events2.
  induction Hfirst; intros result2 events2 Hsecond; inversion Hsecond; subst;
    try congruence.
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
    | IH : forall _ _, audit_semi_compress_run _ _ _ _ _ _ _ -> _,
      Hrun : audit_semi_compress_run _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hevents]; inversion Hresult; subst
    end.
  all: try solve [split; reflexivity].
  all: cbn in *.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try solve [split; congruence].
  all: cbv zeta; split; reflexivity.
Qed.

(** Nested compression retains the same callback receipt on every derivation. *)
Theorem audit_semi_nested_compress_unique : audit_semi_nested_compress_unique_statement.
Proof.
  intros V E B enc r semis st v result1 events1 result2 events2 Hfirst.
  revert result2 events2.
  induction Hfirst; intros result2 events2 Hsecond; inversion Hsecond; subst;
    try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try congruence.
  all: try
    match goal with
    | IH : forall _ _, audit_semi_nested_compress_run _ _ _ _ _ _ _ -> _,
      Hrun : audit_semi_nested_compress_run _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hevents]; inversion Hresult; subst
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: try solve [split; congruence].
  all: cbv zeta; split; reflexivity.
Qed.

(** A predecessor step has a unique result and callback receipt. *)
Lemma audit_semi_producer_pred_unique V E B enc source (r : dfs_result V E) semis
    initial edge first first_events second second_events :
  audit_semi_producer_pred_run (B := B) enc source r semis initial edge first first_events ->
  audit_semi_producer_pred_run enc source r semis initial edge second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst;
    repeat
      match goal with
      | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
        rewrite Hleft in Hright; inversion Hright; clear Hright; subst
      end; try congruence.
  all: repeat
    match goal with
    | Hpair : (?a, ?b) = (?c, ?d) |- _ => inversion Hpair; clear Hpair; subst
    end.
  all: try solve [split; reflexivity].
  all: try
    match goal with
    | Hleft : audit_semi_nested_compress_run _ _ _ _ _ _ _,
      Hright : audit_semi_nested_compress_run _ _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_nested_compress_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; inversion Hresult; subst
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: split; reflexivity.
Qed.

(** Folding predecessor steps preserves determinism of both state and receipt. *)
Lemma audit_semi_producer_preds_unique V E B enc source (r : dfs_result V E) semis
    edges initial first first_events second second_events :
  audit_semi_producer_preds_run (B := B) enc source r semis edges initial first first_events ->
  audit_semi_producer_preds_run enc source r semis edges initial second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  -
    match goal with
    | Hleft : audit_semi_producer_pred_run _ _ _ _ _ _ _ _,
      Hright : audit_semi_producer_pred_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_producer_pred_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_semi_producer_preds_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_semi_producer_preds_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** Settling a vertex has a unique successor and receipt. *)
Lemma audit_semi_producer_settle_unique V E B (EV : encoding V) (g : Graph.t V E)
    enc source (p : prepared EV g) (r : dfs_result V E) st v first first_events
    second second_events :
  audit_semi_producer_settle_run (B := B) enc source p r st v first first_events ->
  audit_semi_producer_settle_run enc source p r st v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst;
    repeat
      match goal with
      | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
        rewrite Hleft in Hright; inversion Hright; clear Hright; subst
      end; try congruence.
  all: try solve [split; reflexivity].
  match goal with
  | Hleft : audit_semi_producer_preds_run _ _ _ _ _ _ _ _,
    Hright : audit_semi_producer_preds_run _ _ _ _ _ _ _ _ |- _ =>
    destruct (audit_semi_producer_preds_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
      as [Hresult Hevents]; inversion Hresult; subst
  end.
  repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  split; reflexivity.
Qed.

(** The reverse settlement traversal has a unique result and complete receipt. *)
Lemma audit_semi_producer_settles_unique V E B (EV : encoding V) (g : Graph.t V E)
    enc source (p : prepared EV g) (r : dfs_result V E) vertices st first first_events
    second second_events :
  audit_semi_producer_settles_run (B := B) enc source p r vertices st first first_events ->
  audit_semi_producer_settles_run enc source p r vertices st second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_semi_producer_settle_run _ _ _ _ _ _ _ _,
      Hright : audit_semi_producer_settle_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_producer_settle_unique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hleft Hright) as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_semi_producer_settles_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_semi_producer_settles_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** Nested production has the same state and receipt for any two runs. *)
Theorem audit_semi_producer_nested_unique : audit_semi_producer_nested_unique_statement.
Proof.
  intros V E B EV g p r enc source first first_events second second_events
    [here [Hfirst ->]] [later [Hsecond ->]].
  destruct (audit_semi_producer_settles_unique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hfirst Hsecond) as [Hresult Hevents].
  subst; split; reflexivity.
Qed.

(** An ordinary predecessor step determines its state and audit events. *)
Lemma audit_semi_pred_unique V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis initial edge first first_events second second_events :
  audit_semi_predecessor_run EV g r semis initial edge first first_events ->
  audit_semi_predecessor_run EV g r semis initial edge second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst;
    repeat
      match goal with
      | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
        rewrite Hleft in Hright; inversion Hright; clear Hright; subst
      end; try congruence.
  all: repeat
    match goal with
    | Hpair : (?a, ?b) = (?c, ?d) |- _ => inversion Hpair; clear Hpair; subst
    end.
  all: repeat
    match goal with
    | Hleft : ?f = Some ?a, Hright : ?f = Some ?b |- _ =>
      assert (a = b) by congruence; subst b; clear Hright
    end.
  all: try solve [split; reflexivity].
  all:
    match goal with
    | Hleft : audit_semi_compress_run _ _ _ _ _ _ _,
      Hright : audit_semi_compress_run _ _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_compress_unique _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; inversion Hresult; subst
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: split; reflexivity.
Qed.

(** Folding ordinary predecessor steps preserves determinism. *)
Lemma audit_semi_preds_unique V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis edges initial first first_events second second_events :
  audit_semi_predecessors_run EV g r semis edges initial first first_events ->
  audit_semi_predecessors_run EV g r semis edges initial second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_semi_predecessor_run _ _ _ _ _ _ _ _,
      Hright : audit_semi_predecessor_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_pred_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_semi_predecessors_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_semi_predecessors_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** Settling an ordinary vertex has one successor and one receipt. *)
Lemma audit_semi_settle_unique V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) st v first first_events second second_events :
  audit_semi_settle_run p r st v first first_events ->
  audit_semi_settle_run p r st v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst; try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = Some ?a, Hright : ?f = Some ?b |- _ =>
      assert (a = b) by congruence; subst b; clear Hright
    end.
  all: try solve [split; reflexivity].
  all:
    match goal with
    | Hleft : audit_semi_predecessors_run _ _ _ _ _ _ _ _,
      Hright : audit_semi_predecessors_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_preds_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; inversion Hresult; subst
    end.
  all: split; congruence.
Qed.

(** The ordinary reverse settlement traversal determines its entire receipt. *)
Lemma audit_semi_settles_unique V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) vertices st first first_events second second_events :
  audit_semi_settles_run p r vertices st first first_events ->
  audit_semi_settles_run p r vertices st second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_semi_settle_run _ _ _ _ _ _,
      Hright : audit_semi_settle_run _ _ _ _ _ _ |- _ =>
      destruct (audit_semi_settle_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_semi_settles_run _ _ _ _ _ _ -> _,
      Hrun : audit_semi_settles_run _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** Ordinary production has a unique result and event list. *)
Theorem audit_semi_compute_unique : audit_semi_compute_unique_statement.
Proof.
  intros V E EV g p r first second first_events second_events
    [here [Hfirst ->]] [later [Hsecond ->]].
  destruct (audit_semi_settles_unique _ _ _ _ _ _ _ _ _ _ _ _ Hfirst Hsecond)
    as [Hresult Hevents].
  subst; split; reflexivity.
Qed.

(** * Nested compression erasure *)

(** A counted rank lookup returns the source rank. *)
Lemma audit_semi_nested_rank_erases V E B (EV : encoding V) enc (r : dfs_result V E) v :
  fst (enc v) = encode EV v ->
  fst (audit_semi_nested_rank (B := B) enc r v) = semi_rank EV r v.
Proof.
  intro Hencode.
  pose proof (audit_map_get_erases V positive B enc EV v (pre_num r) Hencode) as Hget.
  unfold audit_semi_nested_rank, semi_rank.
  destruct (audit_map_get enc v (pre_num r)) as [found events]; cbn in *.
  now rewrite Hget.
Qed.

(** A counted score lookup returns the source score. *)
Lemma audit_semi_nested_score_erases V E B (EV : encoding V) enc (r : dfs_result V E)
    semis v :
  (forall x, fst (enc x) = encode EV x) ->
  fst (audit_semi_nested_score (B := B) enc r semis v) =
    semi_rank EV r (semi_value EV semis v).
Proof.
  intro Hencode.
  pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Hget.
  unfold audit_semi_nested_score, semi_value.
  destruct (audit_map_get enc v semis) as [found events]; cbn in Hget |- *.
  rewrite <- Hget.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r
    (match found with
    | Some x => x
    | None => v
    end) (Hencode _)) as Hrank.
  destruct (audit_semi_nested_rank enc r
    (match found with
    | Some x => x
    | None => v
    end))
    as [rank rank_events]; exact Hrank.
Qed.

(** A counted label lookup returns the source label. *)
Lemma audit_semi_nested_label_erases V B (EV : encoding V) enc st v :
  fst (enc v) = encode EV v ->
  fst (audit_semi_nested_label (B := B) enc st v) = semi_label EV st v.
Proof.
  intro Hencode.
  pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.labels st) Hencode) as Hget.
  unfold audit_semi_nested_label, semi_label.
  destruct (audit_map_get enc v (SemiLinks.labels st)) as [found events]; cbn in *.
  now rewrite Hget.
Qed.

(** Both counted writes produce the same shortcut state as the source writes. *)
Lemma audit_semi_nested_set_erases V B (EV : encoding V) enc st v root best :
  fst (enc v) = encode EV v ->
  fst (audit_semi_nested_shortcut_set (B := B) enc st v root best) =
    semi_shortcut_set EV st v root best.
Proof.
  intro Hencode.
  pose proof (audit_map_set_erases V V B enc EV v root (SemiLinks.shortcut st) Hencode) as Hshort.
  pose proof (audit_map_set_erases V V B enc EV v best (SemiLinks.labels st) Hencode) as Hlabel.
  unfold audit_semi_nested_shortcut_set, semi_shortcut_set.
  destruct (audit_map_set enc v root (SemiLinks.shortcut st)) as [shorts first].
  destruct (audit_map_set enc v best (SemiLinks.labels st)) as [labels second].
  cbn in *; now rewrite Hshort, Hlabel.
Qed.

(** Nested compression erases to the source query while retaining the actual callback events. *)
Theorem audit_semi_nested_compress_erasure : audit_semi_nested_compress_erasure_statement.
Proof.
  intros V E B EV enc r semis st v Hencode.
  induction v using (well_founded_induction
    (well_founded_ltof V (fun x => Pos.to_nat (semi_rank EV r x)))).
  pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.shortcut st) (Hencode v)) as Hget.
  destruct (audit_map_get enc v (SemiLinks.shortcut st)) as [found get_events] eqn:Hread.
  cbn in Hget.
  destruct found as [a|].
  - pose proof (audit_semi_nested_rank_erases V E B EV enc r a (Hencode a)) as Hra.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r v (Hencode v)) as Hrv.
    destruct (audit_semi_nested_rank enc r a) as [ra ea] eqn:Hrank_a.
    destruct (audit_semi_nested_rank enc r v) as [rv ev] eqn:Hrank_v.
    cbn in Hra, Hrv; subst ra rv.
    pose proof (proj1 (audit_positive_order (semi_rank EV r a) (semi_rank EV r v))) as Hcompare.
    destruct (audit_positive_ltb (semi_rank EV r a) (semi_rank EV r v))
      as [less compare_events] eqn:Hcomparison.
    cbn in Hcompare; destruct less.
    + assert (Hdecrease : Pos.to_nat (semi_rank EV r a) < Pos.to_nat (semi_rank EV r v)).
      { apply Pos2Nat.inj_lt, Pos.ltb_lt; symmetry; exact Hcompare. }
      destruct (H a Hdecrease) as [result [inner [Hrun Hresult]]].
      destruct result as [st' [root part]].
      pose proof (audit_semi_nested_label_erases V B EV enc st v (Hencode v)) as Hlabel.
      destruct (audit_semi_nested_label enc st v) as [label label_events] eqn:Hlabel_run.
      cbn in Hlabel.
      destruct part as [u|].
      * pose proof (audit_semi_nested_score_erases V E B EV enc r semis label Hencode) as Hsl.
        pose proof (audit_semi_nested_score_erases V E B EV enc r semis u Hencode) as Hsu.
        destruct (audit_semi_nested_score enc r semis label) as [sl el] eqn:Hscore_l.
        destruct (audit_semi_nested_score enc r semis u) as [su eu] eqn:Hscore_u.
        cbn in Hsl, Hsu; subst sl su.
        pose proof (proj1 (proj2 (audit_positive_order
          (semi_rank EV r (semi_value EV semis label))
          (semi_rank EV r (semi_value EV semis u))))) as Hchoose.
        destruct (audit_positive_leb (semi_rank EV r (semi_value EV semis label))
          (semi_rank EV r (semi_value EV semis u))) as [choose choose_events] eqn:Hchosen.
        cbn in Hchoose.
        pose proof (audit_semi_nested_set_erases V B EV enc st' v root
          (if choose then label else u) (Hencode v)) as Hset.
        destruct (audit_semi_nested_shortcut_set enc st' v root (if choose then label else u))
          as [final set_events] eqn:Hset_run.
        cbn in Hset.
        eexists; eexists; split.
        -- eapply SemiNestedRecurSome; eassumption.
        -- rewrite Hset, semi_compress_unfold; unfold semi_compress_body.
           rewrite <- Hget; destruct (semi_rank_less (semi_rank EV r a) (semi_rank EV r v));
             [|contradiction].
           rewrite <- Hresult; cbn; rewrite <- Hlabel; unfold semi_min.
           rewrite <- Hchoose; reflexivity.
      * pose proof (audit_semi_nested_set_erases V B EV enc st' v root label (Hencode v)) as Hset.
        destruct (audit_semi_nested_shortcut_set enc st' v root label)
          as [final set_events] eqn:Hset_run.
        cbn in Hset.
        eexists; eexists; split.
        -- eapply SemiNestedRecurNone; eassumption.
        -- rewrite Hset, semi_compress_unfold; unfold semi_compress_body.
           rewrite <- Hget; destruct (semi_rank_less (semi_rank EV r a) (semi_rank EV r v));
             [|contradiction].
           rewrite <- Hresult; cbn; now rewrite <- Hlabel.
    + eexists; eexists; split.
      * eapply SemiNestedStopped; eassumption.
      * rewrite semi_compress_unfold; unfold semi_compress_body; rewrite <- Hget.
        destruct (semi_rank_less (semi_rank EV r a) (semi_rank EV r v)) as [Hlt|Hnot];
          [|reflexivity].
        apply Pos2Nat.inj_lt, Pos.ltb_lt in Hlt; congruence.
  - exists (st, (v, None)), (map SemiNestedVertexMap get_events ++ [SemiNestedCase 0]).
    split; [apply SemiNestedRoot; exact Hread|].
    rewrite semi_compress_unfold; unfold semi_compress_body; now rewrite <- Hget.
Qed.

(** A counted predecessor step returns the same state as the source step. *)
Lemma audit_semi_producer_pred_erases V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis st best edge :
  (forall v, fst (enc v) = encode EV v) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_semi_producer_pred_run (B := B) enc source r semis (st, best) edge
    (semi_predecessor EV g r semis (st, best) edge) events.
Proof.
  intros Hencode Hsource.
  pose proof (Hsource edge) as Hsrc.
  destruct (source edge) as [vertex source_body] eqn:Hsource_run; cbn in Hsrc.
  pose proof (audit_map_get_erases V positive B enc EV vertex (pre_num r) (Hencode vertex))
    as Hrank.
  destruct (audit_map_get enc vertex (pre_num r)) as [number rank_events] eqn:Hrank_run.
  cbn in Hrank.
  unfold semi_predecessor; cbn; rewrite <- Hsrc, <- Hrank.
  destruct number as [number|].
  - destruct (audit_semi_nested_compress_erasure V E B EV enc r semis st vertex Hencode)
      as [query [inner [Hquery Herase]]].
    destruct query as [st' [root part]].
    unfold semi_eval; rewrite <- Herase; cbn.
    set (u :=
      match part with
      | Some chosen => chosen
      | None => vertex
      end).
    pose proof (audit_map_get_erases V V B enc EV u semis (Hencode u)) as Hvalue.
    destruct (audit_map_get enc u semis) as [value value_events] eqn:Hvalue_run.
    cbn in Hvalue; unfold semi_value; rewrite <- Hvalue.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r best (Hencode best)) as Hbest.
    destruct (audit_semi_nested_rank enc r best) as [best_rank best_events] eqn:Hbest_run.
    cbn in Hbest.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r
      (match value with
      | Some x => x
      | None => u
      end) (Hencode _)) as Hselected.
    destruct (audit_semi_nested_rank enc r
      (match value with
      | Some x => x
      | None => u
      end))
      as [value_rank value_rank_events] eqn:Hselected_run.
    cbn in Hselected.
    pose proof (proj1 (proj2 (audit_positive_order best_rank value_rank))) as Hcompare.
    destruct (audit_positive_leb best_rank value_rank) as [choose compare_events] eqn:Hcompare_run.
    cbn in Hcompare.
    unfold semi_min; rewrite <- Hbest, <- Hselected, <- Hcompare.
    eexists; eapply SemiProducerPredNumbered; try eassumption.
    reflexivity.
  - eexists; eapply SemiProducerPredMissing; eassumption.
Qed.

(** A counted predecessor fold returns the source fold over the same edge list. *)
Lemma audit_semi_producer_preds_erases V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis edges initial :
  (forall v, fst (enc v) = encode EV v) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_semi_producer_preds_run (B := B) enc source r semis edges initial
    (fold_left (semi_predecessor EV g r semis) edges initial) events.
Proof.
  intros Hencode Hsource; revert initial.
  induction edges as [|edge rest IH]; intro initial.
  - exists [SemiProducerCase 3]; constructor.
  - destruct initial as [st best].
    destruct (audit_semi_producer_pred_erases V E B EV g enc source r semis st best edge
      Hencode Hsource) as [here Hstep].
    destruct (IH (semi_predecessor EV g r semis (st, best) edge)) as [later Hrest].
    cbn [fold_left].
    eexists; econstructor; eassumption.
Qed.

(** The three counted link updates erase to the source link. *)
Lemma audit_semi_producer_link_erases V E B (EV : encoding V) enc st v parent :
  fst (enc v) = encode EV v ->
  fst (audit_semi_producer_link (E := E) (B := B) enc st v parent) = semi_link EV st v parent.
Proof.
  intro Hencode.
  pose proof (audit_map_set_erases V V B enc EV v parent (SemiLinks.original st) Hencode) as Ha.
  pose proof (audit_map_set_erases V V B enc EV v parent (SemiLinks.shortcut st) Hencode) as Hb.
  pose proof (audit_map_set_erases V V B enc EV v v (SemiLinks.labels st) Hencode) as Hc.
  unfold audit_semi_producer_link, semi_link.
  destruct (audit_map_set enc v parent (SemiLinks.original st)) as [original a].
  destruct (audit_map_set enc v parent (SemiLinks.shortcut st)) as [shortcut b].
  destruct (audit_map_set enc v v (SemiLinks.labels st)) as [labels c].
  cbn in *; now rewrite Ha, Hb, Hc.
Qed.

(** A counted settlement returns the source state after processing the same predecessors. *)
Lemma audit_semi_producer_settle_erases V E B (EV : encoding V) (g : Graph.t V E)
    enc source (p : prepared EV g) (r : dfs_result V E) st v :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_semi_producer_settle_run (B := B) enc source p r st v
    (semi_settle p r st v) events.
Proof.
  intros Hencode Hsource.
  pose proof (audit_map_get_erases V E B enc EV v (tree_edge r) (Hencode v)) as Htree.
  destruct (audit_map_get enc v (tree_edge r)) as [edge tree_events] eqn:Htree_run.
  cbn in Htree; unfold semi_settle; rewrite <- Htree.
  destruct edge as [edge|].
  - pose proof (Hsource edge) as Hsrc.
    destruct (source edge) as [parent source_body] eqn:Hsource_run; cbn in Hsrc.
    rewrite <- Hsrc.
    pose proof (audit_map_get_erases V (list E) B enc EV v (in_index p) (Hencode v)) as Hpred.
    destruct (audit_map_get enc v (in_index p)) as [incoming pred_events] eqn:Hpred_run.
    cbn in Hpred.
    unfold pred_edges, index_edges; rewrite <- Hpred.
    destruct (audit_semi_producer_preds_erases V E B EV g enc source r (SemiState.result st)
      (match incoming with
      | Some xs => xs
      | None => []
      end) (SemiState.links st, parent)
      Hencode Hsource) as [pred_events' Hpreds].
    destruct (fold_left (semi_predecessor EV g r (SemiState.result st))
      (match incoming with
      | Some xs => xs
      | None => []
      end) (SemiState.links st, parent))
      as [links' best] eqn:Hfold.
    pose proof (audit_map_set_erases V V B enc EV v best (SemiState.result st) (Hencode v))
      as Hresult.
    destruct (audit_map_set enc v best (SemiState.result st)) as [result_map result_events]
      eqn:Hresult_run.
    cbn in Hresult.
    pose proof (audit_semi_producer_link_erases V E B EV enc links' v parent (Hencode v)) as Hlink.
    destruct (audit_semi_producer_link (E := E) enc links' v parent) as [links'' link_events]
      eqn:Hlink_run.
    cbn in Hlink; rewrite <- Hresult, <- Hlink.
    eexists; eapply SemiProducerSettleNode; try eassumption; reflexivity.
  - eexists; apply SemiProducerSettleRoot; exact Htree_run.
Qed.

(** The counted reverse traversal erases to the source fold. *)
Lemma audit_semi_producer_settles_erases V E B (EV : encoding V) (g : Graph.t V E)
    enc source (p : prepared EV g) (r : dfs_result V E) vertices st :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_semi_producer_settles_run (B := B) enc source p r vertices st
    (fold_left (semi_settle p r) vertices st) events.
Proof.
  intros Hencode Hsource; revert st.
  induction vertices as [|v rest IH]; intro st.
  - exists [SemiProducerCase 7]; constructor.
  - destruct (audit_semi_producer_settle_erases V E B EV g enc source p r st v Hencode Hsource)
      as [here Hstep].
    destruct (IH (semi_settle p r st v)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** The nested producer returns the original computation with its same-run callback receipt. *)
Theorem audit_semi_producer_nested_erasure : audit_semi_producer_nested_erasure_statement.
Proof.
  intros V E B EV g p r enc source Hencode Hsource.
  destruct (audit_semi_producer_settles_erases V E B EV g enc source p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty) Hencode Hsource) as [events Hrun].
  exists (semi_compute p r), (SemiProducerOutput (length (preorder r)) :: events).
  split; [exists events; split; [exact Hrun|reflexivity]|reflexivity].
Qed.

(** Virtual production erases through the same prepared graph and DFS result. *)
Theorem audit_virtual_semi_erasure_holds : audit_virtual_semi_erasure_statement.
Proof.
  intros V E B EV g p cb source Hcallbacks Hsource.
  destruct (audit_virtual_full_callbacks_correct V E B EV g cb Hcallbacks) as [Hprepare Hdfs].
  pose proof (audit_graph_prepare_nested_correct _ _ _ (virtual_encoding EV)
    (virtual_graph EV g) (audit_virtual_full_prepare_callbacks g cb) Hprepare) as Hprepared.
  pose proof (audit_virtual_full_search_correct V E B EV g cb p Hcallbacks) as Hsearch.
  pose proof (audit_virtual_full_source_correct V E B EV g source Hsource) as Hsource_full.
  assert (Hencode : forall v,
    fst (audit_virtual_full_encode cb v) = encode (virtual_encoding EV) v).
  { destruct Hcallbacks as [_ [_ Henc]].
    intros [v|[]]; cbn [audit_virtual_full_encode virtual_encoding].
    - specialize (Henc v); destruct (audit_virtual_base_encode cb v); cbn in *; now rewrite Henc.
    - reflexivity. }
  unfold audit_virtual_full_search_counted, audit_virtual_full_search_with_prepared in Hsearch.
  unfold audit_virtual_semi_run, audit_virtual_full_search_with_prepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as [vp prepare_events] eqn:Hprep_run.
  cbn in Hprepared; destruct Hprepared as [Hprepared _].
  change (vp = virtual_prepared p) in Hprepared; subst vp.
  destruct (audit_dfs_nested_counted (virtual_prepared p) (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty [inr tt]) as [search dfs_events] eqn:Hdfs_run.
  cbn in Hsearch; subst search.
  destruct (audit_semi_producer_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) Hencode Hsource_full) as [result [events [Hrun Hresult]]].
  exists result, events; split; assumption.
Qed.

(** * Nested compression cost *)

(** Each counted map lookup emits one outer map event. *)
Lemma audit_semi_map_get_length K A B (enc : K -> positive * list B) key (m : Map.t K A) :
  length (snd (audit_map_get enc key m)) = 1.
Proof.
  unfold audit_map_get.
  destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code m); reflexivity.
Qed.

(** Each counted map update emits one outer map event. *)
Lemma audit_semi_map_set_length K A B (enc : K -> positive * list B) key value (m : Map.t K A) :
  length (snd (audit_map_set enc key value m)) = 1.
Proof.
  unfold audit_map_set.
  destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_trie_set code (key, value) m); reflexivity.
Qed.

(** Rank and label reads each emit one outer nested event. *)
Lemma audit_semi_nested_reads_length V E B (enc : V -> positive * list B)
    (r : dfs_result V E) st v :
  length (snd (audit_semi_nested_rank enc r v)) = 1 /\
  length (snd (audit_semi_nested_label enc st v)) = 1.
Proof.
  unfold audit_semi_nested_rank, audit_semi_nested_label.
  pose proof (audit_semi_map_get_length V positive B enc v (pre_num r)) as Hrank.
  pose proof (audit_semi_map_get_length V V B enc v (SemiLinks.labels st)) as Hlabel.
  destruct (audit_map_get enc v (pre_num r)) as [rank re].
  destruct (audit_map_get enc v (SemiLinks.labels st)) as [label le].
  cbn in *; now rewrite !length_map.
Qed.

(** A score read records the value lookup and its rank lookup. *)
Lemma audit_semi_nested_score_length V E B (enc : V -> positive * list B)
    (r : dfs_result V E) semis v :
  length (snd (audit_semi_nested_score enc r semis v)) = 2.
Proof.
  unfold audit_semi_nested_score.
  pose proof (audit_semi_map_get_length V V B enc v semis) as Hget.
  destruct (audit_map_get enc v semis) as [value events].
  pose proof (proj1 (audit_semi_nested_reads_length V E B enc r semi_links_empty
    (match value with
    | Some x => x
    | None => v
    end))) as Hrank.
  destruct (audit_semi_nested_rank enc r
    (match value with
    | Some x => x
    | None => v
    end))
    as [rank rank_events].
  cbn in *; rewrite length_app, length_map; lia.
Qed.

(** Updating a shortcut and label emits exactly two nested map events. *)
Lemma audit_semi_nested_set_length V B (enc : V -> positive * list B) st v root best :
  length (snd (audit_semi_nested_shortcut_set enc st v root best)) = 2.
Proof.
  unfold audit_semi_nested_shortcut_set.
  pose proof (audit_semi_map_set_length V V B enc v root (SemiLinks.shortcut st)) as Hshort.
  pose proof (audit_semi_map_set_length V V B enc v best (SemiLinks.labels st)) as Hlabel.
  destruct (audit_map_set enc v root (SemiLinks.shortcut st)) as [shorts first].
  destruct (audit_map_set enc v best (SemiLinks.labels st)) as [labels second].
  cbn in *; rewrite length_app, !length_map; lia.
Qed.

(** The nested query's event count decreases with the actual discovery rank. *)
Lemma audit_semi_nested_compress_count V E B (EV : encoding V) enc (r : dfs_result V E)
    semis st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  length events <= 20 * S (Pos.to_nat (semi_rank EV r v)).
Proof.
  intros Hencode Hrun; induction Hrun as
    [v get_events Hget
    |v a get_events ra rv ea ev compare_events Hget Hrank_a Hrank_v Hcompare
    |v a get_events ra rv ea ev compare_events st' root inner label label_events final
      set_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel Hset_run
    |v a get_events ra rv ea ev compare_events st' root u inner label label_events sl su el eu
      choose choose_events final set_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel Hscore_l
      Hscore_u Hchoose Hset_run].
  - pose proof (audit_semi_map_get_length V V B enc v (SemiLinks.shortcut st)) as Hlen.
    rewrite Hget in Hlen; cbn in Hlen.
    rewrite length_app, length_map; cbn; lia.
  - pose proof (audit_semi_map_get_length V V B enc v (SemiLinks.shortcut st)) as Hlen.
    rewrite Hget in Hlen; cbn in Hlen.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st a)) as Ha.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st v)) as Hv.
    rewrite Hrank_a in Ha; rewrite Hrank_v in Hv; cbn in Ha, Hv.
    repeat rewrite length_app; rewrite length_map; cbn; lia.
  - pose proof (audit_semi_map_get_length V V B enc v (SemiLinks.shortcut st)) as Hlen.
    rewrite Hget in Hlen; cbn in Hlen.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st a)) as Ha.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st v)) as Hv.
    pose proof (proj2 (audit_semi_nested_reads_length V E B enc r st v)) as Hl.
    pose proof (audit_semi_nested_set_length V B enc st' v root label) as Hset.
    rewrite Hrank_a in Ha; rewrite Hrank_v in Hv; rewrite Hlabel in Hl; rewrite Hset_run in Hset.
    cbn in Ha, Hv, Hl, Hset.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r a (Hencode a)) as Hra.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r v (Hencode v)) as Hrv.
    rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
    pose proof (proj1 (audit_positive_order (semi_rank EV r a) (semi_rank EV r v))) as Hlt.
    rewrite Hcompare in Hlt; cbn in Hlt; symmetry in Hlt; apply Pos.ltb_lt, Pos2Nat.inj_lt in Hlt.
    repeat rewrite length_app; rewrite length_map; cbn; lia.
  - pose proof (audit_semi_map_get_length V V B enc v (SemiLinks.shortcut st)) as Hlen.
    rewrite Hget in Hlen; cbn in Hlen.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st a)) as Ha.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st v)) as Hv.
    pose proof (proj2 (audit_semi_nested_reads_length V E B enc r st v)) as Hl.
    pose proof (audit_semi_nested_score_length V E B enc r semis label) as Hsl.
    pose proof (audit_semi_nested_score_length V E B enc r semis u) as Hsu.
    pose proof (audit_semi_nested_set_length V B enc st' v root (if choose then label else u))
      as Hset.
    rewrite Hrank_a in Ha; rewrite Hrank_v in Hv; rewrite Hlabel in Hl.
    rewrite Hscore_l in Hsl; rewrite Hscore_u in Hsu.
    rewrite Hset_run in Hset; cbn in Ha, Hv, Hl, Hsl, Hsu, Hset.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r a (Hencode a)) as Hra.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r v (Hencode v)) as Hrv.
    rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
    pose proof (proj1 (audit_positive_order (semi_rank EV r a) (semi_rank EV r v))) as Hlt.
    rewrite Hcompare in Hlt; cbn in Hlt; symmetry in Hlt; apply Pos.ltb_lt, Pos2Nat.inj_lt in Hlt.
    repeat rewrite length_app; rewrite length_map; cbn; lia.
Qed.

(** Any returned map value occurs in the input enumeration, even for malformed stored keys. *)
Lemma audit_semi_map_get_value_in K A (EV : encoding K) (m : Map.t K A) key value :
  Map.get EV key m = Some value -> exists stored_key, In (stored_key, value) (Map.elements m).
Proof.
  unfold Map.get, Map.code_get.
  destruct (Trie.get (encode EV key) m) as [[stored_key stored_value]|] eqn:Hget;
    cbn; intro Hvalue; [|discriminate].
  inversion Hvalue; subst stored_value.
  exists stored_key; unfold Map.elements; apply in_map_iff.
  exists (encode EV key, (stored_key, value)); split; [reflexivity|].
  apply Trie.elements_complete; exact Hget.
Qed.

(** One counted vertex lookup charges its actual encoder body and key width. *)
Lemma audit_semi_nested_vertex_get_work V B (enc : V -> positive * list B) (weight : B -> nat)
    key (input : Map.t V V) :
  let events := snd (audit_map_get enc key input) in
  audit_semi_nested_work weight (map SemiNestedVertexMap events) <=
    69 + 5 * Pos.size_nat (fst (enc key)) +
      audit_semi_nested_body_work weight (map SemiNestedVertexMap events).
Proof.
  pose proof (audit_map_get_source_work_bound V V B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hbound.
  unfold audit_map_get in *.
  destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trie_events].
  cbn [fst snd map fold_right audit_map_source_work audit_semi_nested_work
    audit_semi_nested_body_work
    audit_semi_nested_event_work audit_semi_nested_body_event_work] in *.
  unfold audit_semi_nested_event_work; cbn [audit_map_source_work].
  lia.
Qed.

(** One counted rank lookup charges its actual encoder body and key width. *)
Lemma audit_semi_nested_rank_get_work V B (enc : V -> positive * list B) (weight : B -> nat)
    key (input : Map.t V positive) :
  let events := snd (audit_map_get enc key input) in
  audit_semi_nested_work weight (map SemiNestedRankMap events) <=
    69 + 5 * Pos.size_nat (fst (enc key)) +
      audit_semi_nested_body_work weight (map SemiNestedRankMap events).
Proof.
  pose proof (audit_map_get_source_work_bound V positive B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hbound.
  unfold audit_map_get in *.
  destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trie_events].
  cbn [fst snd map fold_right audit_map_source_work audit_semi_nested_work
    audit_semi_nested_body_work
    audit_semi_nested_event_work audit_semi_nested_body_event_work] in *.
  unfold audit_semi_nested_event_work; cbn [audit_map_source_work].
  lia.
Qed.

(** One counted vertex update charges its actual encoder body and key width. *)
Lemma audit_semi_nested_vertex_set_work V B (enc : V -> positive * list B) (weight : B -> nat)
    key value (input : Map.t V V) :
  let events := snd (audit_map_set enc key value input) in
  audit_semi_nested_work weight (map SemiNestedVertexMap events) <=
    66 + 16 * Pos.size_nat (fst (enc key)) +
      audit_semi_nested_body_work weight (map SemiNestedVertexMap events).
Proof.
  pose proof (audit_map_set_source_work_bound V V B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key value input) as Hbound.
  unfold audit_map_set in *.
  destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_trie_set code (key, value) input) as [output trie_events].
  cbn [fst snd map fold_right audit_map_source_work audit_semi_nested_work
    audit_semi_nested_body_work
    audit_semi_nested_event_work audit_semi_nested_body_event_work] in *.
  unfold audit_semi_nested_event_work; cbn [audit_map_source_work].
  lia.
Qed.

(** Nested work and callback body work both distribute over concatenated receipts. *)
Lemma audit_semi_nested_work_app V B weight (first second : list (audit_semi_nested_event V B)) :
  audit_semi_nested_work weight (first ++ second) =
    audit_semi_nested_work weight first + audit_semi_nested_work weight second /\
  audit_semi_nested_body_work weight (first ++ second) =
    audit_semi_nested_body_work weight first + audit_semi_nested_body_work weight second.
Proof.
  induction first as [|event rest [IHwork IHbody]]; cbn [app].
  - split; reflexivity.
  - unfold audit_semi_nested_work, audit_semi_nested_body_work in *.
    cbn [fold_right] in *; rewrite IHwork, IHbody; split; lia.
Qed.

(** Every successful map lookup returns one of the enumerated values. *)
Lemma audit_semi_value_member K A (EV : encoding K) (m : Map.t K A) key value :
  Map.get EV key m = Some value -> In value (map snd (Map.elements m)).
Proof.
  intro Hget.
  destruct (audit_semi_map_get_value_in K A EV m key value Hget) as [stored_key Hin].
  apply in_map_iff; exists (stored_key, value); split; [reflexivity|exact Hin].
Qed.

(** Every rank, including the missing-key default, fits the rank-map value envelope. *)
Lemma audit_semi_rank_width V E (EV : encoding V) (r : dfs_result V E) v :
  Pos.size_nat (semi_rank EV r v) <=
    Nat.max 1 (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row))
      (Map.elements (pre_num r)))).
Proof.
  unfold semi_rank; destruct (Map.get EV v (pre_num r)) as [rank|] eqn:Hget.
  - destruct (audit_semi_map_get_value_in V positive EV (pre_num r) v rank Hget)
      as [stored_key Hin].
    eapply Nat.le_trans; [|apply Nat.le_max_r].
    exact (audit_dfs_width_member (fun row => Pos.size_nat (snd row))
      (Map.elements (pre_num r)) (stored_key, rank) Hin).
  - change (1 <= Nat.max 1 (fold_right Nat.max 0
      (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r))))).
    apply Nat.le_max_l.
Qed.

(** Vertices reached by the query come from its starting point or its original stored values. *)
Definition audit_semi_input_vertex V (semis : Map.t V V) (st : SemiLinks.t V) start v : Prop :=
  v = start \/ exists key,
    In (key, v) (Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
      Map.elements semis).

(** A value read from any of the three original maps belongs to the query envelope. *)
Lemma audit_semi_input_vertex_get V (EV : encoding V) semis st start key value :
  (Map.get EV key (SemiLinks.shortcut st) = Some value \/
   Map.get EV key (SemiLinks.labels st) = Some value \/ Map.get EV key semis = Some value) ->
  audit_semi_input_vertex V semis st start value.
Proof.
  intros [Hget|[Hget|Hget]]; right.
  - destruct (audit_semi_map_get_value_in V V EV (SemiLinks.shortcut st) key value Hget)
      as [stored Hin].
    exists stored; apply in_or_app; left; exact Hin.
  - destruct (audit_semi_map_get_value_in V V EV (SemiLinks.labels st) key value Hget)
      as [stored Hin].
    exists stored; apply in_or_app; right; apply in_or_app; left; exact Hin.
  - destruct (audit_semi_map_get_value_in V V EV semis key value Hget) as [stored Hin].
    exists stored; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

(** Each query-envelope vertex fits the original nested input width. *)
Lemma audit_semi_input_vertex_width V E (EV : encoding V) (r : dfs_result V E)
    semis st start v :
  audit_semi_input_vertex V semis st start v ->
  Pos.size_nat (encode EV v) <= audit_semi_nested_width EV r semis st start.
Proof.
  intro Hvertex; unfold audit_semi_nested_width.
  eapply Nat.le_trans; [|apply Nat.le_max_l].
  apply (audit_dfs_width_member (fun x : V => Pos.size_nat (encode EV x))).
  destruct Hvertex as [Heq|[key Hin]].
  - subst v; left; reflexivity.
  - right; apply in_or_app; right; apply in_or_app; left.
    apply in_map_iff; exists (key, v); split; [reflexivity|exact Hin].
Qed.

(** The nested input width also bounds every discovery rank used by the query. *)
Lemma audit_semi_nested_rank_width V E (EV : encoding V) (r : dfs_result V E)
    semis st start v :
  Pos.size_nat (semi_rank EV r v) <= audit_semi_nested_width EV r semis st start.
Proof.
  pose proof (audit_semi_rank_width V E EV r v) as Hrank.
  pose proof (audit_semi_input_vertex_width V E EV r semis st start start (or_introl eq_refl))
    as Hstart.
  assert (Hpositive : 1 <= Pos.size_nat (encode EV start)).
  { destruct (encode EV start); cbn [Pos.size_nat]; lia. }
  unfold audit_semi_nested_width in *.
  pose proof (Nat.le_max_r
    (fold_right Nat.max 0
      (map (fun x => Pos.size_nat (encode EV x))
        (start :: map fst (Map.elements (SemiLinks.shortcut st) ++
          Map.elements (SemiLinks.labels st) ++ Map.elements semis) ++
          map snd (Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
            Map.elements semis) ++ map fst (Map.elements (pre_num r)))))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))))
    as Hrows.
  eapply Nat.le_trans; [exact Hrank|].
  apply Nat.max_lub; lia.
Qed.

(** A nested label is either its input or a value in the original label map. *)
Lemma audit_semi_nested_label_in V B (EV : encoding V) enc semis st start v label events :
  (forall x, fst (enc x) = encode EV x) -> audit_semi_input_vertex V semis st start v ->
  audit_semi_nested_label (B := B) enc st v = (label, events) ->
  audit_semi_input_vertex V semis st start label.
Proof.
  intros Hencode Hv Hlabel.
  pose proof (audit_semi_nested_label_erases V B EV enc st v (Hencode v)) as Herase.
  rewrite Hlabel in Herase; cbn in Herase.
  unfold semi_label in Herase.
  destruct (Map.get EV v (SemiLinks.labels st)) as [found|] eqn:Hget.
  - subst label; eapply audit_semi_input_vertex_get; right; left; exact Hget.
  - now subst label.
Qed.

(** Compression returns a root and optional label from its original input envelope. *)
Lemma audit_semi_nested_result_in V E B (EV : encoding V) enc (r : dfs_result V E)
    semis st start v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  audit_semi_input_vertex V semis st start v ->
  audit_semi_input_vertex V semis st start (fst (snd result)) /\
  match snd (snd result) with
  | Some label => audit_semi_input_vertex V semis st start label
  | None => True
  end.
Proof.
  intros Hencode Hrun; induction Hrun as
    [v get_events Hget
    |v a get_events ra rv ea ev compare_events Hget Hrank_a Hrank_v Hcompare
    |v a get_events ra rv ea ev compare_events st' root inner label label_events final
      set_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel Hset
    |v a get_events ra rv ea ev compare_events st' root u inner label label_events sl su el eu
      choose choose_events final set_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel Hscore_l
      Hscore_u Hchoose Hset]; intro Hv; cbn.
  - split; [exact Hv|exact I].
  - split; [exact Hv|exact I].
  - assert (Ha : audit_semi_input_vertex V semis st start a).
    { pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.shortcut st) (Hencode v))
        as Herase.
      rewrite Hget in Herase; cbn in Herase.
      eapply audit_semi_input_vertex_get; left; symmetry; exact Herase. }
    destruct (IH Ha) as [Hroot _]; split; [exact Hroot|].
    exact (audit_semi_nested_label_in V B EV enc semis st start v label label_events
      Hencode Hv Hlabel).
  - assert (Ha : audit_semi_input_vertex V semis st start a).
    { pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.shortcut st) (Hencode v))
        as Herase.
      rewrite Hget in Herase; cbn in Herase.
      eapply audit_semi_input_vertex_get; left; symmetry; exact Herase. }
    destruct (IH Ha) as [Hroot Hu]; split; [exact Hroot|].
    destruct choose; [|exact Hu].
    exact (audit_semi_nested_label_in V B EV enc semis st start v label label_events
      Hencode Hv Hlabel).
Qed.

(** A safe event charges its own body plus a fixed allowance at the original input width. *)
Definition audit_semi_nested_event_safe V B (weight : B -> nat) width
    (event : audit_semi_nested_event V B) : Prop :=
  audit_semi_nested_event_work weight event <=
    69 + 16 * width + audit_semi_nested_body_event_work weight event.

(** A singleton receipt is safe when its whole work satisfies the same allowance. *)
Lemma audit_semi_nested_singleton_safe V B (weight : B -> nat) width
    (events : list (audit_semi_nested_event V B)) :
  length events = 1 ->
  audit_semi_nested_work weight events <= 69 + 16 * width +
    audit_semi_nested_body_work weight events ->
  Forall (audit_semi_nested_event_safe V B weight width) events.
Proof.
  destruct events as [|event [|next rest]]; cbn [length]; try discriminate.
  intros _ Hwork; constructor; [|constructor].
  unfold audit_semi_nested_event_safe, audit_semi_nested_work, audit_semi_nested_body_work in *.
  cbn [fold_right] in Hwork; lia.
Qed.

(** A vertex-map read is safe when its actual encoded key fits the envelope. *)
Lemma audit_semi_nested_vertex_get_safe V B (EV : encoding V) enc weight width key input :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_nested_event_safe V B weight width)
    (map SemiNestedVertexMap (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth; apply audit_semi_nested_singleton_safe.
  - rewrite length_map; apply audit_semi_map_get_length.
  - pose proof (audit_semi_nested_vertex_get_work V B enc weight key input) as Hwork.
    rewrite Hencode in Hwork.
    cbv zeta in Hwork; lia.
Qed.

(** A rank-map read is safe when its actual encoded key fits the envelope. *)
Lemma audit_semi_nested_rank_get_safe V B (EV : encoding V) enc weight width key input :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_nested_event_safe V B weight width)
    (map SemiNestedRankMap (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth; apply audit_semi_nested_singleton_safe.
  - rewrite length_map; apply audit_semi_map_get_length.
  - pose proof (audit_semi_nested_rank_get_work V B enc weight key input) as Hwork.
    rewrite Hencode in Hwork; cbv zeta in Hwork; lia.
Qed.

(** A vertex-map write is safe when its actual encoded key fits the envelope. *)
Lemma audit_semi_nested_vertex_set_safe V B (EV : encoding V) enc weight width key value input :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_nested_event_safe V B weight width)
    (map SemiNestedVertexMap (snd (audit_map_set enc key value input))).
Proof.
  intros Hencode Hwidth; apply audit_semi_nested_singleton_safe.
  - rewrite length_map; apply audit_semi_map_set_length.
  - pose proof (audit_semi_nested_vertex_set_work V B enc weight key value input) as Hwork.
    rewrite Hencode in Hwork; cbv zeta in Hwork; lia.
Qed.

(** A counted rank receipt uses a single safe rank-map lookup. *)
Lemma audit_semi_nested_rank_safe V E B (EV : encoding V) enc weight width (r : dfs_result V E) v :
  fst (enc v) = encode EV v -> Pos.size_nat (encode EV v) <= width ->
  Forall (audit_semi_nested_event_safe V B weight width) (snd (audit_semi_nested_rank enc r v)).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_nested_rank_get_safe V B EV enc weight width v (pre_num r) Hencode Hwidth)
    as Hsafe.
  unfold audit_semi_nested_rank.
  destruct (audit_map_get enc v (pre_num r)) as [found events]; exact Hsafe.
Qed.

(** A counted label receipt uses a single safe vertex-map lookup. *)
Lemma audit_semi_nested_label_safe V B (EV : encoding V) enc weight width st v :
  fst (enc v) = encode EV v -> Pos.size_nat (encode EV v) <= width ->
  Forall (audit_semi_nested_event_safe V B weight width) (snd (audit_semi_nested_label enc st v)).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v (SemiLinks.labels st)
    Hencode Hwidth) as Hsafe.
  unfold audit_semi_nested_label.
  destruct (audit_map_get enc v (SemiLinks.labels st)) as [found events]; exact Hsafe.
Qed.

(** A counted shortcut update uses two safe writes at the original vertex. *)
Lemma audit_semi_nested_set_safe V B (EV : encoding V) enc weight width st v root best :
  fst (enc v) = encode EV v -> Pos.size_nat (encode EV v) <= width ->
  Forall (audit_semi_nested_event_safe V B weight width)
    (snd (audit_semi_nested_shortcut_set enc st v root best)).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_nested_vertex_set_safe V B EV enc weight width v root
    (SemiLinks.shortcut st) Hencode Hwidth) as Hshort.
  pose proof (audit_semi_nested_vertex_set_safe V B EV enc weight width v best
    (SemiLinks.labels st) Hencode Hwidth) as Hlabel.
  unfold audit_semi_nested_shortcut_set.
  destruct (audit_map_set enc v root (SemiLinks.shortcut st)) as [shorts first].
  destruct (audit_map_set enc v best (SemiLinks.labels st)) as [labels second].
  cbn in *; apply Forall_app; split; assumption.
Qed.

(** A recorded comparison is safe when its actual operands fit the rank width. *)
Lemma audit_semi_nested_compare_safe V B (weight : B -> nat) width left right result events :
  Pos.size_nat left <= width -> Pos.size_nat right <= width ->
  (audit_positive_ltb left right = (result, events) \/
   audit_positive_leb left right = (result, events)) ->
  audit_semi_nested_event_safe V B weight width (SemiNestedCompare left right result events).
Proof.
  intros Hleft Hright Hcompare.
  pose proof (audit_positive_order left right) as [_ [_ [Hlt Hle]]].
  destruct Hcompare as [Hcompare|Hcompare]; rewrite Hcompare in *; cbn in *;
    unfold audit_semi_nested_event_safe, audit_semi_nested_event_work,
      audit_semi_nested_body_event_work; cbn;
    pose proof (Nat.le_min_l (Pos.size_nat left) (Pos.size_nat right)); lia.
Qed.

(** A score receipt reads only vertices in the original query envelope. *)
Lemma audit_semi_nested_score_safe V E B (EV : encoding V) enc weight (r : dfs_result V E)
    semis st start v :
  (forall x, fst (enc x) = encode EV x) -> audit_semi_input_vertex V semis st start v ->
  Forall (audit_semi_nested_event_safe V B weight (audit_semi_nested_width EV r semis st start))
    (snd (audit_semi_nested_score enc r semis v)).
Proof.
  intros Hencode Hv.
  set (width := audit_semi_nested_width EV r semis st start).
  pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hvwidth.
  pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v semis
    (Hencode v) Hvwidth) as Hread.
  pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Herase.
  unfold audit_semi_nested_score.
  destruct (audit_map_get enc v semis) as [found events] eqn:Hget.
  cbn in Hread, Herase.
  assert (Hnext : audit_semi_input_vertex V semis st start
    (match found with
    | Some value => value
    | None => v
    end)).
  { destruct found as [value|]; [|exact Hv].
    eapply audit_semi_input_vertex_get; right; right; symmetry; exact Herase. }
  pose proof (audit_semi_input_vertex_width V E EV r semis st start _ Hnext) as Hnextwidth.
  pose proof (audit_semi_nested_rank_safe V E B EV enc weight width r
    (match found with
    | Some value => value
    | None => v
    end) (Hencode _) Hnextwidth) as Hrank.
  destruct (audit_semi_nested_rank enc r
    (match found with
    | Some value => value
    | None => v
    end))
    as [rank rank_events].
  cbn in Hrank |- *; apply Forall_app; split; assumption.
Qed.

(** Summing safe events keeps the actual callback-body work separate. *)
Lemma audit_semi_nested_safe_work V B (weight : B -> nat) width events :
  Forall (audit_semi_nested_event_safe V B weight width) events ->
  audit_semi_nested_work weight events <=
    length events * (69 + 16 * width) + audit_semi_nested_body_work weight events.
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - unfold audit_semi_nested_work, audit_semi_nested_body_work in *.
    cbn [fold_right length] in *; unfold audit_semi_nested_event_safe in Hevent; lia.
Qed.

(** A query case marker has no callback work. *)
Lemma audit_semi_nested_case_safe V B (weight : B -> nat) width site :
  audit_semi_nested_event_safe V B weight width (SemiNestedCase site).
Proof.
  unfold audit_semi_nested_event_safe, audit_semi_nested_event_work,
    audit_semi_nested_body_event_work; cbn; lia.
Qed.

(** The read-and-compare prefix of a nonroot query stays inside its input envelope. *)
Lemma audit_semi_nested_prefix_safe V E B (EV : encoding V) enc weight (r : dfs_result V E)
    semis st start v a get_events ra rv ea ev less compare_events site :
  (forall x, fst (enc x) = encode EV x) -> audit_semi_input_vertex V semis st start v ->
  audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
  audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
  audit_positive_ltb ra rv = (less, compare_events) ->
  audit_semi_input_vertex V semis st start a /\
  Forall (audit_semi_nested_event_safe V B weight (audit_semi_nested_width EV r semis st start))
    (map SemiNestedVertexMap get_events ++ ea ++ ev ++
      [SemiNestedCompare ra rv less compare_events; SemiNestedCase site]).
Proof.
  intros Hencode Hv Hget Hrank_a Hrank_v Hcompare.
  set (width := audit_semi_nested_width EV r semis st start).
  pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.shortcut st) (Hencode v)) as Herase.
  rewrite Hget in Herase; cbn in Herase.
  assert (Ha : audit_semi_input_vertex V semis st start a).
  { eapply audit_semi_input_vertex_get; left; symmetry; exact Herase. }
  pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hvwidth.
  pose proof (audit_semi_input_vertex_width V E EV r semis st start a Ha) as Hawidth.
  pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v (SemiLinks.shortcut st)
    (Hencode v) Hvwidth) as Hsafe_get.
  rewrite Hget in Hsafe_get; cbn in Hsafe_get.
  pose proof (audit_semi_nested_rank_safe V E B EV enc weight width r a (Hencode a) Hawidth)
    as Hsafe_a.
  pose proof (audit_semi_nested_rank_safe V E B EV enc weight width r v (Hencode v) Hvwidth)
    as Hsafe_v.
  rewrite Hrank_a in Hsafe_a; rewrite Hrank_v in Hsafe_v; cbn in Hsafe_a, Hsafe_v.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r a (Hencode a)) as Hra.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r v (Hencode v)) as Hrv.
  rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
  pose proof (audit_semi_nested_rank_width V E EV r semis st start a) as Hra_width.
  pose proof (audit_semi_nested_rank_width V E EV r semis st start v) as Hrv_width.
  pose proof (audit_semi_nested_compare_safe V B weight width _ _ _ _ Hra_width Hrv_width
    (or_introl Hcompare)) as Hsafe_compare.
  split; [exact Ha|].
  repeat rewrite Forall_app; repeat split; try assumption.
  constructor; [exact Hsafe_compare|].
  constructor; [apply audit_semi_nested_case_safe|constructor].
Qed.

(** Every event in a nested compression run fits the original width and its own body receipt. *)
Lemma audit_semi_nested_compress_safe V E B (EV : encoding V) enc weight (r : dfs_result V E)
    semis st start v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  audit_semi_input_vertex V semis st start v ->
  Forall (audit_semi_nested_event_safe V B weight (audit_semi_nested_width EV r semis st start))
    events.
Proof.
  intros Hencode Hrun; induction Hrun as
    [v get_events Hget
    |v a get_events ra rv ea ev compare_events Hget Hrank_a Hrank_v Hcompare
    |v a get_events ra rv ea ev compare_events st' root inner label label_events final
      set_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel Hset
    |v a get_events ra rv ea ev compare_events st' root u inner label label_events sl su el eu
      choose choose_events final set_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel Hscore_l
      Hscore_u Hchoose Hset]; intro Hv.
  - pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hvwidth.
    pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight
      (audit_semi_nested_width EV r semis st start) v (SemiLinks.shortcut st) (Hencode v) Hvwidth)
      as Hsafe.
    rewrite Hget in Hsafe; cbn in Hsafe.
    apply Forall_app; split; [exact Hsafe|].
    constructor; [apply audit_semi_nested_case_safe|constructor].
  - destruct (audit_semi_nested_prefix_safe V E B EV enc weight r semis st start v a get_events
      ra rv ea ev false compare_events 1 Hencode Hv Hget Hrank_a Hrank_v Hcompare) as [_ Hsafe].
    exact Hsafe.
  - destruct (audit_semi_nested_prefix_safe V E B EV enc weight r semis st start v a get_events
      ra rv ea ev true compare_events 2 Hencode Hv Hget Hrank_a Hrank_v Hcompare) as [Ha Hprefix].
    pose proof (IH Ha) as Hinner.
    pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hvwidth.
    pose proof (audit_semi_nested_label_safe V B EV enc weight
      (audit_semi_nested_width EV r semis st start) st v (Hencode v) Hvwidth) as Hsafe_label.
    rewrite Hlabel in Hsafe_label; cbn in Hsafe_label.
    pose proof (audit_semi_nested_set_safe V B EV enc weight
      (audit_semi_nested_width EV r semis st start) st' v root label (Hencode v) Hvwidth)
      as Hsafe_set.
    rewrite Hset in Hsafe_set; cbn in Hsafe_set.
    repeat rewrite Forall_app in Hprefix.
    destruct Hprefix as [Hget_safe [Ha_safe [Hv_safe Hbranch_safe]]].
    repeat rewrite Forall_app; repeat split; try assumption;
      constructor; [apply audit_semi_nested_case_safe|constructor].
  - destruct (audit_semi_nested_prefix_safe V E B EV enc weight r semis st start v a get_events
      ra rv ea ev true compare_events 2 Hencode Hv Hget Hrank_a Hrank_v Hcompare) as [Ha Hprefix].
    pose proof (IH Ha) as Hinner.
    pose proof (audit_semi_nested_result_in V E B EV enc r semis st start a _ _ Hencode Hrun Ha)
      as [_ Hu].
    cbn in Hu.
    pose proof (audit_semi_nested_label_in V B EV enc semis st start v label label_events
      Hencode Hv Hlabel) as Hl.
    pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hvwidth.
    pose proof (audit_semi_nested_label_safe V B EV enc weight
      (audit_semi_nested_width EV r semis st start) st v (Hencode v) Hvwidth) as Hsafe_label.
    rewrite Hlabel in Hsafe_label; cbn in Hsafe_label.
    pose proof (audit_semi_nested_score_safe V E B EV enc weight r semis st start label Hencode Hl)
      as Hsafe_sl.
    pose proof (audit_semi_nested_score_safe V E B EV enc weight r semis st start u Hencode Hu)
      as Hsafe_su.
    rewrite Hscore_l in Hsafe_sl; rewrite Hscore_u in Hsafe_su; cbn in Hsafe_sl, Hsafe_su.
    pose proof (audit_semi_nested_score_erases V E B EV enc r semis label Hencode) as Hsl.
    pose proof (audit_semi_nested_score_erases V E B EV enc r semis u Hencode) as Hsu.
    rewrite Hscore_l in Hsl; rewrite Hscore_u in Hsu; cbn in Hsl, Hsu; subst sl su.
    pose proof (audit_semi_nested_rank_width V E EV r semis st start (semi_value EV semis label))
      as Hslwidth.
    pose proof (audit_semi_nested_rank_width V E EV r semis st start (semi_value EV semis u))
      as Hsuwidth.
    pose proof (audit_semi_nested_compare_safe V B weight
      (audit_semi_nested_width EV r semis st start)
      _ _ _ _ Hslwidth Hsuwidth (or_intror Hchoose)) as Hsafe_compare.
    pose proof (audit_semi_nested_set_safe V B EV enc weight
      (audit_semi_nested_width EV r semis st start) st' v root (if choose then label else u)
      (Hencode v) Hvwidth) as Hsafe_set.
    rewrite Hset in Hsafe_set; cbn in Hsafe_set.
    repeat rewrite Forall_app in Hprefix.
    destruct Hprefix as [Hget_safe [Ha_safe [Hv_safe Hbranch_safe]]].
    repeat rewrite Forall_app; repeat split; try assumption.
    all: try solve [constructor; [apply audit_semi_nested_case_safe|constructor]].
    all: constructor; [exact Hsafe_compare|constructor].
Qed.

(** Nested compression work is bounded by the original input and actual encoder bodies. *)
Theorem audit_semi_nested_compress_bound : audit_semi_nested_compress_bound_statement.
Proof.
  intros V E B EV enc weight r semis st v result events Hencode Hrun.
  pose proof (audit_semi_nested_compress_count V E B EV enc r semis st v result events
    Hencode Hrun) as Hcount.
  pose proof (audit_semi_nested_compress_safe V E B EV enc weight r semis st v v result events
    Hencode Hrun (or_introl eq_refl)) as Hsafe.
  pose proof (audit_semi_nested_safe_work V B weight (audit_semi_nested_width EV r semis st v)
    events Hsafe) as Hwork.
  split; [exact Hcount|].
  unfold audit_semi_nested_input_budget; nia.
Qed.

(** * Ordinary compression and cost *)

(** The ordinary counted rank operation returns the source rank. *)
Lemma audit_semi_rank_counted_erases V E (EV : encoding V) (r : dfs_result V E) v :
  fst (audit_semi_rank_counted EV r v) = semi_rank EV r v.
Proof.
  unfold audit_semi_rank_counted, semi_rank; destruct (Map.get EV v (pre_num r)); reflexivity.
Qed.

(** The ordinary counted score operation returns the source score. *)
Lemma audit_semi_score_counted_erases V E (EV : encoding V) (r : dfs_result V E) semis v :
  fst (audit_semi_score_counted EV r semis v) = semi_rank EV r (semi_value EV semis v).
Proof.
  unfold audit_semi_score_counted, semi_value.
  destruct (Map.get EV v semis) as [value|].
  - destruct (audit_semi_rank_counted EV r value) as [rank events] eqn:Hrank.
    pose proof (audit_semi_rank_counted_erases V E EV r value) as Herase.
    rewrite Hrank in Herase; exact Herase.
  - destruct (audit_semi_rank_counted EV r v) as [rank events] eqn:Hrank.
    pose proof (audit_semi_rank_counted_erases V E EV r v) as Herase.
    rewrite Hrank in Herase; exact Herase.
Qed.

(** The ordinary counted label operation returns the source label. *)
Lemma audit_semi_label_counted_erases V (EV : encoding V) st v :
  fst (audit_semi_label_counted EV st v) = semi_label EV st v.
Proof.
  unfold audit_semi_label_counted, semi_label.
  destruct (Map.get EV v (SemiLinks.labels st)); reflexivity.
Qed.

(** A nested query prefix and an ordinary prefix read the same keys and comparison operands. *)
Lemma audit_semi_nested_prefix_to_plain V E B (EV : encoding V) enc (r : dfs_result V E)
    st v a get_events ra rv ea ev choice compare_events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
  audit_semi_nested_rank (B := B) enc r a = (ra, ea) ->
  audit_semi_nested_rank enc r v = (rv, ev) ->
  audit_positive_ltb ra rv = (choice, compare_events) ->
  exists plain_a plain_v,
    Map.get EV v (SemiLinks.shortcut st) = Some a /\
    audit_semi_rank_counted EV r a = (ra, plain_a) /\
    audit_semi_rank_counted EV r v = (rv, plain_v) /\ Pos.ltb ra rv = choice.
Proof.
  intros Hencode Hget Hrank_a Hrank_v Hcompare.
  pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.shortcut st) (Hencode v)) as Hsource.
  rewrite Hget in Hsource; cbn in Hsource; symmetry in Hsource.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r a (Hencode a)) as Hra.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r v (Hencode v)) as Hrv.
  rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
  pose proof (proj1 (audit_positive_order (semi_rank EV r a) (semi_rank EV r v))) as Hlt.
  rewrite Hcompare in Hlt; cbn in Hlt; symmetry in Hlt.
  pose proof (audit_semi_rank_counted_erases V E EV r a) as Hplain_a.
  pose proof (audit_semi_rank_counted_erases V E EV r v) as Hplain_v.
  destruct (audit_semi_rank_counted EV r a) as [rank_a events_a] eqn:Hplain_a_run.
  destruct (audit_semi_rank_counted EV r v) as [rank_v events_v] eqn:Hplain_v_run.
  cbn in Hplain_a, Hplain_v; subst rank_a rank_v.
  exists events_a, events_v; repeat split; assumption.
Qed.

(** Every nested query has an ordinary audit run with the same result. *)
Lemma audit_semi_nested_to_plain V E B (EV : encoding V) enc (r : dfs_result V E)
    semis st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  exists plain, audit_semi_compress_run EV r semis st v result plain.
Proof.
  intros Hencode Hrun; induction Hrun as
    [v get_events Hget
    |v a get_events ra rv ea ev compare_events Hget Hrank_a Hrank_v Hcompare
    |v a get_events ra rv ea ev compare_events st' root inner label label_events final
      set_events Hget Hrank_a Hrank_v Hcompare Hrun [plain IH] Hlabel Hset
    |v a get_events ra rv ea ev compare_events st' root u inner label label_events sl su el eu
      choose choose_events final set_events Hget Hrank_a Hrank_v Hcompare Hrun [plain IH] Hlabel
      Hscore_l Hscore_u Hchoose Hset].
  - pose proof (audit_map_get_erases V V B enc EV v (SemiLinks.shortcut st) (Hencode v)) as Herase.
    rewrite Hget in Herase; cbn in Herase.
    eexists; apply AuditSemiCompressRoot; symmetry; exact Herase.
  - destruct (audit_semi_nested_prefix_to_plain V E B EV enc r st v a get_events ra rv ea ev
      _ compare_events Hencode Hget Hrank_a Hrank_v Hcompare)
      as [events_a [events_v [Hsource [Hplain_a_run [Hplain_v_run Hlt]]]]].
    eexists; eapply AuditSemiCompressStopped with (a := a); eassumption.
  - destruct (audit_semi_nested_prefix_to_plain V E B EV enc r st v a get_events ra rv ea ev
      _ compare_events Hencode Hget Hrank_a Hrank_v Hcompare)
      as [events_a [events_v [Hsource [Hplain_a_run [Hplain_v_run Hlt]]]]].
    pose proof (audit_semi_nested_label_erases V B EV enc st v (Hencode v)) as Hnested_label.
    pose proof (audit_semi_label_counted_erases V EV st v) as Hplain_label.
    rewrite Hlabel in Hnested_label; cbn in Hnested_label.
    destruct (audit_semi_label_counted EV st v) as [plain_label label_trace] eqn:Hplain_label_run.
    cbn in Hplain_label; rewrite <- Hnested_label in Hplain_label; subst plain_label.
    pose proof (audit_semi_nested_set_erases V B EV enc st' v root label (Hencode v)) as Hfinal.
    rewrite Hset in Hfinal; cbn in Hfinal; subst final.
    eexists; eapply AuditSemiCompressRecurNone with (a := a);
      eassumption.
  - destruct (audit_semi_nested_prefix_to_plain V E B EV enc r st v a get_events ra rv ea ev
      _ compare_events Hencode Hget Hrank_a Hrank_v Hcompare)
      as [events_a [events_v [Hsource [Hplain_a_run [Hplain_v_run Hlt]]]]].
    pose proof (audit_semi_nested_label_erases V B EV enc st v (Hencode v)) as Hnested_label.
    pose proof (audit_semi_label_counted_erases V EV st v) as Hplain_label.
    rewrite Hlabel in Hnested_label; cbn in Hnested_label.
    destruct (audit_semi_label_counted EV st v) as [plain_label label_trace] eqn:Hplain_label_run.
    cbn in Hplain_label; rewrite <- Hnested_label in Hplain_label; subst plain_label.
    pose proof (audit_semi_nested_score_erases V E B EV enc r semis label Hencode) as Hnested_l.
    pose proof (audit_semi_nested_score_erases V E B EV enc r semis u Hencode) as Hnested_u.
    rewrite Hscore_l in Hnested_l; rewrite Hscore_u in Hnested_u; cbn in Hnested_l, Hnested_u.
    pose proof (audit_semi_score_counted_erases V E EV r semis label) as Hplain_l.
    pose proof (audit_semi_score_counted_erases V E EV r semis u) as Hplain_u.
    destruct (audit_semi_score_counted EV r semis label) as [plain_l trace_l] eqn:Hplain_l_run.
    destruct (audit_semi_score_counted EV r semis u) as [plain_u trace_u] eqn:Hplain_u_run.
    cbn in Hplain_l, Hplain_u; rewrite <- Hnested_l in Hplain_l; rewrite <- Hnested_u in Hplain_u.
    subst plain_l plain_u.
    pose proof (proj1 (proj2 (audit_positive_order sl su))) as Hle.
    rewrite Hchoose in Hle; cbn in Hle.
    pose proof (audit_semi_nested_set_erases V B EV enc st' v root (if choose then label else u)
      (Hencode v)) as Hfinal.
    rewrite Hset in Hfinal; cbn in Hfinal; subst final.
    eexists; eapply AuditSemiCompressRecurSome with (a := a) (u := u) (sl := sl) (su := su);
      eassumption.
Qed.

(** The ordinary audit relation admits the source compression result. *)
Lemma audit_semi_compress_erases V E (EV : encoding V) (r : dfs_result V E) semis st v :
  exists events, audit_semi_compress_run EV r semis st v
    (semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x)) st v)
    events.
Proof.
  set (enc := fun x : V => (encode EV x, @nil unit)).
  assert (Hencode : forall x, fst (enc x) = encode EV x) by reflexivity.
  destruct (audit_semi_nested_compress_erasure V E unit EV enc r semis st v Hencode)
    as [result [events [Hrun Hresult]]].
  destruct (audit_semi_nested_to_plain V E unit EV enc r semis st v result events Hencode Hrun)
    as [plain Hplain].
  subst result; exists plain; exact Hplain.
Qed.

(** A plain counted rank read emits one event. *)
Lemma audit_semi_rank_counted_length V E (EV : encoding V) (r : dfs_result V E) v :
  length (snd (audit_semi_rank_counted EV r v)) = 1.
Proof.
  unfold audit_semi_rank_counted; destruct (Map.get EV v (pre_num r)); reflexivity.
Qed.

(** A plain counted label read emits one event. *)
Lemma audit_semi_label_counted_length V (EV : encoding V) st v :
  length (snd (audit_semi_label_counted EV st v)) = 1.
Proof.
  unfold audit_semi_label_counted; destruct (Map.get EV v (SemiLinks.labels st)); reflexivity.
Qed.

(** A plain counted score read emits its value and rank lookup events. *)
Lemma audit_semi_score_counted_length V E (EV : encoding V) (r : dfs_result V E) semis v :
  length (snd (audit_semi_score_counted EV r semis v)) = 2.
Proof.
  unfold audit_semi_score_counted.
  destruct (Map.get EV v semis) as [value|].
  - pose proof (audit_semi_rank_counted_length V E EV r value) as Hlen.
    destruct (audit_semi_rank_counted EV r value); cbn in *; lia.
  - pose proof (audit_semi_rank_counted_length V E EV r v) as Hlen.
    destruct (audit_semi_rank_counted EV r v); cbn in *; lia.
Qed.

(** The ordinary compression receipt is bounded by the query's actual rank. *)
Lemma audit_semi_compress_count V E (EV : encoding V) (r : dfs_result V E)
    semis st v result events :
  audit_semi_compress_run EV r semis st v result events ->
  length events <= audit_semi_compress_event_bound EV r v.
Proof.
  intro Hrun; induction Hrun as
    [v Hget
    |v a ra rv ea ev Hget Hrank_a Hrank_v Hcompare
    |v a ra rv ea ev st' root inner label label_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel
    |v a ra rv ea ev st' root u inner label label_events sl su el eu choose Hget Hrank_a Hrank_v
      Hcompare Hrun IH Hlabel Hscore_l Hscore_u Hchoose].
  - unfold audit_semi_compress_event_bound; cbn; lia.
  - pose proof (audit_semi_rank_counted_length V E EV r a) as Ha.
    pose proof (audit_semi_rank_counted_length V E EV r v) as Hv.
    rewrite Hrank_a in Ha; rewrite Hrank_v in Hv; cbn in Ha, Hv.
    unfold audit_semi_compress_event_bound; repeat rewrite length_app; cbn; lia.
  - pose proof (audit_semi_rank_counted_length V E EV r a) as Ha.
    pose proof (audit_semi_rank_counted_length V E EV r v) as Hv.
    pose proof (audit_semi_label_counted_length V EV st v) as Hl.
    rewrite Hrank_a in Ha; rewrite Hrank_v in Hv; rewrite Hlabel in Hl; cbn in Ha, Hv, Hl.
    pose proof (audit_semi_rank_counted_erases V E EV r a) as Hra.
    pose proof (audit_semi_rank_counted_erases V E EV r v) as Hrv.
    rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
    apply Pos.ltb_lt, Pos2Nat.inj_lt in Hcompare.
    unfold audit_semi_compress_event_bound in *; repeat rewrite length_app; cbn; lia.
  - pose proof (audit_semi_rank_counted_length V E EV r a) as Ha.
    pose proof (audit_semi_rank_counted_length V E EV r v) as Hv.
    pose proof (audit_semi_label_counted_length V EV st v) as Hl.
    pose proof (audit_semi_score_counted_length V E EV r semis label) as Hsl.
    pose proof (audit_semi_score_counted_length V E EV r semis u) as Hsu.
    rewrite Hrank_a in Ha; rewrite Hrank_v in Hv; rewrite Hlabel in Hl.
    rewrite Hscore_l in Hsl; rewrite Hscore_u in Hsu; cbn in Ha, Hv, Hl, Hsl, Hsu.
    pose proof (audit_semi_rank_counted_erases V E EV r a) as Hra.
    pose proof (audit_semi_rank_counted_erases V E EV r v) as Hrv.
    rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
    apply Pos.ltb_lt, Pos2Nat.inj_lt in Hcompare.
    unfold audit_semi_compress_event_bound in *; repeat rewrite length_app; cbn; lia.
Qed.

(** The abstract and nested compression envelopes use the same input widths. *)
Lemma audit_semi_widths_agree V E (EV : encoding V) (r : dfs_result V E) semis st v :
  audit_semi_compress_width EV r semis st v = audit_semi_nested_width EV r semis st v.
Proof.
  reflexivity.
Qed.

(** A plain audit event is width-safe when its recorded operands fit the input envelope. *)
Definition audit_semi_call_safe V (EV : encoding V) width (event : audit_semi_call V) : Prop :=
  match event with
  | AuditSemiGet v _ _
  | AuditSemiRankGet v _ _
  | AuditSemiSet v _ _ => Pos.size_nat (encode EV v) <= width
  | AuditSemiLess a b _
  | AuditSemiLe a b _ => Pos.size_nat a <= width /\ Pos.size_nat b <= width
  | AuditSemiCase _ => True
  end.

(** A width-safe abstract event costs at most its fixed frame and key or comparison work. *)
Lemma audit_semi_call_work_safe V (EV : encoding V) width event :
  audit_semi_call_safe V EV width event -> audit_semi_call_work EV event <= 68 + 3 * width.
Proof.
  destruct event; cbn [audit_semi_call_safe]; intro Hsafe;
    unfold audit_semi_call_work, audit_encoding_weight, audit_get_weight, audit_set_weight,
      audit_key_bits_weight, audit_binary_weight.
  all: cbn [audit_semi_call_work] in *; try rewrite !audit_dfs_positive_z_bits; lia.
Qed.

(** Summing safe abstract events retains their exact source receipt length. *)
Lemma audit_semi_calls_work_safe V (EV : encoding V) width events :
  Forall (audit_semi_call_safe V EV width) events ->
  fold_right (fun event total => audit_semi_call_work EV event + total) 0 events <=
    length events * (68 + 3 * width).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - cbn [fold_right length].
    pose proof (audit_semi_call_work_safe V EV width event Hevent) as Hwork; lia.
Qed.

(** A plain rank read is safe at the original query width. *)
Lemma audit_semi_rank_counted_safe V E (EV : encoding V) (r : dfs_result V E) semis st start v :
  audit_semi_input_vertex V semis st start v ->
  Forall (audit_semi_call_safe V EV (audit_semi_compress_width EV r semis st start))
    (snd (audit_semi_rank_counted EV r v)).
Proof.
  intro Hv; pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hwidth.
  rewrite <- audit_semi_widths_agree in Hwidth.
  unfold audit_semi_rank_counted; destruct (Map.get EV v (pre_num r)); cbn.
  all:
    constructor; [exact Hwidth|constructor].
Qed.

(** A plain label read is safe at the original query width. *)
Lemma audit_semi_label_counted_safe V E (EV : encoding V) (r : dfs_result V E) semis st start v :
  audit_semi_input_vertex V semis st start v ->
  Forall (audit_semi_call_safe V EV (audit_semi_compress_width EV r semis st start))
    (snd (audit_semi_label_counted EV st v)).
Proof.
  intro Hv; pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hwidth.
  rewrite <- audit_semi_widths_agree in Hwidth.
  unfold audit_semi_label_counted; destruct (Map.get EV v (SemiLinks.labels st)); cbn.
  all:
    constructor; [exact Hwidth|constructor].
Qed.

(** A plain score read follows either the queried vertex or an original map value. *)
Lemma audit_semi_score_counted_safe V E (EV : encoding V) (r : dfs_result V E) semis st start v :
  audit_semi_input_vertex V semis st start v ->
  Forall (audit_semi_call_safe V EV (audit_semi_compress_width EV r semis st start))
    (snd (audit_semi_score_counted EV r semis v)).
Proof.
  intro Hv; pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hwidth.
  rewrite <- audit_semi_widths_agree in Hwidth.
  unfold audit_semi_score_counted.
  destruct (Map.get EV v semis) as [value|] eqn:Hget.
  - assert (Hvalue : audit_semi_input_vertex V semis st start value).
    { eapply audit_semi_input_vertex_get; right; right; exact Hget. }
    pose proof (audit_semi_rank_counted_safe V E EV r semis st start value Hvalue) as Hrank.
    destruct (audit_semi_rank_counted EV r value); cbn in *; constructor; assumption.
  - pose proof (audit_semi_rank_counted_safe V E EV r semis st start v Hv) as Hrank.
    destruct (audit_semi_rank_counted EV r v); cbn in *; constructor; assumption.
Qed.

(** A plain query returns a root and label from its original input envelope. *)
Lemma audit_semi_compress_result_in V E (EV : encoding V) (r : dfs_result V E)
    semis st start v result events :
  audit_semi_compress_run EV r semis st v result events ->
  audit_semi_input_vertex V semis st start v ->
  audit_semi_input_vertex V semis st start (fst (snd result)) /\
  match snd (snd result) with
  | Some label => audit_semi_input_vertex V semis st start label
  | None => True
  end.
Proof.
  intros Hrun Hv.
  set (enc := fun x : V => (encode EV x, @nil unit)).
  assert (Hencode : forall x, fst (enc x) = encode EV x) by reflexivity.
  destruct (audit_semi_nested_compress_erasure V E unit EV enc r semis st v Hencode)
    as [nested [nested_events [Hnested _]]].
  destruct (audit_semi_nested_to_plain V E unit EV enc r semis st v nested nested_events
    Hencode Hnested) as [plain Hplain].
  destruct (audit_semi_compress_unique V E EV r semis st v result events nested plain Hrun Hplain)
    as [Hresult _].
  subst nested; eapply audit_semi_nested_result_in; eassumption.
Qed.

(** A plain label is either the queried vertex or an original stored label. *)
Lemma audit_semi_label_counted_in V (EV : encoding V) semis st start v label events :
  audit_semi_input_vertex V semis st start v ->
  audit_semi_label_counted EV st v = (label, events) ->
  audit_semi_input_vertex V semis st start label.
Proof.
  intros Hv Hlabel.
  pose proof (audit_semi_label_counted_erases V EV st v) as Herase.
  rewrite Hlabel in Herase; cbn in Herase; unfold semi_label in Herase.
  destruct (Map.get EV v (SemiLinks.labels st)) as [found|] eqn:Hget.
  - subst label; eapply audit_semi_input_vertex_get; right; left; exact Hget.
  - now subst label.
Qed.

(** The plain read-and-compare prefix records only original-envelope operands. *)
Lemma audit_semi_compress_prefix_safe V E (EV : encoding V) (r : dfs_result V E)
    semis st start v a ra rv ea ev choice site :
  audit_semi_input_vertex V semis st start v ->
  Map.get EV v (SemiLinks.shortcut st) = Some a ->
  audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
  audit_semi_input_vertex V semis st start a /\
  Forall (audit_semi_call_safe V EV (audit_semi_compress_width EV r semis st start))
    ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
      [AuditSemiLess ra rv choice; AuditSemiCase site]).
Proof.
  intros Hv Hget Hrank_a Hrank_v.
  assert (Ha : audit_semi_input_vertex V semis st start a).
  { eapply audit_semi_input_vertex_get; left; exact Hget. }
  pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hvwidth.
  rewrite <- audit_semi_widths_agree in Hvwidth.
  pose proof (audit_semi_rank_counted_safe V E EV r semis st start a Ha) as Hsafe_a.
  pose proof (audit_semi_rank_counted_safe V E EV r semis st start v Hv) as Hsafe_v.
  rewrite Hrank_a in Hsafe_a; rewrite Hrank_v in Hsafe_v; cbn in Hsafe_a, Hsafe_v.
  pose proof (audit_semi_rank_counted_erases V E EV r a) as Hra.
  pose proof (audit_semi_rank_counted_erases V E EV r v) as Hrv.
  rewrite Hrank_a in Hra; rewrite Hrank_v in Hrv; cbn in Hra, Hrv; subst ra rv.
  pose proof (audit_semi_nested_rank_width V E EV r semis st start a) as Hawidth.
  pose proof (audit_semi_nested_rank_width V E EV r semis st start v) as Hrankwidth.
  rewrite <- audit_semi_widths_agree in Hawidth, Hrankwidth.
  split; [exact Ha|].
  repeat rewrite Forall_app; cbn; repeat split; try assumption.
  - constructor; [exact Hvwidth|constructor].
  - constructor; [split; assumption|constructor; [exact I|constructor]].
Qed.

(** Every plain compression event records operands within the original input width. *)
Lemma audit_semi_compress_safe V E (EV : encoding V) (r : dfs_result V E)
    semis st start v result events :
  audit_semi_compress_run EV r semis st v result events ->
  audit_semi_input_vertex V semis st start v ->
  Forall (audit_semi_call_safe V EV (audit_semi_compress_width EV r semis st start)) events.
Proof.
  intro Hrun; induction Hrun as
    [v Hget
    |v a ra rv ea ev Hget Hrank_a Hrank_v Hcompare
    |v a ra rv ea ev st' root inner label label_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel
    |v a ra rv ea ev st' root u inner label label_events sl su el eu choose Hget Hrank_a Hrank_v
      Hcompare Hrun IH Hlabel Hscore_l Hscore_u Hchoose]; intro Hv.
  - pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hwidth.
    rewrite <- audit_semi_widths_agree in Hwidth.
    constructor; [exact Hwidth|constructor; [exact I|constructor]].
  - destruct (audit_semi_compress_prefix_safe V E EV r semis st start v a ra rv ea ev false 1
      Hv Hget Hrank_a Hrank_v) as [_ Hprefix]; exact Hprefix.
  - destruct (audit_semi_compress_prefix_safe V E EV r semis st start v a ra rv ea ev true 2
      Hv Hget Hrank_a Hrank_v) as [Ha Hprefix].
    pose proof (IH Ha) as Hinner.
    pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hwidth.
    rewrite <- audit_semi_widths_agree in Hwidth.
    pose proof (audit_semi_label_counted_safe V E EV r semis st start v Hv) as Hsafe_label.
    rewrite Hlabel in Hsafe_label; cbn in Hsafe_label.
    repeat rewrite Forall_app in Hprefix.
    destruct Hprefix as [Hget_safe [Ha_safe [Hv_safe Hbranch_safe]]].
    repeat rewrite Forall_app; repeat split; try assumption.
    + constructor; [exact I|constructor].
    + constructor; [exact Hwidth|constructor; [exact Hwidth|constructor]].
  - destruct (audit_semi_compress_prefix_safe V E EV r semis st start v a ra rv ea ev true 2
      Hv Hget Hrank_a Hrank_v) as [Ha Hprefix].
    pose proof (IH Ha) as Hinner.
    pose proof (audit_semi_compress_result_in V E EV r semis st start a _ _ Hrun Ha) as [_ Hu].
    cbn in Hu.
    pose proof (audit_semi_label_counted_in V EV semis st start v label label_events Hv Hlabel)
      as Hl.
    pose proof (audit_semi_input_vertex_width V E EV r semis st start v Hv) as Hwidth.
    rewrite <- audit_semi_widths_agree in Hwidth.
    pose proof (audit_semi_label_counted_safe V E EV r semis st start v Hv) as Hsafe_label.
    pose proof (audit_semi_score_counted_safe V E EV r semis st start label Hl) as Hsafe_l.
    pose proof (audit_semi_score_counted_safe V E EV r semis st start u Hu) as Hsafe_u.
    rewrite Hlabel in Hsafe_label; rewrite Hscore_l in Hsafe_l; rewrite Hscore_u in Hsafe_u.
    cbn in Hsafe_label, Hsafe_l, Hsafe_u.
    pose proof (audit_semi_score_counted_erases V E EV r semis label) as Hsl.
    pose proof (audit_semi_score_counted_erases V E EV r semis u) as Hsu.
    rewrite Hscore_l in Hsl; rewrite Hscore_u in Hsu; cbn in Hsl, Hsu; subst sl su.
    pose proof (audit_semi_nested_rank_width V E EV r semis st start (semi_value EV semis label))
      as Hslwidth.
    pose proof (audit_semi_nested_rank_width V E EV r semis st start (semi_value EV semis u))
      as Hsuwidth.
    rewrite <- audit_semi_widths_agree in Hslwidth, Hsuwidth.
    repeat rewrite Forall_app in Hprefix.
    destruct Hprefix as [Hget_safe [Ha_safe [Hv_safe Hbranch_safe]]].
    repeat rewrite Forall_app; repeat split; try assumption.
    + constructor; [exact I|constructor].
    + constructor; [split; assumption|].
      constructor; [exact Hwidth|constructor; [exact Hwidth|constructor]].
Qed.

(** Plain compression returns the source result within its original input-derived budget. *)
Theorem audit_semi_compress_correct : audit_semi_compress_statement.
Proof.
  intros V E EV r semis st v.
  destruct (audit_semi_compress_erases V E EV r semis st v) as [events Hrun].
  exists (semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x)) st v),
    events.
  split; [exact Hrun|]; split; [reflexivity|].
  pose proof (audit_semi_compress_count V E EV r semis st v _ _ Hrun) as Hcount.
  split; [exact Hcount|].
  pose proof (audit_semi_compress_safe V E EV r semis st v v _ _ Hrun (or_introl eq_refl))
    as Hsafe.
  pose proof (audit_semi_calls_work_safe V EV (audit_semi_compress_width EV r semis st v)
    events Hsafe) as Hwork.
  unfold audit_semi_compress_work, audit_semi_compress_budget in *; nia.
Qed.

(** * Producer input envelopes *)

(** A map envelope keeps its stored keys and values in a chosen vertex set. *)
Definition audit_semi_map_envelope V (EV : encoding V) (vertices : V -> Prop) (m : Map.t V V) :
    Prop :=
  Map.wf EV m /\ forall key value, Map.get EV key m = Some value -> vertices key /\ vertices value.

(** The empty map satisfies every vertex envelope. *)
Lemma audit_semi_map_envelope_empty V (EV : encoding V) vertices :
  audit_semi_map_envelope V EV vertices Map.empty.
Proof.
  split; [apply Map.wf_empty|].
  intros key value Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Writing two enveloped vertices preserves the map envelope. *)
Lemma audit_semi_map_envelope_set V (EV : encoding V) vertices m key value :
  audit_semi_map_envelope V EV vertices m -> vertices key -> vertices value ->
  audit_semi_map_envelope V EV vertices (Map.set EV key value m).
Proof.
  intros [Hwf Henvelope] Hkey Hvalue; split; [apply Map.wf_set; exact Hwf|].
  intros other found Hget.
  destruct (dfs_eq_dec EV other key) as [Heq|Hne].
  - subst other; rewrite Map.get_set_same in Hget; inversion Hget; subst found; auto.
  - rewrite Map.get_set_other in Hget by exact Hne; apply Henvelope; exact Hget.
Qed.

(** Every stored row of an enveloped map contains two enveloped vertices. *)
Lemma audit_semi_map_envelope_elements V (EV : encoding V) vertices m key value :
  audit_semi_map_envelope V EV vertices m -> In (key, value) (Map.elements m) ->
  vertices key /\ vertices value.
Proof.
  intros [Hwf Henvelope] Hin; apply Henvelope.
  apply Map.elements_sound; assumption.
Qed.

(** Both mutable shortcut maps stay within a common producer vertex envelope. *)
Definition audit_semi_links_envelope V (EV : encoding V) vertices (st : SemiLinks.t V) : Prop :=
  audit_semi_map_envelope V EV vertices (SemiLinks.shortcut st) /\
  audit_semi_map_envelope V EV vertices (SemiLinks.labels st).

(** An empty forest satisfies every vertex envelope. *)
Lemma audit_semi_links_envelope_empty V (EV : encoding V) vertices :
  audit_semi_links_envelope V EV vertices semi_links_empty.
Proof.
  split; apply audit_semi_map_envelope_empty.
Qed.

(** A source link keeps its shortcut and label inside the vertex envelope. *)
Lemma audit_semi_links_envelope_link V (EV : encoding V) vertices st v parent :
  audit_semi_links_envelope V EV vertices st -> vertices v -> vertices parent ->
  audit_semi_links_envelope V EV vertices (semi_link EV st v parent).
Proof.
  intros [Hshortcut Hlabels] Hv Hparent; split; cbn [semi_link SemiLinks.shortcut SemiLinks.labels];
    apply audit_semi_map_envelope_set; assumption.
Qed.

(** Updating a shortcut with enveloped vertices preserves both map envelopes. *)
Lemma audit_semi_links_envelope_shortcut V (EV : encoding V) vertices st v root label :
  audit_semi_links_envelope V EV vertices st -> vertices v -> vertices root -> vertices label ->
  audit_semi_links_envelope V EV vertices (semi_shortcut_set EV st v root label).
Proof.
  intros [Hshortcut Hlabels] Hv Hroot Hlabel; split;
    cbn [semi_shortcut_set SemiLinks.shortcut SemiLinks.labels];
    apply audit_semi_map_envelope_set; assumption.
Qed.

(** The query's local input envelope is contained in any producer vertex envelope. *)
Lemma audit_semi_input_vertex_subset V (EV : encoding V) vertices semis st start v :
  audit_semi_map_envelope V EV vertices semis ->
  audit_semi_links_envelope V EV vertices st -> vertices start ->
  audit_semi_input_vertex V semis st start v -> vertices v.
Proof.
  intros Hsemis [Hshortcut Hlabels] Hstart [Heq|[key Hin]]; [now subst v|].
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - exact (proj2 (audit_semi_map_envelope_elements V EV vertices _ key v Hshortcut Hin)).
  - apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + exact (proj2 (audit_semi_map_envelope_elements V EV vertices _ key v Hlabels Hin)).
    + exact (proj2 (audit_semi_map_envelope_elements V EV vertices _ key v Hsemis Hin)).
Qed.

(** An ordinary compression run keeps its final shortcut and label maps in the producer envelope. *)
Lemma audit_semi_compress_envelope V E (EV : encoding V) (r : dfs_result V E)
    vertices semis st v result events :
  audit_semi_map_envelope V EV vertices semis ->
  audit_semi_links_envelope V EV vertices st -> vertices v ->
  audit_semi_compress_run EV r semis st v result events ->
  audit_semi_links_envelope V EV vertices (fst result).
Proof.
  intros Hsemis Hlinks Hv Hrun.
  induction Hrun as
    [v Hget
    |v a ra rv ea ev Hget Hrank_a Hrank_v Hcompare
    |v a ra rv ea ev st' root inner label label_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel
    |v a ra rv ea ev st' root u inner label label_events sl su el eu choose Hget Hrank_a Hrank_v
      Hcompare Hrun IH Hlabel Hscore_l Hscore_u Hchoose]; cbn.
  - exact Hlinks.
  - exact Hlinks.
  - assert (Ha : vertices a).
    { exact (proj2 ((proj2 (proj1 Hlinks)) v a Hget)). }
    specialize (IH Ha).
    assert (Ha_input : audit_semi_input_vertex V semis st v a).
    { eapply audit_semi_input_vertex_get; left; exact Hget. }
    pose proof (audit_semi_compress_result_in V E EV r semis st v a _ _ Hrun Ha_input)
      as [Hroot_in _].
    cbn in Hroot_in.
    assert (Hroot : vertices root).
    { exact (audit_semi_input_vertex_subset V EV vertices semis st v root
        Hsemis Hlinks Hv Hroot_in). }
    assert (Hlabel_in : audit_semi_input_vertex V semis st v label).
    { eapply audit_semi_label_counted_in; [left; reflexivity|exact Hlabel]. }
    assert (Hlabel_vertex : vertices label).
    { exact (audit_semi_input_vertex_subset V EV vertices semis st v label
        Hsemis Hlinks Hv Hlabel_in). }
    apply audit_semi_links_envelope_shortcut; assumption.
  - assert (Ha : vertices a).
    { exact (proj2 ((proj2 (proj1 Hlinks)) v a Hget)). }
    specialize (IH Ha).
    assert (Ha_input : audit_semi_input_vertex V semis st v a).
    { eapply audit_semi_input_vertex_get; left; exact Hget. }
    pose proof (audit_semi_compress_result_in V E EV r semis st v a _ _ Hrun Ha_input)
      as [Hroot_in Hu_in].
    cbn in Hroot_in, Hu_in.
    assert (Hroot : vertices root).
    { exact (audit_semi_input_vertex_subset V EV vertices semis st v root
        Hsemis Hlinks Hv Hroot_in). }
    assert (Hu : vertices u).
    { exact (audit_semi_input_vertex_subset V EV vertices semis st v u
        Hsemis Hlinks Hv Hu_in). }
    assert (Hlabel_in : audit_semi_input_vertex V semis st v label).
    { eapply audit_semi_label_counted_in; [left; reflexivity|exact Hlabel]. }
    assert (Hlabel_vertex : vertices label).
    { exact (audit_semi_input_vertex_subset V EV vertices semis st v label
        Hsemis Hlinks Hv Hlabel_in). }
    apply audit_semi_links_envelope_shortcut; try assumption.
    destruct choose; assumption.
Qed.

(** A nested compression run keeps the same producer map envelope. *)
Lemma audit_semi_nested_compress_envelope V E B (EV : encoding V) enc (r : dfs_result V E)
    vertices semis st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_map_envelope V EV vertices semis ->
  audit_semi_links_envelope V EV vertices st -> vertices v ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  audit_semi_links_envelope V EV vertices (fst result).
Proof.
  intros Hencode Hsemis Hlinks Hv Hrun.
  destruct (audit_semi_nested_to_plain V E B EV enc r semis st v result events Hencode Hrun)
    as [plain Hplain].
  eapply audit_semi_compress_envelope; eassumption.
Qed.

(** The producer envelope contains visited vertices, input-map keys, and every indexed source. *)
Definition audit_semi_producer_vertex V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) (v : V) : Prop :=
  In v (preorder r ++ map fst (Map.elements (pre_num r)) ++ map fst (Map.elements (tree_edge r)) ++
    map fst (Map.elements (in_index p)) ++
    map (Graph.source g) (flat_map snd (Map.elements (in_index p)) ++
      map snd (Map.elements (tree_edge r)))).

(** Each producer-envelope vertex fits the original producer key width. *)
Lemma audit_semi_producer_vertex_width V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) v :
  audit_semi_producer_vertex V E EV g p r v ->
  Pos.size_nat (encode EV v) <= audit_semi_producer_input_width EV g p r.
Proof.
  intro Hin; unfold audit_semi_producer_vertex in Hin; unfold audit_semi_producer_input_width.
  eapply Nat.le_trans;
    [apply (audit_dfs_width_member (fun x : V => Pos.size_nat (encode EV x))); exact Hin|
    apply Nat.le_max_l].
Qed.

(** A tree-edge lookup returns a source in the producer envelope, even for malformed input maps. *)
Lemma audit_semi_producer_tree_source V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) v edge :
  Map.get EV v (tree_edge r) = Some edge ->
  audit_semi_producer_vertex V E EV g p r (Graph.source g edge).
Proof.
  intro Hget.
  destruct (audit_semi_map_get_value_in V E EV (tree_edge r) v edge Hget) as [key Hin].
  unfold audit_semi_producer_vertex; do 4 (apply in_or_app; right).
  apply in_map_iff; exists edge; split; [reflexivity|].
  apply in_or_app; right; apply in_map_iff; exists (key, edge); split; [reflexivity|exact Hin].
Qed.

(** Every edge returned by an indexed predecessor lookup has its source in the producer envelope. *)
Lemma audit_semi_producer_pred_source V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) v edge :
  In edge (pred_edges p v) -> audit_semi_producer_vertex V E EV g p r (Graph.source g edge).
Proof.
  unfold pred_edges, index_edges.
  destruct (Map.get EV v (in_index p)) as [edges|] eqn:Hget; cbn; [|contradiction].
  intro Hedge.
  destruct (audit_semi_map_get_value_in V (list E) EV (in_index p) v edges Hget) as [key Hin].
  unfold audit_semi_producer_vertex; do 4 (apply in_or_app; right).
  apply in_map_iff; exists edge; split; [reflexivity|].
  apply in_or_app; left; apply in_flat_map.
  exists (key, edges); split; [exact Hin|exact Hedge].
Qed.

(** A pointwise width bound bounds the maximum of a mapped list. *)
Lemma audit_semi_max_le A (width_of : A -> nat) values limit :
  (forall value, In value values -> width_of value <= limit) ->
  fold_right Nat.max 0 (map width_of values) <= limit.
Proof.
  induction values as [|value rest IH]; intro Hall; cbn.
  - lia.
  - apply Nat.max_lub; [apply Hall; left; reflexivity|].
    apply IH; intros other Hin; apply Hall; right; exact Hin.
Qed.

(** The intermediate compression input fits the original producer width. *)
Lemma audit_semi_compress_width_in_producer V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) semis st v :
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r v ->
  audit_semi_nested_width EV r semis st v <= audit_semi_producer_input_width EV g p r.
Proof.
  intros Hsemis [Hshortcut Hlabels] Hv.
  set (rows := Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
    Map.elements semis).
  assert (Hrows : forall key value, In (key, value) rows ->
    audit_semi_producer_vertex V E EV g p r key /\ audit_semi_producer_vertex V E EV g p r value).
  { intros key value Hin; unfold rows in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    - exact (audit_semi_map_envelope_elements V EV _ _ key value Hshortcut Hin).
    - apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      + exact (audit_semi_map_envelope_elements V EV _ _ key value Hlabels Hin).
      + exact (audit_semi_map_envelope_elements V EV _ _ key value Hsemis Hin). }
  unfold audit_semi_nested_width; fold rows; apply Nat.max_lub.
  - apply audit_semi_max_le; intros x Hin; cbn in Hin; destruct Hin as [Heq|Hin].
    + subst x; apply audit_semi_producer_vertex_width; exact Hv.
    + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin; destruct Hin as [[key value] [Heq Hin]]; cbn in Heq; subst x.
        apply audit_semi_producer_vertex_width; exact (proj1 (Hrows key value Hin)).
      * apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        -- apply in_map_iff in Hin; destruct Hin as [[key value] [Heq Hin]]; cbn in Heq; subst x.
           apply audit_semi_producer_vertex_width; exact (proj2 (Hrows key value Hin)).
        -- apply audit_semi_producer_vertex_width; unfold audit_semi_producer_vertex.
           apply in_or_app; right; apply in_or_app; left; exact Hin.
  - unfold audit_semi_producer_input_width; apply Nat.le_max_r.
Qed.

(** Any queried rank fits the maximum number in the original DFS map. *)
Lemma audit_semi_rank_in_producer V E (EV : encoding V) (r : dfs_result V E) v :
  Pos.to_nat (semi_rank EV r v) <= audit_semi_producer_input_rank r.
Proof.
  unfold semi_rank, audit_semi_producer_input_rank.
  destruct (Map.get EV v (pre_num r)) as [rank|] eqn:Hget.
  - destruct (audit_semi_map_get_value_in V positive EV (pre_num r) v rank Hget) as [key Hin].
    induction (Map.elements (pre_num r)) as [|[k n] rest IH]; cbn in Hin |- *; [contradiction|].
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst n; apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  - induction (Map.elements (pre_num r)) as [|[k n] rest IH]; cbn; [lia|].
    eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
Qed.

(** Widening the input allowance preserves every nested event's work bound. *)
Lemma audit_semi_nested_safe_mono V B (weight : B -> nat) small large events :
  small <= large -> Forall (audit_semi_nested_event_safe V B weight small) events ->
  Forall (audit_semi_nested_event_safe V B weight large) events.
Proof.
  intros Hwidth Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; constructor; [|exact IH].
  unfold audit_semi_nested_event_safe in *; lia.
Qed.

(** A nested producer query fits the producer's original rank and width envelopes. *)
Lemma audit_semi_nested_query_in_producer V E B (EV : encoding V) (g : Graph.t V E)
    enc weight (p : prepared EV g) (r : dfs_result V E) semis st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r v ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  length events <= 20 * S (audit_semi_producer_input_rank r) /\
  Forall (audit_semi_nested_event_safe V B weight (audit_semi_producer_input_width EV g p r))
    events /\
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst result).
Proof.
  intros Hencode Hsemis Hlinks Hv Hrun.
  pose proof (audit_semi_nested_compress_count V E B EV enc r semis st v result events Hencode Hrun)
    as Hcount.
  pose proof (audit_semi_rank_in_producer V E EV r v) as Hrank.
  split; [lia|].
  split.
  - eapply audit_semi_nested_safe_mono.
    + eapply audit_semi_compress_width_in_producer; eassumption.
    + eapply audit_semi_nested_compress_safe; [exact Hencode|exact Hrun|left; reflexivity].
  - eapply audit_semi_nested_compress_envelope; eassumption.
Qed.

(** Widening an abstract event envelope preserves its operand bounds. *)
Lemma audit_semi_call_safe_mono V (EV : encoding V) small large events :
  small <= large -> Forall (audit_semi_call_safe V EV small) events ->
  Forall (audit_semi_call_safe V EV large) events.
Proof.
  intros Hwidth Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; constructor; [|exact IH].
  destruct event; cbn [audit_semi_call_safe] in *; lia.
Qed.

(** A plain query fits the same producer rank and original input width. *)
Lemma audit_semi_query_in_producer V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) semis st v result events :
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r v ->
  audit_semi_compress_run EV r semis st v result events ->
  length events <= 20 * S (audit_semi_producer_input_rank r) /\
  Forall (audit_semi_call_safe V EV (audit_semi_producer_input_width EV g p r)) events /\
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst result).
Proof.
  intros Hsemis Hlinks Hv Hrun.
  pose proof (audit_semi_compress_count V E EV r semis st v result events Hrun) as Hcount.
  pose proof (audit_semi_rank_in_producer V E EV r v) as Hrank.
  unfold audit_semi_compress_event_bound in Hcount; split; [lia|].
  split.
  - eapply (audit_semi_call_safe_mono V EV (audit_semi_compress_width EV r semis st v)).
    + rewrite audit_semi_widths_agree; eapply audit_semi_compress_width_in_producer; eassumption.
    + eapply audit_semi_compress_safe; [exact Hrun|left; reflexivity].
  - eapply audit_semi_compress_envelope; eassumption.
Qed.

(** * Ordinary producer accounting *)

(** Outer events retain bounded map keys and the original inner compression operands. *)
Definition audit_semi_outer_safe V E (EV : encoding V) width (event : audit_semi_outer_call V E) :
    Prop :=
  match event with
  | AuditSemiOuterInner inner => audit_semi_call_safe V EV width inner
  | AuditSemiOuterTreeGet v _ _
  | AuditSemiOuterPredGet v _ _
  | AuditSemiOuterResultSet v _ _
  | AuditSemiOuterLink v _ _ => Pos.size_nat (encode EV v) <= width
  | AuditSemiOuterCase _
  | AuditSemiOuterSource _ _
  | AuditSemiOuterOutput _ => True
  end.

(** Only the output event charges the size of the returned list. *)
Definition audit_semi_outer_extra V E (event : audit_semi_outer_call V E) : nat :=
  match event with
  | AuditSemiOuterOutput size => size
  | _ => 0
  end.

(** Each safe outer event pays its abstract operation work and any output-size charge. *)
Lemma audit_semi_outer_work_safe V E (EV : encoding V) width event :
  audit_semi_outer_safe V E EV width event ->
  audit_semi_outer_event_work EV event <= 140 + 16 * width + audit_semi_outer_extra V E event.
Proof.
  destruct event; cbn [audit_semi_outer_safe]; intro Hsafe;
    unfold audit_semi_outer_event_work, audit_semi_outer_extra, audit_encoding_weight,
      audit_get_weight, audit_set_weight, audit_key_bits_weight; cbn.
  all: try lia.
  change (64 + audit_semi_call_work EV event <= 140 + 16 * width + 0).
  pose proof (audit_semi_call_work_safe V EV width event Hsafe) as Hwork; lia.
Qed.

(** Summing safe outer events retains the actual output-size charge. *)
Lemma audit_semi_outer_work_sum V E (EV : encoding V) width events :
  Forall (audit_semi_outer_safe V E EV width) events ->
  fold_right (fun event total => audit_semi_outer_event_work EV event + total) 0 events <=
    length events * (140 + 16 * width) +
      fold_right (fun event total => audit_semi_outer_extra V E event + total) 0 events.
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - cbn [fold_right length].
    pose proof (audit_semi_outer_work_safe V E EV width event Hevent) as Hwork; lia.
Qed.

(** Internal producer events carry no output-size charge. *)
Definition audit_semi_outer_quiet V E (EV : encoding V) width (event : audit_semi_outer_call V E) :
    Prop :=
  audit_semi_outer_safe V E EV width event /\ audit_semi_outer_extra V E event = 0.

(** An inner compression receipt embeds into a quiet outer receipt. *)
Lemma audit_semi_outer_inner_quiet V E (EV : encoding V) width events :
  Forall (audit_semi_call_safe V EV width) events ->
  Forall (audit_semi_outer_quiet V E EV width) (map AuditSemiOuterInner events).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; cbn; constructor; [|exact IH].
  split; [exact Hevent|reflexivity].
Qed.

(** A value lookup preserves any envelope containing its key and stored map values. *)
Lemma audit_semi_value_in V (EV : encoding V) vertices semis v :
  audit_semi_map_envelope V EV vertices semis -> vertices v -> vertices (semi_value EV semis v).
Proof.
  intros [_ Henvelope] Hv; unfold semi_value.
  destruct (Map.get EV v semis) as [value|] eqn:Hget; [|exact Hv].
  exact (proj2 (Henvelope v value Hget)).
Qed.

(** A counted value read emits one event and returns the source value. *)
Lemma audit_semi_value_counted_details V (EV : encoding V) semis v :
  fst (audit_semi_value_counted EV semis v) = semi_value EV semis v /\
  snd (audit_semi_value_counted EV semis v) = [AuditSemiGet v semis (Map.get EV v semis)].
Proof.
  unfold audit_semi_value_counted, semi_value; destruct (Map.get EV v semis); split; reflexivity.
Qed.

(** The input-size charge vanishes when every event is internal. *)
Lemma audit_semi_outer_quiet_extra V E (EV : encoding V) width events :
  Forall (audit_semi_outer_quiet V E EV width) events ->
  fold_right (fun event total => audit_semi_outer_extra V E event + total) 0 events = 0.
Proof.
  intro Hquiet; induction Hquiet as [|event rest [_ Hextra] Hrest IH]; cbn [fold_right].
  - reflexivity.
  - now rewrite Hextra, IH.
Qed.

(** A counted rank receipt records the actual lookup result and nothing else. *)
Lemma audit_semi_rank_counted_details V E (EV : encoding V) (r : dfs_result V E) v :
  snd (audit_semi_rank_counted EV r v) =
    [AuditSemiRankGet v (pre_num r) (Map.get EV v (pre_num r))].
Proof.
  unfold audit_semi_rank_counted; destruct (Map.get EV v (pre_num r)); reflexivity.
Qed.

(** A plain predecessor run retains its forest envelope, selected vertex, and actual receipt. *)
Lemma audit_semi_predecessor_in_producer V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) semis st best edge result events :
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r best ->
  audit_semi_producer_vertex V E EV g p r (Graph.source g edge) ->
  audit_semi_predecessor_run EV g r semis (st, best) edge result events ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst result) /\
  audit_semi_producer_vertex V E EV g p r (snd result) /\
  length events <= 20 * S (audit_semi_producer_input_rank r) + 10 /\
  Forall (audit_semi_outer_quiet V E EV (audit_semi_producer_input_width EV g p r)) events.
Proof.
  intros Hsemis Hlinks Hbest Hsource Hrun.
  inversion Hrun as [st0 best0 edge0 v Hvertex Hrank
    |st0 best0 edge0 v number st' root part inner u value value_events best_rank selected_rank
      eb es choose Hvertex Hrank Hquery Hu Hvalue Hbest_rank Hselected_rank Hchoose]; subst.
  - cbn; split; [exact Hlinks|]; split; [exact Hbest|]; split; [lia|].
    pose proof (audit_semi_producer_vertex_width V E EV g p r (Graph.source g edge) Hsource)
      as Hwidth.
    repeat constructor; cbn [audit_semi_outer_quiet audit_semi_outer_safe audit_semi_outer_extra
      audit_semi_call_safe]; auto.
  - pose proof (audit_semi_query_in_producer V E EV g p r semis st (Graph.source g edge)
      (st', (root, part)) inner Hsemis Hlinks Hsource Hquery) as [Hcount [Hsafe Hlinks']].
    cbn in Hlinks'.
    pose proof (audit_semi_compress_result_in V E EV r semis st (Graph.source g edge)
      (Graph.source g edge) _ _ Hquery (or_introl eq_refl)) as [_ Hpart].
    cbn in Hpart.
    set (u :=
      match part with
      | Some chosen => chosen
      | None => Graph.source g edge
      end) in *.
    assert (Hu_vertex : audit_semi_producer_vertex V E EV g p r u).
    { subst u; destruct part as [chosen|]; [|exact Hsource].
      exact (audit_semi_input_vertex_subset V EV _ semis st (Graph.source g edge) chosen
        Hsemis Hlinks Hsource Hpart). }
    pose proof (audit_semi_value_counted_details V EV semis u) as [Hvalue_result Hvalue_events].
    rewrite Hvalue in Hvalue_result, Hvalue_events; cbn in Hvalue_result, Hvalue_events.
    subst value value_events.
    assert (Hvalue_vertex : audit_semi_producer_vertex V E EV g p r (semi_value EV semis u)).
    { apply audit_semi_value_in; assumption. }
    pose proof (audit_semi_rank_counted_erases V E EV r best) as Hbest_result.
    pose proof (audit_semi_rank_counted_details V E EV r best) as Hbest_events.
    rewrite Hbest_rank in Hbest_result, Hbest_events; cbn in Hbest_result, Hbest_events.
    subst best_rank eb.
    pose proof (audit_semi_rank_counted_erases V E EV r (semi_value EV semis u))
      as Hselected_result.
    pose proof (audit_semi_rank_counted_details V E EV r (semi_value EV semis u))
      as Hselected_events.
    rewrite Hselected_rank in Hselected_result, Hselected_events; cbn in Hselected_result,
      Hselected_events.
    subst selected_rank es.
    pose proof (audit_semi_producer_vertex_width V E EV g p r (Graph.source g edge) Hsource)
      as Hsource_width.
    pose proof (audit_semi_producer_vertex_width V E EV g p r best Hbest) as Hbest_width.
    pose proof (audit_semi_producer_vertex_width V E EV g p r u Hu_vertex) as Hu_width.
    pose proof (audit_semi_producer_vertex_width V E EV g p r (semi_value EV semis u) Hvalue_vertex)
      as Hvalue_width.
    pose proof (audit_semi_nested_rank_width V E EV r semis st (Graph.source g edge) best)
      as Hbest_rank_width.
    pose proof (audit_semi_nested_rank_width V E EV r semis st (Graph.source g edge)
      (semi_value EV semis u)) as Hvalue_rank_width.
    pose proof (audit_semi_compress_width_in_producer V E EV g p r semis st
      (Graph.source g edge) Hsemis Hlinks Hsource) as Hwidth.
    pose proof (audit_semi_outer_inner_quiet V E EV (audit_semi_producer_input_width EV g p r)
      inner Hsafe) as Hinner.
    repeat rewrite length_app; repeat rewrite length_map; cbn [length].
    split; [exact Hlinks'|]; split.
    + destruct (Pos.leb (semi_rank EV r best) (semi_rank EV r (semi_value EV semis u)));
        assumption.
    + split; [lia|].
      repeat rewrite Forall_app; cbn [map]; repeat split; try assumption;
        repeat constructor; cbn [audit_semi_outer_quiet audit_semi_outer_safe audit_semi_outer_extra
          audit_semi_call_safe]; auto; lia.
Qed.

(** Folding predecessor runs keeps their source operands and summed event count. *)
Lemma audit_semi_predecessors_in_producer V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) semis edges initial result events :
  audit_semi_predecessors_run EV g r semis edges initial result events ->
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst initial) ->
  audit_semi_producer_vertex V E EV g p r (snd initial) ->
  (forall edge, In edge edges -> audit_semi_producer_vertex V E EV g p r (Graph.source g edge)) ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst result) /\
  audit_semi_producer_vertex V E EV g p r (snd result) /\
  length events <= length edges * (20 * S (audit_semi_producer_input_rank r) + 11) + 1 /\
  Forall (audit_semi_outer_quiet V E EV (audit_semi_producer_input_width EV g p r)) events.
Proof.
  intro Hrun; induction Hrun as [acc|edge rest initial middle result here later Hstep Hrest IH];
    intros Hsemis Hlinks Hbest Hsources.
  - split; [exact Hlinks|]; split; [exact Hbest|]; split; [cbn; lia|].
    repeat constructor; cbn [audit_semi_outer_quiet audit_semi_outer_safe audit_semi_outer_extra];
      auto.
  - destruct initial as [st best]; destruct middle as [st' best'].
    pose proof (audit_semi_predecessor_in_producer V E EV g p r semis st best edge _ _ Hsemis
      Hlinks Hbest (Hsources edge (or_introl eq_refl)) Hstep) as [Hlinks' [Hbest' [Hcount Hsafe]]].
    cbn in Hlinks', Hbest'.
    destruct (IH Hsemis Hlinks' Hbest' (fun e Hin => Hsources e (or_intror Hin)))
      as [Hresult [Hvertex [Hlater Hquiet]]].
    split; [exact Hresult|]; split; [exact Hvertex|]; split.
    + cbn [length]; rewrite length_app; nia.
    + constructor.
      * split; reflexivity.
      * apply Forall_app; split; assumption.
Qed.

(** A producer state keeps both settled values and linked shortcuts within its input envelope. *)
Definition audit_semi_state_envelope V (EV : encoding V) vertices (st : SemiState.t V) : Prop :=
  audit_semi_map_envelope V EV vertices (SemiState.result st) /\
  audit_semi_links_envelope V EV vertices (SemiState.links st).

(** Settling one vertex retains the input envelope and charges its actual predecessor list. *)
Lemma audit_semi_settle_in_producer V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) st v result events :
  audit_semi_settle_run p r st v result events ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r v ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) result /\
  length events <= length (pred_edges p v) * (20 * S (audit_semi_producer_input_rank r) + 11) + 7 /\
  Forall (audit_semi_outer_quiet V E EV (audit_semi_producer_input_width EV g p r)) events.
Proof.
  intros Hrun [Hsemis Hlinks] Hv.
  inversion Hrun as [st0 v0 Htree
    |st0 v0 edge parent incoming edges links' best steps Htree Hparent Hincoming Hedges Hpreds];
    subst.
  - split; [split; assumption|]; split; [cbn; lia|].
    pose proof (audit_semi_producer_vertex_width V E EV g p r v Hv) as Hwidth.
    repeat constructor; cbn [audit_semi_outer_quiet audit_semi_outer_safe audit_semi_outer_extra];
      auto.
  - assert (Hparent_vertex : audit_semi_producer_vertex V E EV g p r (Graph.source g edge)).
    { eapply audit_semi_producer_tree_source; exact Htree. }
    assert (Hpred_edges :
      (match Map.get EV v (in_index p) with
      | Some xs => xs
      | None => []
      end) = pred_edges p v) by reflexivity.
    rewrite Hpred_edges in Hpreds.
    assert (Hsources : forall e, In e (pred_edges p v) ->
      audit_semi_producer_vertex V E EV g p r (Graph.source g e)).
    { intros e Hin; eapply audit_semi_producer_pred_source; exact Hin. }
    destruct (audit_semi_predecessors_in_producer V E EV g p r (SemiState.result st)
      (pred_edges p v) (SemiState.links st, Graph.source g edge) (links', best) steps Hpreds
      Hsemis Hlinks Hparent_vertex Hsources) as [Hlinks' [Hbest [Hcount Hquiet]]].
    cbn in Hlinks', Hbest.
    pose proof (audit_semi_producer_vertex_width V E EV g p r v Hv) as Hwidth.
    split.
    + split; cbn [SemiState.result SemiState.links].
      * apply audit_semi_map_envelope_set; assumption.
      * apply audit_semi_links_envelope_link; assumption.
    + split.
      * repeat rewrite length_app; cbn [length]; lia.
      * repeat rewrite Forall_app; cbn [map]; repeat split; try assumption;
          repeat constructor; cbn [audit_semi_outer_quiet audit_semi_outer_safe
            audit_semi_outer_extra]; auto.
Qed.

(** Reversal preserves the sum of indexed predecessor-list lengths. *)
Lemma audit_semi_pred_sum_reverse V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) vertices :
  fold_right (fun v total => length (pred_edges p v) + total) 0 (rev vertices) =
  fold_right (fun v total => length (pred_edges p v) + total) 0 vertices.
Proof.
  assert (Hoffset : forall xs base,
    fold_right (fun v total => length (pred_edges p v) + total) base xs =
      fold_right (fun v total => length (pred_edges p v) + total) 0 xs + base).
  { induction xs as [|x xs IH]; intro base; cbn [fold_right]; [lia|].
    rewrite IH; lia. }
  induction vertices as [|v rest IH]; cbn [rev fold_right]; [reflexivity|].
  rewrite fold_right_app; cbn [fold_right]; rewrite Hoffset, IH; lia.
Qed.

(** The reverse settlement run sums the actual predecessor lengths for its visited vertices. *)
Lemma audit_semi_settles_in_producer V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) vertices st result events :
  audit_semi_settles_run p r vertices st result events ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  (forall v, In v vertices -> audit_semi_producer_vertex V E EV g p r v) ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) result /\
  length events <=
    fold_right (fun v total => length (pred_edges p v) + total) 0 vertices *
      (20 * S (audit_semi_producer_input_rank r) + 11) + 8 * length vertices + 1 /\
  Forall (audit_semi_outer_quiet V E EV (audit_semi_producer_input_width EV g p r)) events.
Proof.
  intro Hrun; induction Hrun as [st|v rest initial middle result here later Hstep Hrest IH];
    intros Hstate Hvertices.
  - split; [exact Hstate|]; split; [cbn; lia|].
    repeat constructor; cbn [audit_semi_outer_quiet audit_semi_outer_safe audit_semi_outer_extra];
      auto.
  - destruct (audit_semi_settle_in_producer V E EV g p r initial v middle here Hstep Hstate
      (Hvertices v (or_introl eq_refl))) as [Hmiddle [Hhere Hquiet_here]].
    destruct (IH Hmiddle (fun x Hin => Hvertices x (or_intror Hin)))
      as [Hresult [Hlater Hquiet_later]].
    split; [exact Hresult|]; split.
    + cbn [length fold_right]; rewrite length_app; nia.
    + constructor; [split; reflexivity|].
      apply Forall_app; split; assumption.
Qed.

(** A plain predecessor audit exists for the source predecessor step. *)
Lemma audit_semi_predecessor_erases V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis st best edge :
  exists events, audit_semi_predecessor_run EV g r semis (st, best) edge
    (semi_predecessor EV g r semis (st, best) edge) events.
Proof.
  unfold semi_predecessor; cbn.
  destruct (Map.get EV (Graph.source g edge) (pre_num r)) as [number|] eqn:Hrank.
  - destruct (audit_semi_compress_erases V E EV r semis st (Graph.source g edge)) as [inner Hquery].
    unfold semi_eval.
    destruct (semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x))
      st (Graph.source g edge)) as [st' [root part]] eqn:Hresult.
    set (u :=
      match part with
      | Some chosen => chosen
      | None => Graph.source g edge
      end).
    destruct (audit_semi_value_counted EV semis u) as [value value_events] eqn:Hvalue.
    pose proof (audit_semi_value_counted_details V EV semis u) as [Herase _].
    rewrite Hvalue in Herase; cbn in Herase; rewrite <- Herase.
    destruct (audit_semi_rank_counted EV r best) as [best_rank eb] eqn:Hbest.
    destruct (audit_semi_rank_counted EV r value) as [selected_rank es] eqn:Hselected.
    pose proof (audit_semi_rank_counted_erases V E EV r best) as Hbest_result.
    pose proof (audit_semi_rank_counted_erases V E EV r value) as Hselected_result.
    rewrite Hbest in Hbest_result; rewrite Hselected in Hselected_result; cbn in Hbest_result,
      Hselected_result.
    unfold semi_min; rewrite <- Hbest_result, <- Hselected_result.
    eexists; eapply AuditSemiPredNumbered with (v := Graph.source g edge) (number := number)
      (root := root) (part := part) (u := u); try eassumption; reflexivity.
  - eexists; apply AuditSemiPredUnnumbered with (v := Graph.source g edge);
      [reflexivity|exact Hrank].
Qed.

(** A plain predecessor fold audits the same source fold. *)
Lemma audit_semi_predecessors_erases V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis edges initial :
  exists events, audit_semi_predecessors_run EV g r semis edges initial
    (fold_left (semi_predecessor EV g r semis) edges initial) events.
Proof.
  revert initial; induction edges as [|edge rest IH]; intro initial.
  - exists [AuditSemiOuterCase 3]; constructor.
  - destruct initial as [st best].
    destruct (audit_semi_predecessor_erases V E EV g r semis st best edge) as [here Hstep].
    destruct (IH (semi_predecessor EV g r semis (st, best) edge)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** A plain settlement audit exists for the source settlement step. *)
Lemma audit_semi_settle_erases V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) st v :
  exists events, audit_semi_settle_run p r st v (semi_settle p r st v) events.
Proof.
  unfold semi_settle; destruct (Map.get EV v (tree_edge r)) as [edge|] eqn:Htree.
  - destruct (audit_semi_predecessors_erases V E EV g r (SemiState.result st) (pred_edges p v)
      (SemiState.links st, Graph.source g edge)) as [events Hpreds].
    destruct (fold_left (semi_predecessor EV g r (SemiState.result st)) (pred_edges p v)
      (SemiState.links st, Graph.source g edge)) as [links' best] eqn:Hfold.
    eexists; eapply AuditSemiSettleNode with (edge := edge)
      (parent := Graph.source g edge) (incoming := Map.get EV v (in_index p))
      (edges := pred_edges p v); try eassumption; reflexivity.
  - eexists; apply AuditSemiSettleRoot; exact Htree.
Qed.

(** A plain settlement traversal audits the source fold over the same vertices. *)
Lemma audit_semi_settles_erases V E (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) vertices st :
  exists events, audit_semi_settles_run p r vertices st (fold_left (semi_settle p r) vertices st)
    events.
Proof.
  revert st; induction vertices as [|v rest IH]; intro st.
  - exists [AuditSemiOuterCase 7]; constructor.
  - destruct (audit_semi_settle_erases V E EV g p r st v) as [here Hstep].
    destruct (IH (semi_settle p r st v)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** The producer count envelope covers a sum of per-vertex and per-edge charges. *)
Lemma audit_semi_producer_count_arithmetic n edges rank count :
  count <= edges * (20 * S rank + 11) + 11 * n + 2 ->
  count <= 100 * S n * S edges * S rank.
Proof.
  intro Hcount.
  set (budget := 100 * S n * S rank).
  assert (Hedge : 20 * S rank + 11 <= budget) by (unfold budget; nia).
  assert (Hnodes : 11 * n + 2 <= budget) by (unfold budget; nia).
  assert (Hproduct : edges * (20 * S rank + 11) <= edges * budget).
  { apply Nat.mul_le_mono_l; exact Hedge. }
  replace (100 * S n * S edges * S rank) with (S edges * budget) by (unfold budget; ring).
  clearbody budget; nia.
Qed.

(** The producer work envelope absorbs event work and one output-size charge. *)
Lemma audit_semi_producer_work_arithmetic count bound width output work :
  count <= bound -> output <= bound -> work <= count * (140 + 16 * width) + output ->
  256 * S count * S count + work <=
    512 * S bound * S bound + bound * (512 + 16 * width).
Proof.
  intros Hcount Houtput Hwork; nia.
Qed.

(** The ordinary producer returns its source state within the input-derived work budget. *)
Theorem audit_semi_compute_correct : audit_semi_compute_statement.
Proof.
  intros V E EV g p r.
  destruct (audit_semi_settles_erases V E EV g p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty)) as [inner Hrun].
  exists (semi_compute p r), (AuditSemiOuterOutput (length (preorder r)) :: inner).
  split.
  - exists inner; split; [exact Hrun|reflexivity].
  - split; [reflexivity|].
    assert (Hinitial : audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r)
      (SemiState.Make Map.empty semi_links_empty)).
    { split; [apply audit_semi_map_envelope_empty|apply audit_semi_links_envelope_empty]. }
    assert (Hvertices : forall v, In v (rev (preorder r)) ->
      audit_semi_producer_vertex V E EV g p r v).
    { intros v Hin; apply in_rev in Hin; unfold audit_semi_producer_vertex.
      apply in_or_app; left; exact Hin. }
    destruct (audit_semi_settles_in_producer V E EV g p r (rev (preorder r)) _ _ _ Hrun
      Hinitial Hvertices) as [_ [Hcount Hquiet]].
    rewrite audit_semi_pred_sum_reverse, length_rev in Hcount.
    change (length inner <= audit_semi_compute_input_edges p r *
      (20 * S (audit_semi_compute_rank_bound r) + 11) + 8 * length (preorder r) + 1) in Hcount.
    assert (Hbound : S (length inner) <= audit_semi_compute_event_bound p r).
    { apply audit_semi_producer_count_arithmetic; lia. }
    split; [exact Hbound|].
    assert (Hsafe : Forall (audit_semi_outer_safe V E EV (audit_semi_compute_width EV g p r))
      (AuditSemiOuterOutput (length (preorder r)) :: inner)).
    { constructor; [exact I|].
      eapply Forall_impl; [|exact Hquiet].
      intros event [Hsafe _]; exact Hsafe. }
    pose proof (audit_semi_outer_work_sum V E EV (audit_semi_compute_width EV g p r)
      (AuditSemiOuterOutput (length (preorder r)) :: inner) Hsafe) as Hwork.
    pose proof (audit_semi_outer_quiet_extra V E EV (audit_semi_producer_input_width EV g p r)
      inner Hquiet) as Hextra.
    cbn [fold_right audit_semi_outer_extra length] in Hwork.
    rewrite Hextra in Hwork.
    unfold audit_semi_compute_work, audit_semi_compute_input_budget.
    cbn [length].
    eapply audit_semi_producer_work_arithmetic with (output := length (preorder r)).
    + exact Hbound.
    + unfold audit_semi_compute_event_bound; apply audit_semi_producer_count_arithmetic; lia.
    + cbn [fold_right]; lia.
Qed.

(** * Nested producer accounting *)

(** Nested producer work charges each event's actual callback body and any output-size charge. *)
Definition audit_semi_producer_extra V E B (event : audit_semi_producer_nested_event V E B) : nat :=
  match event with
  | SemiProducerOutput size => size
  | _ => 0
  end.

(** A safe producer event fits its fixed frame, input width, and captured body. *)
Definition audit_semi_producer_event_safe V E B (weight : B -> nat) width
    (event : audit_semi_producer_nested_event V E B) : Prop :=
  audit_semi_producer_nested_event_work weight event <=
    140 + 16 * width + audit_semi_producer_nested_body_event_work weight event +
      audit_semi_producer_extra V E B event.

(** Quiet nested producer events carry no output-size charge. *)
Definition audit_semi_producer_event_quiet V E B (weight : B -> nat) width
    (event : audit_semi_producer_nested_event V E B) : Prop :=
  audit_semi_producer_event_safe V E B weight width event /\
    audit_semi_producer_extra V E B event = 0.

(** A safe inner receipt remains safe when wrapped by the producer. *)
Lemma audit_semi_producer_inner_quiet V E B (weight : B -> nat) width events :
  Forall (audit_semi_nested_event_safe V B weight width) events ->
  Forall (audit_semi_producer_event_quiet V E B weight width) (map SemiProducerInner events).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; cbn; constructor; [|exact IH].
  split; [|reflexivity].
  unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
    audit_semi_producer_nested_body_event_work, audit_semi_producer_extra.
  change (64 + audit_semi_nested_event_work weight event <=
    140 + 16 * width + audit_semi_nested_body_event_work weight event + 0).
  unfold audit_semi_nested_event_safe in Hevent; lia.
Qed.

(** Summed safe producer events retain the same captured callback-body work. *)
Lemma audit_semi_producer_safe_work V E B (weight : B -> nat) width events :
  Forall (audit_semi_producer_event_safe V E B weight width) events ->
  audit_semi_producer_nested_work weight events <=
    length events * (140 + 16 * width) + audit_semi_producer_nested_body_work weight events +
      fold_right (fun event total => audit_semi_producer_extra V E B event + total) 0 events.
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - unfold audit_semi_producer_nested_work, audit_semi_producer_nested_body_work in *.
    cbn [fold_right length] in *; unfold audit_semi_producer_event_safe in Hevent; lia.
Qed.

(** Internal nested producer receipts have no output-size charge. *)
Lemma audit_semi_producer_quiet_extra V E B (weight : B -> nat) width events :
  Forall (audit_semi_producer_event_quiet V E B weight width) events ->
  fold_right (fun event total => audit_semi_producer_extra V E B event + total) 0 events = 0.
Proof.
  intro Hquiet; induction Hquiet as [|event rest [_ Hextra] Hrest IH]; cbn [fold_right].
  - reflexivity.
  - now rewrite Hextra, IH.
Qed.

(** A tree-map read keeps the actual encoder body and stays within the input width. *)
Lemma audit_semi_producer_tree_get_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V E) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (map SemiProducerTreeMap (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_get_source_work_bound V E B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in *; destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trace].
  cbn [fst snd] in Hencode, Hwork; subst code.
  cbn [snd map]; constructor; [|constructor]; split; [|reflexivity].
  unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
    audit_semi_producer_nested_body_event_work, audit_semi_producer_extra.
  cbn [audit_map_source_work] in *; lia.
Qed.

(** A predecessor-index read keeps the actual encoder body and key width. *)
Lemma audit_semi_producer_pred_get_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V (list E)) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (map SemiProducerPredMap (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_get_source_work_bound V (list E) B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in *; destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trace].
  cbn [fst snd] in Hencode, Hwork; subst code.
  cbn [snd map]; constructor; [|constructor]; split; [|reflexivity].
  unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
    audit_semi_producer_nested_body_event_work, audit_semi_producer_extra.
  cbn [audit_map_source_work] in *; lia.
Qed.

(** A captured source event charges precisely its supplied callback body. *)
Lemma audit_semi_producer_source_quiet V E B (weight : B -> nat) width edge vertex body :
  audit_semi_producer_event_quiet V E B weight width (SemiProducerSource edge vertex body).
Proof.
  split; [|reflexivity].
  unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
    audit_semi_producer_nested_body_event_work, audit_semi_producer_extra; cbn; lia.
Qed.

(** A producer case marker carries no callback body. *)
Lemma audit_semi_producer_case_quiet V E B (weight : B -> nat) width site :
  audit_semi_producer_event_quiet V E B weight width (SemiProducerCase site).
Proof.
  split; [|reflexivity].
  unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
    audit_semi_producer_nested_body_event_work, audit_semi_producer_extra; cbn; lia.
Qed.

(** Wrapping one safe inner event preserves its body charge. *)
Lemma audit_semi_producer_inner_event_quiet V E B (weight : B -> nat) width event :
  audit_semi_nested_event_safe V B weight width event ->
  audit_semi_producer_event_quiet V E B weight width (SemiProducerInner event).
Proof.
  intro Hsafe; split; [|reflexivity].
  unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
    audit_semi_producer_nested_body_event_work, audit_semi_producer_extra.
  change (64 + audit_semi_nested_event_work weight event <=
    140 + 16 * width + audit_semi_nested_body_event_work weight event + 0).
  unfold audit_semi_nested_event_safe in Hsafe; lia.
Qed.

(** A nested rank-map read is quiet at the producer's chosen width. *)
Lemma audit_semi_producer_rank_get_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key input :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (map (fun item => SemiProducerInner (SemiNestedRankMap item))
      (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_nested_rank_get_safe V B EV enc weight width key input Hencode Hwidth)
    as Hsafe.
  pose proof (audit_semi_producer_inner_quiet V E B weight width _ Hsafe) as Hquiet.
  now rewrite map_map in Hquiet.
Qed.

(** A nested vertex-map read is quiet at the producer's chosen width. *)
Lemma audit_semi_producer_vertex_get_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key input :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (map (fun item => SemiProducerInner (SemiNestedVertexMap item))
      (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width key input Hencode Hwidth)
    as Hsafe.
  pose proof (audit_semi_producer_inner_quiet V E B weight width _ Hsafe) as Hquiet.
  now rewrite map_map in Hquiet.
Qed.

(** A nested rank receipt is quiet at the producer's chosen width. *)
Lemma audit_semi_producer_rank_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width (r : dfs_result V E) v :
  fst (enc v) = encode EV v -> Pos.size_nat (encode EV v) <= width ->
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (map SemiProducerInner (snd (audit_semi_nested_rank enc r v))).
Proof.
  intros Hencode Hwidth; apply audit_semi_producer_inner_quiet.
  apply (audit_semi_nested_rank_safe V E B EV enc); assumption.
Qed.

(** A comparison of original ranks is quiet at the producer's input width. *)
Lemma audit_semi_producer_rank_compare_quiet V E B (EV : encoding V) (g : Graph.t V E)
    (weight : B -> nat) (p : prepared EV g) (r : dfs_result V E) semis st start left right
    choose events :
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r start ->
  audit_positive_leb (semi_rank EV r left) (semi_rank EV r right) = (choose, events) ->
  audit_semi_producer_event_quiet V E B weight (audit_semi_producer_input_width EV g p r)
    (SemiProducerInner
      (SemiNestedCompare (semi_rank EV r left) (semi_rank EV r right) choose events)).
Proof.
  intros Hsemis Hlinks Hstart Hcompare.
  pose proof (audit_semi_nested_rank_width V E EV r semis st start left) as Hleft.
  pose proof (audit_semi_nested_rank_width V E EV r semis st start right) as Hright.
  pose proof (audit_semi_compress_width_in_producer V E EV g p r semis st start
    Hsemis Hlinks Hstart) as Hwidth.
  apply audit_semi_producer_inner_event_quiet.
  eapply audit_semi_nested_compare_safe; [lia|lia|right; exact Hcompare].
Qed.

(** An unnumbered predecessor keeps the state and records its source and rank callbacks. *)
Lemma audit_semi_producer_missing_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc weight (p : prepared EV g) (r : dfs_result V E) st best edge body rank_events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r best ->
  audit_semi_producer_vertex V E EV g p r (Graph.source g edge) ->
  audit_map_get enc (Graph.source g edge) (pre_num r) = (None, rank_events) ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st /\
  audit_semi_producer_vertex V E EV g p r best /\
  length ([SemiProducerSource edge (Graph.source g edge) body] ++
    map (fun item => SemiProducerInner (SemiNestedRankMap item)) rank_events ++
    [SemiProducerCase 0]) <= 20 * S (audit_semi_producer_input_rank r) + 10 /\
  Forall (audit_semi_producer_event_quiet V E B weight (audit_semi_producer_input_width EV g p r))
    ([SemiProducerSource edge (Graph.source g edge) body] ++
      map (fun item => SemiProducerInner (SemiNestedRankMap item)) rank_events ++
      [SemiProducerCase 0]).
Proof.
  intros Hencode Hlinks Hbest Hvertex Hrank.
  pose proof (audit_semi_producer_vertex_width V E EV g p r (Graph.source g edge) Hvertex)
    as Hwidth.
  pose proof (audit_semi_producer_rank_get_quiet V E B EV enc weight
    (audit_semi_producer_input_width EV g p r) (Graph.source g edge) (pre_num r)
    (Hencode _) Hwidth) as Hrank_quiet.
  rewrite Hrank in Hrank_quiet; cbn in Hrank_quiet.
  pose proof (audit_semi_map_get_length V positive B enc (Graph.source g edge) (pre_num r)) as Hlen.
  rewrite Hrank in Hlen; cbn in Hlen.
  split; [exact Hlinks|]; split; [exact Hbest|]; split.
  - cbn [app length]; rewrite length_app, length_map; cbn; lia.
  - constructor; [apply audit_semi_producer_source_quiet|].
    apply Forall_app; split; [exact Hrank_quiet|].
    constructor; [apply audit_semi_producer_case_quiet|constructor].
Qed.

(** A nested query and value read select vertices from the producer input envelope. *)
Lemma audit_semi_producer_selected_in V E B (EV : encoding V) (g : Graph.t V E)
    enc (p : prepared EV g) (r : dfs_result V E) semis st v st' root part inner value value_events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r v ->
  audit_semi_nested_compress_run (B := B) enc r semis st v (st', (root, part)) inner ->
  let u :=
    match part with
    | Some chosen => chosen
    | None => v
    end in
  audit_map_get enc u semis = (value, value_events) ->
  audit_semi_producer_vertex V E EV g p r u /\
  audit_semi_producer_vertex V E EV g p r
    (match value with
    | Some selected => selected
    | None => u
    end).
Proof.
  intros Hencode Hsemis Hlinks Hv Hquery u Hvalue.
  pose proof (audit_semi_nested_result_in V E B EV enc r semis st v v _ _ Hencode Hquery
    (or_introl eq_refl)) as [_ Hpart].
  cbn in Hpart.
  assert (Hu : audit_semi_producer_vertex V E EV g p r u).
  { subst u; destruct part as [chosen|]; [|exact Hv].
    exact (audit_semi_input_vertex_subset V EV _ semis st v chosen Hsemis Hlinks Hv Hpart). }
  split; [exact Hu|].
  pose proof (audit_map_get_erases V V B enc EV u semis (Hencode u)) as Herase.
  rewrite Hvalue in Herase; cbn in Herase.
  destruct value as [selected|]; [|exact Hu].
  symmetry in Herase; exact (proj2 ((proj2 Hsemis) u selected Herase)).
Qed.

(** A nested predecessor step keeps the state envelope and charges the same callback receipts. *)
Lemma audit_semi_producer_pred_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc source weight (p : prepared EV g) (r : dfs_result V E) semis st best edge result events :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r best ->
  audit_semi_producer_vertex V E EV g p r (Graph.source g edge) ->
  audit_semi_producer_pred_run (B := B) enc source r semis (st, best) edge result events ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst result) /\
  audit_semi_producer_vertex V E EV g p r (snd result) /\
  length events <= 20 * S (audit_semi_producer_input_rank r) + 10 /\
  Forall (audit_semi_producer_event_quiet V E B weight (audit_semi_producer_input_width EV g p r))
    events.
Proof.
  intros Hencode Hsource Hsemis Hlinks Hbest Hvertex Hrun.
  inversion Hrun as [st0 best0 edge0 vertex source_body rank_events Hsource_run Hrank
    |st0 best0 edge0 vertex source_body number rank_events st' root part inner u value value_events
      best_rank value_rank best_events value_rank_events choose compare_events Hsource_run Hrank
      Hquery Hu Hvalue Hbest_rank Hvalue_rank Hcompare]; subst.
  - pose proof (Hsource edge) as Hsource_result.
    rewrite Hsource_run in Hsource_result; cbn in Hsource_result; subst vertex.
    cbn; eapply audit_semi_producer_missing_in_input; eassumption.
  - pose proof (Hsource edge) as Hsource_result.
    rewrite Hsource_run in Hsource_result; cbn in Hsource_result; subst vertex.
    set (u :=
      match part with
      | Some chosen => chosen
      | None => Graph.source g edge
      end) in *.
    pose proof (audit_semi_nested_query_in_producer V E B EV g enc weight p r semis st
      (Graph.source g edge) (st', (root, part)) inner Hencode Hsemis Hlinks Hvertex Hquery)
      as [Hcount [Hsafe Hlinks']].
    cbn in Hlinks'.
    pose proof (audit_semi_producer_selected_in V E B EV g enc p r semis st
      (Graph.source g edge) st' root part inner value value_events
      Hencode Hsemis Hlinks Hvertex Hquery Hvalue) as [Hu_vertex Hselected].
    change (audit_semi_producer_vertex V E EV g p r
      (match value with
      | Some x => x
      | None => u
      end)) in Hselected.
    pose proof (audit_semi_producer_vertex_width V E EV g p r (Graph.source g edge) Hvertex)
      as Hvertex_width.
    pose proof (audit_semi_producer_vertex_width V E EV g p r u Hu_vertex) as Hu_width.
    pose proof (audit_semi_producer_vertex_width V E EV g p r best Hbest) as Hbest_width.
    pose proof (audit_semi_producer_vertex_width V E EV g p r _ Hselected) as Hselected_width.
    pose proof (audit_semi_producer_rank_get_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) (Graph.source g edge) (pre_num r)
      (Hencode _) Hvertex_width) as Hrank_quiet.
    pose proof (audit_semi_producer_vertex_get_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) u semis (Hencode u) Hu_width) as Hvalue_quiet.
    pose proof (audit_semi_producer_rank_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) r best (Hencode best) Hbest_width) as Hbest_quiet.
    pose proof (audit_semi_producer_rank_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) r _ (Hencode _) Hselected_width)
      as Hvalue_rank_quiet.
    rewrite Hrank in Hrank_quiet; rewrite Hvalue in Hvalue_quiet;
      rewrite Hbest_rank in Hbest_quiet; rewrite Hvalue_rank in Hvalue_rank_quiet;
      cbn in Hrank_quiet, Hvalue_quiet, Hbest_quiet, Hvalue_rank_quiet.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r best (Hencode best)) as Hbest_result.
    pose proof (audit_semi_nested_rank_erases V E B EV enc r
      (match value with
      | Some x => x
      | None => u
      end) (Hencode _)) as Hselected_result.
    rewrite Hbest_rank in Hbest_result; rewrite Hvalue_rank in Hselected_result;
      cbn in Hbest_result, Hselected_result; subst best_rank value_rank.
    pose proof (audit_semi_producer_rank_compare_quiet V E B EV g weight p r semis st
      (Graph.source g edge) best
      (match value with
      | Some x => x
      | None => u
      end)
      choose compare_events Hsemis Hlinks Hvertex Hcompare) as Hcompare_quiet.
    pose proof (audit_semi_producer_inner_quiet V E B weight
      (audit_semi_producer_input_width EV g p r) inner Hsafe) as Hinner_quiet.
    pose proof (audit_semi_map_get_length V positive B enc (Graph.source g edge) (pre_num r))
      as Hlen.
    pose proof (audit_semi_map_get_length V V B enc u semis) as Hvalue_len.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st best)) as Hbest_len.
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r st
      (match value with
      | Some x => x
      | None => u
      end))) as Hvalue_rank_len.
    rewrite Hrank in Hlen; rewrite Hvalue in Hvalue_len; rewrite Hbest_rank in Hbest_len;
      rewrite Hvalue_rank in Hvalue_rank_len; cbn in Hlen, Hvalue_len, Hbest_len, Hvalue_rank_len.
    cbn [fst snd]; split; [exact Hlinks'|]; split.
    + destruct choose; assumption.
    + split.
      * repeat rewrite length_app; repeat rewrite length_map; cbn; lia.
      * cbn [app]; constructor; [apply audit_semi_producer_source_quiet|].
        apply Forall_app; split; [exact Hrank_quiet|].
        constructor; [apply audit_semi_producer_case_quiet|].
        apply Forall_app; split; [exact Hinner_quiet|].
        constructor; [apply audit_semi_producer_case_quiet|].
        apply Forall_app; split; [exact Hvalue_quiet|].
        apply Forall_app; split; [exact Hbest_quiet|].
        apply Forall_app; split; [exact Hvalue_rank_quiet|].
        constructor; [exact Hcompare_quiet|constructor].
Qed.

(** Nested predecessor traversal preserves its state and aggregates the actual callback events. *)
Lemma audit_semi_producer_preds_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc source weight (p : prepared EV g) (r : dfs_result V E) semis edges initial result events :
  audit_semi_producer_preds_run (B := B) enc source r semis edges initial result events ->
  (forall x, fst (enc x) = encode EV x) -> (forall e, fst (source e) = Graph.source g e) ->
  audit_semi_map_envelope V EV (audit_semi_producer_vertex V E EV g p r) semis ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst initial) ->
  audit_semi_producer_vertex V E EV g p r (snd initial) ->
  (forall edge, In edge edges -> audit_semi_producer_vertex V E EV g p r (Graph.source g edge)) ->
  audit_semi_links_envelope V EV (audit_semi_producer_vertex V E EV g p r) (fst result) /\
  audit_semi_producer_vertex V E EV g p r (snd result) /\
  length events <= length edges * (20 * S (audit_semi_producer_input_rank r) + 11) + 1 /\
  Forall (audit_semi_producer_event_quiet V E B weight (audit_semi_producer_input_width EV g p r))
    events.
Proof.
  intro Hrun; induction Hrun as [acc|edge rest initial middle result here later Hstep Hrest IH];
    intros Hencode Hsource Hsemis Hlinks Hbest Hsources.
  - split; [exact Hlinks|]; split; [exact Hbest|]; split; [cbn; lia|].
    constructor; [apply audit_semi_producer_case_quiet|constructor].
  - destruct initial as [st best]; destruct middle as [st' best'].
    pose proof (audit_semi_producer_pred_in_input V E B EV g enc source weight p r semis st best
      edge
      _ _ Hencode Hsource Hsemis Hlinks Hbest (Hsources edge (or_introl eq_refl)) Hstep)
      as [Hlinks' [Hbest' [Hcount Hquiet_here]]].
    cbn in Hlinks', Hbest'.
    destruct (IH Hencode Hsource Hsemis Hlinks' Hbest' (fun e Hin => Hsources e (or_intror Hin)))
      as [Hresult [Hvertex [Hlater Hquiet_later]]].
    split; [exact Hresult|]; split; [exact Hvertex|]; split.
    + cbn [length]; rewrite length_app; nia.
    + constructor; [apply audit_semi_producer_case_quiet|].
      apply Forall_app; split; assumption.
Qed.

(** A producer's nested map write is quiet and carries the same encoder body. *)
Lemma audit_semi_producer_vertex_set_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key value (input : Map.t V V) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (map (fun item => SemiProducerInner (SemiNestedVertexMap item))
      (snd (audit_map_set enc key value input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_nested_vertex_set_safe V B EV enc weight width key value input
    Hencode Hwidth)
    as Hsafe.
  pose proof (audit_semi_producer_inner_quiet V E B weight width _ Hsafe) as Hquiet.
  now rewrite map_map in Hquiet.
Qed.

(** The three producer link writes retain their receipts and use the same vertex key. *)
Lemma audit_semi_producer_link_details V E B (EV : encoding V) enc (weight : B -> nat)
    width st v parent :
  fst (enc v) = encode EV v -> Pos.size_nat (encode EV v) <= width ->
  length (snd (audit_semi_producer_link (E := E) enc st v parent)) = 3 /\
  Forall (audit_semi_producer_event_quiet V E B weight width)
    (snd (audit_semi_producer_link (E := E) enc st v parent)).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_semi_map_set_length V V B enc v parent (SemiLinks.original st)) as Ha_len.
  pose proof (audit_semi_map_set_length V V B enc v parent (SemiLinks.shortcut st)) as Hb_len.
  pose proof (audit_semi_map_set_length V V B enc v v (SemiLinks.labels st)) as Hc_len.
  pose proof (audit_semi_producer_vertex_set_quiet V E B EV enc weight width v parent
    (SemiLinks.original st) Hencode Hwidth) as Ha.
  pose proof (audit_semi_producer_vertex_set_quiet V E B EV enc weight width v parent
    (SemiLinks.shortcut st) Hencode Hwidth) as Hb.
  pose proof (audit_semi_producer_vertex_set_quiet V E B EV enc weight width v v
    (SemiLinks.labels st) Hencode Hwidth) as Hc.
  unfold audit_semi_producer_link.
  destruct (audit_map_set enc v parent (SemiLinks.original st)) as [original a].
  destruct (audit_map_set enc v parent (SemiLinks.shortcut st)) as [shortcut b].
  destruct (audit_map_set enc v v (SemiLinks.labels st)) as [labels c].
  cbn in Ha_len, Hb_len, Hc_len, Ha, Hb, Hc |- *.
  split; [rewrite length_map, !length_app; lia|].
  rewrite !map_app, !Forall_app; auto.
Qed.

(** Nested settlement preserves the state envelope and all same-call callback charges. *)
Lemma audit_semi_producer_settle_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc source weight (p : prepared EV g) (r : dfs_result V E) st v result events :
  audit_semi_producer_settle_run (B := B) enc source p r st v result events ->
  (forall x, fst (enc x) = encode EV x) -> (forall e, fst (source e) = Graph.source g e) ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  audit_semi_producer_vertex V E EV g p r v ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) result /\
  length events <=
    length (pred_edges p v) * (20 * S (audit_semi_producer_input_rank r) + 11) + 10 /\
  Forall (audit_semi_producer_event_quiet V E B weight (audit_semi_producer_input_width EV g p r))
    events.
Proof.
  intros Hrun Hencode Hsource [Hsemis Hlinks] Hv.
  pose proof (audit_semi_producer_vertex_width V E EV g p r v Hv) as Hwidth.
  inversion Hrun as [st0 v0 tree_events Htree
    |st0 v0 edge tree_events parent source_body incoming pred_events edges links' best pred_steps
      result_map result_events links'' link_events Htree Hsource_run Hpred Hedges Hpreds Hresult
      Hlink];
    subst.
  - pose proof (audit_semi_producer_tree_get_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) v (tree_edge r) (Hencode v) Hwidth) as Htree_quiet.
    pose proof (audit_semi_map_get_length V E B enc v (tree_edge r)) as Htree_len.
    rewrite Htree in Htree_quiet, Htree_len; cbn in Htree_quiet, Htree_len.
    split; [split; assumption|]; split.
    + rewrite length_app, length_map; cbn; lia.
    + apply Forall_app; split; [exact Htree_quiet|].
      constructor; [apply audit_semi_producer_case_quiet|constructor].
  - pose proof (audit_map_get_erases V E B enc EV v (tree_edge r) (Hencode v)) as Htree_result.
    rewrite Htree in Htree_result; cbn in Htree_result.
    pose proof (Hsource edge) as Hsource_result; rewrite Hsource_run in Hsource_result;
      cbn in Hsource_result; subst parent.
    assert (Hparent : audit_semi_producer_vertex V E EV g p r (Graph.source g edge)).
    { eapply audit_semi_producer_tree_source; symmetry; exact Htree_result. }
    pose proof (audit_map_get_erases V (list E) B enc EV v (in_index p) (Hencode v))
      as Hpred_result.
    rewrite Hpred in Hpred_result; cbn in Hpred_result; subst incoming.
    assert (Hpred_edges :
      (match Map.get EV v (in_index p) with
      | Some xs => xs
      | None => []
      end) = pred_edges p v) by reflexivity.
    rewrite Hpred_edges in Hpreds.
    assert (Hsources : forall e, In e (pred_edges p v) ->
      audit_semi_producer_vertex V E EV g p r (Graph.source g e)).
    { intros e Hin; eapply audit_semi_producer_pred_source; exact Hin. }
    destruct (audit_semi_producer_preds_in_input V E B EV g enc source weight p r
      (SemiState.result st) (pred_edges p v) (SemiState.links st, Graph.source g edge)
      (links', best) pred_steps Hpreds Hencode Hsource Hsemis Hlinks Hparent Hsources)
      as [Hlinks' [Hbest [Hcount Hquiet]]].
    cbn in Hlinks', Hbest.
    pose proof (audit_map_set_erases V V B enc EV v best (SemiState.result st) (Hencode v)) as Hr.
    rewrite Hresult in Hr; cbn in Hr; subst result_map.
    pose proof (audit_semi_producer_link_erases V E B EV enc links' v (Graph.source g edge)
      (Hencode v))
      as Hl.
    rewrite Hlink in Hl; cbn in Hl; subst links''.
    pose proof (audit_semi_producer_tree_get_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) v (tree_edge r) (Hencode v) Hwidth) as Htree_quiet.
    pose proof (audit_semi_producer_pred_get_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) v (in_index p) (Hencode v) Hwidth) as Hpred_quiet.
    pose proof (audit_semi_producer_vertex_set_quiet V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) v best (SemiState.result st) (Hencode v) Hwidth)
      as Hresult_quiet.
    pose proof (audit_semi_producer_link_details V E B EV enc weight
      (audit_semi_producer_input_width EV g p r) links' v (Graph.source g edge) (Hencode v) Hwidth)
      as [Hlink_len Hlink_quiet].
    pose proof (audit_semi_map_get_length V E B enc v (tree_edge r)) as Htree_len.
    pose proof (audit_semi_map_get_length V (list E) B enc v (in_index p)) as Hpred_len.
    pose proof (audit_semi_map_set_length V V B enc v best (SemiState.result st)) as Hresult_len.
    rewrite Htree in Htree_quiet, Htree_len; rewrite Hpred in Hpred_quiet, Hpred_len.
    rewrite Hresult in Hresult_quiet, Hresult_len; rewrite Hlink in Hlink_len, Hlink_quiet.
    cbn in Htree_quiet, Htree_len, Hpred_quiet, Hpred_len, Hresult_quiet, Hresult_len,
      Hlink_len, Hlink_quiet.
    split.
    + split; cbn [SemiState.result SemiState.links].
      * apply audit_semi_map_envelope_set; assumption.
      * apply audit_semi_links_envelope_link; assumption.
    + split.
      * repeat rewrite length_app; repeat rewrite length_map; cbn; lia.
      * repeat rewrite Forall_app; repeat split; try assumption.
        constructor; [apply audit_semi_producer_case_quiet|].
        constructor; [apply audit_semi_producer_source_quiet|constructor].
Qed.

(** The nested settlement traversal aggregates the actual per-vertex receipts. *)
Lemma audit_semi_producer_settles_in_input V E B (EV : encoding V) (g : Graph.t V E)
    enc source weight (p : prepared EV g) (r : dfs_result V E) vertices st result events :
  audit_semi_producer_settles_run (B := B) enc source p r vertices st result events ->
  (forall x, fst (enc x) = encode EV x) -> (forall e, fst (source e) = Graph.source g e) ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) st ->
  (forall v, In v vertices -> audit_semi_producer_vertex V E EV g p r v) ->
  audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r) result /\
  length events <=
    fold_right (fun v total => length (pred_edges p v) + total) 0 vertices *
      (20 * S (audit_semi_producer_input_rank r) + 11) + 11 * length vertices + 1 /\
  Forall (audit_semi_producer_event_quiet V E B weight (audit_semi_producer_input_width EV g p r))
    events.
Proof.
  intro Hrun; induction Hrun as [st|v rest initial middle result here later Hstep Hrest IH];
    intros Hencode Hsource Hstate Hvertices.
  - split; [exact Hstate|]; split; [cbn; lia|].
    constructor; [apply audit_semi_producer_case_quiet|constructor].
  - destruct (audit_semi_producer_settle_in_input V E B EV g enc source weight p r initial v
      middle here Hstep Hencode Hsource Hstate (Hvertices v (or_introl eq_refl)))
      as [Hmiddle [Hhere Hquiet_here]].
    destruct (IH Hencode Hsource Hmiddle (fun x Hin => Hvertices x (or_intror Hin)))
      as [Hresult [Hlater Hquiet_later]].
    split; [exact Hresult|]; split.
    + cbn [length fold_right]; rewrite length_app; nia.
    + constructor; [apply audit_semi_producer_case_quiet|].
      apply Forall_app; split; assumption.
Qed.

(** The nested producer budget absorbs the counted frames, output size, and actual body work. *)
Lemma audit_semi_producer_nested_arithmetic count bound width output work body :
  count <= bound -> output <= bound -> work <= count * (140 + 16 * width) + body + output ->
  work <= 512 * S bound * S bound + bound * (512 + 64 * width) + body.
Proof.
  intros Hcount Houtput Hwork.
  assert (Hmul : count * (140 + 16 * width) <= bound * (140 + 16 * width)).
  { apply Nat.mul_le_mono_r; exact Hcount. }
  nia.
Qed.

(** Nested production obeys its original input budget and charges the captured callback bodies. *)
Theorem audit_semi_producer_nested_bound : audit_semi_producer_nested_bound_statement.
Proof.
  intros V E B EV g p r enc source weight result events Hencode Hsource [inner [Hrun ->]].
  assert (Hinitial : audit_semi_state_envelope V EV (audit_semi_producer_vertex V E EV g p r)
    (SemiState.Make Map.empty semi_links_empty)).
  { split; [apply audit_semi_map_envelope_empty|apply audit_semi_links_envelope_empty]. }
  assert (Hvertices : forall v, In v (rev (preorder r)) ->
    audit_semi_producer_vertex V E EV g p r v).
  { intros v Hin; apply in_rev in Hin; unfold audit_semi_producer_vertex.
    apply in_or_app; left; exact Hin. }
  destruct (audit_semi_producer_settles_in_input V E B EV g enc source weight p r
    (rev (preorder r)) _ _ _ Hrun Hencode Hsource Hinitial Hvertices) as [_ [Hcount Hquiet]].
  rewrite audit_semi_pred_sum_reverse, length_rev in Hcount.
  change (length inner <= audit_semi_producer_input_edges p r *
    (20 * S (audit_semi_producer_input_rank r) + 11) + 11 * length (preorder r) + 1) in Hcount.
  assert (Hbound : S (length inner) <= audit_semi_producer_event_bound p r).
  { apply audit_semi_producer_count_arithmetic; lia. }
  split; [exact Hbound|].
  assert (Hsafe : Forall
    (audit_semi_producer_event_safe V E B weight (audit_semi_producer_input_width EV g p r))
    (SemiProducerOutput (length (preorder r)) :: inner)).
  { constructor.
    - unfold audit_semi_producer_event_safe, audit_semi_producer_nested_event_work,
        audit_semi_producer_nested_body_event_work, audit_semi_producer_extra; cbn; lia.
    - eapply Forall_impl; [|exact Hquiet].
      intros event [Hsafe _]; exact Hsafe. }
  pose proof (audit_semi_producer_safe_work V E B weight (audit_semi_producer_input_width EV g p r)
    (SemiProducerOutput (length (preorder r)) :: inner) Hsafe) as Hwork.
  pose proof (audit_semi_producer_quiet_extra V E B weight
    (audit_semi_producer_input_width EV g p r)
    inner Hquiet) as Hextra.
  cbn [fold_right audit_semi_producer_extra length] in Hwork; rewrite Hextra in Hwork.
  unfold audit_semi_producer_input_budget; cbn [length].
  eapply audit_semi_producer_nested_arithmetic with (output := length (preorder r)).
  - exact Hbound.
  - unfold audit_semi_producer_event_bound; apply audit_semi_producer_count_arithmetic; lia.
  - cbn [fold_right audit_semi_producer_extra] in Hwork; lia.
Qed.
