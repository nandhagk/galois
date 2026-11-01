(** * Lengauer--Tarjan audit adequacy

    These proofs connect the recorded bucket traversal to the source computation.
    For example, settling an empty bucket preserves the current provisional parents.
    Builds on: GraphAuditLengauerTarjan and GraphAuditSemiDominatorsAdequacy. *)

From Stdlib Require Import List PArith Lia PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditPrimitive CollectionsAuditPrimitiveAdequacy CollectionsAuditCompare
  CollectionsAuditCompareAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphSemiDominators
  GraphLengauerTarjan GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditBaseAdequacy
  GraphAuditDfsAdequacy GraphAuditVirtualAdequacy
  GraphAuditSemiDominators GraphAuditSemiDominatorsAdequacy GraphAuditLengauerTarjan.
Import List.ListNotations.

(** * Determinism of recorded traversals *)

(** A bucket member has a unique successor and receipt. *)
Lemma audit_lt_member_unique V E (EV : encoding V) (r : dfs_result V E) semis s st v
    first first_events second second_events :
  audit_lt_member_run EV r semis s st v first first_events ->
  audit_lt_member_run EV r semis s st v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst.
  match goal with
  | Hleft : audit_semi_compress_run _ _ _ _ _ _ _,
    Hright : audit_semi_compress_run _ _ _ _ _ _ _ |- _ =>
    destruct (audit_semi_compress_unique _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
      as [Hresult Hevents]; inversion Hresult; subst
  end.
  repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  split; reflexivity.
Qed.

(** The member traversal determines its final state and full receipt. *)
Lemma audit_lt_members_unique V E (EV : encoding V) (r : dfs_result V E) semis s
    vertices st first first_events second second_events :
  audit_lt_members_run EV r semis s vertices st first first_events ->
  audit_lt_members_run EV r semis s vertices st second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_lt_member_run _ _ _ _ _ _ _ _,
      Hright : audit_lt_member_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_lt_member_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_lt_members_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_lt_members_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** A reverse step determines its state and receipt, including its tree lookup. *)
Lemma audit_lt_reverse_unique V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis buckets st v first first_events second second_events :
  audit_lt_reverse_run EV g r semis buckets st v first first_events ->
  audit_lt_reverse_run EV g r semis buckets st v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst; try congruence.
  all: repeat
    match goal with
    | Hleft : ?f = Some ?a, Hright : ?f = Some ?b |- _ =>
      assert (a = b) by congruence; subst b; clear Hright
    end.
  all: match goal with
    | Hleft : audit_lt_members_run _ _ _ _ _ _ _ _,
      Hright : audit_lt_members_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_lt_members_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; subst
    end.
  all: split; congruence.
Qed.

(** Reverse traversal determines the complete receipt. *)
Lemma audit_lt_reverse_fold_unique V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis buckets vertices st first first_events second second_events :
  audit_lt_reverse_fold_run EV g r semis buckets vertices st first first_events ->
  audit_lt_reverse_fold_run EV g r semis buckets vertices st second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_lt_reverse_run _ _ _ _ _ _ _ _ _,
      Hright : audit_lt_reverse_run _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_lt_reverse_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_lt_reverse_fold_run _ _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_lt_reverse_fold_run _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** Any two ordinary LT audit runs return the same result and receipt. *)
Theorem audit_lt_compute_unique : audit_lt_compute_unique_statement.
Proof.
  intros V E EV g r semis first second first_events second_events.
  unfold audit_lt_compute_run.
  destruct (audit_lt_buckets_counted EV semis (preorder r) Map.empty) as [buckets bucket_events].
  intros [settled [here [Hfirst Hresult]]] [settled' [later [Hsecond Hresult']]].
  destruct (audit_lt_reverse_fold_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hfirst Hsecond)
    as [Hstate Hevents].
  subst settled' later.
  destruct (audit_lt_correct_fold EV semis (LtState.parents settled) (preorder r) Map.empty)
    as [result events].
  destruct Hresult as [-> ->]; destruct Hresult' as [-> ->]; split; reflexivity.
Qed.

(** A nested member has a unique successor and callback receipt. *)
Lemma audit_lt_nested_member_unique V E B enc (r : dfs_result V E) semis s st v
    first first_events second second_events :
  audit_lt_nested_member_run (B := B) enc r semis s st v first first_events ->
  audit_lt_nested_member_run enc r semis s st v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst.
  match goal with
  | Hleft : audit_semi_nested_compress_run _ _ _ _ _ _ _,
    Hright : audit_semi_nested_compress_run _ _ _ _ _ _ _ |- _ =>
    destruct (audit_semi_nested_compress_unique _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
      as [Hresult Hevents]; inversion Hresult; subst
  end.
  repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  split; reflexivity.
Qed.

(** A nested member fold determines both its state and receipt. *)
Lemma audit_lt_nested_members_unique V E B enc (r : dfs_result V E) semis s vertices st
    first first_events second second_events :
  audit_lt_nested_members_run (B := B) enc r semis s vertices st first first_events ->
  audit_lt_nested_members_run enc r semis s vertices st second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_lt_nested_member_run _ _ _ _ _ _ _ _,
      Hright : audit_lt_nested_member_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_lt_nested_member_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_lt_nested_members_run _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_lt_nested_members_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** A nested reverse step retains a unique source callback receipt. *)
Lemma audit_lt_nested_reverse_unique V E B enc source (r : dfs_result V E) semis buckets st v
    first first_events second second_events :
  audit_lt_nested_reverse_run (B := B) enc source r semis buckets st v first first_events ->
  audit_lt_nested_reverse_run enc source r semis buckets st v second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst Hsecond; inversion Hfirst; inversion Hsecond; subst;
    repeat
      match goal with
      | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
        rewrite Hleft in Hright; inversion Hright; clear Hright; subst
      end; try congruence.
  all: match goal with
    | Hleft : audit_lt_nested_members_run _ _ _ _ _ _ _ _,
      Hright : audit_lt_nested_members_run _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_lt_nested_members_unique _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hresult Hevents]; subst
    end.
  all: repeat
    match goal with
    | Hleft : ?f = (?a, ?b), Hright : ?f = (?c, ?d) |- _ =>
      rewrite Hleft in Hright; inversion Hright; clear Hright; subst
    end.
  all: split; reflexivity.
Qed.

(** The nested reverse fold determines its result and all recorded callbacks. *)
Lemma audit_lt_nested_reverse_fold_unique V E B enc source (r : dfs_result V E) semis buckets
    vertices st first first_events second second_events :
  audit_lt_nested_reverse_fold_run (B := B) enc source r semis buckets vertices st first
    first_events ->
  audit_lt_nested_reverse_fold_run enc source r semis buckets vertices st second second_events ->
  first = second /\ first_events = second_events.
Proof.
  intros Hfirst; revert second second_events.
  induction Hfirst; intros second second_events Hsecond; inversion Hsecond; subst.
  - split; reflexivity.
  - match goal with
    | Hleft : audit_lt_nested_reverse_run _ _ _ _ _ _ _ _ _,
      Hright : audit_lt_nested_reverse_run _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (audit_lt_nested_reverse_unique _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hleft Hright)
        as [Hmiddle Hhere]; subst
    end.
    match goal with
    | IH : forall _ _, audit_lt_nested_reverse_fold_run _ _ _ _ _ _ _ _ _ -> _,
      Hrun : audit_lt_nested_reverse_fold_run _ _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ Hrun) as [Hresult Hlater]; subst
    end.
    split; reflexivity.
Qed.

(** Any two nested LT runs have the same result and exact callback receipt. *)
Theorem audit_lt_nested_unique : audit_lt_nested_unique_statement.
Proof.
  intros V E B enc source r semis first first_events second second_events.
  unfold audit_lt_nested_run.
  destruct (audit_lt_nested_buckets enc semis (preorder r) Map.empty)
    as [buckets bucket_events].
  intros [settled [here [Hfirst Hresult]]] [settled' [later [Hsecond Hresult']]].
  destruct (audit_lt_nested_reverse_fold_unique _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfirst Hsecond)
    as [Hstate Hevents].
  subst settled' later.
  destruct (audit_lt_nested_correct_fold enc semis (LtState.parents settled) (preorder r) Map.empty)
    as [result events].
  destruct Hresult as [-> ->]; destruct Hresult' as [-> ->]; split; reflexivity.
Qed.

(** * Erasure to the source computation *)

(** Bucket construction uses the same lookups and updates as the source fold. *)
Lemma audit_lt_nested_buckets_erases V E B (EV : encoding V) enc semis vertices buckets :
  (forall v, fst (enc v) = encode EV v) ->
  fst (audit_lt_nested_buckets (E := E) (B := B) enc semis vertices buckets) =
    fold_left (lt_bucket_insert EV semis) vertices buckets.
Proof.
  intro Hencode; revert buckets.
  induction vertices as [|v rest IH]; intro buckets; cbn [audit_lt_nested_buckets fold_left].
  - reflexivity.
  - pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Hget.
    destruct (audit_map_get enc v semis) as [found reads] eqn:Hread; cbn in Hget.
    unfold lt_bucket_insert; rewrite <- Hget.
    destruct found as [s|].
    + pose proof (audit_map_get_erases V (list V) B enc EV s buckets (Hencode s)) as Hbucket.
      destruct (audit_map_get enc s buckets) as [old bucket_events] eqn:Hbucket_run.
      cbn in Hbucket; unfold lt_bucket; rewrite <- Hbucket.
      pose proof (audit_map_set_erases V (list V) B enc EV s
        (v :: match old with
              | Some xs => xs
              | None => nil
              end) buckets (Hencode s)) as Hset.
      destruct (audit_map_set enc s (v :: match old with
                                        | Some xs => xs
                                        | None => nil
                                        end) buckets)
        as [next writes] eqn:Hset_run.
      cbn in Hset; rewrite <- Hset.
      destruct (audit_lt_nested_buckets enc semis rest next) as [result events] eqn:Hrun.
      specialize (IH next); rewrite Hrun in IH; exact IH.
    + destruct (audit_lt_nested_buckets enc semis rest buckets) as [result events] eqn:Hrun.
      specialize (IH buckets); rewrite Hrun in IH; exact IH.
Qed.

(** A nested bucket member returns the source member step. *)
Lemma audit_lt_nested_member_erases V E B (EV : encoding V) enc (r : dfs_result V E)
    semis s st v :
  (forall x, fst (enc x) = encode EV x) ->
  exists events, audit_lt_nested_member_run (B := B) enc r semis s st v
    (lt_bucket_member EV r semis s st v) events.
Proof.
  intro Hencode.
  destruct (audit_semi_nested_compress_erasure V E B EV enc r semis (LtState.links st) v Hencode)
    as [result [inner [Hrun Herase]]].
  destruct result as [links [root part]].
  pose proof (audit_semi_nested_score_erases V E B EV enc r semis
    (match part with
     | Some best => best
     | None => v
     end) Hencode) as Hscore.
  destruct (audit_semi_nested_score enc r semis (match part with
                                               | Some best => best
                                               | None => v
                                               end))
    as [score score_events] eqn:Hscore_run; cbn in Hscore.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r s (Hencode s)) as Hrank.
  destruct (audit_semi_nested_rank enc r s) as [rank rank_events] eqn:Hrank_run; cbn in Hrank.
  pose proof (proj1 (audit_positive_order score rank)) as Hcompare.
  destruct (audit_positive_ltb score rank) as [choose compare_events] eqn:Hcompare_run.
  cbn in Hcompare.
  pose proof (audit_map_set_erases V V B enc EV v
    (if choose then match part with
                    | Some best => best
                    | None => v
                    end else s)
    (LtState.parents st) (Hencode v)) as Hset.
  destruct (audit_map_set enc v
    (if choose then match part with
                    | Some best => best
                    | None => v
                    end else s)
    (LtState.parents st)) as [parents set_events] eqn:Hset_run; cbn in Hset.
  eexists.
  replace (lt_bucket_member EV r semis s st v) with (LtState.Make links parents).
  - eapply LtNestedMember; try eassumption; reflexivity.
  - unfold lt_bucket_member, semi_eval; rewrite <- Herase; cbn.
    rewrite <- Hscore, <- Hrank, <- Hcompare, <- Hset; reflexivity.
Qed.

(** A nested member fold returns the source fold over the same ordered bucket. *)
Lemma audit_lt_nested_members_erases V E B (EV : encoding V) enc (r : dfs_result V E)
    semis s vertices st :
  (forall x, fst (enc x) = encode EV x) ->
  exists events, audit_lt_nested_members_run (B := B) enc r semis s vertices st
    (fold_left (lt_bucket_member EV r semis s) vertices st) events.
Proof.
  intro Hencode; revert st.
  induction vertices as [|v rest IH]; intro st.
  - eexists; constructor.
  - destruct (audit_lt_nested_member_erases V E B EV enc r semis s st v Hencode)
      as [here Hstep].
    destruct (IH (lt_bucket_member EV r semis s st v)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** A nested reverse step returns the source state and records the actual source callback. *)
Lemma audit_lt_nested_reverse_erases V E B (EV : encoding V) (g : Graph.t V E) enc source
    (r : dfs_result V E) semis buckets st s :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_lt_nested_reverse_run (B := B) enc source r semis buckets st s
    (lt_reverse_step EV g r semis buckets st s) events.
Proof.
  intros Hencode Hsource.
  pose proof (audit_map_get_erases V (list V) B enc EV s buckets (Hencode s)) as Hbucket.
  destruct (audit_map_get enc s buckets) as [bucket bucket_events] eqn:Hbucket_run.
  cbn in Hbucket.
  unfold lt_reverse_step, lt_bucket; rewrite <- Hbucket.
  destruct (audit_lt_nested_members_erases V E B EV enc r semis s
    (match bucket with
     | Some xs => xs
     | None => nil
     end) st Hencode) as [events Hmembers].
  pose proof (audit_map_get_erases V E B enc EV s (tree_edge r) (Hencode s)) as Htree.
  destruct (audit_map_get enc s (tree_edge r)) as [edge tree_events] eqn:Htree_run.
  cbn in Htree; rewrite <- Htree.
  destruct edge as [edge|].
  - pose proof (Hsource edge) as Hsrc.
    destruct (source edge) as [parent body] eqn:Hsource_run; cbn in Hsrc.
    rewrite <- Hsrc.
    pose proof (audit_semi_producer_link_erases V E B EV enc
      (LtState.links (fold_left (lt_bucket_member EV r semis s)
        (match bucket with
         | Some xs => xs
         | None => nil
         end) st)) s parent (Hencode s)) as Hlink.
    destruct (audit_semi_producer_link (E := E) enc
      (LtState.links (fold_left (lt_bucket_member EV r semis s)
        (match bucket with
         | Some xs => xs
         | None => nil
         end) st)) s parent)
      as [links link_events] eqn:Hlink_run; cbn in Hlink; rewrite <- Hlink.
    eexists; eapply LtNestedReverseNode; try eassumption; reflexivity.
  - eexists; eapply LtNestedReverseRoot; try eassumption; reflexivity.
Qed.

(** The nested reverse fold erases to the source fold in the same order. *)
Lemma audit_lt_nested_reverse_fold_erases V E B (EV : encoding V) (g : Graph.t V E)
    enc source (r : dfs_result V E) semis buckets vertices st :
  (forall x, fst (enc x) = encode EV x) ->
  (forall e, fst (source e) = Graph.source g e) ->
  exists events, audit_lt_nested_reverse_fold_run (B := B) enc source r semis buckets vertices st
    (fold_left (lt_reverse_step EV g r semis buckets) vertices st) events.
Proof.
  intros Hencode Hsource; revert st.
  induction vertices as [|v rest IH]; intro st.
  - eexists; constructor.
  - destruct (audit_lt_nested_reverse_erases V E B EV g enc source r semis buckets st v
      Hencode Hsource) as [here Hstep].
    destruct (IH (lt_reverse_step EV g r semis buckets st v)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** Nested correction preserves both equality branches and the source lookup defaults. *)
Lemma audit_lt_nested_correct_erases V E B (EV : encoding V) enc semis provisional corrected v :
  (forall x, fst (enc x) = encode EV x) ->
  fst (audit_lt_nested_correct (E := E) (B := B) enc semis provisional corrected v) =
    lt_correct_step EV semis provisional corrected v.
Proof.
  intro Hencode.
  pose proof (audit_map_get_erases V V B enc EV v provisional (Hencode v)) as Hfirst.
  unfold audit_lt_nested_correct, lt_correct_step.
  destruct (audit_map_get enc v provisional) as [found first] eqn:Hfirst_run; cbn in Hfirst.
  rewrite <- Hfirst; destruct found as [u|]; [|reflexivity].
  pose proof (Hencode u) as Hu.
  destruct (enc u) as [a a_body] eqn:Hu_run; cbn in Hu.
  pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Hvalue.
  destruct (audit_map_get enc v semis) as [value value_events] eqn:Hvalue_run; cbn in Hvalue.
  unfold semi_value; rewrite <- Hvalue.
  pose proof (Hencode (match value with
                      | Some x => x
                      | None => v
                      end)) as Hv.
  destruct (enc (match value with
                 | Some x => x
                 | None => v
                 end)) as [b b_body] eqn:Hv_run.
  cbn in Hv.
  pose proof (audit_positive_eqb_erases a b) as Hequal.
  destruct (audit_positive_eqb a b) as [equal equal_events] eqn:Hequal_run; cbn in Hequal.
  rewrite <- Hu, <- Hv, <- Hequal.
  destruct equal.
  - pose proof (audit_map_set_erases V V B enc EV v u corrected (Hencode v)) as Hset.
    destruct (audit_map_set enc v u corrected) as [result events]; exact Hset.
  - pose proof (audit_map_get_erases V V B enc EV u corrected (Hencode u)) as Hparent.
    destruct (audit_map_get enc u corrected) as [parent parent_events] eqn:Hparent_run.
    cbn in Hparent; unfold semi_value; rewrite <- Hparent.
    pose proof (audit_map_set_erases V V B enc EV v
      (match parent with
       | Some x => x
       | None => u
       end) corrected (Hencode v)) as Hset.
    destruct (audit_map_set enc v (match parent with
                                  | Some x => x
                                  | None => u
                                  end) corrected)
      as [result events]; exact Hset.
Qed.

(** Nested correction folds return the source map for arbitrary input maps and order. *)
Lemma audit_lt_nested_correct_fold_erases V E B (EV : encoding V) enc semis provisional
    vertices corrected :
  (forall x, fst (enc x) = encode EV x) ->
  fst (audit_lt_nested_correct_fold (E := E) (B := B) enc semis provisional vertices corrected) =
    fold_left (lt_correct_step EV semis provisional) vertices corrected.
Proof.
  intro Hencode; revert corrected.
  induction vertices as [|v rest IH]; intro corrected; cbn [audit_lt_nested_correct_fold fold_left].
  - reflexivity.
  - pose proof (audit_lt_nested_correct_erases V E B EV enc semis provisional corrected v Hencode)
      as Hstep.
    destruct (audit_lt_nested_correct enc semis provisional corrected v) as [middle here].
    cbn in Hstep; rewrite <- Hstep.
    destruct (audit_lt_nested_correct_fold enc semis provisional rest middle) as [result later]
      eqn:Hrun.
    specialize (IH middle); rewrite Hrun in IH; exact IH.
Qed.

(** The nested LT run returns the source result with its same-run callback receipts. *)
Theorem audit_lt_nested_erasure : audit_lt_nested_erasure_statement.
Proof.
  intros V E B EV g r semis enc source Hencode Hsource.
  pose proof (audit_lt_nested_buckets_erases V E B EV enc semis (preorder r) Map.empty Hencode)
    as Hbuckets.
  destruct (audit_lt_nested_buckets enc semis (preorder r) Map.empty) as [buckets bucket_events]
    eqn:Hbucket_run; cbn in Hbuckets.
  destruct (audit_lt_nested_reverse_fold_erases V E B EV g enc source r semis buckets
    (rev (preorder r)) (LtState.Make semi_links_empty Map.empty) Hencode Hsource) as [events Hrun].
  pose proof (audit_lt_nested_correct_fold_erases V E B EV enc semis
    (LtState.parents (fold_left (lt_reverse_step EV g r semis buckets) (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty))) (preorder r) Map.empty Hencode) as Hcorrect.
  destruct (audit_lt_nested_correct_fold enc semis
    (LtState.parents (fold_left (lt_reverse_step EV g r semis buckets) (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty))) (preorder r) Map.empty) as [result correction]
    eqn:Hcorrect_run; cbn in Hcorrect.
  exists result, (bucket_events ++ [LtNestedOutput (length (preorder r))] ++ events ++ correction).
  split.
  - unfold audit_lt_nested_run; rewrite Hbucket_run.
    eexists; exists events; split; [exact Hrun|].
    rewrite Hcorrect_run; split; reflexivity.
  - unfold lt_compute, lt_provisional, lt_bucket_index; rewrite <- Hbuckets; exact Hcorrect.
Qed.

(** Virtual LT retains the same prepared graph, search, semidominators and parent erasure. *)
Theorem audit_virtual_lt_erasure : audit_virtual_lt_erasure_statement.
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
  unfold audit_virtual_lt_run, audit_virtual_full_search_with_prepared.
  destruct (audit_graph_prepare_nested_counted (virtual_encoding EV) (virtual_graph EV g)
    (audit_virtual_full_prepare_callbacks g cb)) as [vp prepare_events] eqn:Hprep_run.
  cbn in Hprepared; destruct Hprepared as [Hprepared _].
  change (vp = virtual_prepared p) in Hprepared; subst vp.
  destruct (audit_dfs_nested_counted (virtual_prepared p) (audit_virtual_full_dfs_callbacks cb)
    FinSet.empty [inr tt]) as [search dfs_events] eqn:Hdfs_run.
  cbn in Hsearch; subst search.
  destruct (audit_semi_producer_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (virtual_dfs p) (audit_virtual_full_encode cb)
    (audit_virtual_full_source source) Hencode Hsource_full) as [semis [semi_events [Hsemi ->]]].
  destruct (audit_lt_nested_erasure _ _ _ (virtual_encoding EV) (virtual_graph EV g)
    (virtual_dfs p) (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))
    (audit_virtual_full_encode cb) (audit_virtual_full_source source) Hencode Hsource_full)
    as [parents [lt_events [Hlt ->]]].
  destruct Hcallbacks as [_ [_ Hbase]].
  pose proof (audit_erase_nested_correct V B EV (audit_virtual_base_encode cb) (fun _ => 0)
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))) Hbase) as Herase.
  destruct (audit_erase_virtual_nested (audit_virtual_base_encode cb)
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))))
    as [result erase_events] eqn:Herase_run.
  cbn [fst snd] in Herase; destruct Herase as [Hresult _].
  exists result, semi_events, lt_events, erase_events; split.
  - exists (semi_compute (virtual_prepared p) (virtual_dfs p)),
      (lt_compute (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
        (SemiState.result (semi_compute (virtual_prepared p) (virtual_dfs p)))).
    split; [exact Hsemi|].
    split; [exact Hlt|exact Herase_run].
  - unfold simple_lt_idom, virtual_dfs in Hresult |- *; exact Hresult.
Qed.

(** * Bounds on bucket sizes and event counts *)

(** One insertion increases any bucket's length by at most one. *)
Lemma audit_lt_bucket_insert_length V (EV : encoding V) semis buckets v s :
  length (lt_bucket EV (lt_bucket_insert EV semis buckets v) s) <=
    S (length (lt_bucket EV buckets s)).
Proof.
  unfold lt_bucket_insert; destruct (Map.get EV v semis) as [target|].
  - destruct (dfs_eq_dec EV s target) as [Heq|Hne].
    + subst target; unfold lt_bucket at 1; rewrite Map.get_set_same; cbn; lia.
    + unfold lt_bucket at 1; rewrite Map.get_set_other by exact Hne.
      fold (lt_bucket EV buckets s); lia.
  - lia.
Qed.

(** A fold grows each bucket by at most the number of vertices processed. *)
Lemma audit_lt_bucket_fold_length V (EV : encoding V) semis vertices buckets s :
  length (lt_bucket EV (fold_left (lt_bucket_insert EV semis) vertices buckets) s) <=
    length vertices + length (lt_bucket EV buckets s).
Proof.
  revert buckets; induction vertices as [|v rest IH]; intro buckets; cbn [fold_left length].
  - lia.
  - specialize (IH (lt_bucket_insert EV semis buckets v)).
    pose proof (audit_lt_bucket_insert_length V EV semis buckets v s) as Hstep; lia.
Qed.

(** The indexed bucket is bounded by the original preorder length, including duplicates. *)
Lemma audit_lt_bucket_index_length V (EV : encoding V) semis vertices s :
  length (lt_bucket EV (lt_bucket_index EV semis vertices) s) <= length vertices.
Proof.
  unfold lt_bucket_index.
  pose proof (audit_lt_bucket_fold_length V EV semis vertices Map.empty s) as Hbound.
  assert (Hempty : lt_bucket EV Map.empty s = []).
  { unfold lt_bucket; now rewrite Map.get_empty. }
  rewrite Hempty in Hbound; cbn in Hbound; lia.
Qed.

(** One nested member charges compression and a constant number of outer operations. *)
Lemma audit_lt_nested_member_count V E B (EV : encoding V) enc (r : dfs_result V E)
    semis s st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_lt_nested_member_run (B := B) enc r semis s st v result events ->
  length events <= 20 * S (audit_semi_producer_input_rank r) + 6.
Proof.
  intros Hencode Hrun; inversion Hrun; subst.
  match goal with
  | Hcompress : audit_semi_nested_compress_run _ _ _ _ _ _ ?inner,
    Hscore : audit_semi_nested_score _ _ _ ?score_arg = (_, ?score_events),
    Hrank : audit_semi_nested_rank _ _ _ = (_, ?rank_events),
    Hset : audit_map_set _ _ ?set_value _ = (_, ?set_events) |- _ =>
    pose proof (audit_semi_nested_compress_count V E B EV enc r semis (LtState.links st)
      v _ inner Hencode Hcompress) as Hcount;
    pose proof (audit_semi_rank_in_producer V E EV r v) as Hrank_bound;
    pose proof (audit_semi_nested_score_length V E B enc r semis score_arg) as Hscore_length;
    pose proof (proj1 (audit_semi_nested_reads_length V E B enc r semi_links_empty s))
      as Hrank_length;
    pose proof (audit_semi_map_set_length V V B enc v set_value (LtState.parents st))
      as Hset_length;
    rewrite Hscore in Hscore_length; rewrite Hrank in Hrank_length; rewrite Hset in Hset_length;
    cbn in Hscore_length, Hrank_length, Hset_length;
    repeat rewrite length_app; repeat rewrite length_map; cbn; lia
  end.
Qed.

(** The nested member fold charges at most one bounded member receipt per list entry. *)
Lemma audit_lt_nested_members_count V E B (EV : encoding V) enc (r : dfs_result V E)
    semis s vertices st result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_lt_nested_members_run (B := B) enc r semis s vertices st result events ->
  length events <= 1 + length vertices * (20 * S (audit_semi_producer_input_rank r) + 7).
Proof.
  intros Hencode Hrun; induction Hrun.
  - cbn; lia.
  - pose proof (audit_lt_nested_member_count V E B EV enc r semis s initial v middle here
      Hencode H) as Hhere.
    cbn [length]; rewrite length_app; nia.
Qed.

(** Each reverse step reads one bucket of the original indexed size. *)
Lemma audit_lt_nested_reverse_count V E B (EV : encoding V) enc source (r : dfs_result V E)
    semis buckets st s result events limit :
  (forall x, fst (enc x) = encode EV x) ->
  length (lt_bucket EV buckets s) <= limit ->
  audit_lt_nested_reverse_run (B := B) enc source r semis buckets st s result events ->
  length events <= 8 + limit * (20 * S (audit_semi_producer_input_rank r) + 7).
Proof.
  intros Hencode Hbucket Hrun; inversion Hrun; subst.
  all: match goal with
    | Hget : audit_map_get _ _ _ = (?bucket, ?reads),
      Hmembers : audit_lt_nested_members_run _ _ _ _ ?members _ _ ?member_events,
      Htree : audit_map_get _ _ (tree_edge ?dfs) = (_, ?tree_events) |- _ =>
      pose proof (audit_map_get_erases V (list V) B enc EV s buckets (Hencode s)) as Herase;
      rewrite Hget in Herase; cbn in Herase;
      pose proof (audit_semi_map_get_length V (list V) B enc s buckets) as Hreads;
      rewrite Hget in Hreads; cbn in Hreads;
      pose proof (audit_semi_map_get_length V E B enc s (tree_edge dfs)) as Htrees;
      rewrite Htree in Htrees; cbn in Htrees;
      pose proof (audit_lt_nested_members_count V E B EV enc dfs semis s members _ _ member_events
        Hencode Hmembers) as Hcount;
      unfold lt_bucket in Hbucket; rewrite <- Herase in Hbucket
    end.
  - repeat rewrite length_app; repeat rewrite length_map; cbn; nia.
  - match goal with
    | Hlink : audit_semi_producer_link _ ?linkstate _ ?parent = (_, ?link_events) |- _ =>
      pose proof (audit_semi_producer_link_details V E B EV enc (fun _ => 0)
        (Pos.size_nat (encode EV s)) linkstate s parent (Hencode s) (Nat.le_refl _)) as [Hlinks _];
      rewrite Hlink in Hlinks; cbn in Hlinks
    end.
    repeat rewrite length_app; repeat rewrite length_map; cbn; nia.
Qed.

(** Reverse traversal charges one bounded step for every listed vertex. *)
Lemma audit_lt_nested_reverse_fold_count V E B (EV : encoding V) enc source (r : dfs_result V E)
    semis buckets vertices st result events limit :
  (forall x, fst (enc x) = encode EV x) ->
  (forall s, length (lt_bucket EV buckets s) <= limit) ->
  audit_lt_nested_reverse_fold_run (B := B) enc source r semis buckets vertices st result events ->
  length events <= 1 + length vertices *
    (9 + limit * (20 * S (audit_semi_producer_input_rank r) + 7)).
Proof.
  intros Hencode Hbucket Hrun; induction Hrun.
  - cbn; lia.
  - pose proof (audit_lt_nested_reverse_count V E B EV enc source r semis buckets initial v middle
      here limit Hencode (Hbucket v) H) as Hhere.
    cbn [length]; rewrite length_app; nia.
Qed.

(** Nested bucket indexing records at most five events per input vertex. *)
Lemma audit_lt_nested_buckets_count V E B enc semis vertices buckets :
  length (snd (audit_lt_nested_buckets (V := V) (E := E) (B := B) enc semis vertices buckets)) <=
    1 + 5 * length vertices.
Proof.
  revert buckets; induction vertices as [|v rest IH]; intro buckets; cbn [audit_lt_nested_buckets].
  - cbn; lia.
  - pose proof (audit_semi_map_get_length V V B enc v semis) as Hget.
    destruct (audit_map_get enc v semis) as [found reads] eqn:Hread; cbn in Hget.
    destruct found as [s|].
    + pose proof (audit_semi_map_get_length V (list V) B enc s buckets) as Hbucket.
      destruct (audit_map_get enc s buckets) as [old bucket_events]; cbn in Hbucket.
      pose proof (audit_semi_map_set_length V (list V) B enc s
        (v :: match old with
              | Some xs => xs
              | None => []
              end) buckets) as Hset.
      destruct (audit_map_set enc s (v :: match old with
                                        | Some xs => xs
                                        | None => []
                                        end) buckets)
        as [next writes]; cbn in Hset.
      specialize (IH next).
      destruct (audit_lt_nested_buckets enc semis rest next) as [result later]; cbn in IH |- *.
      repeat rewrite length_app; repeat rewrite length_map; cbn;
      repeat rewrite length_app; repeat rewrite length_map; cbn; lia.
    + specialize (IH buckets).
      destruct (audit_lt_nested_buckets enc semis rest buckets) as [result later]; cbn in IH |- *.
      repeat rewrite length_app; repeat rewrite length_map; cbn;
      repeat rewrite length_app; repeat rewrite length_map; cbn; lia.
Qed.

(** Correction emits at most eight events, including both possible parent lookups. *)
Lemma audit_lt_nested_correct_count V E B enc semis provisional corrected v :
  length (snd (audit_lt_nested_correct (V := V) (E := E) (B := B) enc semis provisional
    corrected v)) <= 8.
Proof.
  unfold audit_lt_nested_correct.
  pose proof (audit_semi_map_get_length V V B enc v provisional) as Hfirst.
  destruct (audit_map_get enc v provisional) as [found first]; cbn in Hfirst.
  destruct found as [u|].
  - destruct (enc u) as [a a_body].
    pose proof (audit_semi_map_get_length V V B enc v semis) as Hvalue.
    destruct (audit_map_get enc v semis) as [value value_events]; cbn in Hvalue.
    destruct (enc (match value with
                   | Some x => x
                   | None => v
                   end)) as [b b_body].
    destruct (audit_positive_eqb a b) as [equal equal_events].
    destruct equal.
    + pose proof (audit_semi_map_set_length V V B enc v u corrected) as Hset.
      destruct (audit_map_set enc v u corrected) as [result writes]; cbn in Hset |- *.
      repeat (first [rewrite length_app | rewrite length_map | progress cbn [length]]); lia.
    + pose proof (audit_semi_map_get_length V V B enc u corrected) as Hparent.
      destruct (audit_map_get enc u corrected) as [parent parent_events]; cbn in Hparent.
      pose proof (audit_semi_map_set_length V V B enc v
        (match parent with
         | Some x => x
         | None => u
         end) corrected) as Hset.
      destruct (audit_map_set enc v (match parent with
                                    | Some x => x
                                    | None => u
                                    end) corrected)
        as [result writes]; cbn in Hset |- *.
      repeat (first [rewrite length_app | rewrite length_map | progress cbn [length]]); lia.
  - cbn; rewrite length_app, length_map; cbn; lia.
Qed.

(** The forward correction fold charges each visited vertex once. *)
Lemma audit_lt_nested_correct_fold_count V E B enc semis provisional vertices corrected :
  length (snd (audit_lt_nested_correct_fold (V := V) (E := E) (B := B) enc semis provisional
    vertices corrected)) <= 1 + 9 * length vertices.
Proof.
  revert corrected; induction vertices as [|v rest IH]; intro corrected;
    cbn [audit_lt_nested_correct_fold].
  - cbn; lia.
  - pose proof (audit_lt_nested_correct_count V E B enc semis provisional corrected v) as Hhere.
    destruct (audit_lt_nested_correct enc semis provisional corrected v) as [middle here];
      cbn in Hhere.
    specialize (IH middle).
    destruct (audit_lt_nested_correct_fold enc semis provisional rest middle) as [result later];
      cbn in IH |- *.
    rewrite length_app; cbn; lia.
Qed.

(** Every nested LT run fits its input-derived event-count allowance. *)
Lemma audit_lt_nested_run_count V E B (EV : encoding V) (g : Graph.t V E) enc source
    (r : dfs_result V E) semis result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_lt_nested_run (B := B) enc source r semis result events ->
  length events <= audit_lt_nested_input_event_bound r.
Proof.
  intros Hencode Hrun; unfold audit_lt_nested_run in Hrun.
  pose proof (audit_lt_nested_buckets_erases V E B EV enc semis (preorder r) Map.empty Hencode)
    as Herase.
  pose proof (audit_lt_nested_buckets_count V E B enc semis (preorder r) Map.empty) as Hbuild.
  destruct (audit_lt_nested_buckets enc semis (preorder r) Map.empty) as [buckets bucket_events]
    eqn:Hbucket; cbn in Herase, Hbuild.
  destruct Hrun as [settled [reverse_events [Hreverse Hrun]]].
  pose proof (audit_lt_nested_reverse_fold_count V E B EV enc source r semis buckets
    (rev (preorder r)) (LtState.Make semi_links_empty Map.empty) settled reverse_events
    (length (preorder r)) Hencode) as Hrev.
  assert (Hbucket_bound : forall s, length (lt_bucket EV buckets s) <= length (preorder r)).
  { intro s; rewrite Herase; apply audit_lt_bucket_index_length. }
  specialize (Hrev Hbucket_bound Hreverse); rewrite length_rev in Hrev.
  pose proof (audit_lt_nested_correct_fold_count V E B enc semis (LtState.parents settled)
    (preorder r) Map.empty) as Hcorrect.
  destruct (audit_lt_nested_correct_fold enc semis (LtState.parents settled) (preorder r) Map.empty)
    as [output correction]; cbn in Hcorrect, Hrun.
  destruct Hrun as [_ ->].
  repeat rewrite length_app; cbn [length].
  rewrite length_app.
  unfold audit_lt_nested_input_event_bound.
  pose proof (Nat.le_0_l (audit_semi_producer_input_rank r)); nia.
Qed.

(** * Ordinary traversal erasure *)

(** Ordinary bucket indexing agrees with the same source fold. *)
Lemma audit_lt_buckets_erases V E (EV : encoding V) semis vertices buckets :
  fst (audit_lt_buckets_counted (E := E) EV semis vertices buckets) =
    fold_left (lt_bucket_insert EV semis) vertices buckets.
Proof.
  revert buckets; induction vertices as [|v rest IH]; intro buckets;
    cbn [audit_lt_buckets_counted fold_left].
  - reflexivity.
  - unfold lt_bucket_insert.
    destruct (Map.get EV v semis) as [s|].
    + unfold lt_bucket; destruct (Map.get EV s buckets) as [old|].
      * specialize (IH (Map.set EV s (v :: old) buckets)).
        destruct (audit_lt_buckets_counted EV semis rest (Map.set EV s (v :: old) buckets));
          exact IH.
      * specialize (IH (Map.set EV s [v] buckets)).
        destruct (audit_lt_buckets_counted EV semis rest (Map.set EV s [v] buckets)); exact IH.
    + specialize (IH buckets); destruct (audit_lt_buckets_counted EV semis rest buckets); exact IH.
Qed.

(** An ordinary member run returns the same state as the source member step. *)
Lemma audit_lt_member_erases V E (EV : encoding V) (r : dfs_result V E) semis s st v :
  exists events, audit_lt_member_run EV r semis s st v (lt_bucket_member EV r semis s st v) events.
Proof.
  destruct (audit_semi_compress_erases V E EV r semis (LtState.links st) v) as [inner Hrun].
  destruct (semi_compress EV (semi_rank EV r)
    (fun x => semi_rank EV r (semi_value EV semis x)) (LtState.links st) v)
    as [links [root part]] eqn:Hcompress.
  pose proof (audit_semi_score_counted_erases V E EV r semis
    (match part with
     | Some best => best
     | None => v
     end)) as Hscore.
  destruct (audit_semi_score_counted EV r semis (match part with
                                                 | Some best => best
                                                 | None => v
                                                 end))
    as [score score_events] eqn:Hscore_run; cbn in Hscore.
  pose proof (audit_semi_rank_counted_erases V E EV r s) as Hrank.
  destruct (audit_semi_rank_counted EV r s) as [rank rank_events] eqn:Hrank_run; cbn in Hrank.
  eexists.
  unfold lt_bucket_member, semi_eval; rewrite Hcompress; cbn.
  rewrite <- Hscore, <- Hrank.
  eapply AuditLtMember; try eassumption; reflexivity.
Qed.

(** The ordinary member fold follows the source fold over the bucket. *)
Lemma audit_lt_members_erases V E (EV : encoding V) (r : dfs_result V E) semis s vertices st :
  exists events, audit_lt_members_run EV r semis s vertices st
    (fold_left (lt_bucket_member EV r semis s) vertices st) events.
Proof.
  revert st; induction vertices as [|v rest IH]; intro st.
  - eexists; constructor.
  - destruct (audit_lt_member_erases V E EV r semis s st v) as [here Hstep].
    destruct (IH (lt_bucket_member EV r semis s st v)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** A reverse step records its actual tree lookup and source edge. *)
Lemma audit_lt_reverse_erases V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis buckets st s :
  exists events, audit_lt_reverse_run EV g r semis buckets st s
    (lt_reverse_step EV g r semis buckets st s) events.
Proof.
  unfold lt_reverse_step, lt_bucket.
  destruct (Map.get EV s buckets) as [members|] eqn:Hbucket.
  - destruct (audit_lt_members_erases V E EV r semis s members st) as [events Hmembers].
    destruct (Map.get EV s (tree_edge r)) as [edge|] eqn:Htree.
    + eexists; eapply AuditLtReverseNode; try eassumption; try reflexivity;
        rewrite Hbucket; reflexivity.
    + eexists; eapply AuditLtReverseRoot; try eassumption; try reflexivity;
        rewrite Hbucket; reflexivity.
  - destruct (audit_lt_members_erases V E EV r semis s [] st) as [events Hmembers].
    destruct (Map.get EV s (tree_edge r)) as [edge|] eqn:Htree.
    + eexists; eapply AuditLtReverseNode; try eassumption; try reflexivity;
        rewrite Hbucket; reflexivity.
    + eexists; eapply AuditLtReverseRoot; try eassumption; try reflexivity;
        rewrite Hbucket; reflexivity.
Qed.

(** The ordinary reverse traversal follows the source fold. *)
Lemma audit_lt_reverse_fold_erases V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis buckets vertices st :
  exists events, audit_lt_reverse_fold_run EV g r semis buckets vertices st
    (fold_left (lt_reverse_step EV g r semis buckets) vertices st) events.
Proof.
  revert st; induction vertices as [|v rest IH]; intro st.
  - eexists; constructor.
  - destruct (audit_lt_reverse_erases V E EV g r semis buckets st v) as [here Hstep].
    destruct (IH (lt_reverse_step EV g r semis buckets st v)) as [later Hrest].
    cbn [fold_left]; eexists; econstructor; eassumption.
Qed.

(** Counted correction retains the source defaults on both equality branches. *)
Lemma audit_lt_correct_erases V E (EV : encoding V) semis provisional corrected v :
  fst (audit_lt_correct_counted (E := E) EV semis provisional corrected v) =
    lt_correct_step EV semis provisional corrected v.
Proof.
  unfold audit_lt_correct_counted, lt_correct_step.
  destruct (Map.get EV v provisional) as [u|]; [|reflexivity].
  pose proof (audit_semi_value_counted_details V EV semis v) as [Hvalue _].
  destruct (audit_semi_value_counted EV semis v) as [value value_events]; cbn in Hvalue.
  rewrite <- Hvalue.
  destruct (Pos.eqb (encode EV u) (encode EV value)); [reflexivity|].
  pose proof (audit_semi_value_counted_details V EV corrected u) as [Hparent _].
  destruct (audit_semi_value_counted EV corrected u) as [parent parent_events]; cbn in Hparent.
  now rewrite Hparent.
Qed.

(** Counted correction folds return the source map on arbitrary provisional maps. *)
Lemma audit_lt_correct_fold_erases V E (EV : encoding V) semis provisional vertices corrected :
  fst (audit_lt_correct_fold (E := E) EV semis provisional vertices corrected) =
    fold_left (lt_correct_step EV semis provisional) vertices corrected.
Proof.
  revert corrected; induction vertices as [|v rest IH]; intro corrected;
    cbn [audit_lt_correct_fold fold_left].
  - reflexivity.
  - pose proof (audit_lt_correct_erases V E EV semis provisional corrected v) as Hstep.
    destruct (audit_lt_correct_counted EV semis provisional corrected v) as [middle here].
    cbn in Hstep; rewrite <- Hstep.
    specialize (IH middle).
    destruct (audit_lt_correct_fold EV semis provisional rest middle) as [result later]; exact IH.
Qed.

(** The ordinary LT relation admits the exact source result and its receipt. *)
Lemma audit_lt_compute_erases V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis :
  exists events, audit_lt_compute_run EV g r semis (lt_compute EV g r semis) events.
Proof.
  pose proof (audit_lt_buckets_erases V E EV semis (preorder r) Map.empty) as Hbuckets.
  destruct (audit_lt_buckets_counted EV semis (preorder r) Map.empty) as [buckets bucket_events]
    eqn:Hbucket; cbn in Hbuckets.
  destruct (audit_lt_reverse_fold_erases V E EV g r semis buckets (rev (preorder r))
    (LtState.Make semi_links_empty Map.empty)) as [events Hrun].
  pose proof (audit_lt_correct_fold_erases V E EV semis
    (LtState.parents (fold_left (lt_reverse_step EV g r semis buckets) (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty))) (preorder r) Map.empty) as Hcorrect.
  destruct (audit_lt_correct_fold EV semis
    (LtState.parents (fold_left (lt_reverse_step EV g r semis buckets) (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty))) (preorder r) Map.empty) as [result correction]
    eqn:Hcorrect_run; cbn in Hcorrect.
  exists (bucket_events ++ [AuditLtOutput (length (preorder r))] ++ events ++ correction).
  unfold audit_lt_compute_run; rewrite Hbucket.
  eexists; exists events; split; [exact Hrun|].
  rewrite Hcorrect_run; split; [|reflexivity].
  unfold lt_compute, lt_provisional, lt_bucket_index; rewrite <- Hbuckets; symmetry; exact Hcorrect.
Qed.

(** * Original-input vertex envelope *)

(** The envelope contains the original order, map rows and indexed tree-edge sources. *)
Definition audit_lt_input_vertex V E (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (v : V) : Prop :=
  In v (preorder r ++ map fst (Map.elements semis) ++ map snd (Map.elements semis) ++
    map fst (Map.elements (tree_edge r)) ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++
    map fst (Map.elements (pre_num r))).

(** Each vertex in that envelope fits the nested input key-width allowance. *)
Lemma audit_lt_input_vertex_width V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis v :
  audit_lt_input_vertex V E g r semis v ->
  Pos.size_nat (encode EV v) <= audit_lt_nested_input_width EV g r semis.
Proof.
  intro Hin; unfold audit_lt_input_vertex in Hin; unfold audit_lt_nested_input_width.
  eapply Nat.le_trans.
  - apply (audit_dfs_width_member (fun x : V => Pos.size_nat (encode EV x))); exact Hin.
  - apply Nat.le_max_l.
Qed.

(** Every semidominator map row is included even when its stored key is malformed. *)
Lemma audit_lt_semi_row V E (g : Graph.t V E) (r : dfs_result V E) semis key value :
  In (key, value) (Map.elements semis) ->
  audit_lt_input_vertex V E g r semis key /\ audit_lt_input_vertex V E g r semis value.
Proof.
  intro Hin; unfold audit_lt_input_vertex; split.
  - apply in_or_app; right; apply in_or_app; left.
    apply in_map_iff; exists (key, value); split; [reflexivity|exact Hin].
  - apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
    apply in_map_iff; exists (key, value); split; [reflexivity|exact Hin].
Qed.

(** Any vertex in a local compression input is covered by the original input envelope. *)
Lemma audit_lt_query_vertex V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis st start v :
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) st ->
  audit_lt_input_vertex V E g r semis start ->
  audit_semi_input_vertex V semis st start v -> audit_lt_input_vertex V E g r semis v.
Proof.
  intros [Hshortcut Hlabels] Hstart [Heq|[key Hin]]; [now subst v|].
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - exact (proj2 (audit_semi_map_envelope_elements V EV _ _ key v Hshortcut Hin)).
  - apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + exact (proj2 (audit_semi_map_envelope_elements V EV _ _ key v Hlabels Hin)).
    + exact (proj2 (audit_lt_semi_row V E g r semis key v Hin)).
Qed.

(** The local compression width is no larger than the input-derived LT width. *)
Lemma audit_lt_query_width V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis st v :
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) st ->
  audit_lt_input_vertex V E g r semis v ->
  audit_semi_nested_width EV r semis st v <= audit_lt_nested_input_width EV g r semis.
Proof.
  intros [Hshortcut Hlabels] Hv.
  set (rows := Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
    Map.elements semis).
  assert (Hrows : forall key value, In (key, value) rows ->
    audit_lt_input_vertex V E g r semis key /\ audit_lt_input_vertex V E g r semis value).
  { intros key value Hin; unfold rows in Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    - exact (audit_semi_map_envelope_elements V EV _ _ key value Hshortcut Hin).
    - apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      + exact (audit_semi_map_envelope_elements V EV _ _ key value Hlabels Hin).
      + exact (audit_lt_semi_row V E g r semis key value Hin). }
  unfold audit_semi_nested_width; fold rows; apply Nat.max_lub.
  - apply audit_semi_max_le; intros x Hin; cbn in Hin; destruct Hin as [Heq|Hin].
    + subst x; apply audit_lt_input_vertex_width; exact Hv.
    + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin; destruct Hin as [[key value] [Heq Hin]]; cbn in Heq; subst x.
        apply audit_lt_input_vertex_width; exact (proj1 (Hrows key value Hin)).
      * apply in_app_or in Hin; destruct Hin as [Hin|Hin].
        -- apply in_map_iff in Hin; destruct Hin as [[key value] [Heq Hin]]; cbn in Heq; subst x.
           apply audit_lt_input_vertex_width; exact (proj2 (Hrows key value Hin)).
        -- apply audit_lt_input_vertex_width; unfold audit_lt_input_vertex.
           do 5 (apply in_or_app; right); exact Hin.
  - unfold audit_lt_nested_input_width; apply Nat.le_max_r.
Qed.

(** Compression preserves the original-input envelope even for a malformed semidominator map. *)
Lemma audit_lt_compress_envelope V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis st v result events :
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) st ->
  audit_lt_input_vertex V E g r semis v ->
  audit_semi_compress_run EV r semis st v result events ->
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) (fst result).
Proof.
  intros Hlinks Hv Hrun.
  induction Hrun as
    [v Hget
    |v a ra rv ea ev Hget Hrank_a Hrank_v Hcompare
    |v a ra rv ea ev st' root inner label label_events Hget Hrank_a Hrank_v Hcompare Hrun IH Hlabel
    |v a ra rv ea ev st' root u inner label label_events sl su el eu choose Hget Hrank_a Hrank_v
      Hcompare Hrun IH Hlabel Hscore_l Hscore_u Hchoose]; cbn.
  - exact Hlinks.
  - exact Hlinks.
  - assert (Ha : audit_lt_input_vertex V E g r semis a).
    { exact (proj2 ((proj2 (proj1 Hlinks)) v a Hget)). }
    specialize (IH Ha).
    assert (Ha_input : audit_semi_input_vertex V semis st v a).
    { eapply audit_semi_input_vertex_get; left; exact Hget. }
    pose proof (audit_semi_compress_result_in V E EV r semis st v a _ _ Hrun Ha_input)
      as [Hroot_in _].
    cbn in Hroot_in.
    assert (Hroot : audit_lt_input_vertex V E g r semis root).
    { exact (audit_lt_query_vertex V E EV g r semis st v root Hlinks Hv Hroot_in). }
    assert (Hlabel_in : audit_semi_input_vertex V semis st v label).
    { eapply audit_semi_label_counted_in; [left; reflexivity|exact Hlabel]. }
    assert (Hlabel_vertex : audit_lt_input_vertex V E g r semis label).
    { exact (audit_lt_query_vertex V E EV g r semis st v label Hlinks Hv Hlabel_in). }
    apply audit_semi_links_envelope_shortcut; assumption.
  - assert (Ha : audit_lt_input_vertex V E g r semis a).
    { exact (proj2 ((proj2 (proj1 Hlinks)) v a Hget)). }
    specialize (IH Ha).
    assert (Ha_input : audit_semi_input_vertex V semis st v a).
    { eapply audit_semi_input_vertex_get; left; exact Hget. }
    pose proof (audit_semi_compress_result_in V E EV r semis st v a _ _ Hrun Ha_input)
      as [Hroot_in Hu_in].
    cbn in Hroot_in, Hu_in.
    assert (Hroot : audit_lt_input_vertex V E g r semis root).
    { exact (audit_lt_query_vertex V E EV g r semis st v root Hlinks Hv Hroot_in). }
    assert (Hu : audit_lt_input_vertex V E g r semis u).
    { exact (audit_lt_query_vertex V E EV g r semis st v u Hlinks Hv Hu_in). }
    assert (Hlabel_in : audit_semi_input_vertex V semis st v label).
    { eapply audit_semi_label_counted_in; [left; reflexivity|exact Hlabel]. }
    assert (Hlabel_vertex : audit_lt_input_vertex V E g r semis label).
    { exact (audit_lt_query_vertex V E EV g r semis st v label Hlinks Hv Hlabel_in). }
    apply audit_semi_links_envelope_shortcut; try assumption.
    destruct choose; assumption.
Qed.

(** Nested compression retains that envelope and bounds every captured query event. *)
Lemma audit_lt_nested_query_safe V E B (EV : encoding V) (g : Graph.t V E) enc weight
    (r : dfs_result V E) semis st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) st ->
  audit_lt_input_vertex V E g r semis v ->
  audit_semi_nested_compress_run (B := B) enc r semis st v result events ->
  Forall (audit_semi_nested_event_safe V B weight (audit_lt_nested_input_width EV g r semis))
    events /\
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) (fst result).
Proof.
  intros Hencode Hlinks Hv Hrun; split.
  - eapply audit_semi_nested_safe_mono.
    + eapply audit_lt_query_width; eassumption.
    + eapply audit_semi_nested_compress_safe; [exact Hencode|exact Hrun|left; reflexivity].
  - destruct (audit_semi_nested_to_plain V E B EV enc r semis st v result events Hencode Hrun)
      as [plain Hplain].
    eapply audit_lt_compress_envelope; eassumption.
Qed.

(** * Same-run nested work accounting *)

(** Only the output marker carries an input-size charge outside the fixed event allowance. *)
Definition audit_lt_nested_extra V E B (event : audit_lt_nested_event V E B) : nat :=
  match event with
  | LtNestedOutput size => S size
  | _ => 0
  end.

(** A safe event charges its actual callback body and its input-bounded internal work. *)
Definition audit_lt_nested_event_safe V E B (weight : B -> nat) width
    (event : audit_lt_nested_event V E B) : Prop :=
  audit_lt_nested_event_work weight event <=
    256 + 32 * width + audit_lt_nested_body_event_work weight event +
      audit_lt_nested_extra V E B event.

(** Safe nested events sum without discarding their captured callback bodies. *)
Lemma audit_lt_nested_safe_work V E B (weight : B -> nat) width events :
  Forall (audit_lt_nested_event_safe V E B weight width) events ->
  audit_lt_nested_work weight events <=
    length events * (256 + 32 * width) + audit_lt_nested_body_work weight events +
      fold_right (fun event total => audit_lt_nested_extra V E B event + total) 0 events.
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - unfold audit_lt_nested_work, audit_lt_nested_body_work in *.
    cbn [fold_right length] in *; unfold audit_lt_nested_event_safe in Hevent; lia.
Qed.

(** An inner semidominator event retains the same body charge in the LT receipt. *)
Lemma audit_lt_nested_inner_safe V E B (weight : B -> nat) width events :
  Forall (audit_semi_nested_event_safe V B weight width) events ->
  Forall (audit_lt_nested_event_safe V E B weight width) (map LtNestedSemi events).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; cbn; constructor; [|exact IH].
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra.
  change (64 + audit_semi_nested_event_work weight event <=
    256 + 32 * width + audit_semi_nested_body_event_work weight event + 0).
  unfold audit_semi_nested_event_safe in Hevent; lia.
Qed.

(** A producer link event keeps the captured encoder body in the LT receipt. *)
Lemma audit_lt_nested_producer_safe V E B (weight : B -> nat) width events :
  Forall (audit_semi_producer_event_quiet V E B weight width) events ->
  Forall (audit_lt_nested_event_safe V E B weight width) (map LtNestedProducer events).
Proof.
  intro Hsafe; induction Hsafe as [|event rest [Hevent Hextra] Hrest IH]; cbn; constructor;
    [|exact IH].
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra.
  change (64 + audit_semi_producer_nested_event_work weight event <=
    256 + 32 * width + audit_semi_producer_nested_body_event_work weight event + 0).
  unfold audit_semi_producer_event_safe in Hevent; lia.
Qed.

(** A case or source event has no unrecorded callback work. *)
Lemma audit_lt_nested_case_source_safe V E B (weight : B -> nat) width :
  (forall site, audit_lt_nested_event_safe V E B weight width (LtNestedCase site)) /\
  (forall edge vertex body,
    audit_lt_nested_event_safe V E B weight width (LtNestedSource edge vertex body)).
Proof.
  split; intros; unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra; cbn; lia.
Qed.

(** Bucket lookups and writes charge their actual encoder and trie operations. *)
Lemma audit_lt_nested_bucket_get_safe V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V (list V)) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_lt_nested_event_safe V E B weight width)
    (map LtNestedBucket (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_get_source_work_bound V (list V) B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in *; destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trace].
  cbn [fst snd] in Hencode, Hwork; subst code.
  cbn [snd map]; constructor; [|constructor].
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra.
  cbn [audit_map_source_work] in *; lia.
Qed.

(** Bucket writes retain the exact value and encoder callback. *)
Lemma audit_lt_nested_bucket_set_safe V E B (EV : encoding V) enc (weight : B -> nat)
    width key value (input : Map.t V (list V)) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_lt_nested_event_safe V E B weight width)
    (map LtNestedBucket (snd (audit_map_set enc key value input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_set_source_work_bound V (list V) B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key value input) as Hwork.
  unfold audit_map_set in *; destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_trie_set code (key, value) input) as [result trace].
  cbn [fst snd] in Hencode, Hwork; subst code.
  cbn [snd map]; constructor; [|constructor].
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra.
  cbn [audit_map_source_work] in *; lia.
Qed.

(** Tree-edge lookup is bounded by its actual encoded key and body. *)
Lemma audit_lt_nested_tree_get_safe V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V E) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_lt_nested_event_safe V E B weight width)
    (map LtNestedTree (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth.
  pose proof (audit_map_get_source_work_bound V E B enc
    (fun body => fold_right (fun item n => weight item + n) 0 body) key input) as Hwork.
  unfold audit_map_get in *; destruct (enc key) as [code body].
  destruct (CollectionsAuditTrie.audit_map_code_get code input) as [found trace].
  cbn [fst snd] in Hencode, Hwork; subst code.
  cbn [snd map]; constructor; [|constructor].
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra.
  cbn [audit_map_source_work] in *; lia.
Qed.

(** Every semidominator lookup returns an original input vertex, regardless of stored key shape. *)
Lemma audit_lt_semi_value_vertex V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis v :
  audit_lt_input_vertex V E g r semis v ->
  audit_lt_input_vertex V E g r semis (semi_value EV semis v).
Proof.
  intro Hv; unfold semi_value.
  destruct (Map.get EV v semis) as [value|] eqn:Hget; [|exact Hv].
  destruct (audit_semi_map_get_value_in V V EV semis v value Hget) as [key Hin].
  exact (proj2 (audit_lt_semi_row V E g r semis key value Hin)).
Qed.

(** A source returned by the tree map belongs to the original input vertex envelope. *)
Lemma audit_lt_tree_source_vertex V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis v edge :
  Map.get EV v (tree_edge r) = Some edge ->
  audit_lt_input_vertex V E g r semis (Graph.source g edge).
Proof.
  intro Hget.
  destruct (audit_semi_map_get_value_in V E EV (tree_edge r) v edge Hget) as [key Hin].
  unfold audit_lt_input_vertex; do 4 (apply in_or_app; right); apply in_or_app; left.
  apply in_map_iff; exists edge; split; [reflexivity|].
  apply in_map_iff; exists (key, edge); split; [reflexivity|exact Hin].
Qed.

(** Every listed preorder vertex belongs to the original input envelope. *)
Lemma audit_lt_preorder_vertex V E (g : Graph.t V E) (r : dfs_result V E) semis v :
  In v (preorder r) -> audit_lt_input_vertex V E g r semis v.
Proof.
  intro Hin; unfold audit_lt_input_vertex; apply in_or_app; now left.
Qed.

(** Quiet events have no output marker charge. *)
Definition audit_lt_nested_quiet V E B (weight : B -> nat) width
    (event : audit_lt_nested_event V E B) : Prop :=
  audit_lt_nested_event_safe V E B weight width event /\ audit_lt_nested_extra V E B event = 0.

(** Wrapping an inner receipt produces quiet LT events. *)
Lemma audit_lt_nested_inner_quiet V E B (weight : B -> nat) width events :
  Forall (audit_semi_nested_event_safe V B weight width) events ->
  Forall (audit_lt_nested_quiet V E B weight width) (map LtNestedSemi events).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; cbn.
  - constructor.
  - constructor; [|exact IH]; split; [|reflexivity].
    pose proof (audit_lt_nested_inner_safe V E B weight width [event]) as Hwrapped.
    specialize (Hwrapped (Forall_cons _ Hevent (Forall_nil _))).
    inversion Hwrapped; assumption.
Qed.

(** Wrapping link receipts produces quiet LT events. *)
Lemma audit_lt_nested_producer_quiet V E B (weight : B -> nat) width events :
  Forall (audit_semi_producer_event_quiet V E B weight width) events ->
  Forall (audit_lt_nested_quiet V E B weight width) (map LtNestedProducer events).
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH]; cbn.
  - constructor.
  - constructor; [|exact IH]; split; [|reflexivity].
    pose proof (audit_lt_nested_producer_safe V E B weight width [event]) as Hwrapped.
    specialize (Hwrapped (Forall_cons _ Hevent (Forall_nil _))).
    inversion Hwrapped; assumption.
Qed.

(** The reverse state keeps links and provisional parent bindings in the original envelope. *)
Definition audit_lt_state_envelope V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis (st : LtState.t V) : Prop :=
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) (LtState.links st) /\
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) (LtState.parents st).

(** Member score and rank receipts use operands within the original input width. *)
Lemma audit_lt_nested_member_operands V E B (EV : encoding V) (g : Graph.t V E)
    (enc : V -> positive * list B) (weight : B -> nat) (r : dfs_result V E) semis
    links start selected s score score_events rank rank_events choose comparison :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_links_envelope V EV (audit_lt_input_vertex V E g r semis) links ->
  audit_lt_input_vertex V E g r semis start -> audit_lt_input_vertex V E g r semis s ->
  audit_semi_input_vertex V semis links start selected ->
  audit_semi_nested_score enc r semis selected = (score, score_events) ->
  audit_semi_nested_rank enc r s = (rank, rank_events) ->
  audit_positive_ltb score rank = (choose, comparison) ->
  let width := audit_lt_nested_input_width EV g r semis in
  Forall (audit_semi_nested_event_safe V B weight width) score_events /\
  Forall (audit_semi_nested_event_safe V B weight width) rank_events /\
  audit_semi_nested_event_safe V B weight width (SemiNestedCompare score rank choose comparison).
Proof.
  intros Hencode Hlinks Hstart Hs Hlocal Hscore Hrank Hcompare.
  pose proof (audit_lt_query_width V E EV g r semis links start Hlinks Hstart) as Hwidth.
  pose proof (audit_semi_nested_score_safe V E B EV enc weight r semis links start selected
    Hencode Hlocal) as Hscore_safe.
  rewrite Hscore in Hscore_safe; cbn [snd] in Hscore_safe.
  pose proof (audit_lt_input_vertex_width V E EV g r semis s Hs) as Hswidth.
  pose proof (audit_semi_nested_rank_safe V E B EV enc weight
    (audit_lt_nested_input_width EV g r semis) r s (Hencode s) Hswidth) as Hrank_safe.
  rewrite Hrank in Hrank_safe; cbn [snd] in Hrank_safe.
  pose proof (audit_semi_nested_score_erases V E B EV enc r semis selected Hencode) as Hscore_eq.
  rewrite Hscore in Hscore_eq; cbn in Hscore_eq.
  pose proof (audit_semi_nested_rank_erases V E B EV enc r s (Hencode s)) as Hrank_eq.
  rewrite Hrank in Hrank_eq; cbn in Hrank_eq.
  pose proof (audit_semi_nested_rank_width V E EV r semis links start
    (semi_value EV semis selected)) as Hscore_width.
  pose proof (audit_semi_nested_rank_width V E EV r semis links start s) as Hrank_width.
  split.
  - eapply (audit_semi_nested_safe_mono V B weight
      (audit_semi_nested_width EV r semis links start));
      eassumption.
  - split; [exact Hrank_safe|].
    eapply audit_semi_nested_compare_safe; [rewrite Hscore_eq; lia|rewrite Hrank_eq; lia|].
    left; exact Hcompare.
Qed.

(** A nested member preserves its state envelope and every same-run body charge. *)
Lemma audit_lt_nested_member_safe V E B (EV : encoding V) (g : Graph.t V E) enc weight
    (r : dfs_result V E) semis s st v result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_lt_state_envelope V E EV g r semis st ->
  audit_lt_input_vertex V E g r semis s -> audit_lt_input_vertex V E g r semis v ->
  audit_lt_nested_member_run (B := B) enc r semis s st v result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis)) events.
Proof.
  intros Hencode [Hlinks Hparents] Hs Hv Hrun; inversion Hrun; subst.
  set (width := audit_lt_nested_input_width EV g r semis).
  match goal with
  | Hcompress : audit_semi_nested_compress_run _ _ _ _ _ _ ?inner,
    Hscore : audit_semi_nested_score _ _ _ ?selected = (?score, ?score_events),
    Hrank : audit_semi_nested_rank _ _ _ = (?rank, ?rank_events),
    Hcompare : audit_positive_ltb _ _ = (?choose, ?comparison),
    Hset : audit_map_set _ _ ?parent _ = (?parents, ?writes) |- _ =>
    destruct (audit_lt_nested_query_safe V E B EV g enc weight r semis (LtState.links st) v
      _ inner Hencode Hlinks Hv Hcompress) as [Hinner Hlinks'];
    pose proof (audit_semi_nested_result_in V E B EV enc r semis (LtState.links st) v v
      _ inner Hencode Hcompress (or_introl eq_refl)) as Hselected;
    cbn in Hselected;
    assert (Hlocal : audit_semi_input_vertex V semis (LtState.links st) v selected)
      by (destruct part as [best|]; cbn [fst snd] in Hselected |- *;
        [exact (proj2 Hselected)|left; reflexivity]);
    pose proof (audit_lt_query_vertex V E EV g r semis (LtState.links st) v selected
      Hlinks Hv Hlocal) as Hselected_vertex;
    destruct (audit_lt_nested_member_operands V E B EV g enc weight r semis (LtState.links st) v
      selected s score score_events rank rank_events choose comparison Hencode Hlinks Hv Hs Hlocal
      Hscore Hrank Hcompare) as [Hscore_safe [Hrank_safe Hcompare_safe]];
    pose proof (audit_lt_input_vertex_width V E EV g r semis v Hv) as Hvwidth;
    pose proof (audit_semi_nested_vertex_set_safe V B EV enc weight width v parent
      (LtState.parents st) (Hencode v) Hvwidth) as Hset_safe;
    rewrite Hset in Hset_safe; cbn in Hset_safe;
    pose proof (audit_map_set_erases V V B enc EV v parent (LtState.parents st) (Hencode v))
      as Hparents_eq;
    rewrite Hset in Hparents_eq; cbn in Hparents_eq;
    split
  end.
  - split; cbn; [exact Hlinks'|].
    rewrite Hparents_eq; apply audit_semi_map_envelope_set; try assumption.
    destruct choose; assumption.
  - repeat rewrite Forall_app; repeat split.
    + apply audit_lt_nested_inner_quiet; exact Hinner.
    + constructor; [split; [apply (proj1 (audit_lt_nested_case_source_safe V E B weight width))|
        reflexivity]|constructor].
    + apply audit_lt_nested_inner_quiet; exact Hscore_safe.
    + apply audit_lt_nested_inner_quiet; exact Hrank_safe.
    + constructor; [|constructor]; split; [|reflexivity].
      apply (proj1 (Forall_forall _ _) (audit_lt_nested_inner_safe V E B weight width
        [SemiNestedCompare score rank choose compare_events]
        (Forall_cons _ Hcompare_safe (Forall_nil _))));
        left; reflexivity.
    + rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hset_safe.
Qed.

(** The member fold preserves the envelope and accounts for the same event list. *)
Lemma audit_lt_nested_members_safe V E B (EV : encoding V) (g : Graph.t V E) enc weight
    (r : dfs_result V E) semis s vertices st result events :
  (forall x, fst (enc x) = encode EV x) ->
  audit_lt_state_envelope V E EV g r semis st ->
  audit_lt_input_vertex V E g r semis s ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  audit_lt_nested_members_run (B := B) enc r semis s vertices st result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis)) events.
Proof.
  intros Hencode Hstate Hs Hvertices Hrun; revert Hstate Hvertices.
  induction Hrun; intros Hstate Hvertices.
  - split; [exact Hstate|].
    constructor; [split; [apply (proj1 (audit_lt_nested_case_source_safe V E B weight _))|
      reflexivity]|constructor].
  - inversion Hvertices as [|? ? Hv Hrest]; subst.
    destruct (audit_lt_nested_member_safe V E B EV g enc weight r semis s initial v middle here
      Hencode Hstate Hs Hv H) as [Hmiddle Hhere].
    destruct (IHHrun Hmiddle Hrest) as [Hresult Hlater].
    split; [exact Hresult|].
    constructor; [split; [apply (proj1 (audit_lt_nested_case_source_safe V E B weight _))|
      reflexivity]|].
    apply Forall_app; split; assumption.
Qed.

(** Every member of a source-built bucket comes from the original preorder. *)
Lemma audit_lt_bucket_vertices V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis s :
  Forall (audit_lt_input_vertex V E g r semis)
    (lt_bucket EV (lt_bucket_index EV semis (preorder r)) s).
Proof.
  apply Forall_forall; intros v Hin.
  apply audit_lt_preorder_vertex.
  exact (proj1 (proj1 (lt_bucket_index_in EV semis (preorder r) s v) Hin)).
Qed.

(** A safe mapped receipt is quiet when its wrapper never emits an output marker. *)
Lemma audit_lt_nested_mapped_quiet V E B A (weight : B -> nat) width
    (wrap : A -> audit_lt_nested_event V E B) events :
  (forall event, audit_lt_nested_extra V E B (wrap event) = 0) ->
  Forall (audit_lt_nested_event_safe V E B weight width) (map wrap events) ->
  Forall (audit_lt_nested_quiet V E B weight width) (map wrap events).
Proof.
  intros Hextra Hsafe; apply Forall_forall; intros event Hin.
  split.
  - apply (proj1 (Forall_forall _ _) Hsafe); exact Hin.
  - apply in_map_iff in Hin; destruct Hin as [item [<- _]]; apply Hextra.
Qed.

(** A case marker is a quiet event. *)
Lemma audit_lt_nested_case_quiet V E B (weight : B -> nat) width site :
  audit_lt_nested_quiet V E B weight width (LtNestedCase site).
Proof.
  split; [apply (proj1 (audit_lt_nested_case_source_safe V E B weight width))|reflexivity].
Qed.

(** A source event includes its entire body and has no output-size charge. *)
Lemma audit_lt_nested_source_quiet V E B (weight : B -> nat) width edge vertex body :
  audit_lt_nested_quiet V E B weight width (LtNestedSource edge vertex body).
Proof.
  split; [apply (proj2 (audit_lt_nested_case_source_safe V E B weight width))|reflexivity].
Qed.

(** A bounded bucket read is a quiet LT receipt. *)
Lemma audit_lt_nested_bucket_get_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V (list V)) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_lt_nested_quiet V E B weight width)
    (map LtNestedBucket (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth; apply audit_lt_nested_mapped_quiet; [reflexivity|].
  apply (audit_lt_nested_bucket_get_safe V E B EV); assumption.
Qed.

(** A bounded bucket write is a quiet LT receipt. *)
Lemma audit_lt_nested_bucket_set_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key value (input : Map.t V (list V)) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_lt_nested_quiet V E B weight width)
    (map LtNestedBucket (snd (audit_map_set enc key value input))).
Proof.
  intros Hencode Hwidth; apply audit_lt_nested_mapped_quiet; [reflexivity|].
  apply (audit_lt_nested_bucket_set_safe V E B EV); assumption.
Qed.

(** A bounded tree lookup is a quiet LT receipt. *)
Lemma audit_lt_nested_tree_get_quiet V E B (EV : encoding V) enc (weight : B -> nat)
    width key (input : Map.t V E) :
  fst (enc key) = encode EV key -> Pos.size_nat (encode EV key) <= width ->
  Forall (audit_lt_nested_quiet V E B weight width)
    (map LtNestedTree (snd (audit_map_get enc key input))).
Proof.
  intros Hencode Hwidth; apply audit_lt_nested_mapped_quiet; [reflexivity|].
  apply (audit_lt_nested_tree_get_safe V E B EV); assumption.
Qed.

(** A nested reverse step preserves the state envelope and all same-call receipts. *)
Lemma audit_lt_nested_reverse_safe V E B (EV : encoding V) (g : Graph.t V E) enc source weight
    (r : dfs_result V E) semis buckets st s result events :
  (forall x, fst (enc x) = encode EV x) ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  buckets = lt_bucket_index EV semis (preorder r) ->
  audit_lt_state_envelope V E EV g r semis st ->
  audit_lt_input_vertex V E g r semis s ->
  audit_lt_nested_reverse_run (B := B) enc source r semis buckets st s result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis)) events.
Proof.
  intros Hencode Hsource Hbuckets Hstate Hs Hrun; inversion Hrun; subst result events members.
  all: match goal with
    | Hbucket : audit_map_get _ _ _ = (?bucket, ?bucket_events),
      Hmembers : audit_lt_nested_members_run _ _ _ _ ?members _ ?settled ?member_events,
      Htree : audit_map_get _ _ (tree_edge ?dfs) = (_, ?tree_events) |- _ =>
      pose proof (audit_lt_input_vertex_width V E EV g r semis s Hs) as Hwidth;
      pose proof (audit_lt_nested_bucket_get_quiet V E B EV enc weight
        (audit_lt_nested_input_width EV g r semis) s buckets (Hencode s) Hwidth) as Hbucket_safe;
      rewrite Hbucket in Hbucket_safe; cbn in Hbucket_safe;
      pose proof (audit_lt_nested_tree_get_quiet V E B EV enc weight
        (audit_lt_nested_input_width EV g r semis) s (tree_edge r) (Hencode s) Hwidth)
        as Htree_safe;
      rewrite Htree in Htree_safe; cbn in Htree_safe;
      pose proof (audit_map_get_erases V (list V) B enc EV s buckets (Hencode s)) as Hget;
      rewrite Hbucket in Hget; cbn in Hget;
      assert (Hvertices : Forall (audit_lt_input_vertex V E g r semis) members)
        by (rewrite Hget; change (Forall (audit_lt_input_vertex V E g r semis)
          (lt_bucket EV buckets s)); rewrite Hbuckets; apply audit_lt_bucket_vertices);
      destruct (audit_lt_nested_members_safe V E B EV g enc weight r semis s members st settled
        member_events Hencode Hstate Hs Hvertices Hmembers) as [Hsettled Hmember_safe]
    end.
  - split; [exact Hsettled|].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [apply audit_lt_nested_case_quiet|constructor].
  - match goal with
    | Htree : audit_map_get _ _ (tree_edge ?dfs) = (Some ?edge, _),
      Hsrc : source ?edge = (?parent, _),
      Hlink : audit_semi_producer_link _ ?links _ ?parent = (?new_links, ?link_events) |- _ =>
      pose proof (audit_map_get_erases V E B enc EV s (tree_edge r) (Hencode s)) as Htree_erases;
      rewrite Htree in Htree_erases; cbn in Htree_erases;
      pose proof (Hsource edge) as Hsource_erases; rewrite Hsrc in Hsource_erases;
      cbn in Hsource_erases;
      assert (Hparent : audit_lt_input_vertex V E g r semis parent)
        by (rewrite Hsource_erases; apply (audit_lt_tree_source_vertex V E EV g r semis s edge);
          symmetry; exact Htree_erases);
      pose proof (audit_semi_producer_link_erases V E B EV enc links s parent (Hencode s))
        as Hlink_eq;
      rewrite Hlink in Hlink_eq; cbn in Hlink_eq;
      pose proof (audit_semi_producer_link_details V E B EV enc weight
        (audit_lt_nested_input_width EV g r semis) links s parent (Hencode s) Hwidth)
        as [_ Hlink_safe];
      rewrite Hlink in Hlink_safe; cbn in Hlink_safe;
      split
    end.
    + destruct Hsettled as [Hlinks Hparents]; split; cbn; [|exact Hparents].
      rewrite Hlink_eq; apply audit_semi_links_envelope_link; assumption.
    + repeat rewrite Forall_app; repeat split; try assumption.
      * constructor; [apply audit_lt_nested_case_quiet|].
        constructor; [apply audit_lt_nested_source_quiet|constructor].
      * apply audit_lt_nested_producer_quiet; exact Hlink_safe.
Qed.

(** The reverse fold preserves the envelope and retains all nested work receipts. *)
Lemma audit_lt_nested_reverse_fold_safe V E B (EV : encoding V) (g : Graph.t V E)
    enc source weight (r : dfs_result V E) semis buckets vertices st result events :
  (forall x, fst (enc x) = encode EV x) ->
  (forall edge, fst (source edge) = Graph.source g edge) ->
  buckets = lt_bucket_index EV semis (preorder r) ->
  audit_lt_state_envelope V E EV g r semis st ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  audit_lt_nested_reverse_fold_run (B := B) enc source r semis buckets vertices st result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis)) events.
Proof.
  intros Hencode Hsource Hbuckets Hstate Hvertices Hrun; revert Hstate Hvertices.
  induction Hrun; intros Hstate Hvertices.
  - split; [exact Hstate|].
    constructor; [apply audit_lt_nested_case_quiet|constructor].
  - inversion Hvertices as [|? ? Hv Hrest].
    destruct (audit_lt_nested_reverse_safe V E B EV g enc source weight r semis buckets initial v
      middle here Hencode Hsource Hbuckets Hstate Hv H) as [Hmiddle Hhere].
    destruct (IHHrun Hmiddle Hrest) as [Hresult Hlater].
    split; [exact Hresult|].
    constructor; [apply audit_lt_nested_case_quiet|].
    apply Forall_app; split; assumption.
Qed.

(** Building nested buckets charges only input-order keys and semidominator values. *)
Lemma audit_lt_nested_buckets_safe V E B (EV : encoding V) (g : Graph.t V E)
    enc weight (r : dfs_result V E) semis vertices buckets :
  (forall x, fst (enc x) = encode EV x) ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis))
    (snd (audit_lt_nested_buckets enc semis vertices buckets)).
Proof.
  intros Hencode Hvertices; revert buckets.
  induction Hvertices as [|v rest Hv Hrest IH]; intro buckets; cbn [audit_lt_nested_buckets].
  - constructor; [apply audit_lt_nested_case_quiet|constructor].
  - set (width := audit_lt_nested_input_width EV g r semis).
    pose proof (audit_lt_input_vertex_width V E EV g r semis v Hv) as Hvwidth.
    pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v semis
      (Hencode v) Hvwidth) as Hget_safe.
    pose proof (audit_map_get_erases V V B enc EV v semis (Hencode v)) as Hget.
    destruct (audit_map_get enc v semis) as [found reads] eqn:Hread; cbn in Hget, Hget_safe.
    destruct found as [s|].
    + assert (Hs : audit_lt_input_vertex V E g r semis s).
      { destruct (audit_semi_map_get_value_in V V EV semis v s (eq_sym Hget)) as [key Hin].
        exact (proj2 (audit_lt_semi_row V E g r semis key s Hin)). }
      pose proof (audit_lt_input_vertex_width V E EV g r semis s Hs) as Hswidth.
      pose proof (audit_lt_nested_bucket_get_quiet V E B EV enc weight width s buckets
        (Hencode s) Hswidth) as Hbucket_safe.
      destruct (audit_map_get enc s buckets) as [old bucket_events] eqn:Hbucket.
      cbn in Hbucket_safe.
      pose proof (audit_lt_nested_bucket_set_quiet V E B EV enc weight width s
        (v :: match old with
              | Some xs => xs
              | None => []
              end) buckets (Hencode s) Hswidth)
        as Hset_safe.
      destruct (audit_map_set enc s (v :: match old with
                                        | Some xs => xs
                                        | None => []
                                        end) buckets)
        as [next writes] eqn:Hset; cbn in Hset_safe.
      specialize (IH next).
      destruct (audit_lt_nested_buckets enc semis rest next) as [result later]; cbn in IH |- *.
      constructor; [apply audit_lt_nested_case_quiet|].
      apply Forall_app; split.
      * rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hget_safe.
      * constructor; [apply audit_lt_nested_case_quiet|].
        repeat rewrite Forall_app; repeat split; assumption.
    + specialize (IH buckets).
      destruct (audit_lt_nested_buckets enc semis rest buckets) as [result later]; cbn in IH |- *.
      constructor; [apply audit_lt_nested_case_quiet|].
      apply Forall_app; split.
      * rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hget_safe.
      * constructor; [apply audit_lt_nested_case_quiet|exact IH].
Qed.

(** An encoder event charges its captured body exactly. *)
Lemma audit_lt_nested_encode_quiet V E B (weight : B -> nat) width v code body :
  audit_lt_nested_quiet V E B weight width (LtNestedEncode v code body).
Proof.
  split; [|reflexivity].
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra; cbn; lia.
Qed.

(** Positive equality charges at most the width of its actual first operand. *)
Lemma audit_lt_nested_equal_quiet V E B (weight : B -> nat) width a b equal events :
  Pos.size_nat a <= width -> audit_positive_eqb a b = (equal, events) ->
  audit_lt_nested_quiet V E B weight width (LtNestedEqual a b equal events).
Proof.
  intros Hwidth Hrun; split; [|reflexivity].
  pose proof (audit_positive_eqb_source_bound a b) as Hwork.
  rewrite Hrun in Hwork; cbn [snd] in Hwork.
  unfold audit_positive_eqb_source_work in Hwork.
  unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
    audit_lt_nested_body_event_work, audit_lt_nested_extra; cbn.
  pose proof (Nat.le_min_l (Pos.size_nat a) (Pos.size_nat b)); lia.
Qed.

(** A deferred correction reads its parent from the same enveloped map and captures the lookup. *)
Lemma audit_lt_nested_parent_safe V E B (EV : encoding V) (g : Graph.t V E)
    (enc : V -> positive * list B) (weight : B -> nat) (r : dfs_result V E)
    semis corrected u (equal : bool) :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) corrected ->
  audit_lt_input_vertex V E g r semis u ->
  exists parent parent_events,
    (if equal then (u, []) else
      let '(found_parent, events) := audit_map_get enc u corrected in
      (match found_parent with
       | Some x => x
       | None => u
       end, events)) = (parent, parent_events) /\
    audit_lt_input_vertex V E g r semis parent /\
    Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis))
      (map (fun item => LtNestedSemi (SemiNestedVertexMap item)) parent_events).
Proof.
  intros Hencode Hcorrected Hu; destruct equal.
  - exists u, []; cbn; repeat split; try assumption; constructor.
  - pose proof (audit_lt_input_vertex_width V E EV g r semis u Hu) as Huwidth.
    pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight
      (audit_lt_nested_input_width EV g r semis) u corrected (Hencode u) Huwidth) as Hparent_safe.
    pose proof (audit_map_get_erases V V B enc EV u corrected (Hencode u)) as Hparent_eq.
    destruct (audit_map_get enc u corrected) as [found_parent parent_events] eqn:Hparent_run.
    cbn in Hparent_safe, Hparent_eq.
    exists (match found_parent with
            | Some x => x
            | None => u
            end), parent_events; split;
      [reflexivity|].
    split.
    + destruct found_parent as [parent|]; [|exact Hu].
      exact (proj2 ((proj2 Hcorrected) u parent (eq_sym Hparent_eq))).
    + rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hparent_safe.
Qed.

(** A correction step preserves the parent envelope and charges its actual captured operations. *)
Lemma audit_lt_nested_correct_safe V E B (EV : encoding V) (g : Graph.t V E)
    enc weight (r : dfs_result V E) semis provisional corrected v :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) provisional ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) corrected ->
  audit_lt_input_vertex V E g r semis v ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis)
    (fst (audit_lt_nested_correct (E := E) (B := B) enc semis provisional corrected v)) /\
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis))
    (snd (audit_lt_nested_correct (E := E) (B := B) enc semis provisional corrected v)).
Proof.
  intros Hencode Hprovisional Hcorrected Hv.
  set (width := audit_lt_nested_input_width EV g r semis).
  pose proof (audit_lt_input_vertex_width V E EV g r semis v Hv) as Hvwidth.
  pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v provisional
    (Hencode v) Hvwidth) as Hfirst_safe.
  pose proof (audit_map_get_erases V V B enc EV v provisional (Hencode v)) as Hfirst_eq.
  unfold audit_lt_nested_correct.
  destruct (audit_map_get enc v provisional) as [found first] eqn:Hfirst;
    cbn in Hfirst_safe, Hfirst_eq.
  destruct found as [u|].
  - assert (Hu : audit_lt_input_vertex V E g r semis u).
    { exact (proj2 ((proj2 Hprovisional) v u (eq_sym Hfirst_eq))). }
    pose proof (audit_lt_input_vertex_width V E EV g r semis u Hu) as Huwidth.
    pose proof (Hencode u) as Ha.
    destruct (enc u) as [a a_body] eqn:Ha_run; cbn in Ha.
    pose proof (audit_semi_nested_vertex_get_safe V B EV enc weight width v semis
      (Hencode v) Hvwidth) as Hvalue_safe.
    destruct (audit_map_get enc v semis) as [value value_events] eqn:Hvalue;
      cbn in Hvalue_safe.
    destruct (enc (match value with
                   | Some x => x
                   | None => v
                   end)) as [b b_body] eqn:Hb_run.
    destruct (audit_positive_eqb a b) as [equal equal_events] eqn:Hequal.
    assert (Hequal_safe : audit_lt_nested_quiet V E B weight width
      (LtNestedEqual a b equal equal_events)).
    { apply audit_lt_nested_equal_quiet; [rewrite Ha; exact Huwidth|exact Hequal]. }
    destruct (audit_lt_nested_parent_safe V E B EV g enc weight r semis corrected u equal
      Hencode Hcorrected Hu)
      as [parent [parent_events [Hparent_run [Hparent_vertex Hparent_safe]]]].
    rewrite Hparent_run.
    pose proof (audit_semi_nested_vertex_set_safe V B EV enc weight width v parent corrected
      (Hencode v) Hvwidth) as Hset_safe.
    pose proof (audit_map_set_erases V V B enc EV v parent corrected (Hencode v)) as Hset_eq.
    destruct (audit_map_set enc v parent corrected) as [result writes] eqn:Hset;
      cbn in Hset_safe, Hset_eq |- *.
    split.
    + rewrite Hset_eq; apply audit_semi_map_envelope_set; assumption.
    + apply Forall_app; split.
      * rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hfirst_safe.
      * constructor; [apply audit_lt_nested_case_quiet|].
        constructor; [apply audit_lt_nested_encode_quiet|].
        apply Forall_app; split.
        -- rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hvalue_safe.
        -- constructor; [apply audit_lt_nested_encode_quiet|].
           constructor; [exact Hequal_safe|].
           apply Forall_app; split; [exact Hparent_safe|].
           rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hset_safe.
  - split; [exact Hcorrected|].
    apply Forall_app; split.
    + rewrite <- map_map; apply audit_lt_nested_inner_quiet; exact Hfirst_safe.
    + constructor; [apply audit_lt_nested_case_quiet|constructor].
Qed.

(** Correction over a vertex list preserves the envelope and accounts for every receipt. *)
Lemma audit_lt_nested_correct_fold_safe V E B (EV : encoding V) (g : Graph.t V E)
    enc weight (r : dfs_result V E) semis provisional vertices corrected :
  (forall x, fst (enc x) = encode EV x) ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) provisional ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) corrected ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis)
    (fst (audit_lt_nested_correct_fold (E := E) (B := B) enc semis provisional vertices
      corrected)) /\
  Forall (audit_lt_nested_quiet V E B weight (audit_lt_nested_input_width EV g r semis))
    (snd (audit_lt_nested_correct_fold (E := E) (B := B) enc semis provisional vertices corrected)).
Proof.
  intros Hencode Hprovisional Hcorrected Hvertices; revert corrected Hcorrected.
  induction Hvertices as [|v rest Hv Hrest IH]; intros corrected Hcorrected;
    cbn [audit_lt_nested_correct_fold].
  - split; [exact Hcorrected|].
    constructor; [apply audit_lt_nested_case_quiet|constructor].
  - destruct (audit_lt_nested_correct_safe V E B EV g enc weight r semis provisional corrected v
      Hencode Hprovisional Hcorrected Hv) as [Hmiddle Hhere].
    destruct (audit_lt_nested_correct enc semis provisional corrected v) as [middle here];
      cbn in Hmiddle, Hhere.
    destruct (IH middle Hmiddle) as [Hresult Hlater].
    destruct (audit_lt_nested_correct_fold enc semis provisional rest middle) as [result later];
      cbn in Hresult, Hlater |- *.
    split; [exact Hresult|].
    constructor; [apply audit_lt_nested_case_quiet|].
    apply Forall_app; split; assumption.
Qed.

(** A quiet receipt contributes no output marker charge. *)
Lemma audit_lt_nested_quiet_extra V E B (weight : B -> nat) width events :
  Forall (audit_lt_nested_quiet V E B weight width) events ->
  fold_right (fun event total => audit_lt_nested_extra V E B event + total) 0 events = 0.
Proof.
  intro Hquiet; induction Hquiet as [|event rest [_ Hextra] Hrest IH]; cbn [fold_right].
  - reflexivity.
  - now rewrite Hextra, IH.
Qed.

(** Quiet events are safe after forgetting the zero output-charge refinement. *)
Lemma audit_lt_nested_quiet_safe V E B (weight : B -> nat) width events :
  Forall (audit_lt_nested_quiet V E B weight width) events ->
  Forall (audit_lt_nested_event_safe V E B weight width) events.
Proof.
  intro Hquiet; induction Hquiet as [|event rest [Hsafe _] Hrest IH]; constructor; assumption.
Qed.

(** Output charges distribute over consecutive parts of one receipt. *)
Lemma audit_lt_nested_extra_app V E B (first second : list (audit_lt_nested_event V E B)) :
  fold_right (fun event total => audit_lt_nested_extra V E B event + total) 0 (first ++ second) =
  fold_right (fun event total => audit_lt_nested_extra V E B event + total) 0 first +
    fold_right (fun event total => audit_lt_nested_extra V E B event + total) 0 second.
Proof.
  induction first as [|event rest IH]; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

(** The captured nested LT execution fits its original input count and work allowances. *)
Theorem audit_lt_nested_bound : audit_lt_nested_bound_statement.
Proof.
  intros V E B EV g r semis enc source weight result events Hencode Hsource Hrun.
  pose proof (audit_lt_nested_run_count V E B EV g enc source r semis result events Hencode Hrun)
    as Hcount.
  split; [exact Hcount|].
  assert (Horder : Forall (audit_lt_input_vertex V E g r semis) (preorder r)).
  { apply Forall_forall; intros v Hin; apply audit_lt_preorder_vertex; exact Hin. }
  pose proof (audit_lt_nested_buckets_erases V E B EV enc semis (preorder r) Map.empty Hencode)
    as Hbuckets.
  pose proof (audit_lt_nested_buckets_safe V E B EV g enc weight r semis (preorder r) Map.empty
    Hencode Horder) as Hbuild.
  unfold audit_lt_nested_run in Hrun.
  destruct (audit_lt_nested_buckets enc semis (preorder r) Map.empty) as [buckets bucket_events];
    cbn in Hbuckets, Hbuild, Hrun.
  destruct Hrun as [settled [reverse_events [Hreverse Hrun]]].
  assert (Hinitial : audit_lt_state_envelope V E EV g r semis
    (LtState.Make semi_links_empty Map.empty)).
  { split; cbn; [apply audit_semi_links_envelope_empty|apply audit_semi_map_envelope_empty]. }
  assert (Hreverse_order : Forall (audit_lt_input_vertex V E g r semis) (rev (preorder r))).
  { apply Forall_forall; intros v Hin; apply audit_lt_preorder_vertex; now apply in_rev. }
  destruct (audit_lt_nested_reverse_fold_safe V E B EV g enc source weight r semis buckets
    (rev (preorder r)) (LtState.Make semi_links_empty Map.empty) settled reverse_events Hencode
    Hsource Hbuckets Hinitial Hreverse_order Hreverse) as [Hsettled Hreverse_safe].
  destruct Hsettled as [_ Hprovisional].
  destruct (audit_lt_nested_correct_fold_safe V E B EV g enc weight r semis
    (LtState.parents settled)
    (preorder r) Map.empty Hencode Hprovisional (audit_semi_map_envelope_empty V EV _) Horder)
    as [_ Hcorrect_safe].
  destruct (audit_lt_nested_correct_fold enc semis (LtState.parents settled) (preorder r) Map.empty)
    as [output correction]; cbn in Hcorrect_safe, Hrun.
  destruct Hrun as [_ ->].
  set (width := audit_lt_nested_input_width EV g r semis).
  assert (Hsafe : Forall (audit_lt_nested_event_safe V E B weight width)
    (bucket_events ++ [LtNestedOutput (length (preorder r))] ++ reverse_events ++ correction)).
  { repeat rewrite Forall_app; repeat split.
    - apply audit_lt_nested_quiet_safe; exact Hbuild.
    - constructor; [|constructor].
      unfold audit_lt_nested_event_safe, audit_lt_nested_event_work,
        audit_lt_nested_body_event_work, audit_lt_nested_extra; cbn; lia.
    - apply audit_lt_nested_quiet_safe; exact Hreverse_safe.
    - apply audit_lt_nested_quiet_safe; exact Hcorrect_safe. }
  pose proof (audit_lt_nested_safe_work V E B weight width _ Hsafe) as Hwork.
  repeat rewrite audit_lt_nested_extra_app in Hwork.
  rewrite (audit_lt_nested_quiet_extra V E B weight width bucket_events Hbuild) in Hwork.
  rewrite (audit_lt_nested_quiet_extra V E B weight width reverse_events Hreverse_safe) in Hwork.
  rewrite (audit_lt_nested_quiet_extra V E B weight width correction Hcorrect_safe) in Hwork.
  cbn [fold_right audit_lt_nested_extra] in Hwork.
  unfold audit_lt_nested_input_budget.
  cbn [app] in Hwork.
  unfold width in Hwork.
  assert (Hsize : S (length (preorder r)) <= audit_lt_nested_input_event_bound r).
  { unfold audit_lt_nested_input_event_bound; nia. }
  nia.
Qed.

(** * Ordinary event counts *)

(** One ordinary member has a rank-bounded compression receipt and fixed outer work. *)
Lemma audit_lt_member_count V E (EV : encoding V) (r : dfs_result V E)
    semis s st v result events :
  audit_lt_member_run EV r semis s st v result events ->
  length events <= 20 * S (audit_semi_compute_rank_bound r) + 6.
Proof.
  intro Hrun; inversion Hrun; subst.
  match goal with
  | Hcompress : audit_semi_compress_run _ _ _ _ _ _ ?inner,
    Hscore : audit_semi_score_counted _ _ _ ?selected = (_, ?score_events),
    Hrank : audit_semi_rank_counted _ _ _ = (_, ?rank_events) |- _ =>
    pose proof (audit_semi_compress_count V E EV r semis (LtState.links st) v _ inner Hcompress)
      as Hcount;
    pose proof (audit_semi_rank_in_producer V E EV r v) as Hrank_bound;
    pose proof (audit_semi_score_counted_length V E EV r semis selected) as Hscore_length;
    pose proof (audit_semi_rank_counted_length V E EV r s) as Hrank_length;
    rewrite Hscore in Hscore_length; rewrite Hrank in Hrank_length;
    cbn in Hscore_length, Hrank_length;
    unfold audit_semi_compress_event_bound in Hcount;
    change (Pos.to_nat (semi_rank EV r v) <= audit_semi_compute_rank_bound r) in Hrank_bound;
    repeat rewrite length_app; repeat rewrite length_map; cbn; lia
  end.
Qed.

(** An ordinary member fold charges each listed vertex once. *)
Lemma audit_lt_members_count V E (EV : encoding V) (r : dfs_result V E)
    semis s vertices st result events :
  audit_lt_members_run EV r semis s vertices st result events ->
  length events <= 1 + length vertices * (20 * S (audit_semi_compute_rank_bound r) + 7).
Proof.
  intro Hrun; induction Hrun.
  - cbn; lia.
  - pose proof (audit_lt_member_count V E EV r semis s initial v middle here H) as Hhere.
    cbn [length]; rewrite length_app; nia.
Qed.

(** One ordinary reverse step reads at most the stated bucket size. *)
Lemma audit_lt_reverse_count V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis buckets st s result events limit :
  length (lt_bucket EV buckets s) <= limit ->
  audit_lt_reverse_run EV g r semis buckets st s result events ->
  length events <= 6 + limit * (20 * S (audit_semi_compute_rank_bound r) + 7).
Proof.
  intros Hbucket Hrun; inversion Hrun; subst result events members.
  all: match goal with
    | Hget : ?bucket = Map.get _ _ _,
      Hmembers : audit_lt_members_run _ _ _ _ ?members _ _ ?member_events |- _ =>
      pose proof (audit_lt_members_count V E EV r semis s members st _ member_events Hmembers)
        as Hcount;
      unfold lt_bucket in Hbucket; rewrite <- Hget in Hbucket
    end.
  all: repeat rewrite length_app; cbn; nia.
Qed.

(** The ordinary reverse fold charges one bounded step per visited vertex. *)
Lemma audit_lt_reverse_fold_count V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis buckets vertices st result events limit :
  (forall s, length (lt_bucket EV buckets s) <= limit) ->
  audit_lt_reverse_fold_run EV g r semis buckets vertices st result events ->
  length events <= 1 + length vertices *
    (7 + limit * (20 * S (audit_semi_compute_rank_bound r) + 7)).
Proof.
  intros Hbucket Hrun; induction Hrun.
  - cbn; lia.
  - pose proof (audit_lt_reverse_count V E EV g r semis buckets initial v middle here limit
      (Hbucket v) H) as Hhere.
    cbn [length]; rewrite length_app; nia.
Qed.

(** Ordinary bucket construction emits at most five events per original vertex. *)
Lemma audit_lt_buckets_count V E (EV : encoding V) semis vertices buckets :
  length (snd (audit_lt_buckets_counted (E := E) EV semis vertices buckets)) <=
    1 + 5 * length vertices.
Proof.
  revert buckets; induction vertices as [|v rest IH]; intro buckets; cbn [audit_lt_buckets_counted].
  - cbn; lia.
  - destruct (Map.get EV v semis) as [s|].
    + destruct (Map.get EV s buckets) as [old|].
      * specialize (IH (Map.set EV s (v :: old) buckets)).
        destruct (audit_lt_buckets_counted EV semis rest (Map.set EV s (v :: old) buckets));
          cbn in *; lia.
      * specialize (IH (Map.set EV s [v] buckets)).
        destruct (audit_lt_buckets_counted EV semis rest (Map.set EV s [v] buckets)); cbn in *; lia.
    + specialize (IH buckets).
      destruct (audit_lt_buckets_counted EV semis rest buckets); cbn in *; lia.
Qed.

(** Ordinary correction emits a constant number of events on either equality branch. *)
Lemma audit_lt_correct_count V E (EV : encoding V) semis provisional corrected v :
  length (snd (audit_lt_correct_counted (E := E) EV semis provisional corrected v)) <= 8.
Proof.
  unfold audit_lt_correct_counted.
  destruct (Map.get EV v provisional) as [u|]; [|cbn; lia].
  pose proof (audit_semi_value_counted_details V EV semis v) as [_ Hvalue].
  destruct (audit_semi_value_counted EV semis v) as [value value_events];
    cbn in Hvalue; subst value_events.
  destruct (Pos.eqb (encode EV u) (encode EV value)).
  - cbn; lia.
  - pose proof (audit_semi_value_counted_details V EV corrected u) as [_ Hparent].
    destruct (audit_semi_value_counted EV corrected u) as [parent parent_events];
      cbn in Hparent; subst parent_events; cbn; lia.
Qed.

(** Ordinary correction visits each input vertex once. *)
Lemma audit_lt_correct_fold_count V E (EV : encoding V) semis provisional vertices corrected :
  length (snd (audit_lt_correct_fold (E := E) EV semis provisional vertices corrected)) <=
    1 + 9 * length vertices.
Proof.
  revert corrected; induction vertices as [|v rest IH]; intro corrected;
    cbn [audit_lt_correct_fold].
  - cbn; lia.
  - pose proof (audit_lt_correct_count V E EV semis provisional corrected v) as Hhere.
    destruct (audit_lt_correct_counted EV semis provisional corrected v) as [middle here];
      cbn in Hhere.
    specialize (IH middle).
    destruct (audit_lt_correct_fold EV semis provisional rest middle) as [result later];
      cbn in IH |- *.
    rewrite length_app; cbn; lia.
Qed.

(** Every ordinary LT run fits its original input event-count allowance. *)
Lemma audit_lt_compute_run_count V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis result events :
  audit_lt_compute_run EV g r semis result events -> length events <= audit_lt_event_bound r.
Proof.
  intro Hrun; unfold audit_lt_compute_run in Hrun.
  pose proof (audit_lt_buckets_erases V E EV semis (preorder r) Map.empty) as Herase.
  pose proof (audit_lt_buckets_count V E EV semis (preorder r) Map.empty) as Hbuild.
  destruct (audit_lt_buckets_counted EV semis (preorder r) Map.empty) as [buckets bucket_events];
    cbn in Herase, Hbuild, Hrun.
  destruct Hrun as [settled [reverse_events [Hreverse Hrun]]].
  pose proof (audit_lt_reverse_fold_count V E EV g r semis buckets (rev (preorder r))
    (LtState.Make semi_links_empty Map.empty) settled reverse_events (length (preorder r))) as Hrev.
  assert (Hbucket_bound : forall s, length (lt_bucket EV buckets s) <= length (preorder r)).
  { intro s; rewrite Herase; apply audit_lt_bucket_index_length. }
  specialize (Hrev Hbucket_bound Hreverse); rewrite length_rev in Hrev.
  pose proof (audit_lt_correct_fold_count V E EV semis (LtState.parents settled) (preorder r)
    Map.empty) as Hcorrect.
  destruct (audit_lt_correct_fold EV semis (LtState.parents settled) (preorder r) Map.empty)
    as [output correction]; cbn in Hcorrect, Hrun.
  destruct Hrun as [_ ->].
  repeat rewrite length_app; cbn [length]; rewrite length_app.
  unfold audit_lt_event_bound.
  pose proof (Nat.le_0_l (audit_semi_compute_rank_bound r)); nia.
Qed.

(** * Ordinary input-derived operand accounting *)

(** The abstract and nested input widths use the same positive-key bit size. *)
Lemma audit_lt_input_width_agrees V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis :
  audit_lt_input_width EV g r semis = audit_lt_nested_input_width EV g r semis.
Proof.
  reflexivity.
Qed.

(** The output marker alone carries an additional input-size charge. *)
Definition audit_lt_extra V E (event : audit_lt_call V E) : nat :=
  match event with
  | AuditLtOutput size => S size
  | _ => 0
  end.

(** Recorded keys and comparison operands must fit the original input width. *)
Definition audit_lt_call_safe V E (EV : encoding V) width (event : audit_lt_call V E) : Prop :=
  match event with
  | AuditLtInner item => audit_semi_call_safe V EV width item
  | AuditLtBucketGet v _ _
  | AuditLtBucketSet v _ _
  | AuditLtTreeGet v _ _
  | AuditLtLink v _ _ => Pos.size_nat (encode EV v) <= width
  | AuditLtEncode _ code => Pos.size_nat code <= width
  | AuditLtEq a b _ => Pos.size_nat a <= width /\ Pos.size_nat b <= width
  | AuditLtCase _
  | AuditLtSource _ _
  | AuditLtOutput _ => True
  end.

(** Each safe ordinary event fits its fixed allowance and explicit output-size charge. *)
Lemma audit_lt_call_work_safe V E (EV : encoding V) width event :
  audit_lt_call_safe V E EV width event ->
  audit_lt_event_work EV event <= 256 + 16 * width + audit_lt_extra V E event.
Proof.
  destruct event; cbn [audit_lt_call_safe]; intro Hsafe;
    unfold audit_lt_event_work, audit_lt_extra, audit_encoding_weight, audit_get_weight,
      audit_set_weight, audit_key_bits_weight, audit_binary_weight;
    cbn [audit_lt_event_work audit_lt_extra] in *; try rewrite !audit_dfs_positive_z_bits.
  all: try lia.
  match goal with
  | H : audit_semi_call_safe _ _ _ ?item |- _ =>
    pose proof (audit_semi_call_work_safe V EV width item H); lia
  end.
Qed.

(** Safe events sum to their input-width allowance plus output-marker charges. *)
Lemma audit_lt_calls_work_safe V E (EV : encoding V) width events :
  Forall (audit_lt_call_safe V E EV width) events ->
  fold_right (fun event total => audit_lt_event_work EV event + total) 0 events <=
    length events * (256 + 16 * width) +
      fold_right (fun event total => audit_lt_extra V E event + total) 0 events.
Proof.
  intro Hsafe; induction Hsafe as [|event rest Hevent Hrest IH].
  - reflexivity.
  - cbn [fold_right length].
    pose proof (audit_lt_call_work_safe V E EV width event Hevent); lia.
Qed.

(** Wrapping safe semidominator events preserves all operand bounds. *)
Lemma audit_lt_inner_safe V E (EV : encoding V) width events :
  Forall (audit_semi_call_safe V EV width) events ->
  Forall (audit_lt_call_safe V E EV width) (map AuditLtInner events).
Proof.
  intro Hsafe; induction Hsafe; cbn; constructor; assumption.
Qed.

(** Quiet ordinary events have no output-size charge. *)
Definition audit_lt_quiet V E (EV : encoding V) width (event : audit_lt_call V E) : Prop :=
  audit_lt_call_safe V E EV width event /\ audit_lt_extra V E event = 0.

(** Wrapped ordinary semidominator receipts contain no LT output marker. *)
Lemma audit_lt_inner_quiet V E (EV : encoding V) width events :
  Forall (audit_semi_call_safe V EV width) events ->
  Forall (audit_lt_quiet V E EV width) (map AuditLtInner events).
Proof.
  intro Hsafe; induction Hsafe; cbn; constructor; [split; [assumption|reflexivity]|assumption].
Qed.

(** An ordinary member preserves its input envelope and records only bounded operands. *)
Lemma audit_lt_member_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis s st v result events :
  audit_lt_state_envelope V E EV g r semis st ->
  audit_lt_input_vertex V E g r semis s -> audit_lt_input_vertex V E g r semis v ->
  audit_lt_member_run EV r semis s st v result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis)) events.
Proof.
  intros [Hlinks Hparents] Hs Hv Hrun; inversion Hrun; subst.
  rewrite audit_lt_input_width_agrees.
  set (width := audit_lt_nested_input_width EV g r semis).
  match goal with
  | Hcompress : audit_semi_compress_run _ _ _ _ _ _ ?inner,
    Hscore : audit_semi_score_counted _ _ _ ?selected = (?score, ?score_events),
    Hrank : audit_semi_rank_counted _ _ _ = (?rank, ?rank_events) |- _ =>
    pose proof (audit_lt_query_width V E EV g r semis (LtState.links st) v Hlinks Hv) as Hwidth;
    pose proof (audit_semi_compress_safe V E EV r semis (LtState.links st) v v _ inner
      Hcompress (or_introl eq_refl)) as Hinner;
    pose proof (audit_semi_compress_result_in V E EV r semis (LtState.links st) v v _ inner
      Hcompress (or_introl eq_refl)) as Hselected;
    cbn in Hselected;
    assert (Hlocal : audit_semi_input_vertex V semis (LtState.links st) v selected)
      by (destruct part as [best|]; cbn [fst snd] in Hselected |- *;
        [exact (proj2 Hselected)|left; reflexivity]);
    pose proof (audit_lt_query_vertex V E EV g r semis (LtState.links st) v selected
      Hlinks Hv Hlocal) as Hselected_vertex;
    pose proof (audit_lt_compress_envelope V E EV g r semis (LtState.links st) v _ inner
      Hlinks Hv Hcompress) as Hlinks';
    pose proof (audit_semi_score_counted_safe V E EV r semis (LtState.links st) v selected Hlocal)
      as Hscore_safe;
    rewrite Hscore in Hscore_safe; cbn [snd] in Hscore_safe;
    pose proof (audit_semi_score_counted_erases V E EV r semis selected) as Hscore_eq;
    rewrite Hscore in Hscore_eq; cbn in Hscore_eq;
    pose proof (audit_semi_rank_counted_erases V E EV r s) as Hrank_eq;
    rewrite Hrank in Hrank_eq; cbn in Hrank_eq;
    pose proof (audit_semi_rank_counted_details V E EV r s) as Hrank_details;
    rewrite Hrank in Hrank_details; cbn in Hrank_details;
    pose proof (audit_lt_input_vertex_width V E EV g r semis s Hs) as Hswidth;
    pose proof (audit_lt_input_vertex_width V E EV g r semis v Hv) as Hvwidth;
    pose proof (audit_semi_nested_rank_width V E EV r semis (LtState.links st) v
      (semi_value EV semis selected)) as Hscore_width;
    pose proof (audit_semi_nested_rank_width V E EV r semis (LtState.links st) v s) as Hrank_width;
    split
  end.
  - split; cbn; [exact Hlinks'|].
    apply audit_semi_map_envelope_set; try assumption; destruct (Pos.ltb score rank); assumption.
  - rewrite audit_semi_widths_agree in Hinner, Hscore_safe.
    pose proof (audit_semi_call_safe_mono V EV _ width inner Hwidth Hinner) as Hinner'.
    pose proof (audit_semi_call_safe_mono V EV _ width score_events Hwidth Hscore_safe) as Hscore'.
    repeat rewrite Forall_app; repeat split.
    + apply audit_lt_inner_quiet; exact Hinner'.
    + constructor; [split; [exact I|reflexivity]|constructor].
    + apply audit_lt_inner_quiet; exact Hscore'.
    + apply audit_lt_inner_quiet; rewrite Hrank_details.
      constructor; [exact Hswidth|constructor].
    + constructor.
      * split; [|reflexivity].
        cbn [audit_lt_call_safe audit_semi_call_safe]; rewrite Hscore_eq, Hrank_eq; lia.
      * constructor; [split; [exact Hvwidth|reflexivity]|constructor].
Qed.

(** An ordinary member fold preserves state and all recorded operand bounds. *)
Lemma audit_lt_members_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis s vertices st result events :
  audit_lt_state_envelope V E EV g r semis st ->
  audit_lt_input_vertex V E g r semis s ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  audit_lt_members_run EV r semis s vertices st result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis)) events.
Proof.
  intros Hstate Hs Hvertices Hrun; revert Hstate Hvertices.
  induction Hrun; intros Hstate Hvertices.
  - split; [exact Hstate|].
    constructor; [split; [exact I|reflexivity]|constructor].
  - inversion Hvertices as [|? ? Hv Hrest]; subst.
    destruct (audit_lt_member_safe V E EV g r semis s initial v middle here Hstate Hs Hv H)
      as [Hmiddle Hhere].
    destruct (IHHrun Hmiddle Hrest) as [Hresult Hlater].
    split; [exact Hresult|].
    constructor; [split; [exact I|reflexivity]|].
    apply Forall_app; split; assumption.
Qed.

(** Each ordinary reverse step retains its operand envelope. *)
Lemma audit_lt_reverse_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis buckets st s result events :
  buckets = lt_bucket_index EV semis (preorder r) ->
  audit_lt_state_envelope V E EV g r semis st -> audit_lt_input_vertex V E g r semis s ->
  audit_lt_reverse_run EV g r semis buckets st s result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis)) events.
Proof.
  intros Hbuckets Hstate Hs Hrun; inversion Hrun; subst result events members.
  all: match goal with
    | Hbucket : ?bucket = Map.get _ _ _,
      Hmembers : audit_lt_members_run _ _ _ _ ?members _ ?settled ?member_events |- _ =>
      pose proof (audit_lt_input_vertex_width V E EV g r semis s Hs) as Hwidth;
      rewrite <- audit_lt_input_width_agrees in Hwidth;
      assert (Hvertices : Forall (audit_lt_input_vertex V E g r semis) members)
        by (rewrite Hbucket; change (Forall (audit_lt_input_vertex V E g r semis)
          (lt_bucket EV buckets s)); rewrite Hbuckets; apply audit_lt_bucket_vertices);
      destruct (audit_lt_members_safe V E EV g r semis s members st settled member_events
        Hstate Hs Hvertices Hmembers) as [Hsettled Hmember_safe]
    end.
  - split; [exact Hsettled|].
    cbn [app]; constructor; [split; [exact Hwidth|reflexivity]|].
    apply Forall_app; split; [exact Hmember_safe|].
    constructor; [split; [exact Hwidth|reflexivity]|].
    constructor; [split; [exact I|reflexivity]|constructor].
  - match goal with
    | Htree : Map.get _ _ (tree_edge ?dfs) = Some ?edge,
      Hparent : ?parent = Graph.source _ ?edge |- _ =>
      assert (Hparent_vertex : audit_lt_input_vertex V E g r semis parent)
        by (rewrite Hparent; apply (audit_lt_tree_source_vertex V E EV g r semis s edge);
          exact Htree);
      split
    end.
    + destruct Hsettled as [Hlinks Hparents]; split; cbn; [|exact Hparents].
      apply audit_semi_links_envelope_link; assumption.
    + cbn [app]; constructor; [split; [exact Hwidth|reflexivity]|].
      apply Forall_app; split; [exact Hmember_safe|].
      constructor; [split; [exact Hwidth|reflexivity]|].
      constructor; [split; [exact I|reflexivity]|].
      constructor; [split; [exact I|reflexivity]|].
      constructor; [split; [exact Hwidth|reflexivity]|constructor].
Qed.

(** Ordinary reverse traversal preserves the envelope and each captured event. *)
Lemma audit_lt_reverse_fold_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis buckets vertices st result events :
  buckets = lt_bucket_index EV semis (preorder r) ->
  audit_lt_state_envelope V E EV g r semis st ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  audit_lt_reverse_fold_run EV g r semis buckets vertices st result events ->
  audit_lt_state_envelope V E EV g r semis result /\
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis)) events.
Proof.
  intros Hbuckets Hstate Hvertices Hrun; revert Hstate Hvertices.
  induction Hrun; intros Hstate Hvertices.
  - split; [exact Hstate|].
    constructor; [split; [exact I|reflexivity]|constructor].
  - inversion Hvertices as [|? ? Hv Hrest].
    destruct (audit_lt_reverse_safe V E EV g r semis buckets initial v middle here
      Hbuckets Hstate Hv H) as [Hmiddle Hhere].
    destruct (IHHrun Hmiddle Hrest) as [Hresult Hlater].
    split; [exact Hresult|].
    constructor; [split; [exact I|reflexivity]|].
    apply Forall_app; split; assumption.
Qed.

(** Bucket construction uses only original order vertices and semidominator values. *)
Lemma audit_lt_buckets_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis vertices buckets :
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis))
    (snd (audit_lt_buckets_counted (E := E) EV semis vertices buckets)).
Proof.
  intro Hvertices; revert buckets.
  induction Hvertices as [|v rest Hv Hrest IH]; intro buckets; cbn [audit_lt_buckets_counted].
  - constructor; [split; [exact I|reflexivity]|constructor].
  - pose proof (audit_lt_input_vertex_width V E EV g r semis v Hv) as Hvwidth.
    rewrite <- audit_lt_input_width_agrees in Hvwidth.
    destruct (Map.get EV v semis) as [s|] eqn:Hget.
    + destruct (audit_semi_map_get_value_in V V EV semis v s Hget) as [key Hin].
      pose proof (audit_lt_input_vertex_width V E EV g r semis s
        (proj2 (audit_lt_semi_row V E g r semis key s Hin))) as Hswidth.
      rewrite <- audit_lt_input_width_agrees in Hswidth.
      destruct (Map.get EV s buckets) as [old|].
      * specialize (IH (Map.set EV s (v :: old) buckets)).
        destruct (audit_lt_buckets_counted EV semis rest (Map.set EV s (v :: old) buckets));
          cbn in IH |- *.
        constructor; [split; [exact I|reflexivity]|].
        constructor; [split; [exact Hvwidth|reflexivity]|].
        constructor; [split; [exact I|reflexivity]|].
        constructor; [split; [exact Hswidth|reflexivity]|].
        constructor; [split; [exact Hswidth|reflexivity]|exact IH].
      * specialize (IH (Map.set EV s [v] buckets)).
        destruct (audit_lt_buckets_counted EV semis rest (Map.set EV s [v] buckets));
          cbn in IH |- *.
        constructor; [split; [exact I|reflexivity]|].
        constructor; [split; [exact Hvwidth|reflexivity]|].
        constructor; [split; [exact I|reflexivity]|].
        constructor; [split; [exact Hswidth|reflexivity]|].
        constructor; [split; [exact Hswidth|reflexivity]|exact IH].
    + specialize (IH buckets).
      destruct (audit_lt_buckets_counted EV semis rest buckets); cbn in IH |- *.
      constructor; [split; [exact I|reflexivity]|].
      constructor; [split; [exact Hvwidth|reflexivity]|].
      constructor; [split; [exact I|reflexivity]|exact IH].
Qed.

(** A counted value lookup preserves its input vertex and records a bounded key. *)
Lemma audit_lt_value_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis v :
  audit_lt_input_vertex V E g r semis v ->
  audit_lt_input_vertex V E g r semis (fst (audit_semi_value_counted EV semis v)) /\
  Forall (audit_semi_call_safe V EV (audit_lt_input_width EV g r semis))
    (snd (audit_semi_value_counted EV semis v)).
Proof.
  intro Hv.
  pose proof (audit_semi_value_counted_details V EV semis v) as [Hvalue Hevents].
  rewrite Hvalue; split; [apply audit_lt_semi_value_vertex; exact Hv|].
  rewrite Hevents; constructor; [|constructor].
  rewrite audit_lt_input_width_agrees; apply audit_lt_input_vertex_width; exact Hv.
Qed.

(** Ordinary correction preserves the parent envelope and records only input-bounded operands. *)
Lemma audit_lt_correct_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis provisional corrected v :
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) provisional ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) corrected ->
  audit_lt_input_vertex V E g r semis v ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis)
    (fst (audit_lt_correct_counted (E := E) EV semis provisional corrected v)) /\
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis))
    (snd (audit_lt_correct_counted (E := E) EV semis provisional corrected v)).
Proof.
  intros Hprovisional Hcorrected Hv.
  pose proof (audit_lt_input_vertex_width V E EV g r semis v Hv) as Hvwidth.
  rewrite <- audit_lt_input_width_agrees in Hvwidth.
  unfold audit_lt_correct_counted.
  destruct (Map.get EV v provisional) as [u|] eqn:Hfirst.
  - assert (Hu : audit_lt_input_vertex V E g r semis u).
    { exact (proj2 ((proj2 Hprovisional) v u Hfirst)). }
    pose proof (audit_lt_input_vertex_width V E EV g r semis u Hu) as Huwidth.
    rewrite <- audit_lt_input_width_agrees in Huwidth.
    destruct (audit_lt_value_safe V E EV g r semis v Hv) as [Hvalue_vertex Hvalue_safe].
    destruct (audit_semi_value_counted EV semis v) as [value value_events] eqn:Hvalue;
      cbn in Hvalue_vertex, Hvalue_safe.
    pose proof (audit_lt_input_vertex_width V E EV g r semis value Hvalue_vertex) as Hvaluewidth.
    rewrite <- audit_lt_input_width_agrees in Hvaluewidth.
    destruct (Pos.eqb (encode EV u) (encode EV value)) eqn:Hequal.
    + split.
      * apply audit_semi_map_envelope_set; assumption.
      * cbn [app].
        constructor; [split; [exact Hvwidth|reflexivity]|].
        constructor; [split; [exact I|reflexivity]|].
        constructor; [split; [exact Huwidth|reflexivity]|].
        apply Forall_app; split; [apply audit_lt_inner_quiet; exact Hvalue_safe|].
        constructor; [split; [exact Hvaluewidth|reflexivity]|].
        constructor; [split; [split; assumption|reflexivity]|].
        constructor; [split; [exact Hvwidth|reflexivity]|constructor].
    + pose proof (audit_semi_value_counted_details V EV corrected u)
        as [Hparent_value Hparent_events].
      destruct (audit_semi_value_counted EV corrected u) as [parent parent_events] eqn:Hparent;
        cbn in Hparent_value, Hparent_events.
      assert (Hparent_vertex : audit_lt_input_vertex V E g r semis parent).
      { rewrite Hparent_value; unfold semi_value.
        destruct (Map.get EV u corrected) as [p|] eqn:Hlookup; [|exact Hu].
        exact (proj2 ((proj2 Hcorrected) u p Hlookup)). }
      subst parent_events; split.
      * apply audit_semi_map_envelope_set; assumption.
      * cbn [app].
        constructor; [split; [exact Hvwidth|reflexivity]|].
        constructor; [split; [exact I|reflexivity]|].
        constructor; [split; [exact Huwidth|reflexivity]|].
        apply Forall_app; split; [apply audit_lt_inner_quiet; exact Hvalue_safe|].
        constructor; [split; [exact Hvaluewidth|reflexivity]|].
        constructor; [split; [split; assumption|reflexivity]|].
        constructor; [split; [exact Huwidth|reflexivity]|].
        constructor; [split; [exact Hvwidth|reflexivity]|constructor].
  - split; [exact Hcorrected|].
    cbn; constructor; [split; [exact Hvwidth|reflexivity]|].
    constructor; [split; [exact I|reflexivity]|constructor].
Qed.

(** Ordinary correction over a list preserves the envelope and all operand bounds. *)
Lemma audit_lt_correct_fold_safe V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    semis provisional vertices corrected :
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) provisional ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis) corrected ->
  Forall (audit_lt_input_vertex V E g r semis) vertices ->
  audit_semi_map_envelope V EV (audit_lt_input_vertex V E g r semis)
    (fst (audit_lt_correct_fold (E := E) EV semis provisional vertices corrected)) /\
  Forall (audit_lt_quiet V E EV (audit_lt_input_width EV g r semis))
    (snd (audit_lt_correct_fold (E := E) EV semis provisional vertices corrected)).
Proof.
  intros Hprovisional Hcorrected Hvertices; revert corrected Hcorrected.
  induction Hvertices as [|v rest Hv Hrest IH]; intros corrected Hcorrected;
    cbn [audit_lt_correct_fold].
  - split; [exact Hcorrected|].
    constructor; [split; [exact I|reflexivity]|constructor].
  - destruct (audit_lt_correct_safe V E EV g r semis provisional corrected v
      Hprovisional Hcorrected Hv) as [Hmiddle Hhere].
    destruct (audit_lt_correct_counted EV semis provisional corrected v) as [middle here];
      cbn in Hmiddle, Hhere.
    destruct (IH middle Hmiddle) as [Hresult Hlater].
    destruct (audit_lt_correct_fold EV semis provisional rest middle) as [result later];
      cbn in Hresult, Hlater |- *.
    split; [exact Hresult|].
    constructor; [split; [exact I|reflexivity]|].
    apply Forall_app; split; assumption.
Qed.

(** Quiet ordinary events contribute no output marker charge. *)
Lemma audit_lt_quiet_extra V E (EV : encoding V) width events :
  Forall (audit_lt_quiet V E EV width) events ->
  fold_right (fun event total => audit_lt_extra V E event + total) 0 events = 0.
Proof.
  intro Hquiet; induction Hquiet as [|event rest [_ Hextra] Hrest IH]; cbn [fold_right].
  - reflexivity.
  - now rewrite Hextra, IH.
Qed.

(** Forgetting the zero marker charge retains all ordinary operand bounds. *)
Lemma audit_lt_quiet_safe V E (EV : encoding V) width events :
  Forall (audit_lt_quiet V E EV width) events -> Forall (audit_lt_call_safe V E EV width) events.
Proof.
  intro Hquiet; induction Hquiet as [|event rest [Hsafe _] Hrest IH]; constructor; assumption.
Qed.

(** Ordinary output charges distribute over consecutive receipt segments. *)
Lemma audit_lt_extra_app V E (first second : list (audit_lt_call V E)) :
  fold_right (fun event total => audit_lt_extra V E event + total) 0 (first ++ second) =
  fold_right (fun event total => audit_lt_extra V E event + total) 0 first +
    fold_right (fun event total => audit_lt_extra V E event + total) 0 second.
Proof.
  induction first as [|event rest IH]; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

(** Every ordinary run's work fits its original input-derived budget. *)
Lemma audit_lt_compute_run_work V E (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis result events :
  audit_lt_compute_run EV g r semis result events ->
  audit_lt_model_work EV events <= audit_lt_input_budget EV g r semis.
Proof.
  intro Hrun.
  pose proof (audit_lt_compute_run_count V E EV g r semis result events Hrun) as Hcount.
  assert (Horder : Forall (audit_lt_input_vertex V E g r semis) (preorder r)).
  { apply Forall_forall; intros v Hin; apply audit_lt_preorder_vertex; exact Hin. }
  pose proof (audit_lt_buckets_erases V E EV semis (preorder r) Map.empty) as Hbuckets.
  pose proof (audit_lt_buckets_safe V E EV g r semis (preorder r) Map.empty Horder) as Hbuild.
  unfold audit_lt_compute_run in Hrun.
  destruct (audit_lt_buckets_counted EV semis (preorder r) Map.empty) as [buckets bucket_events];
    cbn in Hbuckets, Hbuild, Hrun.
  destruct Hrun as [settled [reverse_events [Hreverse Hrun]]].
  assert (Hinitial : audit_lt_state_envelope V E EV g r semis
    (LtState.Make semi_links_empty Map.empty)).
  { split; cbn; [apply audit_semi_links_envelope_empty|apply audit_semi_map_envelope_empty]. }
  assert (Hreverse_order : Forall (audit_lt_input_vertex V E g r semis) (rev (preorder r))).
  { apply Forall_forall; intros v Hin; apply audit_lt_preorder_vertex; now apply in_rev. }
  destruct (audit_lt_reverse_fold_safe V E EV g r semis buckets (rev (preorder r))
    (LtState.Make semi_links_empty Map.empty) settled reverse_events Hbuckets Hinitial
    Hreverse_order
    Hreverse) as [Hsettled Hreverse_safe].
  destruct Hsettled as [_ Hprovisional].
  destruct (audit_lt_correct_fold_safe V E EV g r semis (LtState.parents settled) (preorder r)
    Map.empty Hprovisional (audit_semi_map_envelope_empty V EV _) Horder) as [_ Hcorrect_safe].
  destruct (audit_lt_correct_fold EV semis (LtState.parents settled) (preorder r) Map.empty)
    as [output correction]; cbn in Hcorrect_safe, Hrun.
  destruct Hrun as [_ ->].
  set (width := audit_lt_input_width EV g r semis).
  assert (Hsafe : Forall (audit_lt_call_safe V E EV width)
    (bucket_events ++ [AuditLtOutput (length (preorder r))] ++ reverse_events ++ correction)).
  { repeat rewrite Forall_app; repeat split.
    - apply audit_lt_quiet_safe; exact Hbuild.
    - constructor; [exact I|constructor].
    - apply audit_lt_quiet_safe; exact Hreverse_safe.
    - apply audit_lt_quiet_safe; exact Hcorrect_safe. }
  pose proof (audit_lt_calls_work_safe V E EV width _ Hsafe) as Hwork.
  repeat rewrite audit_lt_extra_app in Hwork.
  rewrite (audit_lt_quiet_extra V E EV width bucket_events Hbuild) in Hwork.
  rewrite (audit_lt_quiet_extra V E EV width reverse_events Hreverse_safe) in Hwork.
  rewrite (audit_lt_quiet_extra V E EV width correction Hcorrect_safe) in Hwork.
  cbn [fold_right audit_lt_extra app] in Hwork; unfold width in Hwork.
  unfold audit_lt_model_work, audit_lt_input_budget.
  assert (Hsize : S (length (preorder r)) <= audit_lt_event_bound r).
  { unfold audit_lt_event_bound; nia. }
  nia.
Qed.

(** The ordinary LT run returns the source result within both input-derived bounds. *)
Theorem audit_lt_compute_correct : audit_lt_compute_statement.
Proof.
  intros V E EV g r semis.
  destruct (audit_lt_compute_erases V E EV g r semis) as [events Hrun].
  exists (lt_compute EV g r semis), events.
  split; [exact Hrun|]; split; [reflexivity|].
  split.
  - eapply audit_lt_compute_run_count; exact Hrun.
  - eapply audit_lt_compute_run_work; exact Hrun.
Qed.
