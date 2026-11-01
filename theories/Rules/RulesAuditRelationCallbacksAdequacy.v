(** * Relation callback source adequacy

    Source receipts follow the actual predicate encodings and environment calls.
    For example, duplicate predicates retain separate encoder bodies.
    Builds on: RulesAuditRelationCallbacks and relation snapshot adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditFinSet CollectionsAuditFinSetAdequacy
  CollectionsAuditElements
  CollectionsAuditElementsAdequacy.
From Galois.Rules Require Import RulesSyntax RulesJoin RulesAuditRelations
  RulesAuditRelationsAdequacy RulesAuditPrepareCallbacks RulesAuditRelationCallbacks.
Import List.ListNotations.

(** * Predicate set encoding receipts *)

(** The finite-set fold records one exact encoding entry for each input occurrence. *)
Lemma rules_relation_fold_entries P (E : encoding P) keys initial :
    rules_relation_entries (snd (audit_finset_fold (rules_encoder E) keys initial)) =
      map (fun p => RulesEncodeEntry p (encode E p)) keys.
Proof.
  revert initial. induction keys as [|p rest IH]; intro initial.
  - reflexivity.
  - cbn [audit_finset_fold audit_finset_add rules_encoder].
    destruct (audit_trie_set (encode E p) (p, tt) initial) as [next body].
    specialize (IH next).
    destruct (audit_finset_fold (rules_encoder E) rest next) as [out events]. cbn in IH.
    cbn [snd rules_relation_entries flat_map app map]. now rewrite IH.
Qed.

(** Body-work addition respects concatenation of event groups. *)
Lemma rules_relation_bodies_work_app B weight (left right : list (list (list B))) :
    rules_predicate_bodies_work weight (left ++ right) =
      rules_predicate_bodies_work weight left + rules_predicate_bodies_work weight right.
Proof.
  unfold rules_predicate_bodies_work. induction left as [|group rest IH];
    cbn [app fold_right]; lia.
Qed.

(** One source body exists for every actual predicate encoding, including duplicates. *)
Lemma rules_relation_encoding_bodies P B (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) keys :
    rules_predicate_source_laws E source weight bound ->
    exists bodies,
      Forall2 (rules_relation_entry_source source)
        (map (fun p => RulesEncodeEntry p (encode E p)) keys) bodies /\
      fold_right (fun body n => fold_right (fun item total => weight item + total) 0 body + n)
        0 bodies <= fold_right (fun p n => bound p + n) 0 keys.
Proof.
  intros [Hexists Hbound]. induction keys as [|p rest IH].
  - exists []. split; constructor.
  - destruct (Hexists p) as [body Hsource]. destruct IH as [bodies [Hsources Hwork]].
    exists (body :: bodies). split.
    + constructor; [exact Hsource | exact Hsources].
    + cbn [fold_right]. specialize (Hbound p (encode E p) body Hsource). lia.
Qed.

(** Predicate collection has no external callback bodies. *)
Lemma rules_relation_predicate_sources P B (source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) weight atoms :
    exists bodies, rules_relation_trace_source source env_source
      (snd (rules_relation_predicates atoms)) bodies /\
      rules_predicate_bodies_work weight bodies = 0.
Proof.
  induction atoms as [|a rest IH]; cbn [rules_relation_predicates].
  - exists [[]]. split; [constructor; [reflexivity | constructor] | reflexivity].
  - destruct IH as [tail_bodies [Htail Hwork]].
    destruct (rules_relation_predicates rest) as [tail events]. cbn in Htail.
    exists ([] :: [] :: tail_bodies ++ [[]]). split.
    + unfold rules_relation_trace_source in *.
      constructor; [reflexivity |]. constructor; [reflexivity |].
      apply Forall2_app; [exact Htail |]. constructor; [reflexivity | constructor].
    + change (rules_predicate_bodies_work weight (tail_bodies ++ [[]]) = 0).
      rewrite rules_relation_bodies_work_app. cbn [rules_predicate_bodies_work fold_right].
      lia.
Qed.

(** Each row enumeration retains the environment body for its actual predicate and result. *)
Lemma rules_relation_rows_sources P B (env : P -> FinSet.t tuple)
    (source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) weight env_bound keys :
    rules_environment_source_laws env env_source weight env_bound ->
    exists bodies, rules_relation_trace_source source env_source
      (snd (rules_relation_rows_counted env keys)) bodies /\
      rules_predicate_bodies_work weight bodies <=
        fold_right (fun p n => env_bound p + n) 0 keys.
Proof.
  intros [Hexists Hbound]. induction keys as [|p rest IH]; cbn [rules_relation_rows_counted].
  - exists [[]]. split; [constructor; [reflexivity | constructor] | reflexivity].
  - destruct (Hexists p) as [body Hsource]. destruct IH as [tail_bodies [Htail Hwork]].
    destruct (audit_finset_elements (env p)) as [rows events].
    destruct (rules_relation_rows_counted env rest) as [tail te]. cbn in Htail.
    exists ([] :: [body] :: [] :: tail_bodies ++ [[]]). split.
    + unfold rules_relation_trace_source in *.
      constructor; [reflexivity |]. constructor; [exists body; auto |].
      constructor; [reflexivity |].
      apply Forall2_app; [exact Htail |]. constructor; [reflexivity | constructor].
    + unfold rules_predicate_bodies_work at 1. cbn [fold_right].
      fold (rules_predicate_bodies_work weight (tail_bodies ++ [[]])).
      rewrite rules_relation_bodies_work_app. cbn [rules_predicate_bodies_work fold_right].
      specialize (Hbound p (env p) body Hsource). lia.
Qed.

(** Each tail-first map write retains the actual predicate-encoder body. *)
Lemma rules_relation_fill_sources P B (E : encoding P)
    (source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) weight bound keys values :
    length keys = length values -> rules_predicate_source_laws E source weight bound ->
    exists bodies, rules_relation_trace_source source env_source
      (snd (rules_relation_fill_counted E keys values)) bodies /\
      rules_predicate_bodies_work weight bodies <=
        fold_right (fun p n => bound p + n) 0 keys.
Proof.
  intros Hlength [Hexists Hbound]. revert values Hlength.
  induction keys as [|p rest IH]; intros [|rows values] Hlength;
    cbn [rules_relation_fill_counted]; try discriminate.
  - exists [[]]. split; [constructor; [reflexivity | constructor] | reflexivity].
  - assert (Htail_length : length rest = length values) by (injection Hlength; auto).
    destruct (IH values Htail_length) as [tail_bodies [Htail Hwork]].
    destruct (Hexists p) as [body Hsource].
    destruct (rules_relation_fill_counted E rest values) as [before events]. cbn in Htail.
    destruct (audit_trie_set (encode E p) (p, rows) before) as [after trace].
    exists ([] :: tail_bodies ++ [[body]]). split.
    + unfold rules_relation_trace_source in *.
      constructor; [reflexivity |]. apply Forall2_app; [exact Htail |].
      constructor; [exists body; auto | constructor].
    + change (rules_predicate_bodies_work weight (tail_bodies ++ [[body]]) <=
        bound p + fold_right (fun p n => bound p + n) 0 rest).
      rewrite rules_relation_bodies_work_app. cbn [rules_predicate_bodies_work fold_right].
      specialize (Hbound p (encode E p) body Hsource). lia.
Qed.

(** The per-key external budget combines encoder and environment allowances. *)
Lemma rules_relation_external_sum P (pred_bound env_bound : P -> nat) keys :
    fold_right (fun p n => pred_bound p + n) 0 keys +
    fold_right (fun p n => env_bound p + n) 0 keys =
    fold_right (fun p n => pred_bound p + env_bound p + n) 0 keys.
Proof.
  induction keys as [|p rest IH]; cbn [fold_right]; lia.
Qed.

(** Receipt groups follow the same ordered concatenation as the snapshot events. *)
Lemma rules_relation_receipt_assembly P B
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop)
    pe predicates distinct se keys ke re fe pe_bodies encoded_bodies row_bodies fill_bodies :
    rules_relation_trace_source pred_source env_source pe pe_bodies ->
    Forall2 (rules_relation_entry_source pred_source) (rules_relation_entries se) encoded_bodies ->
    rules_relation_trace_source pred_source env_source re row_bodies ->
    rules_relation_trace_source pred_source env_source fe fill_bodies ->
    rules_relation_trace_source pred_source env_source
      (pe ++ [RulesRelationDistinct predicates distinct se; RulesRelationKeys distinct keys ke] ++
        re ++ fe) (pe_bodies ++ [encoded_bodies; []] ++ row_bodies ++ fill_bodies).
Proof.
  intros Hpe Hencoded Hrows Hfill. unfold rules_relation_trace_source in *.
  apply Forall2_app; [exact Hpe |].
  constructor; [exact Hencoded |].
  constructor; [reflexivity |]. apply Forall2_app; assumption.
Qed.

(** Callback body work fits the separate per-occurrence and per-key allowances. *)
Lemma rules_relation_receipt_budget P B (weight : B -> nat) pred_bound env_bound
    (predicates keys : list P) pe_bodies (encoded_bodies : list (list B)) row_bodies fill_bodies :
    rules_predicate_bodies_work weight pe_bodies = 0 ->
    fold_right (fun body n => fold_right (fun item total => weight item + total) 0 body + n)
      0 encoded_bodies <= fold_right (fun p n => pred_bound p + n) 0 predicates ->
    rules_predicate_bodies_work weight row_bodies <=
      fold_right (fun p n => env_bound p + n) 0 keys ->
    rules_predicate_bodies_work weight fill_bodies <=
      fold_right (fun p n => pred_bound p + n) 0 keys ->
    rules_predicate_bodies_work weight
      (pe_bodies ++ [encoded_bodies; []] ++ row_bodies ++ fill_bodies) <=
      fold_right (fun p n => pred_bound p + n) 0 predicates +
      fold_right (fun p n => pred_bound p + env_bound p + n) 0 keys.
Proof.
  intros Hpe Hencoded Hrows Hfill.
  repeat rewrite rules_relation_bodies_work_app.
  cbn [rules_predicate_bodies_work fold_right].
  pose proof (rules_relation_external_sum P pred_bound env_bound keys) as Hsum.
  rewrite Hpe. lia.
Qed.

(** Actual callbacks have same-run bodies whose total work fits the external allowance. *)
Lemma rules_relations_source_bodies P B (E : encoding P) atoms env
    (pred_source : P -> positive -> list B -> Prop)
    (env_source : P -> FinSet.t tuple -> list B -> Prop) weight pred_bound env_bound :
    rules_predicate_source_laws E pred_source weight pred_bound ->
    rules_environment_source_laws env env_source weight env_bound ->
    exists bodies,
      rules_relation_trace_source pred_source env_source
        (snd (rules_join_relations_counted E atoms env)) bodies /\
      rules_predicate_bodies_work weight bodies <=
        rules_relation_external_input_budget E atoms pred_bound env_bound.
Proof.
  intros Hpred Henv.
  pose proof (rules_relation_predicates_erases P atoms) as Hpredicates.
  pose proof (rules_relation_predicate_sources P B pred_source env_source weight atoms) as Hpe.
  unfold rules_join_relations_counted.
  destruct (rules_relation_predicates atoms) as [predicates pe]. cbn in Hpredicates, Hpe.
  destruct Hpe as [pe_bodies [Hpe Hpework]].
  destruct (rules_relation_encoding_bodies P B E pred_source weight pred_bound predicates Hpred)
    as [encoded_bodies [Hencoded Hencodedwork]].
  pose proof (rules_relation_fold_entries P E predicates FinSet.empty) as Hentries.
  pose proof (audit_finset_of_list_erases _ _ (rules_encoder E) E predicates
    (fun _ _ => eq_refl)) as Hset.
  unfold audit_finset_of_list in Hset |- *.
  destruct (audit_finset_fold (rules_encoder E) predicates FinSet.empty) as [distinct se].
  cbn in Hset, Hentries.
  pose proof (audit_finset_elements_erases _ distinct) as Hkeys.
  destruct (audit_finset_elements distinct) as [keys ke]. cbn in Hkeys.
  pose proof (rules_relation_rows_erases P env keys) as Hrows.
  pose proof (rules_relation_rows_sources P B env pred_source env_source weight env_bound keys Henv)
    as Hrow_source.
  destruct (rules_relation_rows_counted env keys) as [rows re]. cbn in Hrows, Hrow_source.
  destruct Hrow_source as [row_bodies [Hrow_source Hrowwork]].
  assert (Hlength : length keys = length rows) by (rewrite Hrows, length_map; reflexivity).
  pose proof (rules_relation_fill_sources P B E pred_source env_source weight pred_bound keys rows
    Hlength Hpred) as Hfill_source.
  destruct (rules_relation_fill_counted E keys rows) as [out fe]. cbn in Hfill_source.
  destruct Hfill_source as [fill_bodies [Hfill_source Hfillwork]].
  exists (pe_bodies ++ [encoded_bodies; []] ++ row_bodies ++ fill_bodies). split.
  - apply rules_relation_receipt_assembly; try assumption.
    change (rules_relation_entries se =
      map (fun p => RulesEncodeEntry p (encode E p)) predicates) in Hentries.
    rewrite Hentries. exact Hencoded.
  - unfold rules_relation_external_input_budget. rewrite <- Hpredicates, <- Hset, <- Hkeys.
    exact (rules_relation_receipt_budget P B weight pred_bound env_bound predicates keys
      pe_bodies encoded_bodies row_bodies fill_bodies Hpework Hencodedwork Hrowwork Hfillwork).
Qed.

(** Every external callback in the same snapshot has its own bounded source body. *)
Theorem rules_relations_external_source : rules_relations_external_source_statement.
Proof.
  intros P B E atoms env pred_source env_source weight pred_bound env_bound Hpred Henv.
  pose proof (rules_join_relations_input_bound P E atoms env) as Hinternal.
  destruct (rules_relations_source_bodies P B E atoms env pred_source env_source weight
    pred_bound env_bound Hpred Henv) as [bodies [Hsource Hwork]].
  destruct (rules_join_relations_counted E atoms env) as [out events].
  cbn in Hinternal, Hsource, Hwork. exists bodies. split; [exact Hsource |].
  split; [exact (proj1 Hinternal) |].
  destruct Hinternal as [_ Hinternal].
  change (rules_relation_work events <= rules_join_relations_input_budget E atoms env)
    in Hinternal. lia.
Qed.
