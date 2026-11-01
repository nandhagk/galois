(** * Join-relation snapshot adequacy

    Counted preparation preserves the source snapshot and its enumeration occurrences.
    For example, repeated predicates share a single environment enumeration.
    Builds on: RulesAuditRelations and collection adequacy. *)

From Stdlib Require Import List PeanoNat PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditElements CollectionsAuditElementsAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditRelations.
Import List.ListNotations.

(** * Erasure of each snapshot stage *)

(** Predicate collection preserves the input atom order. *)
Lemma rules_relation_predicates_erases P (atoms : list (atom P)) :
    fst (rules_relation_predicates atoms) = map pred atoms.
Proof.
  induction atoms as [|a rest IH]; cbn [rules_relation_predicates map]; try reflexivity.
  destruct (rules_relation_predicates rest) as [tail events]. cbn in *. now rewrite IH.
Qed.

(** Enumerating relation keys returns the source rows in key order. *)
Lemma rules_relation_rows_erases P (env : P -> FinSet.t tuple) keys :
    fst (rules_relation_rows_counted env keys) = map (fun p => FinSet.elements (env p)) keys.
Proof.
  induction keys as [|p rest IH]; cbn [rules_relation_rows_counted map]; try reflexivity.
  pose proof (audit_finset_elements_erases _ (env p)) as Helem.
  destruct (audit_finset_elements (env p)) as [rows body].
  destruct (rules_relation_rows_counted env rest) as [tail events].
  cbn in *. now rewrite Helem, IH.
Qed.

(** Filling counted keys preserves the source's tail-first updates. *)
Lemma rules_relation_fill_erases P (E : encoding P) keys values :
    fst (rules_relation_fill_counted E keys values) = fill_values E keys values.
Proof.
  revert values. induction keys as [|p rest IH]; intros [|rows values]; try reflexivity.
  cbn [rules_relation_fill_counted fill_values].
  specialize (IH values).
  destruct (rules_relation_fill_counted E rest values) as [before events].
  cbn in IH.
  pose proof (audit_trie_set_erases _ (encode E p) (p, rows) before) as Hset.
  destruct (audit_trie_set (encode E p) (p, rows) before) as [after body].
  cbn in Hset. rewrite Hset, IH. reflexivity.
Qed.

(** Removing events from preparation returns the source relation map. *)
Theorem rules_join_relations_erasure : rules_join_relations_erasure_statement.
Proof.
  intros P E atoms env.
  unfold rules_join_relations_counted, prepare_join_relations, join_relation_keys.
  pose proof (rules_relation_predicates_erases P atoms) as Hpred.
  destruct (rules_relation_predicates atoms) as [predicates pe]. cbn in Hpred.
  pose proof (audit_finset_of_list_erases _ _ (rules_encoder E) E predicates
    (fun _ _ => eq_refl)) as Hset.
  destruct (audit_finset_of_list (rules_encoder E) predicates) as [distinct se]. cbn in Hset.
  pose proof (audit_finset_elements_erases _ distinct) as Hkeys.
  destruct (audit_finset_elements distinct) as [keys ke]. cbn in Hkeys.
  pose proof (rules_relation_rows_erases P env keys) as Hrows.
  destruct (rules_relation_rows_counted env keys) as [rows re]. cbn in Hrows.
  pose proof (rules_relation_fill_erases P E keys rows) as Hfill.
  destruct (rules_relation_fill_counted E keys rows) as [out fe]. cbn in Hfill.
  rewrite Hfill, Hrows, Hkeys, Hset, Hpred. reflexivity.
Qed.

(** * Environment-call counts *)

(** Select recorded calls to the relation environment. *)
Definition rules_relation_is_env P (event : rules_relation_event P) : bool :=
  match event with
  | RulesRelationEnv _ _ => true
  | _ => false
  end.

(** Predicate collection does not call the relation environment. *)
Lemma rules_relation_predicates_no_env P (atoms : list (atom P)) :
    filter (rules_relation_is_env P) (snd (rules_relation_predicates atoms)) = [].
Proof.
  induction atoms as [|a rest IH]; cbn [rules_relation_predicates]; try reflexivity.
  destruct (rules_relation_predicates rest) as [tail events]. cbn in IH.
  cbn [snd filter rules_relation_is_env]. rewrite filter_app. cbn [filter rules_relation_is_env].
  now rewrite IH.
Qed.

(** Filling the result map does not call the relation environment. *)
Lemma rules_relation_fill_no_env P (E : encoding P) keys values :
    filter (rules_relation_is_env P) (snd (rules_relation_fill_counted E keys values)) = [].
Proof.
  revert values. induction keys as [|p rest IH]; intros [|rows values]; try reflexivity.
  cbn [rules_relation_fill_counted]. specialize (IH values).
  destruct (rules_relation_fill_counted E rest values) as [before events]. cbn in IH.
  destruct (audit_trie_set (encode E p) (p, rows) before) as [out body].
  cbn [snd filter rules_relation_is_env]. rewrite filter_app. cbn [filter rules_relation_is_env].
  now rewrite IH.
Qed.

(** The number of environment events equals the number of selected keys. *)
Lemma rules_relation_rows_env_count P (env : P -> FinSet.t tuple) keys :
    length (filter (rules_relation_is_env P) (snd (rules_relation_rows_counted env keys))) =
      length keys.
Proof.
  induction keys as [|p rest IH]; cbn [rules_relation_rows_counted]; try reflexivity.
  destruct (audit_finset_elements (env p)) as [rows body].
  destruct (rules_relation_rows_counted env rest) as [tail events]. cbn in IH.
  cbn [snd filter rules_relation_is_env]. rewrite filter_app.
  cbn [filter rules_relation_is_env length]. rewrite app_nil_r, IH. reflexivity.
Qed.

(** The total environment-event count equals the number of distinct predicate keys. *)
Theorem rules_join_relations_row_count : rules_join_relations_row_count_statement.
Proof.
  intros P E atoms env.
  unfold rules_join_relations_counted, join_relation_keys.
  pose proof (rules_relation_predicates_erases P atoms) as Hpred.
  pose proof (rules_relation_predicates_no_env P atoms) as Hpe.
  destruct (rules_relation_predicates atoms) as [predicates pe]. cbn in Hpred, Hpe.
  pose proof (audit_finset_of_list_erases _ _ (rules_encoder E) E predicates
    (fun _ _ => eq_refl)) as Hset.
  destruct (audit_finset_of_list (rules_encoder E) predicates) as [distinct se]. cbn in Hset.
  pose proof (audit_finset_elements_erases _ distinct) as Hkeys.
  destruct (audit_finset_elements distinct) as [keys ke]. cbn in Hkeys.
  pose proof (rules_relation_rows_env_count P env keys) as Hrows.
  destruct (rules_relation_rows_counted env keys) as [rows re]. cbn in Hrows.
  pose proof (rules_relation_fill_no_env P E keys rows) as Hfill.
  destruct (rules_relation_fill_counted E keys rows) as [out fe]. cbn in Hfill.
  change (length (filter (rules_relation_is_env P)
    (pe ++ [RulesRelationDistinct predicates distinct se; RulesRelationKeys distinct keys ke] ++
      re ++ fe)) = length (FinSet.elements (FinSet.of_list E (map pred atoms)))).
  repeat rewrite filter_app. repeat rewrite length_app.
  rewrite Hpe, Hfill. cbn [length filter rules_relation_is_env] in *.
  rewrite Hrows, Hkeys, Hset, Hpred. lia.
Qed.

(** * Source work and input budgets *)

(** Relation work adds across concatenated traces. *)
Lemma rules_relation_work_app P (left right : list (rules_relation_event P)) :
    rules_relation_work (left ++ right) = rules_relation_work left + rules_relation_work right.
Proof.
  unfold rules_relation_work. induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

(** Relation budgets add across concatenated traces. *)
Lemma rules_relation_budget_app P (E : encoding P) (left right : list (rules_relation_event P)) :
    rules_relation_budget E (left ++ right) =
      rules_relation_budget E left + rules_relation_budget E right.
Proof.
  unfold rules_relation_budget. induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

(** Predicate collection charges three frames per atom and one terminal frame. *)
Lemma rules_relation_predicates_work P (atoms : list (atom P)) :
    rules_relation_work (snd (rules_relation_predicates atoms)) = 1 + 3 * length atoms /\
    forall E,
      rules_relation_budget E (snd (rules_relation_predicates atoms)) = 1 + 3 * length atoms.
Proof.
  induction atoms as [|a rest IH]; cbn [rules_relation_predicates].
  - split; [reflexivity | intros; reflexivity].
  - destruct (rules_relation_predicates rest) as [tail events]. cbn in IH.
    destruct IH as [Hwork Hbudget].
    change (rules_relation_work events = 1 + 3 * length rest) in Hwork. split.
    + change (1 + (1 + rules_relation_work (events ++ [RulesRelationCase 1])) =
        1 + 3 * length (a :: rest)).
      rewrite rules_relation_work_app. unfold rules_relation_work at 2.
      cbn [fold_right rules_relation_event_work length]. lia.
    + intro E. specialize (Hbudget E).
      change (rules_relation_budget E events = 1 + 3 * length rest) in Hbudget.
      change (1 + (1 + rules_relation_budget E (events ++ [RulesRelationCase 1])) =
        1 + 3 * length (a :: rest)).
      rewrite rules_relation_budget_app. unfold rules_relation_budget at 2.
      cbn [fold_right rules_relation_event_budget length]. lia.
Qed.

(** The set-construction budget charges every predicate encoder occurrence. *)
Lemma rules_relation_distinct_budget P (E : encoding P) keys :
    audit_finset_of_list_budget (rules_encoder E) (@length (rules_encode_entry P)) keys <=
      11 + 12 * length keys + 17 * rules_relation_predicate_bits E keys.
Proof.
  induction keys as [|p rest IH]; cbn [audit_finset_of_list_budget rules_encoder
    rules_relation_predicate_bits length fst snd]; lia.
Qed.

(** A distinct-set event bounds its actual set-construction body. *)
Lemma rules_relation_distinct_work P (E : encoding P) keys set events :
    audit_finset_of_list (rules_encoder E) keys = (set, events) ->
    rules_relation_event_work (RulesRelationDistinct keys set events) <=
      rules_relation_event_budget E (RulesRelationDistinct keys set events).
Proof.
  intro Hrun.
  pose proof (audit_finset_of_list_source_bound P _ (rules_encoder E)
    (@length (rules_encode_entry P)) keys) as Hwork.
  rewrite Hrun in Hwork. cbn in Hwork.
  pose proof (rules_relation_distinct_budget P E keys) as Hbudget.
  assert (Hbits : rules_relation_predicate_bits E keys =
    fold_right (fun p n => Pos.size_nat (encode E p) + n) 0 keys).
  { clear Hrun Hwork Hbudget. induction keys as [|p rest IH];
      cbn [rules_relation_predicate_bits fold_right];
      try reflexivity. now rewrite IH. }
  rewrite Hbits in Hbudget.
  cbn [rules_relation_event_work rules_relation_event_budget]. lia.
Qed.

(** A key or row enumeration event bounds its actual finite-set traversal. *)
Lemma rules_relation_elements_work K (input : FinSet.t K) rows events :
    audit_finset_elements input = (rows, events) ->
    audit_set_elements_work events <=
      6 + 19 * audit_trie_nodes input + audit_trie_output_bits input.
Proof.
  intro Hrun. pose proof (audit_finset_elements_work_bound K input) as Hwork.
  rewrite Hrun in Hwork. cbn in Hwork. lia.
Qed.

(** A recorded map write pays for its actual source trie update. *)
Polymorphic Lemma rules_relation_set_work P (E : encoding P) p rows before after events :
    audit_trie_set (encode E p) (p, rows) before = (after, events) ->
    rules_relation_event_work (RulesRelationSet p rows (encode E p) before after events) <=
      rules_relation_event_budget E (RulesRelationSet p rows (encode E p) before after events).
Proof.
  intro Hrun.
  pose proof (audit_trie_update_trace_adequate _ (encode E p) (Some (p, rows)) before) as Htrace.
  pose proof (audit_trie_update_source_work_bound _ (encode E p) (Some (p, rows)) before) as Hbound.
  unfold audit_trie_set in Hrun.
  destruct (audit_trie_update (encode E p) (Some (p, rows)) before) as [out body].
  inversion Hrun; subst. cbn in Htrace.
  cbn [rules_relation_event_work rules_relation_event_budget].
  unfold audit_encoding_weight. lia.
Qed.

(** Charge each key for its environment and row enumeration frames. *)
Fixpoint rules_relation_rows_budget P (env : P -> FinSet.t tuple) keys : nat :=
  match keys with
  | [] => 1
  | p :: rest =>
      3 + (7 + 19 * audit_trie_nodes (env p) + audit_trie_output_bits (env p)) +
        rules_relation_rows_budget P env rest
  end.

(** Charge each key for its tail-first snapshot map update. *)
Fixpoint rules_relation_fill_budget P (E : encoding P) keys : nat :=
  match keys with
  | [] => 1
  | p :: rest => 1 + (2 + 17 * Pos.size_nat (encode E p)) + rules_relation_fill_budget P E rest
  end.

(** Combining the row callback and recursive trace preserves frame costs. *)
Lemma rules_relation_rows_combine a b c d :
    a <= b -> c <= d -> 1 + (1 + (1 + a + (c + (1 + 0)))) <=
      1 + (1 + (1 + b + (d + (1 + 0)))).
Proof.
  intros. lia.
Qed.

(** Row enumeration work fits both the selected and the input budgets. *)
Lemma rules_relation_rows_work P (E : encoding P) (env : P -> FinSet.t tuple) keys :
    rules_relation_work (snd (rules_relation_rows_counted env keys)) <=
      rules_relation_budget E (snd (rules_relation_rows_counted env keys)) /\
    rules_relation_budget E (snd (rules_relation_rows_counted env keys)) =
      rules_relation_rows_budget P env keys.
Proof.
  induction keys as [|p rest IH]; cbn [rules_relation_rows_counted].
  - split; reflexivity.
  - pose proof (audit_finset_elements_work_bound _ (env p)) as Hbody.
    destruct (audit_finset_elements (env p)) as [rows body]. cbn in Hbody.
    destruct (rules_relation_rows_counted env rest) as [tail events]. cbn in IH.
    change (rules_relation_work (RulesRelationCase 2 :: RulesRelationEnv p (env p) ::
      RulesRelationRows p (env p) rows body :: events ++ [RulesRelationCase 3]) <=
      rules_relation_budget E (RulesRelationCase 2 :: RulesRelationEnv p (env p) ::
      RulesRelationRows p (env p) rows body :: events ++ [RulesRelationCase 3]) /\
      rules_relation_budget E (RulesRelationCase 2 :: RulesRelationEnv p (env p) ::
      RulesRelationRows p (env p) rows body :: events ++ [RulesRelationCase 3]) =
      rules_relation_rows_budget P env (p :: rest)).
    unfold rules_relation_work at 1. unfold rules_relation_budget at 1 2.
    cbn [fold_right rules_relation_event_work rules_relation_event_budget].
    fold (rules_relation_work (events ++ [RulesRelationCase 3])).
    fold (rules_relation_budget E (events ++ [RulesRelationCase 3])).
    rewrite rules_relation_work_app, !rules_relation_budget_app.
    change (rules_relation_work events <= rules_relation_budget E events /\
      rules_relation_budget E events = rules_relation_rows_budget P env rest) in IH.
    unfold rules_relation_work at 2. unfold rules_relation_budget at 2 3.
    cbn [fold_right rules_relation_event_work rules_relation_event_budget
      rules_relation_rows_budget].
    destruct IH as [IHwork IHbudget]. split.
    + assert (Hbody_bound : audit_set_elements_work body <=
        6 + 19 * audit_trie_nodes (env p) + audit_trie_output_bits (env p)).
      { eapply Nat.le_trans; [exact Hbody | lia]. }
      exact (rules_relation_rows_combine _ _ _ _ Hbody_bound IHwork).
    + fold (rules_relation_budget E events).
      unfold rules_relation_budget at 2. cbn [fold_right rules_relation_event_budget].
      rewrite IHbudget. lia.
Qed.

(** Combining a write event with the recursive trace preserves the case charge. *)
Lemma rules_relation_fill_combine a b c d :
    a <= b -> c <= d -> 1 + (c + (a + 0)) <= 1 + (d + (b + 0)).
Proof.
  intros. lia.
Qed.

(** Filling the snapshot fits the selected and input budgets when every key has rows. *)
Lemma rules_relation_fill_work P (E : encoding P) keys values :
    length keys = length values ->
    rules_relation_work (snd (rules_relation_fill_counted E keys values)) <=
      rules_relation_budget E (snd (rules_relation_fill_counted E keys values)) /\
    rules_relation_budget E (snd (rules_relation_fill_counted E keys values)) =
      rules_relation_fill_budget P E keys.
Proof.
  revert values. induction keys as [|p rest IH]; intros [|rows values] Hlength;
    cbn [rules_relation_fill_counted] in *; try discriminate.
  - split; reflexivity.
  - assert (Htail : length rest = length values) by (injection Hlength; auto).
    specialize (IH values Htail).
    destruct (rules_relation_fill_counted E rest values) as [before events]. cbn in IH.
    destruct (audit_trie_set (encode E p) (p, rows) before) as [after body] eqn:Hset.
    pose proof (rules_relation_set_work P E p rows before after body Hset) as Hbody.
    change (rules_relation_work (RulesRelationCase 4 :: events ++
      [RulesRelationSet p rows (encode E p) before after body]) <=
      rules_relation_budget E (RulesRelationCase 4 :: events ++
      [RulesRelationSet p rows (encode E p) before after body]) /\
      rules_relation_budget E (RulesRelationCase 4 :: events ++
      [RulesRelationSet p rows (encode E p) before after body]) =
      rules_relation_fill_budget P E (p :: rest)).
    unfold rules_relation_work at 1. unfold rules_relation_budget at 1 2.
    cbn [fold_right rules_relation_event_work rules_relation_event_budget].
    fold (rules_relation_work (events ++
      [RulesRelationSet p rows (encode E p) before after body])).
    fold (rules_relation_budget E (events ++
      [RulesRelationSet p rows (encode E p) before after body])).
    rewrite rules_relation_work_app, !rules_relation_budget_app.
    change (rules_relation_work events <= rules_relation_budget E events /\
      rules_relation_budget E events = rules_relation_fill_budget P E rest) in IH.
    unfold rules_relation_work at 2. unfold rules_relation_budget at 2 3.
    cbn [fold_right rules_relation_fill_budget].
    destruct IH as [IHwork IHbudget]. split.
    + cbn [rules_relation_event_work rules_relation_event_budget] in Hbody |- *.
      unfold audit_encoding_weight in Hbody |- *.
      exact (rules_relation_fill_combine _ _ _ _ Hbody IHwork).
    + fold (rules_relation_budget E events).
      unfold rules_relation_budget at 2. cbn [fold_right rules_relation_event_budget].
      rewrite IHbudget. lia.
Qed.

(** Separate enumeration and write budgets partition the joint input recurrence. *)
Lemma rules_relation_rows_fill_budget P (E : encoding P) env keys :
    rules_relation_rows_budget P env keys + rules_relation_fill_budget P E keys =
      rules_relation_input_rows_budget E env keys.
Proof.
  induction keys as [|p rest IH]; cbn [rules_relation_rows_budget rules_relation_fill_budget
    rules_relation_input_rows_budget]; lia.
Qed.

(** Combining snapshot stage bounds preserves their concatenation. *)
Lemma rules_relation_snapshot_combine a b c d e f g h i j :
    a <= b -> c <= d -> e <= f -> g <= h -> i <= j ->
    a + (c + (e + 0) + (g + i)) <= b + (d + (f + 0) + (h + j)).
Proof.
  intros. lia.
Qed.

(** The snapshot's selected event budgets cover its recorded work. *)
Lemma rules_join_relations_selected_work P (E : encoding P) atoms env :
    rules_relation_work (snd (rules_join_relations_counted E atoms env)) <=
      rules_relation_budget E (snd (rules_join_relations_counted E atoms env)).
Proof.
  pose proof (rules_relation_predicates_work P atoms) as Hpredwork.
  unfold rules_join_relations_counted.
  destruct (rules_relation_predicates atoms) as [predicates pe]. cbn in Hpredwork.
  destruct Hpredwork as [Hpework Hpebudget]. specialize (Hpebudget E).
  destruct (audit_finset_of_list (rules_encoder E) predicates) as [distinct se] eqn:Hsetrun.
  pose proof (rules_relation_distinct_work P E predicates distinct se Hsetrun) as Hdistinct.
  destruct (audit_finset_elements distinct) as [keys ke] eqn:Hkeyrun.
  pose proof (rules_relation_elements_work _ distinct keys ke Hkeyrun) as Hkeywork.
  pose proof (rules_relation_rows_erases P env keys) as Hrows.
  pose proof (rules_relation_rows_work P E env keys) as Hrowwork.
  destruct (rules_relation_rows_counted env keys) as [rows re]. cbn in Hrows, Hrowwork.
  assert (Hlength : length keys = length rows) by (rewrite Hrows, length_map; reflexivity).
  pose proof (rules_relation_fill_work P E keys rows Hlength) as Hfillwork.
  destruct (rules_relation_fill_counted E keys rows) as [out fe]. cbn in Hfillwork.
  destruct Hrowwork as [Hrowwork _]. destruct Hfillwork as [Hfillwork _].
  change (rules_relation_work (pe ++
    [RulesRelationDistinct predicates distinct se; RulesRelationKeys distinct keys ke] ++ re ++ fe)
    <= rules_relation_budget E (pe ++
    [RulesRelationDistinct predicates distinct se; RulesRelationKeys distinct keys ke] ++
      re ++ fe)).
  repeat rewrite rules_relation_work_app. repeat rewrite rules_relation_budget_app.
  unfold rules_relation_work at 2. unfold rules_relation_budget at 2.
  cbn [fold_right rules_relation_event_work rules_relation_event_budget] in Hdistinct |- *.
  change (rules_relation_work pe = 1 + 3 * length atoms) in Hpework.
  change (rules_relation_budget E pe = 1 + 3 * length atoms) in Hpebudget.
  change (rules_relation_work re <= rules_relation_budget E re) in Hrowwork.
  change (rules_relation_work fe <= rules_relation_budget E fe) in Hfillwork.
  assert (Hpe : rules_relation_work pe <= rules_relation_budget E pe) by lia.
  assert (Hkey : 1 + audit_set_elements_work ke <=
    7 + 19 * audit_trie_nodes distinct + audit_trie_output_bits distinct).
  { eapply Nat.le_trans; [apply Nat.add_le_mono_l; exact Hkeywork | lia]. }
  exact (rules_relation_snapshot_combine _ _ _ _ _ _ _ _ _ _
    Hpe Hdistinct Hkey Hrowwork Hfillwork).
Qed.

(** Selected event allowances fit the recurrence over the original snapshot inputs. *)
Lemma rules_join_relations_budget_input P (E : encoding P) atoms env :
    rules_relation_budget E (snd (rules_join_relations_counted E atoms env)) <=
      rules_join_relations_input_budget E atoms env.
Proof.
  pose proof (rules_relation_predicates_erases P atoms) as Hpred.
  pose proof (rules_relation_predicates_work P atoms) as Hpredwork.
  unfold rules_join_relations_counted.
  destruct (rules_relation_predicates atoms) as [predicates pe]. cbn in Hpred, Hpredwork.
  destruct Hpredwork as [_ Hpebudget]. specialize (Hpebudget E).
  pose proof (audit_finset_of_list_erases _ _ (rules_encoder E) E predicates
    (fun _ _ => eq_refl)) as Hset.
  destruct (audit_finset_of_list (rules_encoder E) predicates) as [distinct se]. cbn in Hset.
  pose proof (audit_finset_elements_erases _ distinct) as Hkeys.
  destruct (audit_finset_elements distinct) as [keys ke]. cbn in Hkeys.
  pose proof (rules_relation_rows_erases P env keys) as Hrows.
  pose proof (rules_relation_rows_work P E env keys) as Hrowwork.
  destruct (rules_relation_rows_counted env keys) as [rows re]. cbn in Hrows, Hrowwork.
  assert (Hlength : length keys = length rows) by (rewrite Hrows, length_map; reflexivity).
  pose proof (rules_relation_fill_work P E keys rows Hlength) as Hfillwork.
  destruct (rules_relation_fill_counted E keys rows) as [out fe]. cbn in Hfillwork.
  destruct Hrowwork as [_ Hrowbudget]. destruct Hfillwork as [_ Hfillbudget].
  change (rules_relation_budget E (pe ++
    [RulesRelationDistinct predicates distinct se; RulesRelationKeys distinct keys ke] ++ re ++ fe)
    <= rules_join_relations_input_budget E atoms env).
  repeat rewrite rules_relation_budget_app.
  unfold rules_relation_budget at 2. cbn [fold_right rules_relation_event_budget].
  unfold rules_join_relations_input_budget. rewrite <- Hpred, <- Hset, <- Hkeys.
  change (rules_relation_budget E pe = 1 + 3 * length atoms) in Hpebudget.
  change (rules_relation_budget E re = rules_relation_rows_budget P env keys) in Hrowbudget.
  change (rules_relation_budget E fe = rules_relation_fill_budget P E keys) in Hfillbudget.
  rewrite Hpebudget, Hrowbudget, Hfillbudget.
  pose proof (rules_relation_rows_fill_budget P E env keys) as Hjoint.
  assert (Hbits : rules_relation_predicate_bits E predicates =
    fold_right (fun p n => Pos.size_nat (encode E p) + n) 0 predicates).
  { clear Hset Hkeys Hrows Hlength Hpred Hpebudget Hrowbudget Hfillbudget Hjoint.
    induction predicates as [|p rest IH]; cbn [rules_relation_predicate_bits fold_right];
      try reflexivity. now rewrite IH. }
  rewrite Hbits. lia.
Qed.

(** Both selected events and the original inputs bound snapshot work. *)
Lemma rules_join_relations_work_bounds P (E : encoding P) atoms env :
    rules_relation_work (snd (rules_join_relations_counted E atoms env)) <=
      rules_relation_budget E (snd (rules_join_relations_counted E atoms env)) /\
    rules_relation_budget E (snd (rules_join_relations_counted E atoms env)) <=
      rules_join_relations_input_budget E atoms env.
Proof.
  split; [apply rules_join_relations_selected_work | apply rules_join_relations_budget_input].
Qed.

(** The selected snapshot events bound work while preserving the source map. *)
Theorem rules_join_relations_selected_cost : rules_join_relations_selected_cost_statement.
Proof.
  intros P E atoms env.
  pose proof (rules_join_relations_erasure P E atoms env) as Herase.
  pose proof (rules_join_relations_work_bounds P E atoms env) as Hwork.
  destruct (rules_join_relations_counted E atoms env) as [out events]. cbn in *.
  split; [exact Herase | exact (proj1 Hwork)].
Qed.

(** The snapshot's original atoms and environment bound its recorded work. *)
Theorem rules_join_relations_input_bound : rules_join_relations_input_bound_statement.
Proof.
  intros P E atoms env.
  pose proof (rules_join_relations_erasure P E atoms env) as Herase.
  pose proof (rules_join_relations_work_bounds P E atoms env) as Hwork.
  destruct (rules_join_relations_counted E atoms env) as [out events]. cbn in *.
  split; [exact Herase |].
  eapply Nat.le_trans; [exact (proj1 Hwork) | exact (proj2 Hwork)].
Qed.
