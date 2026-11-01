(** * Materialization row snapshot adequacy

    A counted snapshot preserves its map and accounts for its traversal.
    For example, a missing predicate still returns an empty row list.
    Builds on: RulesAuditDeltaRows and collection traversal adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditTrie
  CollectionsAuditTrieAdequacy CollectionsAuditElements CollectionsAuditElementsAdequacy
  CollectionsAuditMapTraverse CollectionsAuditMapTraverseAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesDelta RulesAuditDeltaRows.

(** * Snapshot and lookup *)

(** Snapshot lookup returns the same rows as the original lookup. *)
Theorem rules_delta_rows_erasure : rules_delta_rows_erasure_statement.
Proof.
  intros P prog db p.
  unfold rules_delta_rows_snapshot_counted, rules_delta_rows_lookup_counted, delta_rows.
  pose proof (audit_map_transform_erases P _ _ _ audit_finset_elements FinSet.elements db
    (audit_finset_elements_erases _)) as Hsnapshot.
  destruct (audit_map_transform audit_finset_elements db) as [snapshot events] eqn:Hrun.
  cbn in Hsnapshot.
  rewrite Hsnapshot.
  pose proof (audit_map_code_get_erases P _ (encode (penc prog) p)
    (Map.map FinSet.elements db)) as Hget.
  destruct (audit_map_code_get (encode (penc prog) p) (Map.map FinSet.elements db))
    as [raw body].
  cbn in Hget.
  rewrite Hget.
  reflexivity.
Qed.

(** Snapshot traversal preserves the map and bounds its recorded work. *)
Theorem rules_delta_rows_snapshot_cost : rules_delta_rows_snapshot_cost_statement.
Proof.
  intros P db.
  unfold rules_delta_rows_snapshot_counted, rules_delta_rows_snapshot_work,
    rules_delta_rows_snapshot_budget.
  pose proof (audit_map_transform_erases P _ _ _ audit_finset_elements FinSet.elements db
    (audit_finset_elements_erases _)) as Herase.
  pose proof (audit_map_transform_source_bound P _ _ _ audit_finset_elements
    audit_set_elements_work db) as Hwork.
  destruct (audit_map_transform audit_finset_elements db) as [snapshot events].
  cbn in *.
  split; [exact Herase | lia].
Qed.

(** * Input-only child traversal bound *)

(** A stored relation is charged for its complete set enumeration. *)
Definition rules_delta_relation_budget (relation : FinSet.t tuple) : nat :=
  6 + 19 * audit_trie_nodes relation + audit_trie_output_bits relation.

(** Sum the relation enumeration budgets of position-tagged map entries. *)
Definition rules_delta_entry_sum {P} (entries : list (positive * (P * FinSet.t tuple))) : nat :=
  fold_right (fun entry n => rules_delta_relation_budget (snd (snd entry)) + n) 0 entries.

(** Relation budgets add across concatenated entries. *)
Lemma rules_delta_entry_sum_app P (left right : list (positive * (P * FinSet.t tuple))) :
    rules_delta_entry_sum (left ++ right) =
      rules_delta_entry_sum left + rules_delta_entry_sum right.
Proof.
  unfold rules_delta_entry_sum. induction left as [|entry rest IH]; cbn [app fold_right].
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** Changing trie positions leaves relation budgets unchanged. *)
Lemma rules_delta_entry_sum_lift P direction
    (entries : list (positive * (P * FinSet.t tuple))) :
    rules_delta_entry_sum (map (Trie.lift direction) entries) = rules_delta_entry_sum entries.
Proof.
  unfold rules_delta_entry_sum.
  induction entries as [|[pos [key relation]] rest IH]; cbn [map fold_right Trie.lift snd];
    try reflexivity. now rewrite IH.
Qed.

(** Total child work is bounded by the sum of budgets for all stored relations. *)
Lemma rules_delta_transform_ne_children P (node : Trie.ne (P * FinSet.t tuple)) :
    audit_map_transform_child_work audit_set_elements_work
      (snd (audit_map_transform_ne audit_finset_elements node)) <=
      rules_delta_entry_sum (Trie.entries_ne node).
Proof.
  induction node as [r IHr | [key relation] | [key relation] r IHr | l IHl |
    l IHl r IHr | l IHl [key relation] | l IHl [key relation] r IHr];
    cbn [audit_map_transform_ne Trie.entries_ne].
  all: try (destruct (audit_map_transform_ne audit_finset_elements l) as [lo le]).
  all: try (destruct (audit_map_transform_ne audit_finset_elements r) as [ro re]).
  all: try (pose proof (audit_finset_elements_work_bound _ relation) as Hrelation;
    destruct (audit_finset_elements relation) as [rows body]; cbn in Hrelation).
  all: try (rewrite <- (rules_delta_entry_sum_lift P xI (Trie.entries_ne r)) in IHr).
  all: cbn [snd audit_map_transform_child_work] in *;
    repeat rewrite (proj2 (audit_transform_work_app _ _ _ _ _ _ _));
    repeat rewrite rules_delta_entry_sum_app;
    fold (@rules_delta_entry_sum P); repeat rewrite rules_delta_entry_sum_lift;
    cbn [audit_map_transform_child_work rules_delta_entry_sum
      fold_right snd] in *;
    fold (@rules_delta_entry_sum P); repeat rewrite rules_delta_entry_sum_lift;
    unfold rules_delta_relation_budget in *;
    fold (@rules_delta_entry_sum P); repeat rewrite rules_delta_entry_sum_lift; try lia.
  all: try (pose proof (rules_delta_entry_sum_lift P xI (Trie.entries_ne r)) as Hlift;
    unfold rules_delta_entry_sum, rules_delta_relation_budget in Hlift; rewrite Hlift).
  all: try (rewrite rules_delta_entry_sum_lift in IHr).
  all: try (unfold rules_delta_entry_sum, rules_delta_relation_budget in IHr).
  all: try (unfold rules_delta_entry_sum, rules_delta_relation_budget in IHl).
  all: unfold rules_delta_entry_sum, rules_delta_relation_budget; lia.
Qed.

(** The entry sum is the input budget folded over the map's public enumeration. *)
Lemma rules_delta_entry_sum_elements P (db : Map.t P (FinSet.t tuple)) :
    rules_delta_entry_sum (Trie.entries db) =
      fold_right (fun pair n => rules_delta_relation_budget (snd pair) + n) 0 (Map.elements db).
Proof.
  unfold Map.elements. rewrite Trie.elements_entries.
  unfold rules_delta_entry_sum. induction (Trie.entries db) as [|[pos [key value]] rest IH];
    cbn [map fold_right snd]; try reflexivity. now rewrite IH.
Qed.

(** Snapshot work is bounded by the relations stored in the input map. *)
Theorem rules_delta_rows_input_bound : rules_delta_rows_input_bound_statement.
Proof.
  intros P db.
  pose proof (rules_delta_rows_snapshot_cost P db) as Hsnapshot.
  pose proof (audit_map_transform_source_bound P _ _ _ audit_finset_elements
    audit_set_elements_work db) as Houter.
  assert (Hchildren :
    audit_map_transform_child_work audit_set_elements_work
      (snd (audit_map_transform audit_finset_elements db)) <=
    rules_delta_entry_sum (Trie.entries db)).
  { destruct db as [|node]; cbn [audit_map_transform Trie.entries]; [reflexivity |].
    apply rules_delta_transform_ne_children. }
  unfold rules_delta_rows_snapshot_counted in Hsnapshot |- *.
  destruct (audit_map_transform audit_finset_elements db) as [snapshot events].
  cbn in Hsnapshot, Houter, Hchildren.
  split; [exact (proj1 Hsnapshot) |].
  unfold rules_delta_rows_snapshot_work, rules_delta_rows_input_budget.
  rewrite <- rules_delta_entry_sum_elements.
  unfold rules_delta_relation_budget in Hchildren.
  unfold rules_delta_entry_sum in Hchildren |- *.
  cbn in Houter, Hchildren |- *.
  lia.
Qed.
