(** * Adequacy of primitive trie frames

    Literal accessor and smart-constructor cases agree with their source operations,
    including their fixed charges. For example, constructing three absent fields stays empty.
    Builds on: CollectionsAuditPrimitive and CollectionsAuditTrieAdequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsAuditCost
  CollectionsAuditTrie CollectionsAuditPrimitive CollectionsAuditTrieAdequacy.

(** Literal left access preserves its selected source result and charge. *)
Theorem audit_trie_left_source_adequate : audit_trie_left_source_adequate_statement.
Proof.
  intros A [| node]; [reflexivity | destruct node; reflexivity].
Qed.

(** Literal right access preserves its selected source result and charge. *)
Theorem audit_trie_right_source_adequate : audit_trie_right_source_adequate_statement.
Proof.
  intros A [| node]; [reflexivity | destruct node; reflexivity].
Qed.

(** Literal value access preserves both absence and the actual stored value. *)
Theorem audit_trie_value_source_adequate : audit_trie_value_source_adequate_statement.
Proof.
  intros A [| node]; [reflexivity | destruct node; reflexivity].
Qed.

(** Literal node construction agrees in every combination of present and absent fields. *)
Theorem audit_trie_node_source_adequate : audit_trie_node_source_adequate_statement.
Proof.
  intros A left value right; destruct left, value, right; reflexivity.
Qed.

(** Every position-map lookup has a source derivation projecting the actual stored pair. *)
Theorem audit_map_code_get_run_total : audit_map_code_get_run_total_statement.
Proof.
  intros K V key input.
  destruct (audit_trie_get_run_total (K * V)%type key input)
    as [found [events [work Hrun]]].
  eexists; eexists; eexists; apply AuditMapCodeGet; exact Hrun.
Qed.

(** Position-map source derivations preserve their exact output, trace and projection charge. *)
Theorem audit_map_code_get_run_correct : audit_map_code_get_run_correct_statement.
Proof.
  intros K V key input output events work Hrun.
  destruct Hrun as [key input found events work Hget].
  destruct (audit_trie_get_run_correct (K * V)%type key input found events work Hget)
    as [Hresult [Htrace [Hwork Hbound]]].
  unfold Map.code_get, audit_map_code_get.
  destruct (audit_trie_get key input) as [result trace].
  injection Htrace as Hfound Hevents; subst result trace; cbn [fst snd].
  split; [rewrite Hresult; reflexivity |].
  split; [reflexivity | destruct found; lia].
Qed.

(** All literal trie access and construction clauses satisfy their source contracts. *)
Theorem audit_trie_access_source_clauses : audit_trie_access_source_clauses_statement.
Proof.
  split; [exact audit_trie_left_source_adequate |].
  split; [exact audit_trie_right_source_adequate |].
  split; [exact audit_trie_value_source_adequate | exact audit_trie_node_source_adequate].
Qed.

(** Erasing positive equality events recovers the standard bitwise equality test. *)
Theorem audit_positive_eqb_erases : audit_positive_eqb_erases_statement.
Proof.
  intros left right; revert left.
  induction right as [right IH | right IH |]; intros [left | left |];
    cbn [audit_positive_eqb Pos.eqb]; try reflexivity;
    specialize (IH left); destruct (audit_positive_eqb left right) as [result events]; exact IH.
Qed.

(** Equality source work is bounded by twice the smaller original operand width. *)
Theorem audit_positive_eqb_source_bound : audit_positive_eqb_source_bound_statement.
Proof.
  intros left right; revert left.
  induction right as [right IH | right IH |]; intros [left | left |];
    cbn [audit_positive_eqb Pos.size_nat Nat.min];
    try (unfold audit_positive_eqb_source_work; cbn [snd List.length]; lia).
  - specialize (IH left).
    destruct (audit_positive_eqb left right) as [result events].
    unfold audit_positive_eqb_source_work in *; cbn [snd List.length] in *; lia.
  - specialize (IH left).
    destruct (audit_positive_eqb left right) as [result events].
    unfold audit_positive_eqb_source_work in *; cbn [snd List.length] in *; lia.
Qed.
