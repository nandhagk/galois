(** * Adequacy of literal trie operations

    The counted trie operations preserve the canonical source operations and charge
    their actual selected branches. For example, a missing lookup still consumes its key.
    Builds on: CollectionsTrie, CollectionsMap, CollectionsAuditCost, CollectionsAuditTrie. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsAuditCost
  CollectionsAuditTrie.
Import List.ListNotations.

(** Erasing lookup events recovers the original lookup at every input. *)
Theorem audit_trie_get_erases : audit_trie_get_erases_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intro input;
    cbn [audit_trie_get Trie.get]; try reflexivity;
    match goal with
    | |- context [audit_trie_get rest ?child] =>
      specialize (IH child); destruct (audit_trie_get rest child) as [result events]
    end; exact IH.
Qed.

(** Erasing insertion events recovers the original persistent insertion. *)
Theorem audit_trie_set_erases : audit_trie_set_erases_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intros value input;
    cbn [audit_trie_set audit_trie_update Trie.set]; try reflexivity;
    match goal with
    | |- context [audit_trie_update rest (Some value) ?child] =>
      specialize (IH value child); unfold audit_trie_set in IH;
      destruct (audit_trie_update rest (Some value) child) as [result events]
    end;
    cbn in IH; rewrite IH; reflexivity.
Qed.

(** Erasing removal events recovers the original collapsing removal. *)
Theorem audit_trie_remove_erases : audit_trie_remove_erases_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intro input;
    cbn [audit_trie_remove audit_trie_update Trie.remove]; try reflexivity;
    match goal with
    | |- context [audit_trie_update rest None ?child] =>
      specialize (IH child); unfold audit_trie_remove in IH;
      destruct (audit_trie_update rest None child) as [result events]
    end;
    cbn in IH; rewrite IH; reflexivity.
Qed.

(** Erasing position lookup events preserves projection of the actual stored pair. *)
Theorem audit_map_code_get_erases : audit_map_code_get_erases_statement.
Proof.
  intros K V key input.
  pose proof (audit_trie_get_erases (K * V)%type key input) as Herases.
  unfold audit_map_code_get, Map.code_get.
  destruct (audit_trie_get key input) as [result events].
  cbn in Herases; rewrite Herases; reflexivity.
Qed.

(** A lookup emits exactly two events for each key bit. *)
Theorem audit_trie_get_events_bound : audit_trie_get_events_bound_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intro input;
    cbn [audit_trie_get Pos.size_nat]; try reflexivity;
    match goal with
    | |- context [audit_trie_get rest ?child] =>
      specialize (IH child); destruct (audit_trie_get rest child) as [result events]
    end;
    cbn [snd audit_work List.length] in *; lia.
Qed.

(** An update emits at most five events for each key bit. *)
Theorem audit_trie_update_events_bound : audit_trie_update_events_bound_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intros value input;
    cbn [audit_trie_update Pos.size_nat]; try (cbn [audit_work snd List.length]; lia);
    match goal with
    | |- context [audit_trie_update rest value ?child] =>
      specialize (IH value child); destruct (audit_trie_update rest value child) as [result events]
    end;
    unfold audit_work in *; cbn in *; rewrite List.length_app; cbn; lia.
Qed.

Lemma audit_accessor_bound A (input : Trie.t A) : audit_trie_accessor_work input <= 2.
Proof.
  destruct input; cbn [audit_trie_accessor_work]; lia.
Qed.

Lemma audit_node_bound A (left : Trie.t A) value right :
  audit_trie_node_work left value right <= 5.
Proof.
  destruct left, value, right; cbn [audit_trie_node_work]; lia.
Qed.

(** Lookup source work is bounded solely by its original key width. *)
Theorem audit_trie_get_source_work_bound : audit_trie_get_source_work_bound_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intro input;
    cbn [audit_trie_get_source_work Pos.size_nat];
    pose proof (audit_accessor_bound A input);
    try match goal with
    | |- context [audit_trie_get_source_work rest ?child] =>
      specialize (IH child)
    end; lia.
Qed.

(** Update source work covers every strict accessor and rebuilding frame. *)
Theorem audit_trie_update_source_work_bound : audit_trie_update_source_work_bound_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intros value input;
    cbn [audit_trie_update_source_work Pos.size_nat];
    pose proof (audit_accessor_bound A input).
  - specialize (IH value (Trie.right input)).
    pose proof (audit_node_bound A (Trie.left input) (Trie.value input)
      (fst (audit_trie_update rest value (Trie.right input)))); lia.
  - specialize (IH value (Trie.left input)).
    pose proof (audit_node_bound A (fst (audit_trie_update rest value (Trie.left input)))
      (Trie.value input) (Trie.right input)); lia.
  - pose proof (audit_node_bound A (Trie.left input) value (Trie.right input)); lia.
Qed.

(** Every source lookup derivation has the exact original result, trace and work. *)
Theorem audit_trie_get_run_correct : audit_trie_get_run_correct_statement.
Proof.
  intros A key input result events work Hrun.
  induction Hrun as [input | rest input result events work Hrun IH |
    rest input result events work Hrun IH].
  - cbn [Trie.get audit_trie_get audit_trie_get_source_work].
    repeat split; try reflexivity.
    exact (audit_trie_get_source_work_bound A xH input).
  - destruct IH as [Hresult [Htrace [Hwork Hbound]]].
    cbn [Trie.get audit_trie_get audit_trie_get_source_work].
    rewrite <- Htrace; cbn; repeat split; try assumption; try reflexivity.
    + rewrite Hwork; reflexivity.
    + pose proof (audit_accessor_bound A input); cbn [Pos.size_nat]; lia.
  - destruct IH as [Hresult [Htrace [Hwork Hbound]]].
    cbn [Trie.get audit_trie_get audit_trie_get_source_work].
    rewrite <- Htrace; cbn; repeat split; try assumption; try reflexivity.
    + rewrite Hwork; reflexivity.
    + pose proof (audit_accessor_bound A input); cbn [Pos.size_nat]; lia.
Qed.

(** Every input admits a source lookup derivation with its returned state. *)
Theorem audit_trie_get_run_total : audit_trie_get_run_total_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intro input.
  - destruct (IH (Trie.right input)) as [result [events [work Hrun]]].
    eexists; eexists; eexists; apply AuditGetRight; exact Hrun.
  - destruct (IH (Trie.left input)) as [result [events [work Hrun]]].
    eexists; eexists; eexists; apply AuditGetLeft; exact Hrun.
  - eexists; eexists; eexists; apply AuditGetHere.
Qed.

(** Each update derivation threads the actual child trie into the parent reconstruction. *)
Theorem audit_trie_update_run_correct : audit_trie_update_run_correct_statement.
Proof.
  intros A key value input result events work Hrun.
  induction Hrun as [value input | rest value input child events work Hrun IH |
    rest value input child events work Hrun IH].
  - cbn [audit_trie_update audit_trie_update_source_work].
    repeat split; try reflexivity.
    exact (audit_trie_update_source_work_bound A xH value input).
  - destruct IH as [Htrace [Hwork Hbound]].
    pose proof (f_equal (@fst _ _) Htrace) as Hchild.
    cbn [audit_trie_update audit_trie_update_source_work].
    rewrite <- Htrace; cbn; repeat split; try reflexivity.
    + cbn [fst] in Hchild; rewrite Hwork.
      rewrite Hchild; reflexivity.
    + pose proof (audit_accessor_bound A input).
      pose proof (audit_node_bound A child (Trie.value input) (Trie.right input)).
      cbn [Pos.size_nat]; lia.
  - destruct IH as [Htrace [Hwork Hbound]].
    pose proof (f_equal (@fst _ _) Htrace) as Hchild.
    cbn [audit_trie_update audit_trie_update_source_work].
    rewrite <- Htrace; cbn; repeat split; try reflexivity.
    + cbn [fst] in Hchild; rewrite Hwork, Hchild; reflexivity.
    + pose proof (audit_accessor_bound A input).
      pose proof (audit_node_bound A (Trie.left input) (Trie.value input) child).
      cbn [Pos.size_nat]; lia.
Qed.

(** Every input admits a persistent source update derivation. *)
Theorem audit_trie_update_run_total : audit_trie_update_run_total_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intros value input.
  - destruct (IH value (Trie.right input)) as [result [events [work Hrun]]].
    eexists; eexists; eexists; apply AuditUpdateRight; exact Hrun.
  - destruct (IH value (Trie.left input)) as [result [events [work Hrun]]].
    eexists; eexists; eexists; apply AuditUpdateLeft; exact Hrun.
  - eexists; eexists; eexists; apply AuditUpdateHere.
Qed.

(** Folding lookup charges over the emitted trace recovers the direct source account. *)
Theorem audit_trie_get_trace_adequate : audit_trie_get_trace_adequate_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intro input;
    cbn [audit_trie_get audit_trie_get_source_work];
    try (cbn [snd audit_trie_get_trace_source_work]; lia);
    match goal with
    | |- context [audit_trie_get rest ?child] =>
      specialize (IH child); destruct (audit_trie_get rest child) as [result events]
    end;
    cbn [snd audit_trie_get_trace_source_work] in *; lia.
Qed.

Lemma audit_update_trace_app A (left right : audit_trace (audit_trie_call A)) :
  audit_trie_update_trace_source_work (left ++ right) =
    audit_trie_update_trace_source_work left + audit_trie_update_trace_source_work right.
Proof.
  induction left as [| event rest IH].
  - reflexivity.
  - destruct event as [site operands | call | site operands | bit | site operands];
      try destruct call; cbn [app audit_trie_update_trace_source_work]; rewrite IH; lia.
Qed.

(** Folding update charges preserves the exact trace and all rebuilt child operands. *)
Theorem audit_trie_update_trace_adequate : audit_trie_update_trace_adequate_statement.
Proof.
  intros A key; induction key as [rest IH | rest IH |]; intros value input;
    cbn [audit_trie_update audit_trie_update_source_work].
  - specialize (IH value (Trie.right input)).
    destruct (audit_trie_update rest value (Trie.right input)) as [result events].
    cbn [snd fst audit_trie_update_trace_source_work] in *.
    rewrite !audit_update_trace_app; cbn [audit_trie_update_trace_source_work]; lia.
  - specialize (IH value (Trie.left input)).
    destruct (audit_trie_update rest value (Trie.left input)) as [result events].
    cbn [snd fst audit_trie_update_trace_source_work] in *.
    rewrite !audit_update_trace_app; cbn [audit_trie_update_trace_source_work]; lia.
  - cbn [snd audit_trie_update_trace_source_work]; lia.
Qed.
