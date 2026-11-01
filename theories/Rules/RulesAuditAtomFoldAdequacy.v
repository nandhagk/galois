(** * Atom fold run adequacy

    Recorded runs describe the same recursive fold as the executable model.
    For example, an empty atom list preserves the initial database.
    Builds on: RulesAuditAtomFold. *)

From Stdlib Require Import List PeanoNat PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy CollectionsAuditEncoding CollectionsAuditEncodingAdequacy
  CollectionsAuditElements CollectionsAuditElementsAdequacy CollectionsAuditCost
  CollectionsAuditEncoderBudget CollectionsAuditEncoderBudgetAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta RulesAuditAtomFold.
Import List.ListNotations.

(** * Recorded fold runs *)

(** Every counted fold has a source-shaped derivation. *)
Theorem rules_atom_fold_run_total : rules_atom_fold_run_total_statement.
Proof.
  intros P prog atoms.
  induction atoms as [|[p row] rest IH]; intros initial.
  - cbn [rules_atom_fold_counted]. constructor.
  - cbn [rules_atom_fold_counted].
    specialize (IH initial).
    destruct (rules_atom_fold_counted prog rest initial) as [before tail].
    destruct (audit_map_code_get (encode (penc prog) p) before) as [raw get_body] eqn:Hget.
    set (relation :=
      match raw with
      | Some r => r
      | None => FinSet.empty
      end).
    fold relation.
    destruct (audit_finset_add (audit_list_encode audit_positive_encode) row relation)
      as [next add_body] eqn:Hadd.
    destruct (audit_trie_set (encode (penc prog) p) (p, next) before)
      as [after set_body] eqn:Hset.
    eapply RulesAtomFoldCons; eauto.
Qed.

(** Each recorded run is the unique result of its counted fold. *)
Theorem rules_atom_fold_run_unique : rules_atom_fold_run_unique_statement.
Proof.
  intros P prog atoms initial result events Hrun.
  induction Hrun as [initial | p row rest initial before tail raw get_body relation next add_body
    after set_body Hrun IH Hget Hrelation Hadd Hset].
  - reflexivity.
  - cbn [rules_atom_fold_counted].
    rewrite IH.
    replace (audit_map_code_get (encode (penc prog) p) before) with (raw, get_body)
      by (symmetry; exact Hget).
    subst relation. rewrite Hadd, Hset.
    reflexivity.
Qed.

(** Erasing each recorded insertion recovers the original atom fold. *)
Lemma rules_atom_fold_list_erases P (prog : program P) atoms initial :
    fst (rules_atom_fold_counted prog atoms initial) = delta_add_atoms prog atoms initial.
Proof.
  revert initial.
  induction atoms as [|[p row] rest IH]; intro initial.
  - reflexivity.
  - cbn [rules_atom_fold_counted delta_add_atoms fold_right fst snd].
    specialize (IH initial).
    destruct (rules_atom_fold_counted prog rest initial) as [before tail].
    cbn in IH.
    pose proof (audit_map_code_get_erases P _ (encode (penc prog) p) before) as Hget.
    destruct (audit_map_code_get (encode (penc prog) p) before) as [raw get_body].
    cbn in Hget.
    set (relation :=
      match raw with
      | Some r => r
      | None => FinSet.empty
      end).
    fold relation.
    assert (Hencoding : fst (audit_list_encode audit_positive_encode row) =
      encode tuple_encoding row).
    { apply audit_list_encode_erases. intros; apply audit_positive_encode_erases. }
    pose proof (audit_finset_add_erases _ _ (audit_list_encode audit_positive_encode)
      tuple_encoding row relation Hencoding) as Hadd.
    destruct (audit_finset_add (audit_list_encode audit_positive_encode) row relation)
      as [next add_body].
    cbn in Hadd.
    pose proof (audit_trie_set_erases _ (encode (penc prog) p) (p, next) before) as Hset.
    destruct (audit_trie_set (encode (penc prog) p) (p, next) before) as [after set_body]
      eqn:Hsetrun in *.
    cbn in Hset.
    unfold relation in Hadd.
    rewrite Hget in Hadd.
    rewrite Hset, Hadd, IH.
    reflexivity.
Qed.

(** Erasing the recorded insertions and enumeration recovers the original delta index. *)
Theorem rules_atom_fold_erasure : rules_atom_fold_erasure_statement.
Proof.
  split; [exact rules_atom_fold_list_erases |].
  intros P prog input.
  unfold rules_delta_index_counted, delta_index.
  pose proof (audit_finset_elements_erases _ input) as Helements.
  destruct (audit_finset_elements input) as [atoms events].
  cbn in Helements.
  rewrite <- Helements.
  pose proof (rules_atom_fold_list_erases P prog atoms Map.empty) as Hrun.
  destruct (rules_atom_fold_counted prog atoms Map.empty); exact Hrun.
Qed.

(** Work adds across concatenated atom-fold event traces. *)
Lemma rules_atom_full_work_app P (left right : list (rules_atom_full_event P)) :
    rules_atom_full_work (left ++ right) = rules_atom_full_work left + rules_atom_full_work right.
Proof.
  unfold rules_atom_full_work.
  induction left as [|event rest IH]; cbn; lia.
Qed.

(** Budget adds across concatenated atom-fold event traces. *)
Lemma rules_atom_full_budget_app P (left right : list (rules_atom_full_event P)) :
    rules_atom_full_budget (left ++ right) =
      rules_atom_full_budget left + rules_atom_full_budget right.
Proof.
  unfold rules_atom_full_budget.
  induction left as [|event rest IH]; cbn; lia.
Qed.

(** A lookup trace charges at most five units per encoded key bit. *)
Polymorphic Lemma rules_atom_get_trace_bound A code (input : Trie.t A) :
    audit_trie_get_trace_source_work (snd (audit_trie_get code input)) <= 5 * Pos.size_nat code.
Proof.
  revert input. induction code as [rest IH | rest IH |]; intro input.
  - cbn [audit_trie_get]. specialize (IH (Trie.right input)).
    destruct (audit_trie_get rest (Trie.right input)) as [result events].
    cbn [snd audit_trie_get_trace_source_work] in *.
    pose proof (audit_accessor_bound A input). cbn [Pos.size_nat]. lia.
  - cbn [audit_trie_get]. specialize (IH (Trie.left input)).
    destruct (audit_trie_get rest (Trie.left input)) as [result events].
    cbn [snd audit_trie_get_trace_source_work] in *.
    pose proof (audit_accessor_bound A input). cbn [Pos.size_nat]. lia.
  - cbn [audit_trie_get snd audit_trie_get_trace_source_work].
    pose proof (audit_accessor_bound A input). cbn [Pos.size_nat]. lia.
Qed.

(** A relation lookup charges the actual trie body at the encoded key. *)
Polymorphic Lemma rules_atom_get_bound P code (db : database P) :
    let '(_, events) := audit_map_code_get code db in
    audit_trie_get_trace_source_work events <= 5 * Pos.size_nat code.
Proof.
  pose proof (rules_atom_get_trace_bound (P * FinSet.t tuple)%type code db) as Htrace.
  unfold audit_map_code_get.
  destruct (audit_trie_get code db); cbn in *. exact Htrace.
Qed.

(** A relation write charges the actual trie update at the encoded key. *)
Polymorphic Lemma rules_atom_set_bound P code value (db : database P) after events :
    audit_trie_set code (value : P * FinSet.t tuple) db = (after, events) ->
    audit_trie_update_trace_source_work events <= 16 * Pos.size_nat code.
Proof.
  intro Hrun.
  pose proof (audit_trie_update_trace_adequate _ code (Some value) db) as Htrace.
  pose proof (audit_trie_update_source_work_bound _ code (Some value) db) as Hbound.
  unfold audit_trie_set in Hrun.
  destruct (audit_trie_update code (Some value) db) as [out body] eqn:Hupdate.
  inversion Hrun; subst. cbn in Htrace. lia.
Qed.

(** Tuple insertion pays for list encoding and the actual trie update. *)
Polymorphic Lemma rules_atom_add_bound row relation :
    let '(_, events) := audit_finset_add (audit_list_encode audit_positive_encode) row relation in
    audit_finset_source_work (audit_list_events_work audit_basic_encoding_work) events <=
      10 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
        16 * Pos.size_nat (encode tuple_encoding row).
Proof.
  pose proof (audit_list_input_bound _ _ audit_positive_encode audit_basic_encoding_work
    (fun _ => 1) row (proj1 audit_base_encoder_input_bound)) as Hencode.
  pose proof (audit_list_encode_erases _ _ audit_positive_encode positive_encoding row
    (fun x _ => audit_positive_encode_erases x)) as Herase.
  unfold audit_finset_add.
  destruct (audit_list_encode audit_positive_encode row) as [code events] eqn:Henc.
  cbn in Herase, Hencode.
  pose proof (audit_trie_update_trace_adequate _ code (Some (row, tt)) relation) as Htrace.
  pose proof (audit_trie_update_source_work_bound _ code (Some (row, tt)) relation) as Hbound.
  unfold audit_trie_set.
  destruct (audit_trie_update code (Some (row, tt)) relation) as [out trace].
  cbn [snd audit_finset_source_work] in *.
  unfold audit_list_input_budget in Hencode.
  assert (Hchildren : audit_child_input_budget (fun _ : positive => 1) row = length row).
  { clear Hencode Herase Henc Htrace Hbound.
    induction row as [|x xs IH]; cbn [audit_child_input_budget length].
    - reflexivity.
    - rewrite IH. reflexivity. }
  rewrite Hchildren in Hencode.
  rewrite Herase in *. unfold tuple_encoding, list_encoding in *. cbn in *. lia.
Qed.

(** A recorded relation read fits the event budget. *)
Polymorphic Lemma rules_atom_get_event_bound P p code (db : database P) raw events :
    audit_map_code_get code db = (raw, events) ->
    rules_atom_full_event_work (RafRelationGet p code db raw events) <=
      rules_atom_full_event_budget (RafRelationGet p code db raw events).
Proof.
  intro Hrun.
  pose proof (rules_atom_get_bound P code db) as Hbound.
  rewrite Hrun in Hbound. cbn in Hbound.
  cbn [rules_atom_full_event_work rules_atom_full_event_budget].
  unfold audit_encoding_weight. lia.
Qed.

(** A recorded relation write fits the event's budget. *)
Polymorphic Lemma rules_atom_set_event_bound P code value (db : database P) after events :
    audit_trie_set code (value : P * FinSet.t tuple) db = (after, events) ->
    rules_atom_full_event_work (RafRelationSet (fst value) (snd value) code db after events) <=
      rules_atom_full_event_budget (RafRelationSet (fst value) (snd value) code db after events).
Proof.
  intro Hrun.
  pose proof (rules_atom_set_bound P code value db after events Hrun) as Hbound.
  cbn [rules_atom_full_event_work rules_atom_full_event_budget audit_encoding_weight].
  unfold audit_encoding_weight. lia.
Qed.

(** Combining four component budgets preserves the fold frame charges. *)
Lemma rules_atom_combine_bounds a b c d e f g h :
    a <= b -> c <= d -> e <= f -> g <= h ->
    1 + (a + (c + (1 + (e + (g + 0))))) <= 1 + b + d + 1 + f + h.
Proof.
  intros. lia.
Qed.

(** A fold step separates its recursive trace from its three concrete operations. *)
Lemma rules_atom_cons_trace_work P (prog : program P) p row before tail raw get_body
    relation next add_body after set_body :
    rules_atom_full_work (RafCase 0 :: tail ++
      [RafRelationGet p (encode (penc prog) p) before raw get_body; RafCase 1;
       RafTupleAdd row relation next add_body;
       RafRelationSet p next (encode (penc prog) p) before after set_body]) =
      1 + (rules_atom_full_work tail +
        (rules_atom_full_event_work (RafRelationGet p (encode (penc prog) p) before raw get_body) +
         (1 + (rules_atom_full_event_work (@RafTupleAdd P row relation next add_body) +
          (rules_atom_full_event_work
            (RafRelationSet p next (encode (penc prog) p) before after set_body) + 0))))).
Proof.
  unfold rules_atom_full_work at 1. cbn [fold_right rules_atom_full_event_work].
  fold (rules_atom_full_work (tail ++
    [RafRelationGet p (encode (penc prog) p) before raw get_body; RafCase 1;
     RafTupleAdd row relation next add_body;
     RafRelationSet p next (encode (penc prog) p) before after set_body])).
  rewrite rules_atom_full_work_app. unfold rules_atom_full_work at 2.
  cbn [fold_right rules_atom_full_event_work]. reflexivity.
Qed.

(** The input recurrence bounds the actual fold work. *)
Lemma rules_atom_fold_work_input P (prog : program P) atoms initial :
    rules_atom_full_work (snd (rules_atom_fold_counted prog atoms initial)) <=
      rules_atom_fold_input_budget prog atoms.
Proof.
  induction atoms as [|[p row] rest IH].
  - reflexivity.
  - cbn [rules_atom_fold_counted].
    destruct (rules_atom_fold_counted prog rest initial) as [before tail]. cbn in IH.
    destruct (audit_map_code_get (encode (penc prog) p) before) as [raw get_body] eqn:Hgetrun.
    pose proof (rules_atom_get_event_bound P p (encode (penc prog) p) before
      raw get_body Hgetrun) as Hget.
    cbn [rules_atom_full_event_work rules_atom_full_event_budget] in Hget.
    set (relation :=
      match raw with
      | Some r => r
      | None => FinSet.empty
      end).
    fold relation.
    pose proof (rules_atom_add_bound row relation) as Hadd.
    destruct (audit_finset_add (audit_list_encode audit_positive_encode) row relation)
      as [next add_body]. cbn in Hadd.
    destruct (audit_trie_set (encode (penc prog) p) (p, next) before)
      as [after set_body] eqn:Hsetrun.
    pose proof (rules_atom_set_event_bound P (encode (penc prog) p) (p, next) before
      after set_body Hsetrun) as Hset.
    cbn [rules_atom_full_event_work rules_atom_full_event_budget] in Hset.
    change (rules_atom_full_work (RafCase 0 :: tail ++
      [RafRelationGet p (encode (penc prog) p) before raw get_body; RafCase 1;
       RafTupleAdd row relation next add_body;
       RafRelationSet p next (encode (penc prog) p) before after set_body]) <=
      rules_atom_fold_input_budget prog ((p, row) :: rest)).
    rewrite rules_atom_cons_trace_work.
    cbn [rules_atom_full_event_work rules_atom_fold_input_budget].
    change (rules_atom_full_work tail <= rules_atom_fold_input_budget prog rest) in IH.
    change (audit_finset_source_work (audit_list_events_work audit_basic_encoding_work) add_body <=
      10 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
      16 * Pos.size_nat (encode tuple_encoding row)) in Hadd.
    unfold audit_encoding_weight in *.
    exact (rules_atom_combine_bounds _ _ _ _ _ _ _ _ IH Hget Hadd Hset).
Qed.

(** Every counted fold returns the source result within the input budget. *)
Theorem rules_atom_fold_input_bound : rules_atom_fold_input_bound_statement.
Proof.
  intros P prog atoms initial.
  pose proof (proj1 rules_atom_fold_erasure P prog atoms initial) as Herase.
  pose proof (rules_atom_fold_work_input P prog atoms initial) as Hwork.
  destruct (rules_atom_fold_counted prog atoms initial) as [out events].
  cbn in *. auto.
Qed.

(** The recorded run erases to the source fold and respects its input budget. *)
Theorem rules_atom_fold_run_erasure : rules_atom_fold_run_erasure_statement.
Proof.
  intros P prog atoms initial result events Hrun.
  pose proof (rules_atom_fold_run_unique P prog atoms initial result events Hrun) as Hunique.
  pose proof (rules_atom_fold_input_bound P prog atoms initial) as Hbound.
  rewrite Hunique in Hbound. exact Hbound.
Qed.

(** The event budget is exactly the recurrence over the input atom list. *)
Lemma rules_atom_fold_budget_input P (prog : program P) atoms initial :
    rules_atom_full_budget (snd (rules_atom_fold_counted prog atoms initial)) =
      rules_atom_fold_input_budget prog atoms.
Proof.
  induction atoms as [|[p row] rest IH].
  - reflexivity.
  - cbn [rules_atom_fold_counted].
    destruct (rules_atom_fold_counted prog rest initial) as [before tail]. cbn in IH.
    destruct (audit_map_code_get (encode (penc prog) p) before) as [raw get_body].
    set (relation :=
      match raw with
      | Some r => r
      | None => FinSet.empty
      end).
    fold relation.
    destruct (audit_finset_add (audit_list_encode audit_positive_encode) row relation)
      as [next add_body].
    destruct (audit_trie_set (encode (penc prog) p) (p, next) before) as [after set_body].
    change (rules_atom_full_budget (RafCase 0 :: tail ++
      [RafRelationGet p (encode (penc prog) p) before raw get_body; RafCase 1;
       RafTupleAdd row relation next add_body;
       RafRelationSet p next (encode (penc prog) p) before after set_body]) =
      rules_atom_fold_input_budget prog ((p, row) :: rest)).
    unfold rules_atom_full_budget at 1. cbn [fold_right rules_atom_full_event_budget].
    fold (rules_atom_full_budget (tail ++
      [RafRelationGet p (encode (penc prog) p) before raw get_body; RafCase 1;
       RafTupleAdd row relation next add_body;
       RafRelationSet p next (encode (penc prog) p) before after set_body])).
    rewrite rules_atom_full_budget_app.
    unfold rules_atom_full_budget at 2.
    cbn [fold_right rules_atom_full_event_budget rules_atom_fold_input_budget].
    change (rules_atom_full_budget tail = rules_atom_fold_input_budget prog rest) in IH.
    lia.
Qed.

(** The selected event budget bounds the same fold work. *)
Theorem rules_atom_fold_selected_cost : rules_atom_fold_selected_cost_statement.
Proof.
  intros P prog atoms initial.
  pose proof (rules_atom_fold_input_bound P prog atoms initial) as Hbound.
  pose proof (rules_atom_fold_budget_input P prog atoms initial) as Hbudget.
  destruct (rules_atom_fold_counted prog atoms initial) as [out events]. cbn in *.
  change (rules_atom_full_budget events = rules_atom_fold_input_budget prog atoms) in Hbudget.
  rewrite Hbudget. exact Hbound.
Qed.

(** Delta indexing adds one enumeration budget to the atom-fold recurrence. *)
Theorem rules_delta_index_input_bound : rules_delta_index_input_bound_statement.
Proof.
  intros P prog input.
  pose proof (proj2 rules_atom_fold_erasure P prog input) as Herase.
  pose proof (audit_finset_elements_erases _ input) as Helements.
  pose proof (audit_finset_elements_work_bound _ input) as Hwork.
  unfold rules_delta_index_counted in Herase |- *.
  destruct (audit_finset_elements input) as [atoms body]. cbn in Helements, Hwork.
  pose proof (rules_atom_fold_work_input P prog atoms Map.empty) as Hfold.
  destruct (rules_atom_fold_counted prog atoms Map.empty) as [out events]. cbn in Herase, Hfold.
  split; [exact Herase |].
  unfold rules_atom_full_work at 1. cbn [fold_right rules_atom_full_event_work].
  fold (rules_atom_full_work events).
  unfold rules_delta_index_input_budget. rewrite <- Helements.
  change (rules_atom_full_work events <= rules_atom_fold_input_budget prog atoms) in Hfold.
  eapply Nat.le_trans; [apply Nat.add_le_mono; eassumption | lia].
Qed.
