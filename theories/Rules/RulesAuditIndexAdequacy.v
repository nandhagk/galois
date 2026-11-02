(** * Prepared index adequacy

    The counted row and variable indexes preserve the original source operations.
    For example, a wrong-arity row leaves the previous index unchanged.
    Builds on: RulesAuditIndex, row-count and nested-probe adequacy. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsTable CollectionsAuditTrie CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditPrimitive CollectionsAuditEncodingAdequacy
  CollectionsAuditFinSetAdequacy
  CollectionsAuditStateENCAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditIndexCountsAdequacy RulesAuditNestedProbe
  RulesAuditNestedProbeAdequacy.
Import List.ListNotations.

(** * Tuple encoding and indexed operations *)

Lemma mat_tuple_encoder_erases key :
  fst (mat_tuple_encoder key) = encode tuple_encoding key.
Proof.
  unfold mat_tuple_encoder, mat_lift, tuple_encoding.
  pose proof (audit_list_encode_erases positive (audit_basic_encoding_event positive)
    audit_positive_encode positive_encoding key) as Herase.
  assert (Hall : forall x, In x key -> fst (audit_positive_encode x) =
    encode positive_encoding x) by (intros; apply audit_positive_encode_erases).
  specialize (Herase Hall).
  destruct (audit_list_encode audit_positive_encode key) as [code events]; cbn in Herase.
  cbn; cbv [encode list_encoding] in Herase |- *; exact Herase.
Qed.

Lemma mat_index_get_erases {A : Type} key (before : Map.t tuple A) :
  fst (mat_get_encoded mat_tuple_encoder key before) = Map.get tuple_encoding key before.
Proof.
  unfold mat_get_encoded, mat_bind, Map.get.
  pose proof (mat_tuple_encoder_erases key) as Hcode.
  destruct (mat_tuple_encoder key) as [code events]; cbn in Hcode.
  cbn.
  pose proof (rules_probe_map_get_erases (K := tuple) (V := A) code before) as Hget.
  case_eq (audit_map_code_get code before); intros result get_events Hrun.
  apply (f_equal fst) in Hrun; cbn in Hrun.
  assert (Hresult : result = Map.code_get code before) by (rewrite <- Hrun; exact Hget).
  cbn; rewrite Hresult, Hcode; reflexivity.
Qed.

Lemma mat_index_set_erases {A : Type} key (value : A) (before : Map.t tuple A) :
  fst (mat_set_encoded mat_tuple_encoder key value before) =
    Map.set tuple_encoding key value before.
Proof.
  unfold mat_set_encoded, mat_bind, Map.set.
  pose proof (mat_tuple_encoder_erases key) as Hcode.
  destruct (mat_tuple_encoder key) as [code events]; cbn in Hcode.
  cbn.
  pose proof (rules_probe_trie_set_erases code (key, value) before) as Hset.
  case_eq (audit_trie_set code (key, value) before); intros out set_events Hrun.
  apply (f_equal fst) in Hrun; cbn in Hrun.
  assert (Hout : out = Trie.set code (key, value) before) by (rewrite <- Hrun; exact Hset).
  cbn; rewrite Hout, Hcode; reflexivity.
Qed.

Lemma mat_index_add_erases bound terms row before :
  fst (mat_index_add_full bound terms row before) = index_add bound terms row before.
Proof.
  unfold mat_index_add_full, mat_bind, index_add.
  pose proof (mat_tuple_key_erases bound terms row) as Hkey.
  destruct (mat_tuple_key bound terms row) as [[key |] key_events]; cbn in Hkey.
  - cbn; rewrite <- Hkey.
    pose proof (mat_index_get_erases key before) as Hget.
    destruct (mat_get_encoded mat_tuple_encoder key before) as [raw get_events]; cbn in Hget.
    cbn; unfold index_get; rewrite <- Hget.
    pose proof (mat_index_set_erases key (row :: match raw with
      | Some rows => rows
      | None => []
      end) before) as Hset.
    destruct (mat_set_encoded mat_tuple_encoder key (row :: match raw with
      | Some rows => rows
      | None => []
      end) before) as [out set_events]; cbn in Hset.
    cbn [mat_return]; exact Hset.
  - cbn [mat_return]; rewrite <- Hkey; reflexivity.
Qed.

Lemma mat_build_index_erases bound terms rows :
  fst (mat_build_index_full bound terms rows) = build_index bound terms rows.
Proof.
  unfold mat_build_index_full, build_index.
  induction rows as [|row rows IH]; cbn [mat_foldr mat_mark mat_return fold_right];
    [reflexivity |].
  destruct (mat_foldr (mat_index_add_full bound terms) rows Map.empty) as [before events].
  cbn in IH; cbn [mat_bind].
  pose proof (mat_index_add_erases bound terms row before) as Hadd.
  destruct (mat_index_add_full bound terms row before) as [out here]; cbn in Hadd.
  cbn; rewrite Hadd, IH; reflexivity.
Qed.

Lemma mat_bind_erases {A B} (run : mat_run A) (next : A -> mat_run B) :
  fst (mat_bind run next) = fst (next (fst run)).
Proof.
  destruct run as [value events]; unfold mat_bind; cbn;
    destruct (next value) as [result later]; reflexivity.
Qed.

Lemma mat_lift_erases {A E} site size work (run : A * list E) :
  fst (mat_lift site size work run) = fst run.
Proof.
  destruct run; reflexivity.
Qed.

Lemma mat_variable_add_erases bound terms variable row before :
  fst (mat_variable_add_full bound terms variable row before) =
    variable_index_add bound terms variable row before.
Proof.
  unfold mat_variable_add_full, variable_index_add.
  rewrite mat_bind_erases, mat_tuple_key_erases.
  destruct (tuple_key bound terms row) as [key |] eqn:Hkey.
  - rewrite mat_bind_erases, mat_lift_erases, rules_bind_terms_erases.
    destruct (bind_terms terms row Map.empty) as [binding |] eqn:Hbind.
    + rewrite mat_bind_erases, mat_lift_erases, rules_probe_value_erases.
      rewrite mat_bind_erases, mat_index_get_erases.
      rewrite mat_bind_erases, mat_lift_erases.
      rewrite (audit_finset_add_erases positive (audit_basic_encoding_event positive)
        audit_positive_encode positive_encoding _ _ (audit_positive_encode_erases _)).
      rewrite mat_index_set_erases.
      unfold variable_index_get, Table.get, Table.set.
      reflexivity.
    + reflexivity.
  - destruct (bind_terms terms row Map.empty); reflexivity.
Qed.

Lemma mat_build_variable_erases bound terms variable rows :
  fst (mat_build_variable_full bound terms variable rows) =
    build_variable_index bound terms variable rows.
Proof.
  unfold mat_build_variable_full, build_variable_index.
  induction rows as [|row rows IH]; cbn [mat_foldr mat_mark mat_return fold_right];
    [reflexivity |].
  destruct (mat_foldr (mat_variable_add_full bound terms variable) rows Table.empty)
    as [before events].
  cbn in IH; cbn [mat_bind].
  pose proof (mat_variable_add_erases bound terms variable row before) as Hadd.
  destruct (mat_variable_add_full bound terms variable row before) as [out here]; cbn in Hadd.
  cbn; rewrite Hadd, IH; reflexivity.
Qed.

(** Both prepared index variants erase to their source row and fold operations. *)
Theorem mat_index_full_erases : mat_index_full_erases_statement.
Proof.
  unfold mat_index_full_erases_statement.
  repeat split.
  - exact mat_index_add_erases.
  - exact mat_build_index_erases.
  - exact mat_variable_add_erases.
  - exact mat_build_variable_erases.
Qed.

(** * Input-derived work bounds *)

Lemma mat_work_app first second :
  mat_work (first ++ second) = mat_work first + mat_work second.
Proof.
  induction first as [|frame first IH].
  - reflexivity.
  - unfold mat_work in *; cbn; rewrite IH; lia.
Qed.

Lemma mat_bind_work {A B} (run : mat_run A) (next : A -> mat_run B) :
  mat_work (snd (mat_bind run next)) =
    mat_work (snd run) + mat_work (snd (next (fst run))).
Proof.
  destruct run as [value events]; unfold mat_bind; cbn.
  destruct (next value) as [result later]; cbn; apply mat_work_app.
Qed.

Lemma mat_lift_work {A E} site size work (run : A * list E) :
  mat_work (snd (mat_lift site size work run)) = work (snd run).
Proof.
  destruct run as [result events]; unfold mat_lift, mat_work;
    cbn [snd fold_right mat_frame_work]; lia.
Qed.

Lemma mat_positive_succ_size_bound value :
  Pos.size_nat (Pos.succ value) <= S (Pos.size_nat value).
Proof.
  induction value as [value IH | value IH |]; cbn [Pos.succ Pos.size_nat] in *; lia.
Qed.

Lemma mat_nat_code_size_bound variable :
  Pos.size_nat (encode nat_encoding variable) <= S variable.
Proof.
  induction variable as [|variable IH].
  - reflexivity.
  - change (Pos.size_nat (Pos.succ (encode nat_encoding variable)) <= S (S variable)).
    pose proof (mat_positive_succ_size_bound (encode nat_encoding variable)); lia.
Qed.

Definition mat_term_index_size (term : term) : nat :=
  match term with
  | TVar variable => variable
  | TConst _ => 0
  end.

Lemma mat_bound_term_work_bound bound term :
  mat_work (snd (mat_bound_term bound term)) <=
    200 + 10 * S (mat_term_index_size term) * S (mat_term_index_size term).
Proof.
  destruct term as [variable | constant].
  - pose proof (rules_probe_bound_events_valid bound (TVar variable)) as Hvalid.
    unfold rules_probe_bound_term in Hvalid.
    destruct (audit_finset_mem audit_nat_encode variable bound) as [result events] eqn:Hrun.
    cbn in Hvalid; inversion Hvalid as [|event later Hcase Htail]; subst.
    inversion Htail as [|event later Hwork Hnil]; subst.
    unfold rules_probe_event_valid, rules_nested_probe_event_work,
      rules_nested_probe_event_budget in Hwork.
    pose proof (mat_nat_code_size_bound variable) as Hsize.
    unfold rules_nat_encoder_budget in Hwork.
    unfold mat_bound_term, mat_mark; rewrite Hrun; unfold mat_lift, mat_work.
    cbn [snd fold_right mat_frame_work mat_term_index_size]; nia.
  - unfold mat_bound_term, mat_mark, mat_return, mat_work.
    cbn [snd fst fold_right mat_frame_work mat_term_index_size]; lia.
Qed.

Lemma mat_mark_work {A} site (run : mat_run A) :
  mat_work (snd (mat_mark site run)) = 100 + mat_work (snd run).
Proof.
  destruct run as [value events]; unfold mat_mark, mat_work;
    cbn [snd fst fold_right mat_frame_work].
  reflexivity.
Qed.

Lemma mat_return_work {A} (value : A) : mat_work (snd (mat_return value)) = 100.
Proof.
  reflexivity.
Qed.

Lemma mat_tuple_key_work_bound bound terms row :
  let size := S (mat_index_terms_input terms) in
  mat_work (snd (mat_tuple_key bound terms row)) <= 300 * size * size * size.
Proof.
  revert row; induction terms as [|term terms IH]; intros [|value row].
  - change (mat_work (snd (mat_mark 103 (mat_return (Some ([] : tuple))))) <= 300 * 2 * 2 * 2).
    rewrite mat_mark_work, mat_return_work; cbn [mat_index_terms_input]; lia.
  - change (mat_work (snd (mat_mark 103 (mat_return (None : option tuple)))) <= 300 * 2 * 2 * 2).
    rewrite mat_mark_work, mat_return_work; cbn [mat_index_terms_input]; lia.
  - change (mat_work (snd (mat_mark 103 (mat_return (None : option tuple)))) <=
      300 * S (mat_index_terms_input (term :: terms)) *
      S (mat_index_terms_input (term :: terms)) * S (mat_index_terms_input (term :: terms))).
    rewrite mat_mark_work, mat_return_work.
    destruct term; cbn [mat_index_terms_input mat_term_index_size]; nia.
  - change (mat_work (snd (mat_mark 103
      (mat_bind (mat_tuple_key bound terms row) (fun tail =>
        match tail with
        | None => mat_return None
        | Some key => mat_bind (mat_bound_term bound term) (fun kept =>
            mat_return (Some (if kept then value :: key else key)))
        end)))) <= 300 * S (mat_index_terms_input (term :: terms)) *
      S (mat_index_terms_input (term :: terms)) * S (mat_index_terms_input (term :: terms))).
    rewrite mat_mark_work, mat_bind_work.
    specialize (IH row).
    destruct (fst (mat_tuple_key bound terms row)) as [key |] eqn:Hkey.
    + rewrite mat_bind_work, mat_return_work.
      pose proof (mat_bound_term_work_bound bound term) as Hterm.
      destruct term as [v | c]; cbn [mat_term_index_size] in Hterm;
        unfold mat_index_terms_input in *; cbn [fold_right] in *; nia.
    + rewrite mat_return_work.
      destruct term; unfold mat_index_terms_input in *; cbn [fold_right] in *; nia.
Qed.

Lemma mat_tuple_key_size_bound bound terms row key :
  tuple_key bound terms row = Some key -> mat_tuple_size key <= mat_tuple_size row.
Proof.
  revert row key; induction terms as [|term terms IH]; intros [|value row] key Hkey;
    cbn [tuple_key] in Hkey; try discriminate.
  - inversion Hkey; reflexivity.
  - destruct (tuple_key bound terms row) as [tail |] eqn:Htail; [|discriminate].
    pose proof (IH row tail Htail) as Hsize.
    destruct (bound_term bound term); inversion Hkey; subst key;
      unfold mat_tuple_size in *; cbn [fold_right] in *; lia.
Qed.

Lemma mat_tuple_size_bounds row :
  length row <= mat_tuple_size row /\
  audit_encoded_bits audit_positive_encode row <= mat_tuple_size row.
Proof.
  induction row as [|value row [Hlength Hbits]].
  - cbv [mat_tuple_size audit_encoded_bits length fold_right]; lia.
  - unfold mat_tuple_size, audit_encoded_bits in *;
    cbn [fold_right length audit_encoded_bits audit_positive_encode]
      in *; split; [lia | unfold audit_positive_encode in *; cbn in *; lia].
Qed.

Lemma mat_tuple_encoding_size_bound row :
  Pos.size_nat (encode tuple_encoding row) <= 1 + 2 * mat_tuple_size row.
Proof.
  unfold tuple_encoding; cbv [encode list_encoding].
  rewrite stream_positive_size, emit_list_length.
  induction row as [|value row IH].
  - cbv [mat_tuple_size fold_right]; lia.
  - unfold mat_tuple_size in *; cbn [fold_right] in *; cbv [encode positive_encoding] in *; lia.
Qed.

Lemma mat_tuple_encoder_work_bound row :
  mat_work (snd (mat_tuple_encoder row)) <= 8 + 20 * mat_tuple_size row.
Proof.
  unfold mat_tuple_encoder; rewrite mat_lift_work.
  pose proof (rules_probe_list_encode_bound row) as Hwork.
  destruct (mat_tuple_size_bounds row) as [Hlength Hbits].
  nia.
Qed.

Lemma mat_index_get_work_bound {A : Type} key (before : Map.t tuple A) :
  mat_work (snd (mat_get_encoded mat_tuple_encoder key before)) <= 13 + 30 * mat_tuple_size key.
Proof.
  unfold mat_get_encoded; rewrite mat_bind_work.
  pose proof (mat_tuple_encoder_work_bound key) as Hencoder.
  pose proof (mat_tuple_encoder_erases key) as Hcode.
  destruct (mat_tuple_encoder key) as [code events]; cbn in Hencoder, Hcode |- *.
  pose proof (rules_probe_map_get_trace_bound (K := tuple) (V := A) code before) as Hget.
  destruct (audit_map_code_get code before) as [out get_events]; cbn in Hget.
  pose proof (mat_tuple_encoding_size_bound key) as Hsize.
  change (code = encode tuple_encoding key) in Hcode.
  rewrite <- Hcode in Hsize.
  unfold mat_work; cbn [snd fold_right mat_frame_work]; nia.
Qed.

Lemma mat_index_set_work_bound {A : Type} key (value : A) (before : Map.t tuple A) :
  mat_work (snd (mat_set_encoded mat_tuple_encoder key value before)) <=
    24 + 52 * mat_tuple_size key.
Proof.
  unfold mat_set_encoded; rewrite mat_bind_work.
  pose proof (mat_tuple_encoder_work_bound key) as Hencoder.
  pose proof (mat_tuple_encoder_erases key) as Hcode.
  destruct (mat_tuple_encoder key) as [code events]; cbn in Hencoder, Hcode |- *.
  pose proof (rules_probe_update_trace_bound code (Some (key, value)) before) as Hset.
  unfold audit_trie_set in Hset.
  destruct (audit_trie_update code (Some (key, value)) before) as [out set_events]; cbn in Hset.
  pose proof (mat_tuple_encoding_size_bound key) as Hsize.
  change (code = encode tuple_encoding key) in Hcode.
  rewrite <- Hcode in Hsize.
  unfold mat_work; cbn [snd fold_right mat_frame_work]; nia.
Qed.

Lemma mat_index_add_work_bound bound terms row before :
  let size := S (mat_index_terms_input terms) in
  mat_work (snd (mat_index_add_full bound terms row before)) <=
    300 * size * size * size + 137 + 82 * mat_tuple_size row.
Proof.
  unfold mat_index_add_full; rewrite mat_bind_work.
  pose proof (mat_tuple_key_work_bound bound terms row) as Hkeywork.
  pose proof (mat_tuple_key_erases bound terms row) as Hkey.
  destruct (fst (mat_tuple_key bound terms row)) as [key |] eqn:Hresult.
  - assert (Hkeysize : mat_tuple_size key <= mat_tuple_size row).
    { apply (mat_tuple_key_size_bound bound terms row key); congruence. }
    rewrite mat_bind_work, mat_bind_work, mat_return_work.
    pose proof (mat_index_get_work_bound key before) as Hget.
    pose proof (mat_index_set_work_bound key
      (row :: match fst (mat_get_encoded mat_tuple_encoder key before) with
       | Some rows => rows
       | None => []
       end) before) as Hset.
    cbn [fst mat_return] in *; nia.
  - rewrite mat_return_work; cbn zeta in Hkeywork |- *; lia.
Qed.

Lemma mat_index_rows_length_bound rows : length rows <= mat_index_rows_input rows.
Proof.
  induction rows as [|row rows IH].
  - cbv [mat_index_rows_input length fold_right]; lia.
  - unfold mat_index_rows_input in *; cbn [length fold_right] in *.
    destruct row; unfold mat_tuple_size in *; cbn [fold_right] in *; lia.
Qed.

Lemma mat_build_index_work_bound bound terms rows :
  let size := S (mat_index_terms_input terms) in
  mat_work (snd (mat_build_index_full bound terms rows)) <=
    length rows * (300 * size * size * size + 237) + 82 * mat_index_rows_input rows + 200.
Proof.
  unfold mat_build_index_full.
  induction rows as [|row rows IH].
  - change (mat_work (snd (mat_mark 5 (mat_return (Map.empty : tuple_index)))) <=
      0 * (300 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) + 237) + 82 * mat_index_rows_input [] + 200).
    rewrite mat_mark_work, mat_return_work; unfold mat_index_rows_input;
      cbn [fold_right length]; lia.
  - change (mat_work (snd (mat_mark 5
      (mat_bind (mat_foldr (mat_index_add_full bound terms) rows Map.empty)
        (mat_index_add_full bound terms row)))) <=
      length (row :: rows) * (300 * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) * S (mat_index_terms_input terms) + 237) +
      82 * mat_index_rows_input (row :: rows) + 200).
    rewrite mat_mark_work, mat_bind_work.
    pose proof (mat_index_add_work_bound bound terms row
      (fst (mat_foldr (mat_index_add_full bound terms) rows Map.empty))) as Hrow.
    unfold mat_index_rows_input in *; cbn [fold_right length] in *; nia.
Qed.

Lemma mat_index_polynomial_bound size rows bound :
  1 <= size -> size <= bound -> rows <= bound ->
  rows * (300 * size * size * size + 237) + 82 * rows + 200 <=
    (1000 * 1000) * Nat.pow bound 6.
Proof.
  intros Hsize Hsizebound Hrows.
  assert (Hbound : 1 <= bound) by lia.
  assert (Hsquare : size * size <= bound * bound) by nia.
  assert (Hcube : size * size * size <= bound * bound * bound) by nia.
  assert (Hbound2 : 1 <= bound * bound) by nia.
  assert (Hbound3 : 1 <= bound * bound * bound) by nia.
  assert (Hbound4 : bound * bound * bound <= bound * bound * bound * bound) by nia.
  assert (Hbound5 : bound * bound * bound * bound <=
      bound * bound * bound * bound * bound) by nia.
  assert (Hbound6 : bound * bound * bound * bound * bound <=
      bound * bound * bound * bound * bound * bound) by nia.
  cbn [Nat.pow]; nia.
Qed.

(** Row-index construction stays within the input-derived polynomial budget. *)
Theorem mat_index_full_input_bound : mat_index_full_input_bound_statement.
Proof.
  unfold mat_index_full_input_bound_statement; split.
  - intros bound terms row before.
    pose proof (mat_index_add_work_bound bound terms row before) as Hwork.
    set (size := S (mat_index_terms_input terms)) in *.
    set (rows := mat_index_rows_input [row]).
    set (total := 1 + CollectionsAuditElements.audit_trie_nodes bound +
      mat_index_terms_input terms + rows + CollectionsAuditElements.audit_trie_nodes before).
    assert (Hsize : 1 <= size) by (unfold size; lia).
    assert (Hsizetotal : size <= total) by (unfold size, total; lia).
    assert (Hrowstotal : rows <= total) by (unfold total; lia).
    assert (Hrow : mat_tuple_size row + 1 = rows)
      by (unfold rows, mat_index_rows_input; reflexivity).
    pose proof (mat_index_polynomial_bound size rows total Hsize Hsizetotal Hrowstotal) as Hpoly.
    change (mat_work (snd (mat_index_add_full bound terms row before)) <=
      (1000 * 1000) * Nat.pow total 6).
    eapply Nat.le_trans; [| exact Hpoly].
    clear Hpoly; cbn zeta in Hwork; nia.
  - intros bound terms rows.
    pose proof (mat_build_index_work_bound bound terms rows) as Hwork.
    pose proof (mat_index_rows_length_bound rows) as Hlength.
    set (size := S (mat_index_terms_input terms)) in *.
    set (rowsize := mat_index_rows_input rows) in *.
    set (total := 1 + CollectionsAuditElements.audit_trie_nodes bound +
      mat_index_terms_input terms + rowsize +
      CollectionsAuditElements.audit_trie_nodes (Map.empty : tuple_index)).
    assert (Hsize : 1 <= size) by (unfold size; lia).
    assert (Hsizetotal : size <= total) by (unfold size, total; lia).
    assert (Hrowstotal : rowsize <= total) by (unfold total; lia).
    pose proof (mat_index_polynomial_bound size rowsize total Hsize Hsizetotal Hrowstotal) as Hpoly.
    change (mat_work (snd (mat_build_index_full bound terms rows)) <=
      (1000 * 1000) * Nat.pow total 6).
    eapply Nat.le_trans; [| exact Hpoly].
    clear Hpoly; cbn zeta in Hwork.
    assert (Hmul : length rows * (300 * size * size * size + 237) <=
      rowsize * (300 * size * size * size + 237)) by (apply Nat.mul_le_mono_r; exact Hlength).
    lia.
Qed.

Lemma mat_bind_term_work_bound binding term value :
  rules_nested_probe_work (snd (rules_bind_term_counted binding term value)) <=
    10 + 50 * S (mat_term_index_size term) * S (mat_term_index_size term) +
    2 * Pos.size_nat value.
Proof.
  pose proof (rules_bind_term_events_valid binding term value) as Hvalid.
  pose proof (rules_probe_valid_work_bound _ Hvalid) as Hwork.
  destruct term as [variable | constant].
  - unfold rules_bind_term_counted in Hwork |- *.
    pose proof (mat_nat_code_size_bound variable) as Hsize.
    pose proof (audit_nat_encode_erases variable) as Hencode.
    destruct (audit_nat_encode variable) as [code encoding_events] eqn:Henc; cbn in Hencode.
    change (code = encode nat_encoding variable) in Hencode.
    destruct (audit_map_code_get@{Set Set Set Set} code binding) as [raw get_events] eqn:Hget.
    destruct raw as [old |].
    + destruct (audit_positive_eqb value old) as [equal equal_events].
      unfold rules_nested_probe_budget, rules_nat_encoder_budget in Hwork.
      cbv [snd app fold_right rules_nested_probe_event_budget rules_nat_encoder_budget] in Hwork.
      cbn [mat_term_index_size]; rewrite <- Hencode in Hsize;
      rewrite <- Hencode in Hwork.
      pose proof (Nat.le_min_l (Pos.size_nat value) (Pos.size_nat old)); cbv [snd app]; nia.
    + destruct (audit_trie_set@{Set Set} code (variable, value) binding) as [after set_events].
      unfold rules_nested_probe_budget, rules_nat_encoder_budget in Hwork.
      cbv [snd app fold_right rules_nested_probe_event_budget rules_nat_encoder_budget] in Hwork.
      cbn [mat_term_index_size]; rewrite <- Hencode in Hsize;
      rewrite <- Hencode in Hwork; cbv [snd app]; nia.
  - unfold rules_bind_term_counted in Hwork |- *.
    destruct (audit_positive_eqb value constant) as [equal events].
    unfold rules_nested_probe_budget in Hwork.
    cbv [snd app fold_right rules_nested_probe_event_budget rules_nat_encoder_budget] in Hwork.
    cbn [mat_term_index_size].
    pose proof (Nat.le_min_l (Pos.size_nat value) (Pos.size_nat constant)); cbv [snd app]; nia.
Qed.

Lemma mat_nested_work_app first second :
  rules_nested_probe_work (first ++ second) =
    rules_nested_probe_work first + rules_nested_probe_work second.
Proof.
  induction first as [|event first IH].
  - reflexivity.
  - unfold rules_nested_probe_work in *; cbn; rewrite IH; lia.
Qed.

Lemma mat_bind_terms_work_bound terms row binding :
  let size := S (mat_index_terms_input terms) in
  rules_nested_probe_work (snd (rules_bind_terms_counted terms row binding)) <=
    1000 * size * size * size + 2 * mat_tuple_size row * size.
Proof.
  revert row binding; induction terms as [|term terms IH]; intros [|value row] binding.
  - cbv [rules_bind_terms_counted snd rules_nested_probe_work fold_right
      rules_nested_probe_event_work mat_index_terms_input]; lia.
  - cbv [rules_bind_terms_counted snd rules_nested_probe_work fold_right
      rules_nested_probe_event_work mat_index_terms_input]; lia.
  - destruct term; cbv [rules_bind_terms_counted snd rules_nested_probe_work fold_right
      rules_nested_probe_event_work mat_index_terms_input]; nia.
  - pose proof (mat_bind_term_work_bound binding term value) as Hhead.
    cbn [rules_bind_terms_counted].
    destruct (rules_bind_term_counted binding term value) as [[next |] events] eqn:Hterm;
      change (rules_nested_probe_work events <=
        10 + 50 * S (mat_term_index_size term) * S (mat_term_index_size term) +
        2 * Pos.size_nat value) in Hhead.
    + specialize (IH row next).
      destruct (rules_bind_terms_counted terms row next) as [out later] eqn:Htail.
      change (rules_nested_probe_work later <=
        1000 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) + 2 * mat_tuple_size row *
        S (mat_index_terms_input terms)) in IH.
      change (1 + rules_nested_probe_work (events ++ RprobeCase 13 :: later) <=
        1000 * S (mat_index_terms_input (term :: terms)) *
        S (mat_index_terms_input (term :: terms)) * S (mat_index_terms_input (term :: terms)) +
        2 * mat_tuple_size (value :: row) * S (mat_index_terms_input (term :: terms))).
      rewrite mat_nested_work_app.
      change (rules_nested_probe_work (RprobeCase 13 :: later)) with
        (1 + rules_nested_probe_work later).
      cbn zeta in IH.
      destruct term as [v | c].
      * change (mat_term_index_size (TVar v)) with v in Hhead.
        change (mat_index_terms_input (TVar v :: terms)) with
          (1 + mat_index_terms_input terms + v).
        change (mat_tuple_size (value :: row)) with
          (1 + Pos.size_nat value + mat_tuple_size row).
        nia.
      * change (mat_term_index_size (TConst c)) with 0 in Hhead.
        change (mat_index_terms_input (TConst c :: terms)) with
          (1 + mat_index_terms_input terms + Pos.size_nat c).
        change (mat_tuple_size (value :: row)) with
          (1 + Pos.size_nat value + mat_tuple_size row).
        nia.
    + change (1 + rules_nested_probe_work (events ++ [RprobeCase 13]) <=
        1000 * S (mat_index_terms_input (term :: terms)) *
        S (mat_index_terms_input (term :: terms)) * S (mat_index_terms_input (term :: terms)) +
        2 * mat_tuple_size (value :: row) * S (mat_index_terms_input (term :: terms))).
      rewrite mat_nested_work_app.
      change (rules_nested_probe_work [RprobeCase 13]) with 1.
      destruct term as [v | c].
      * change (mat_term_index_size (TVar v)) with v in Hhead.
        change (mat_index_terms_input (TVar v :: terms)) with
          (1 + mat_index_terms_input terms + v).
        change (mat_tuple_size (value :: row)) with
          (1 + Pos.size_nat value + mat_tuple_size row).
        nia.
      * change (mat_term_index_size (TConst c)) with 0 in Hhead.
        change (mat_index_terms_input (TConst c :: terms)) with
          (1 + mat_index_terms_input terms + Pos.size_nat c).
        change (mat_tuple_size (value :: row)) with
          (1 + Pos.size_nat value + mat_tuple_size row).
        nia.
Qed.

Fixpoint mat_positive_ones (value : positive) : nat :=
  match value with
  | xH => 1
  | xO rest => mat_positive_ones rest
  | xI rest => S (mat_positive_ones rest)
  end.

Lemma mat_positive_succ_amortized value :
  length (snd (audit_positive_succ value)) + mat_positive_ones (fst (audit_positive_succ value)) <=
    mat_positive_ones value + 2.
Proof.
  induction value as [value IH | value IH |].
  - cbn [audit_positive_succ].
    destruct (audit_positive_succ value) as [out events] eqn:Hrun; cbn in IH |- *; lia.
  - cbv [audit_positive_succ snd fst mat_positive_ones length]; lia.
  - cbv [audit_positive_succ snd fst mat_positive_ones length]; lia.
Qed.

Lemma mat_nat_encode_linear variable :
  length (snd (audit_nat_encode variable)) + mat_positive_ones (fst (audit_nat_encode variable)) <=
    3 * S variable.
Proof.
  induction variable as [|variable IH].
  - cbv [audit_nat_encode fst snd length mat_positive_ones]; lia.
  - cbn [audit_nat_encode].
    destruct (audit_nat_encode variable) as [previous events] eqn:Hrun; cbn in IH.
    pose proof (mat_positive_succ_amortized previous) as Hsucc.
    destruct (audit_positive_succ previous) as [next succ_events] eqn:Hsuccrun; cbn in Hsucc.
    cbn [snd fst length]; rewrite length_app; cbn in *; lia.
Qed.

Lemma mat_probe_value_work_bound binding variable :
  rules_nested_probe_work (snd (rules_probe_value binding variable)) <= 13 * S variable.
Proof.
  pose proof (mat_nat_encode_linear variable) as Hnat.
  pose proof (mat_nat_code_size_bound variable) as Hsize.
  pose proof (audit_nat_encode_erases variable) as Hcode.
  unfold rules_probe_value.
  destruct (audit_nat_encode variable) as [code encoding_events] eqn:Hencode.
  cbn in Hnat, Hcode.
  change (code = encode nat_encoding variable) in Hcode.
  rewrite <- Hcode in Hsize.
  pose proof (rules_probe_map_get_trace_bound (K := nat) (V := positive) code binding) as Hget.
  destruct (audit_map_code_get@{Set Set Set Set} code binding) as [raw get_events] eqn:Hrun.
  cbn in Hget.
  unfold rules_nested_probe_work, rules_nested_probe_event_work, audit_nat_events_work.
  cbv [snd fold_right]; nia.
Qed.

Lemma mat_positive_set_add_work_bound value set :
  audit_finset_source_work audit_basic_encoding_work
    (snd (audit_finset_add audit_positive_encode value set)) <= 3 + 16 * Pos.size_nat value.
Proof.
  unfold audit_finset_add, audit_positive_encode.
  pose proof (rules_probe_update_trace_bound value (Some (value, tt)) set) as Hset.
  destruct (audit_trie_set value (value, tt) set) as [out events] eqn:Hrun.
  change (audit_trie_update value (Some (value, tt)) set = (out, events)) in Hrun.
  rewrite Hrun in Hset; cbn in Hset.
  unfold audit_finset_source_work, audit_basic_encoding_work.
  cbv [snd length]; lia.
Qed.

Definition mat_binding_bounded size (binding : RulesCompile.binding) : Prop :=
  forall variable value, Map.get nat_encoding variable binding = Some value ->
    Pos.size_nat value <= size.

Lemma mat_bind_term_preserves_bound size binding term value next :
  mat_binding_bounded size binding -> Pos.size_nat value <= size ->
  bind_term binding term value = Some next -> mat_binding_bounded size next.
Proof.
  intros Hbinding Hvalue Hrun.
  destruct term as [variable | constant].
  - cbn [bind_term] in Hrun.
    destruct (Map.get nat_encoding variable binding) as [old |] eqn:Hget.
    + destruct (Pos.eqb value old); inversion Hrun; subst; exact Hbinding.
    + inversion Hrun; subst next.
      intros other found Hfound.
      destruct (Nat.eq_dec other variable) as [Heq | Hne].
      * subst other; rewrite Map.get_set_same in Hfound; inversion Hfound; subst; exact Hvalue.
      * rewrite Map.get_set_other in Hfound by exact Hne; eapply Hbinding; exact Hfound.
  - cbn [bind_term] in Hrun.
    destruct (Pos.eqb value constant); inversion Hrun; subst; exact Hbinding.
Qed.

Lemma mat_bind_terms_preserves_bound size terms row binding next :
  mat_binding_bounded size binding ->
  Forall (fun value => Pos.size_nat value <= size) row ->
  bind_terms terms row binding = Some next -> mat_binding_bounded size next.
Proof.
  revert row binding next; induction terms as [|term terms IH];
    intros [|value row] binding next Hbinding Hrow Hrun; cbn [bind_terms] in Hrun;
    try discriminate.
  - inversion Hrun; subst; exact Hbinding.
  - inversion Hrow as [|head tail Hvalue Htail]; subst.
    destruct (bind_term binding term value) as [updated |] eqn:Hterm; [|discriminate].
    eapply IH; [eapply mat_bind_term_preserves_bound; eassumption | exact Htail | exact Hrun].
Qed.

Lemma mat_tuple_members_size_bound row :
  Forall (fun value => Pos.size_nat value <= mat_tuple_size row) row.
Proof.
  induction row as [|value row IH]; [constructor |].
  constructor.
  - change (Pos.size_nat value <= 1 + Pos.size_nat value + mat_tuple_size row); lia.
  - eapply Forall_impl; [|exact IH].
    intros item Hitem; change (Pos.size_nat item <= 1 + Pos.size_nat value + mat_tuple_size row).
    cbn beta in Hitem; lia.
Qed.

Lemma mat_bound_binding_value terms row binding variable :
  bind_terms terms row Map.empty = Some binding ->
  Pos.size_nat (binding_value binding variable) <= mat_tuple_size row.
Proof.
  intro Hbind.
  assert (Hempty : mat_binding_bounded (mat_tuple_size row) Map.empty).
  { intros key value Hget; rewrite Map.get_empty in Hget; discriminate. }
  pose proof (mat_bind_terms_preserves_bound (mat_tuple_size row) terms row Map.empty binding
    Hempty (mat_tuple_members_size_bound row) Hbind) as Hbounded.
  unfold binding_value; destruct (Map.get nat_encoding variable binding) as [value |] eqn:Hget.
  - eapply Hbounded; exact Hget.
  - destruct row; unfold mat_tuple_size; cbn [fold_right Pos.size_nat]; lia.
Qed.

Lemma mat_variable_add_work_bound bound terms variable row before :
  let size := S (mat_index_terms_input terms) in
  mat_work (snd (mat_variable_add_full bound terms variable row before)) <=
    1300 * size * size * size + 2 * mat_tuple_size row * size +
    13 * S variable + 100 + 98 * mat_tuple_size row.
Proof.
  unfold mat_variable_add_full; rewrite mat_bind_work.
  pose proof (mat_tuple_key_work_bound bound terms row) as Hkeywork.
  pose proof (mat_tuple_key_erases bound terms row) as Hkey.
  destruct (fst (mat_tuple_key bound terms row)) as [key |] eqn:Hresult.
  - assert (Hkeysize : mat_tuple_size key <= mat_tuple_size row).
    { apply (mat_tuple_key_size_bound bound terms row key); congruence. }
    rewrite mat_bind_work, mat_lift_work, mat_lift_erases.
    pose proof (mat_bind_terms_work_bound terms row Map.empty) as Hbindwork.
    pose proof (rules_bind_terms_erases terms row Map.empty) as Hbind.
    destruct (fst (rules_bind_terms_counted terms row Map.empty)) as [binding |] eqn:Hresultbind.
    + assert (Hvalue : Pos.size_nat (binding_value binding variable) <= mat_tuple_size row).
      { apply (mat_bound_binding_value terms row binding variable); congruence. }
      rewrite mat_bind_work, mat_lift_work, mat_lift_erases.
      pose proof (mat_probe_value_work_bound binding variable) as Hvaluework.
      pose proof (rules_probe_value_erases binding variable) as Hvalueerase.
      rewrite mat_bind_work.
      pose proof (mat_index_get_work_bound key before) as Hget.
      rewrite mat_bind_work, mat_lift_work, mat_lift_erases.
      pose proof (mat_positive_set_add_work_bound (fst (rules_probe_value binding variable))
        (match fst (mat_get_encoded mat_tuple_encoder key before) with
         | Some set => set
         | None => FinSet.empty
         end)) as Hadd.
      pose proof (mat_index_set_work_bound key
        (fst (audit_finset_add audit_positive_encode (fst (rules_probe_value binding variable))
          (match fst (mat_get_encoded mat_tuple_encoder key before) with
           | Some set => set
           | None => FinSet.empty
           end))) before) as Hset.
      rewrite Hvalueerase in Hadd, Hset.
      cbn zeta in Hkeywork, Hbindwork |- *;
      rewrite Hvalueerase;
      replace (1300 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms)) with
        (300 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) +
        1000 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms)) by nia;
      set (size := S (mat_index_terms_input terms)) in *;
      assert (H300 : 300 * size * size * size = 300 * (size * size * size)) by nia;
      assert (H1000 : 1000 * size * size * size = 1000 * (size * size * size)) by nia;
      rewrite H300 in Hkeywork |- *; rewrite H1000 in Hbindwork |- *;
      set (cube := size * size * size) in *.
      eapply Nat.le_trans with (m := 300 * cube +
        ((1000 * cube + 2 * mat_tuple_size row * size) +
         (13 * S variable + ((13 + 30 * mat_tuple_size key) +
          ((3 + 16 * Pos.size_nat (binding_value binding variable)) +
           (24 + 52 * mat_tuple_size key)))))).
      * apply Nat.add_le_mono; [exact Hkeywork |].
        apply Nat.add_le_mono; [exact Hbindwork |].
        apply Nat.add_le_mono; [exact Hvaluework |].
        apply Nat.add_le_mono; [exact Hget |].
        apply Nat.add_le_mono; [exact Hadd | exact Hset].
      * clear H300 H1000 Hkey Hbind Hresult Hresultbind Hvalueerase;
          clearbody cube size; lia.
    + rewrite mat_return_work; cbn zeta in Hkeywork, Hbindwork |- *;
      replace (1300 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms)) with
        (300 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) +
        1000 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms)) by nia; lia.
  - rewrite mat_return_work; cbn zeta in Hkeywork |- *; nia.
Qed.

Lemma mat_build_variable_work_bound bound terms variable rows :
  let size := S (mat_index_terms_input terms) in
  mat_work (snd (mat_build_variable_full bound terms variable rows)) <=
    length rows * (1300 * size * size * size + 13 * S variable + 200) +
    mat_index_rows_input rows * (2 * size + 98) + 200.
Proof.
  unfold mat_build_variable_full.
  induction rows as [|row rows IH].
  - change (mat_work (snd (mat_mark 5 (mat_return (Table.empty : variable_index)))) <=
      0 * (1300 * S (mat_index_terms_input terms) * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) + 13 * S variable + 200) +
      mat_index_rows_input [] * (2 * S (mat_index_terms_input terms) + 98) + 200).
    rewrite mat_mark_work, mat_return_work; unfold mat_index_rows_input; cbn [fold_right]; lia.
  - change (mat_work (snd (mat_mark 5
      (mat_bind (mat_foldr (mat_variable_add_full bound terms variable) rows Table.empty)
        (mat_variable_add_full bound terms variable row)))) <=
      length (row :: rows) * (1300 * S (mat_index_terms_input terms) *
        S (mat_index_terms_input terms) * S (mat_index_terms_input terms) + 13 * S variable + 200) +
      mat_index_rows_input (row :: rows) * (2 * S (mat_index_terms_input terms) + 98) + 200).
    rewrite mat_mark_work, mat_bind_work.
    pose proof (mat_variable_add_work_bound bound terms variable row
      (fst (mat_foldr (mat_variable_add_full bound terms variable) rows Table.empty))) as Hrow.
    unfold mat_index_rows_input in *; cbn [fold_right length] in *; nia.
Qed.

Lemma mat_variable_polynomial_unscaled size rows bound :
  1 <= size -> size <= bound -> rows <= bound ->
  rows * (1300 * size * size * size + 213) + rows * (2 * size + 98) + 200 <=
    (1000 * 1000) * Nat.pow bound 6.
Proof.
  intros Hsize Hsizebound Hrows.
  assert (Hbound : 1 <= bound) by lia.
  assert (Hsquare : size * size <= bound * bound) by nia.
  assert (Hcube : size * size * size <= bound * bound * bound) by nia.
  assert (Hbound2 : 1 <= bound * bound) by nia.
  assert (Hbound3 : 1 <= bound * bound * bound) by nia.
  assert (Hbound4 : bound * bound * bound <= bound * bound * bound * bound) by nia.
  assert (Hbound5 : bound * bound * bound * bound <=
      bound * bound * bound * bound * bound) by nia.
  assert (Hbound6 : bound * bound * bound * bound * bound <=
      bound * bound * bound * bound * bound * bound) by nia.
  cbn [Nat.pow]; nia.
Qed.

Lemma mat_variable_polynomial_bound size rows bound factor :
  1 <= size -> size <= bound -> rows <= bound -> 1 <= factor ->
  rows * (1300 * size * size * size + 13 * factor + 200) +
    rows * (2 * size + 98) + 200 <= factor * ((1000 * 1000) * Nat.pow bound 6).
Proof.
  intros Hsize Hsizebound Hrows Hfactor.
  pose proof (mat_variable_polynomial_unscaled size rows bound Hsize Hsizebound Hrows) as Hbase.
  eapply Nat.le_trans.
  2: { apply Nat.mul_le_mono_l; exact Hbase. }
  clear Hbase Hsizebound Hrows; set (cube := size * size * size) in *.
  assert (Hcube : 1300 * size * size * size = 1300 * cube) by (unfold cube; nia).
  rewrite Hcube.
  clear Hcube; clearbody cube; nia.
Qed.

(** Variable-index construction stays within its variable-scaled input budget. *)
Theorem mat_variable_full_input_bound : mat_variable_full_input_bound_statement.
Proof.
  unfold mat_variable_full_input_bound_statement; split.
  - intros bound terms variable row before.
    pose proof (mat_variable_add_work_bound bound terms variable row before) as Hwork.
    set (size := S (mat_index_terms_input terms)) in *.
    set (rows := mat_index_rows_input [row]).
    set (total := 1 + CollectionsAuditElements.audit_trie_nodes bound +
      mat_index_terms_input terms + rows + CollectionsAuditElements.audit_trie_nodes before).
    assert (Hsize : 1 <= size) by (unfold size; lia).
    assert (Hsizetotal : size <= total) by (unfold size, total; lia).
    assert (Hrowstotal : rows <= total) by (unfold total; lia).
    assert (Hrow : mat_tuple_size row + 1 = rows)
      by (unfold rows, mat_index_rows_input; reflexivity).
    pose proof (mat_variable_polynomial_bound size rows total (S variable)
      Hsize Hsizetotal Hrowstotal ltac:(lia)) as Hpoly.
    change (mat_work (snd (mat_variable_add_full bound terms variable row before)) <=
      S variable * ((1000 * 1000) * Nat.pow total 6)).
    eapply Nat.le_trans; [|exact Hpoly].
    clear Hpoly; cbn zeta in Hwork.
    set (cube := size * size * size) in *.
    assert (Hcube : 1300 * size * size * size = 1300 * cube) by (unfold cube; nia).
    rewrite Hcube in Hwork |- *; clear Hcube; clearbody cube size; nia.
  - intros bound terms variable rows.
    pose proof (mat_build_variable_work_bound bound terms variable rows) as Hwork.
    pose proof (mat_index_rows_length_bound rows) as Hlength.
    set (size := S (mat_index_terms_input terms)) in *.
    set (rowsize := mat_index_rows_input rows) in *.
    set (total := 1 + CollectionsAuditElements.audit_trie_nodes bound +
      mat_index_terms_input terms + rowsize +
      CollectionsAuditElements.audit_trie_nodes (Table.empty : variable_index)).
    assert (Hsize : 1 <= size) by (unfold size; lia).
    assert (Hsizetotal : size <= total) by (unfold size, total; lia).
    assert (Hrowstotal : rowsize <= total) by (unfold total; lia).
    pose proof (mat_variable_polynomial_bound size rowsize total (S variable)
      Hsize Hsizetotal Hrowstotal ltac:(lia)) as Hpoly.
    change (mat_work (snd (mat_build_variable_full bound terms variable rows)) <=
      S variable * ((1000 * 1000) * Nat.pow total 6)).
    eapply Nat.le_trans; [|exact Hpoly].
    clear Hpoly; cbn zeta in Hwork.
    assert (Hmul : length rows * (1300 * size * size * size + 13 * S variable + 200) <=
      rowsize * (1300 * size * size * size + 13 * S variable + 200))
      by (apply Nat.mul_le_mono_r; exact Hlength).
    lia.
Qed.

(** The combined source claim joins the erasure and both independently proved phase bounds. *)
Theorem mat_index_full_source : mat_index_full_source_statement.
Proof.
  unfold mat_index_full_source_statement; split; [exact mat_index_full_erases |].
  split; [exact mat_index_full_input_bound | exact mat_variable_full_input_bound].
Qed.
