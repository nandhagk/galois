(** * Nested probe adequacy

    Counted nested probes preserve the original binding and index operations.
    For example, repeated variables compare against their existing binding.
    Builds on: RulesAuditNestedProbe and collection adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet
  CollectionsAuditTrie CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditPrimitive
  CollectionsAuditTrieAdequacy CollectionsAuditFinSetAdequacy CollectionsAuditEncodingAdequacy
  CollectionsAuditPrimitiveAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditNestedProbe.
Import List.ListNotations.

(** * Erasure of individual operations *)

Lemma rules_probe_bound_term_erases bound term :
  fst (rules_probe_bound_term bound term) = bound_term bound term.
Proof.
  destruct term as [variable | constant].
  - unfold rules_probe_bound_term, bound_term.
    pose proof (audit_finset_mem_erases nat audit_nat_encoding_event audit_nat_encode
      nat_encoding variable bound (audit_nat_encode_erases variable)) as Hmem.
    destruct (audit_finset_mem audit_nat_encode variable bound) as [result events].
    exact Hmem.
  - reflexivity.
Qed.

Lemma rules_probe_filter_erases bound terms :
  fst (rules_probe_filter bound terms) = filter (bound_term bound) terms.
Proof.
  induction terms as [|term terms IH]; cbn [rules_probe_filter filter]; [reflexivity |].
  pose proof (rules_probe_bound_term_erases bound term) as Hhead.
  destruct (rules_probe_bound_term bound term) as [keep head] eqn:Hheadrun; cbn in Hhead.
  destruct (rules_probe_filter bound terms) as [tail events] eqn:Htail; cbn in IH.
  cbn; rewrite <- Hhead, <- IH; reflexivity.
Qed.

Polymorphic Lemma rules_probe_trie_get_erases {A : Type} key (input : Trie.t A) :
  fst (audit_trie_get key input) = Trie.get key input.
Proof.
  revert input; induction key as [key IH | key IH |]; intro input.
  - cbn [audit_trie_get Trie.get].
    specialize (IH (Trie.right input)).
    destruct (audit_trie_get key (Trie.right input)) as [result events].
    exact IH.
  - cbn [audit_trie_get Trie.get].
    specialize (IH (Trie.left input)).
    destruct (audit_trie_get key (Trie.left input)) as [result events].
    exact IH.
  - reflexivity.
Qed.

Polymorphic Lemma rules_probe_map_get_erases {K V : Type} key (input : Map.t K V) :
  fst (audit_map_code_get key input) = Map.code_get key input.
Proof.
  pose proof (rules_probe_trie_get_erases key input) as Herase.
  unfold audit_map_code_get, Map.code_get.
  destruct (audit_trie_get key input) as [result events].
  cbn in Herase; rewrite Herase; reflexivity.
Qed.

Lemma rules_probe_value_erases binding variable :
  fst (rules_probe_value binding variable) = binding_value binding variable.
Proof.
  unfold rules_probe_value, binding_value, Map.get.
  pose proof (audit_nat_encode_erases variable) as Hencode.
  destruct (audit_nat_encode variable) as [code enc_events] eqn:Henc; cbn in Hencode.
  assert (Hget : fst (audit_map_code_get code binding) =
    Map.code_get code binding).
  { apply rules_probe_map_get_erases. }
  case_eq (audit_map_code_get code binding); intros result events Hrun.
  cbn in Hget.
  cbn; apply (f_equal fst) in Hrun; cbn in Hrun;
  assert (Hresult : result = Map.code_get code binding) by (rewrite <- Hrun; exact Hget);
  rewrite Hresult, Hencode; reflexivity.
Qed.

Lemma rules_probe_instantiate_erases binding terms :
  fst (rules_probe_instantiate binding terms) = map (inst (binding_value binding)) terms.
Proof.
  induction terms as [|term terms IH]; cbn [rules_probe_instantiate map]; [reflexivity |].
  destruct term as [variable | constant].
  - pose proof (rules_probe_value_erases binding variable) as Hvalue.
    destruct (rules_probe_value binding variable) as [value events]; cbn in Hvalue.
    destruct (rules_probe_instantiate binding terms) as [tail later]; cbn in IH.
    cbn [inst]; rewrite Hvalue, IH; reflexivity.
  - destruct (rules_probe_instantiate binding terms) as [tail later]; cbn in IH.
    cbn [inst]; rewrite IH; reflexivity.
Qed.

Lemma rules_bound_key_erases bound binding terms :
  fst (rules_bound_key_counted bound binding terms) = bound_key bound binding terms.
Proof.
  unfold rules_bound_key_counted, bound_key.
  pose proof (rules_probe_filter_erases bound terms) as Hfilter.
  destruct (rules_probe_filter bound terms) as [selected events]; cbn in Hfilter.
  pose proof (rules_probe_instantiate_erases binding selected) as Hinst.
  destruct (rules_probe_instantiate binding selected) as [key key_events]; cbn in Hinst.
  cbn; rewrite Hinst, Hfilter; reflexivity.
Qed.

Polymorphic Lemma rules_probe_trie_set_erases {A : Type} key (value : A) (input : Trie.t A) :
  fst (audit_trie_set key value input) = Trie.set key value input.
Proof.
  revert input; induction key as [key IH | key IH |]; intro input.
  - cbn [audit_trie_set audit_trie_update Trie.set].
    specialize (IH (Trie.right input)); unfold audit_trie_set in IH.
    destruct (audit_trie_update key (Some value) (Trie.right input))
      as [updated events].
    cbn in IH; rewrite IH; reflexivity.
  - cbn [audit_trie_set audit_trie_update Trie.set].
    specialize (IH (Trie.left input)); unfold audit_trie_set in IH.
    destruct (audit_trie_update key (Some value) (Trie.left input))
      as [updated events].
    cbn in IH; rewrite IH; reflexivity.
  - reflexivity.
Qed.

Lemma rules_bind_term_erases binding term value :
  fst (rules_bind_term_counted binding term value) = bind_term binding term value.
Proof.
  destruct term as [variable | constant].
  - unfold rules_bind_term_counted, bind_term, Map.get, Map.set.
    pose proof (audit_nat_encode_erases variable) as Hencode.
    destruct (audit_nat_encode variable) as [code enc_events] eqn:Henc; cbn in Hencode.
    cbn.
    pose proof (rules_probe_map_get_erases code binding) as Hget.
    case_eq (audit_map_code_get code binding); intros result events Hrun.
    apply (f_equal fst) in Hrun; cbn in Hrun.
    assert (Hresult : result = Map.code_get code binding) by (rewrite <- Hrun; exact Hget).
    rewrite <- Hencode, <- Hresult; destruct result as [old |].
    + pose proof (audit_positive_eqb_erases value old) as Hequal.
      destruct (audit_positive_eqb value old) as [equal equal_events]; cbn in Hequal.
      cbn; rewrite <- Hequal; reflexivity.
    + cbn.
      pose proof (rules_probe_trie_set_erases code (variable, value) binding) as Hset.
      destruct (audit_trie_set code (variable, value) binding)
        as [after set_events]; cbn in Hset.
      cbn; rewrite Hset; reflexivity.
  - unfold rules_bind_term_counted, bind_term.
    pose proof (audit_positive_eqb_erases value constant) as Hequal.
    destruct (audit_positive_eqb value constant) as [equal equal_events]; cbn in Hequal.
    cbn; rewrite <- Hequal; reflexivity.
Qed.

Lemma rules_bind_terms_erases terms row binding :
  fst (rules_bind_terms_counted terms row binding) = bind_terms terms row binding.
Proof.
  revert row binding; induction terms as [|term terms IH]; intros [|value row] binding;
    cbn [rules_bind_terms_counted bind_terms]; try reflexivity.
  pose proof (rules_bind_term_erases binding term value) as Hhead.
  destruct (rules_bind_term_counted binding term value) as [[next |] events]; cbn in Hhead.
  - rewrite <- Hhead; specialize (IH row next).
    destruct (rules_bind_terms_counted terms row next) as [out later]; cbn in IH.
    cbn; exact IH.
  - rewrite <- Hhead; reflexivity.
Qed.

Lemma rules_probe_rows_erases terms binding rows :
  fst (rules_probe_rows terms binding rows) =
    flat_map (fun row => option_binding (bind_terms terms row binding)) rows.
Proof.
  induction rows as [|row rows IH]; cbn [rules_probe_rows flat_map]; [reflexivity |].
  pose proof (rules_bind_terms_erases terms row binding) as Hbind.
  destruct (rules_bind_terms_counted terms row binding) as [candidate events]; cbn in Hbind.
  destruct (rules_probe_rows terms binding rows) as [tail later]; cbn in IH.
  cbn; rewrite <- Hbind, <- IH; destruct candidate; reflexivity.
Qed.

Lemma rules_probe_bindings_erases search bindings :
  fst (rules_probe_bindings search bindings) = nested_probe search bindings.
Proof.
  unfold nested_probe; induction bindings as [|binding bindings IH];
    cbn [rules_probe_bindings flat_map]; [reflexivity |].
  pose proof (rules_bound_key_erases (nested_bound search) binding (nested_terms search)) as Hkey.
  destruct (rules_bound_key_counted (nested_bound search) binding (nested_terms search))
    as [key key_events]; cbn in Hkey.
  pose proof (audit_list_encode_erases positive (audit_basic_encoding_event positive)
    audit_positive_encode positive_encoding key) as Hencode.
  assert (Hall : forall x, In x key -> fst (audit_positive_encode x) =
    encode positive_encoding x) by (intros; apply audit_positive_encode_erases).
  specialize (Hencode Hall).
  destruct (audit_list_encode audit_positive_encode key) as [code enc_events]; cbn in Hencode.
  pose proof (rules_probe_map_get_erases (K := tuple) (V := list tuple) code
    (nested_index search)) as Hget.
  case_eq (audit_map_code_get code (nested_index search));
    intros raw get_events Hrun.
  apply (f_equal fst) in Hrun; cbn in Hrun.
  assert (Hresult : raw = Map.code_get code (nested_index search))
    by (rewrite <- Hrun; exact Hget).
  cbn.
  destruct (rules_probe_rows (nested_terms search) binding
    (match raw with
    | Some found => found
    | None => []
    end)) as [head row_events] eqn:Hrows.
  pose proof (rules_probe_rows_erases (nested_terms search) binding
    (match raw with
    | Some found => found
    | None => []
    end)) as Hrow.
  rewrite Hrows in Hrow; cbn in Hrow.
  destruct (rules_probe_bindings search bindings) as [tail tail_events]; cbn in IH.
  cbn; rewrite <- IH, Hrow.
  unfold index_get, Map.get, tuple_encoding; rewrite <- Hkey.
  change (code = encode (list_encoding positive_encoding) key) in Hencode.
  cbv [encode list_encoding] in Hencode |- *.
  rewrite <- Hencode, <- Hresult.
  reflexivity.
Qed.

Lemma rules_run_nested_erases searches bindings :
  fst (rules_run_nested_counted searches bindings) = run_nested searches bindings.
Proof.
  revert bindings; induction searches as [|search searches IH]; intro bindings;
    cbn [rules_run_nested_counted run_nested]; [reflexivity |].
  pose proof (rules_probe_bindings_erases search bindings) as Hprobe.
  destruct (rules_probe_bindings search bindings) as [next events]; cbn in Hprobe.
  specialize (IH next).
  destruct (rules_run_nested_counted searches next) as [result later]; cbn in IH.
  cbn; rewrite <- Hprobe; exact IH.
Qed.

(** Counted nested probing preserves the exact source bindings and their order. *)
Theorem rules_nested_probe_erasure : rules_nested_probe_erasure_statement.
Proof.
  unfold rules_nested_probe_erasure_statement.
  repeat split.
  - exact rules_bound_key_erases.
  - exact rules_bind_term_erases.
  - exact rules_bind_terms_erases.
  - exact rules_probe_bindings_erases.
  - exact rules_run_nested_erases.
Qed.

(** * Bounds for actual collection calls *)

Polymorphic Lemma rules_probe_get_trace_bound {A : Type} key (input : Trie.t A) :
  audit_trie_get_trace_source_work (snd (audit_trie_get key input)) <= 5 * Pos.size_nat key.
Proof.
  revert input; induction key as [key IH | key IH |]; intro input.
  - cbn [audit_trie_get Pos.size_nat].
    specialize (IH (Trie.right input)).
    destruct (audit_trie_get key (Trie.right input)) as [result events]; cbn in IH.
    cbn [audit_trie_get_trace_source_work].
    destruct input; cbn [snd audit_trie_get_trace_source_work audit_trie_accessor_work] in *; lia.
  - cbn [audit_trie_get Pos.size_nat].
    specialize (IH (Trie.left input)).
    destruct (audit_trie_get key (Trie.left input)) as [result events]; cbn in IH.
    cbn [audit_trie_get_trace_source_work].
    destruct input; cbn [snd audit_trie_get_trace_source_work audit_trie_accessor_work] in *; lia.
  - cbn [audit_trie_get Pos.size_nat audit_trie_get_trace_source_work].
    destruct input; cbn [snd audit_trie_get_trace_source_work audit_trie_accessor_work]; lia.
Qed.

Polymorphic Lemma rules_probe_update_trace_app {A : Type}
    (first second : CollectionsAuditCost.audit_trace (audit_trie_call A)) :
  audit_trie_update_trace_source_work (first ++ second) =
    audit_trie_update_trace_source_work first + audit_trie_update_trace_source_work second.
Proof.
  induction first as [|event first IH]; [reflexivity |].
  destruct event as [site operands | call | site operands | bit | site operands];
    try destruct call; cbn [app audit_trie_update_trace_source_work]; rewrite IH; lia.
Qed.

Polymorphic Lemma rules_probe_update_trace_bound {A : Type} key (value : option A)
    (input : Trie.t A) :
  audit_trie_update_trace_source_work (snd (audit_trie_update key value input)) <=
    16 * Pos.size_nat key.
Proof.
  revert input; induction key as [key IH | key IH |]; intro input.
  - cbn [audit_trie_update Pos.size_nat].
    specialize (IH (Trie.right input)).
    destruct (audit_trie_update key value (Trie.right input)) as [result events]; cbn in IH.
    cbn; repeat rewrite rules_probe_update_trace_app.
    cbn [snd audit_trie_update_trace_source_work].
    pose proof (audit_accessor_bound A input) as Haccess.
    pose proof (audit_node_bound A (Trie.left input) (Trie.value input) result) as Hnode.
    lia.
  - cbn [audit_trie_update Pos.size_nat].
    specialize (IH (Trie.left input)).
    destruct (audit_trie_update key value (Trie.left input)) as [result events]; cbn in IH.
    cbn; repeat rewrite rules_probe_update_trace_app.
    cbn [snd audit_trie_update_trace_source_work].
    pose proof (audit_accessor_bound A input) as Haccess.
    pose proof (audit_node_bound A result (Trie.value input) (Trie.right input)) as Hnode.
    lia.
  - cbn [audit_trie_update Pos.size_nat audit_trie_update_trace_source_work].
    pose proof (audit_accessor_bound A input) as Haccess.
    pose proof (audit_node_bound A (Trie.left input) value (Trie.right input)) as Hnode.
    cbn [snd audit_trie_update_trace_source_work]; lia.
Qed.

Polymorphic Lemma rules_probe_map_get_trace_bound {K V : Type} key (input : Map.t K V) :
  audit_trie_get_trace_source_work (snd (audit_map_code_get key input)) <= 5 * Pos.size_nat key.
Proof.
  pose proof (rules_probe_get_trace_bound key input) as Hbound.
  unfold audit_map_code_get.
  destruct (audit_trie_get key input) as [result events]; cbn in Hbound |- *; exact Hbound.
Qed.

Lemma rules_probe_nat_encode_bound variable :
  audit_nat_events_work (snd (audit_nat_encode variable)) <= rules_nat_encoder_budget variable.
Proof.
  pose proof (audit_nat_encode_count variable) as Hcount.
  unfold audit_nat_encode_count_statement in Hcount.
  unfold audit_nat_events_work, rules_nat_encoder_budget; lia.
Qed.

Definition rules_probe_encoding_event_valid
    (event : audit_list_event positive (audit_basic_encoding_event positive)) : Prop :=
  match event with
  | AuditListComponent _ _ child => length child <= 1
  | _ => True
  end.

Lemma rules_probe_encoding_frames_valid frames :
  Forall rules_probe_encoding_event_valid (map (@AuditListFrame positive _) frames).
Proof.
  induction frames as [|frame frames IH]; cbn.
  - constructor.
  - constructor; [exact I | exact IH].
Qed.

Lemma rules_probe_emit_list_valid values :
  Forall rules_probe_encoding_event_valid
    (snd (audit_emit_list audit_positive_encode values)).
Proof.
  induction values as [|value values IH].
  - cbn [audit_emit_list]; constructor; [exact I | constructor].
  - cbn [audit_emit_list audit_positive_encode].
    destruct (audit_emit_list audit_positive_encode values) as [tail events]; cbn in IH.
    destruct (audit_emit_code value tail) as [bits frames].
    cbn; constructor; [exact I | constructor; [cbn; lia |]].
    apply Forall_app; split; [exact IH | apply rules_probe_encoding_frames_valid].
Qed.

Lemma rules_probe_list_encode_valid values :
  Forall rules_probe_encoding_event_valid
    (snd (audit_list_encode audit_positive_encode values)).
Proof.
  pose proof (rules_probe_emit_list_valid values) as Hvalid.
  unfold audit_list_encode.
  destruct (audit_emit_list audit_positive_encode values) as [bits events]; cbn in Hvalid.
  destruct (audit_stream_positive bits) as [code frames]; cbn.
  apply Forall_app; split; [exact Hvalid | apply rules_probe_encoding_frames_valid].
Qed.

Lemma rules_probe_list_work_bound events :
  Forall rules_probe_encoding_event_valid events ->
  audit_list_events_work audit_basic_encoding_work events <= 4 * length events.
Proof.
  intro Hvalid; induction Hvalid as [|event events Hhead Htail IH].
  - reflexivity.
  - destruct event as [values | value code child | frame].
    + cbn [audit_list_events_work]; cbn in *; lia.
    + cbn [rules_probe_encoding_event_valid audit_list_events_work
        audit_basic_encoding_work] in *; unfold audit_basic_encoding_work in *;
      cbn [length] in *; lia.
    + destruct frame; cbn [audit_list_events_work audit_encoding_frame_charge] in *;
      cbn [length] in *; lia.
Qed.

Lemma rules_probe_list_encode_bound values :
  audit_list_events_work audit_basic_encoding_work
    (snd (audit_list_encode audit_positive_encode values)) <=
    8 + 8 * length values + 12 * audit_encoded_bits audit_positive_encode values.
Proof.
  pose proof (rules_probe_list_work_bound _ (rules_probe_list_encode_valid values)) as Hwork.
  pose proof (audit_list_encode_count positive (audit_basic_encoding_event positive)
    audit_positive_encode values) as Hcount.
  rewrite Hcount in Hwork; lia.
Qed.

Definition rules_probe_event_valid (event : rules_nested_probe_event) : Prop :=
  rules_nested_probe_event_work event <= rules_nested_probe_event_budget event.

Lemma rules_probe_bound_events_valid bound term :
  Forall rules_probe_event_valid (snd (rules_probe_bound_term bound term)).
Proof.
  destruct term as [variable | constant].
  - unfold rules_probe_bound_term, audit_finset_mem.
    pose proof (rules_probe_nat_encode_bound variable) as Hnat.
    pose proof (audit_nat_encode_erases variable) as Hcode.
    destruct (audit_nat_encode variable) as [code encoding_events]; cbn in Hnat, Hcode.
    pose proof (rules_probe_map_get_trace_bound code bound) as Hget.
    destruct (audit_map_code_get code bound) as [raw get_events]; cbn in Hget.
    cbn; constructor.
    + unfold rules_probe_event_valid; cbn [rules_nested_probe_event_work
        rules_nested_probe_event_budget]; lia.
    + constructor.
      * unfold rules_probe_event_valid; cbn [rules_nested_probe_event_work
          rules_nested_probe_event_budget audit_finset_source_work].
        unfold audit_nat_events_work in *; cbn in *; rewrite <- Hcode in *.
        destruct raw; cbn in *; lia.
      * constructor.
  - cbn [rules_probe_bound_term]; constructor.
    + unfold rules_probe_event_valid; cbn [rules_nested_probe_event_work
        rules_nested_probe_event_budget]; lia.
    + constructor.
Qed.

Lemma rules_probe_binding_get_valid variable binding code encoding_events raw get_events :
  audit_nat_encode variable = (code, encoding_events) ->
  audit_map_code_get@{Set Set Set Set} code binding = (raw, get_events) ->
  rules_probe_event_valid (RprobeBindingGet variable code binding raw encoding_events get_events).
Proof.
  intros Hencode Hget.
  pose proof (rules_probe_nat_encode_bound variable) as Hnat.
  rewrite Hencode in Hnat; cbn in Hnat.
  pose proof (rules_probe_map_get_trace_bound (K := nat) (V := positive) code binding) as Htrace.
  rewrite Hget in Htrace; cbn in Htrace.
  unfold rules_probe_event_valid, rules_nested_probe_event_work, rules_nested_probe_event_budget.
  unfold audit_nat_events_work, rules_nat_encoder_budget in *; cbn in *; lia.
Qed.

Lemma rules_probe_binding_set_valid variable value binding code encoding_events after set_events :
  audit_nat_encode variable = (code, encoding_events) ->
  audit_trie_set@{Set Set} code (variable, value) binding = (after, set_events) ->
  rules_probe_event_valid
    (RprobeBindingSet variable value code binding after encoding_events set_events).
Proof.
  intros Hencode Hset.
  pose proof (rules_probe_nat_encode_bound variable) as Hnat.
  rewrite Hencode in Hnat; cbn in Hnat.
  pose proof (rules_probe_update_trace_bound code (Some (variable, value)) binding) as Htrace.
  change (audit_trie_update code (Some (variable, value)) binding = (after, set_events)) in Hset.
  rewrite Hset in Htrace; cbn in Htrace.
  unfold rules_probe_event_valid, rules_nested_probe_event_work, rules_nested_probe_event_budget.
  unfold audit_nat_events_work, rules_nat_encoder_budget in *; cbn in *; lia.
Qed.

Lemma rules_probe_equal_valid lhs rhs equal events :
  audit_positive_eqb lhs rhs = (equal, events) ->
  rules_probe_event_valid (RprobeEqual lhs rhs equal events).
Proof.
  intro Hequal; pose proof (audit_positive_eqb_source_bound lhs rhs) as Hbound.
  rewrite Hequal in Hbound; exact Hbound.
Qed.

Lemma rules_probe_index_get_valid key index code encoding_events raw get_events :
  audit_list_encode audit_positive_encode key = (code, encoding_events) ->
  audit_map_code_get code index = (raw, get_events) ->
  rules_probe_event_valid (RprobeIndexGet key code index raw encoding_events get_events).
Proof.
  intros Hencode Hget.
  pose proof (rules_probe_list_encode_bound key) as Hencoding.
  rewrite Hencode in Hencoding; cbn in Hencoding.
  pose proof (rules_probe_map_get_trace_bound (K := tuple) (V := list tuple) code index) as Htrace.
  rewrite Hget in Htrace; cbn in Htrace.
  unfold rules_probe_event_valid, rules_nested_probe_event_work, rules_nested_probe_event_budget.
  lia.
Qed.

Lemma rules_probe_case_valid site : rules_probe_event_valid (RprobeCase site).
Proof.
  unfold rules_probe_event_valid; cbn [rules_nested_probe_event_work
    rules_nested_probe_event_budget]; lia.
Qed.

Lemma rules_probe_append_valid size : rules_probe_event_valid (RprobeAppend size).
Proof.
  unfold rules_probe_event_valid; cbn [rules_nested_probe_event_work
    rules_nested_probe_event_budget]; lia.
Qed.

Lemma rules_probe_filter_events_valid bound terms :
  Forall rules_probe_event_valid (snd (rules_probe_filter bound terms)).
Proof.
  induction terms as [|term terms IH].
  - cbn [rules_probe_filter]; constructor; [apply rules_probe_case_valid | constructor].
  - cbn [rules_probe_filter].
    pose proof (rules_probe_bound_events_valid bound term) as Hhead.
    destruct (rules_probe_bound_term bound term) as [keep head]; cbn in Hhead.
    destruct (rules_probe_filter bound terms) as [tail events]; cbn in IH.
    cbn; constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact Hhead |].
    constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact IH |].
    destruct keep; cbn; [constructor; [apply rules_probe_case_valid | constructor] | constructor].
Qed.

Lemma rules_probe_value_events_valid binding variable :
  Forall rules_probe_event_valid (snd (rules_probe_value binding variable)).
Proof.
  unfold rules_probe_value.
  destruct (audit_nat_encode variable) as [code encoding_events] eqn:Hencode.
  destruct (audit_map_code_get@{Set Set Set Set} code binding) as [raw get_events] eqn:Hget.
  cbn; constructor.
  - eapply rules_probe_binding_get_valid; eassumption.
  - constructor; [apply rules_probe_case_valid | constructor].
Qed.

Lemma rules_probe_instantiate_events_valid binding terms :
  Forall rules_probe_event_valid (snd (rules_probe_instantiate binding terms)).
Proof.
  induction terms as [|term terms IH].
  - cbn [rules_probe_instantiate]; constructor; [apply rules_probe_case_valid | constructor].
  - cbn [rules_probe_instantiate].
    destruct term as [variable | constant].
    + pose proof (rules_probe_value_events_valid binding variable) as Hvalue.
      destruct (rules_probe_value binding variable) as [value value_events]; cbn in Hvalue.
      destruct (rules_probe_instantiate binding terms) as [tail events]; cbn in IH.
      cbn; constructor; [apply rules_probe_case_valid |].
      constructor; [apply rules_probe_case_valid |].
      apply Forall_app; split; [exact Hvalue |].
      apply Forall_app; split; [exact IH |].
      constructor; [apply rules_probe_case_valid | constructor].
    + destruct (rules_probe_instantiate binding terms) as [tail events]; cbn in IH.
      cbn; constructor; [apply rules_probe_case_valid |].
      constructor; [apply rules_probe_case_valid |].
      apply Forall_app; split; [exact IH |].
      constructor; [apply rules_probe_case_valid | constructor].
Qed.

Lemma rules_probe_bound_key_events_valid bound binding terms :
  Forall rules_probe_event_valid (snd (rules_bound_key_counted bound binding terms)).
Proof.
  unfold rules_bound_key_counted.
  pose proof (rules_probe_filter_events_valid bound terms) as Hfilter.
  destruct (rules_probe_filter bound terms) as [selected events]; cbn in Hfilter.
  pose proof (rules_probe_instantiate_events_valid binding selected) as Hinst.
  destruct (rules_probe_instantiate binding selected) as [key key_events]; cbn in Hinst.
  cbn; apply Forall_app; split; assumption.
Qed.

Lemma rules_bind_term_events_valid binding term value :
  Forall rules_probe_event_valid (snd (rules_bind_term_counted binding term value)).
Proof.
  destruct term as [variable | constant].
  - unfold rules_bind_term_counted.
    destruct (audit_nat_encode variable) as [code encoding_events] eqn:Hencode.
    destruct (audit_map_code_get@{Set Set Set Set} code binding) as [raw get_events] eqn:Hget.
    destruct raw as [old |].
    + destruct (audit_positive_eqb value old) as [equal equal_events] eqn:Hequal.
      cbn; constructor; [apply rules_probe_case_valid |].
      constructor; [eapply rules_probe_binding_get_valid; eassumption |].
      constructor; [apply rules_probe_case_valid |].
      constructor; [eapply rules_probe_equal_valid; exact Hequal |].
      constructor; [apply rules_probe_case_valid | constructor].
    + cbn.
      destruct (audit_trie_set@{Set Set} code (variable, value) binding)
        as [after set_events] eqn:Hset.
      cbn; constructor; [apply rules_probe_case_valid |].
      constructor; [eapply rules_probe_binding_get_valid; eassumption |].
      constructor; [apply rules_probe_case_valid |].
      constructor; [eapply rules_probe_binding_set_valid; eassumption | constructor].
  - unfold rules_bind_term_counted.
    destruct (audit_positive_eqb value constant) as [equal equal_events] eqn:Hequal.
    cbn; constructor; [apply rules_probe_case_valid |].
    constructor; [eapply rules_probe_equal_valid; exact Hequal |].
    constructor; [apply rules_probe_case_valid | constructor].
Qed.

Lemma rules_bind_terms_events_valid terms row binding :
  Forall rules_probe_event_valid (snd (rules_bind_terms_counted terms row binding)).
Proof.
  revert row binding; induction terms as [|term terms IH]; intros [|value row] binding;
    cbn [rules_bind_terms_counted]; try (constructor; [apply rules_probe_case_valid | constructor]).
  pose proof (rules_bind_term_events_valid binding term value) as Hhead.
  destruct (rules_bind_term_counted binding term value) as [[next |] events]; cbn in Hhead.
  - specialize (IH row next).
    destruct (rules_bind_terms_counted terms row next) as [out later]; cbn in IH.
    cbn; constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact Hhead |].
    constructor; [apply rules_probe_case_valid | exact IH].
  - cbn; constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact Hhead |].
    constructor; [apply rules_probe_case_valid | constructor].
Qed.

Lemma rules_probe_rows_events_valid terms binding rows :
  Forall rules_probe_event_valid (snd (rules_probe_rows terms binding rows)).
Proof.
  induction rows as [|row rows IH].
  - cbn [rules_probe_rows]; constructor; [apply rules_probe_case_valid | constructor].
  - cbn [rules_probe_rows].
    pose proof (rules_bind_terms_events_valid terms row binding) as Hrow.
    destruct (rules_bind_terms_counted terms row binding) as [candidate events]; cbn in Hrow.
    destruct (rules_probe_rows terms binding rows) as [tail later]; cbn in IH.
    cbn; constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact Hrow |].
    constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact IH |].
    constructor; [apply rules_probe_append_valid | constructor].
Qed.

Lemma rules_probe_bindings_events_valid search bindings :
  Forall rules_probe_event_valid (snd (rules_probe_bindings search bindings)).
Proof.
  induction bindings as [|binding bindings IH].
  - cbn [rules_probe_bindings]; constructor; [apply rules_probe_case_valid | constructor].
  - cbn [rules_probe_bindings].
    pose proof (rules_probe_bound_key_events_valid (nested_bound search) binding
      (nested_terms search)) as Hkey.
    destruct (rules_bound_key_counted (nested_bound search) binding (nested_terms search))
      as [key key_events]; cbn in Hkey.
    destruct (audit_list_encode audit_positive_encode key) as [code encoding_events] eqn:Hencode.
    destruct (audit_map_code_get code (nested_index search)) as [raw get_events] eqn:Hget.
    pose proof (rules_probe_rows_events_valid (nested_terms search) binding
      (match raw with
      | Some found => found
      | None => []
      end)) as Hrows.
    destruct (rules_probe_rows (nested_terms search) binding
      (match raw with
      | Some found => found
      | None => []
      end)) as [head row_events]; cbn in Hrows.
    destruct (rules_probe_bindings search bindings) as [tail tail_events]; cbn in IH.
    cbn; constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact Hkey |].
    constructor; [eapply rules_probe_index_get_valid; eassumption |].
    constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; [exact Hrows |].
    apply Forall_app; split; [exact IH |].
    constructor; [apply rules_probe_append_valid | constructor].
Qed.

Lemma rules_run_nested_events_valid searches bindings :
  Forall rules_probe_event_valid (snd (rules_run_nested_counted searches bindings)).
Proof.
  revert bindings; induction searches as [|search searches IH]; intro bindings.
  - cbn [rules_run_nested_counted]; constructor; [apply rules_probe_case_valid | constructor].
  - cbn [rules_run_nested_counted].
    pose proof (rules_probe_bindings_events_valid search bindings) as Hfirst.
    destruct (rules_probe_bindings search bindings) as [next first]; cbn in Hfirst.
    specialize (IH next).
    destruct (rules_run_nested_counted searches next) as [result later]; cbn in IH.
    cbn; constructor; [apply rules_probe_case_valid |].
    apply Forall_app; split; assumption.
Qed.

Lemma rules_probe_valid_work_bound events :
  Forall rules_probe_event_valid events ->
  rules_nested_probe_work events <= rules_nested_probe_budget events.
Proof.
  intro Hvalid; induction Hvalid as [|event events Hhead Htail IH].
  - reflexivity.
  - unfold rules_probe_event_valid in Hhead.
    unfold rules_nested_probe_work, rules_nested_probe_budget in *; cbn in *; lia.
Qed.

(** Actual nested runs erase to the source and satisfy their selected event budget. *)
Theorem rules_run_nested_selected_cost : rules_run_nested_selected_cost_statement.
Proof.
  unfold rules_run_nested_selected_cost_statement.
  intros searches bindings.
  pose proof (rules_run_nested_erases searches bindings) as Herase.
  pose proof (rules_run_nested_events_valid searches bindings) as Hvalid.
  destruct (rules_run_nested_counted searches bindings) as [result events]; cbn in Herase, Hvalid.
  split; [exact Herase | apply rules_probe_valid_work_bound, Hvalid].
Qed.
