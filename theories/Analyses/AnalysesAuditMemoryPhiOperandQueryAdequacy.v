(** * Guarded operand query adequacy

    These proofs connect retained-set probes and optional operand reads to their source work.
    For example, a removed node skips the operand callback and representative lookup.
    Builds on: guarded query model and collection adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditCallback CollectionsAuditEncoding CollectionsAuditTrieAdequacy
  CollectionsAuditFinSetAdequacy CollectionsAuditMapAdequacy.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryPhiInputBudget AnalysesAuditMemoryPhiProducer
  AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiOperandQuery
  AnalysesAuditMemoryInputBudgetAdequacy.
Import List.ListNotations.

(** * Erasure and trace *)

(** An optional body erases using the actual representative map lookup. *)
Lemma audit_phi_query_optional_erases : audit_phi_output_optional_erases_statement.
Proof.
  intros I N E CV CE EN EE version_enc base original reps input Hversion Hbase.
  unfold audit_phi_output_optional_call.
  destruct (base input) as [found body] eqn:Hcall; cbn in Hbase.
  rewrite <- Hbase; destruct found as [v|]; cbn in *; [|reflexivity].
  pose proof (audit_map_get_erases (memory_version N E) (memory_version N E) CV
    version_enc (memory_version_encoding EN EE) v reps (Hversion v)) as Hget.
  destruct (audit_map_get version_enc v reps) as [result calls]; cbn in Hget |- *.
  unfold audit_phi_producer_rep; rewrite <- Hget; destruct result; reflexivity.
Qed.

(** Erasure retains the set guard and the original operand's representative. *)
Theorem audit_phi_output_operand_erases : audit_phi_output_operand_erases_statement.
Proof.
  intros N E CN CV CE EN EE node_enc version_enc base original reps kept input
    Hnode Hversion Hbase.
  pose proof (audit_finset_mem_erases N CN node_enc EN (fst input) kept (Hnode (fst input)))
    as Hguard.
  pose proof (audit_phi_query_optional_erases (N * option E)%type N E CV CE EN EE
    version_enc base original reps input Hversion Hbase) as Hbody.
  unfold audit_phi_output_operand_call.
  destruct (audit_finset_mem node_enc (fst input) kept) as [retained probe]; cbn in Hguard.
  rewrite <- Hguard; destruct retained; [|reflexivity].
  destruct (audit_phi_output_optional_call version_enc base reps input) as [result calls].
  exact Hbody.
Qed.

(** The trace exposes the probe followed by the selected branch only. *)
Theorem audit_phi_operand_query_trace : audit_phi_operand_query_trace_statement.
Proof.
  intros N E CN CV CE node_enc version_enc base reps kept input.
  unfold audit_phi_output_operand_call.
  destruct (audit_finset_mem node_enc (fst input) kept); reflexivity.
Qed.

(** * Exact work and input budgets *)

(** The retained probe pays the actual trie path and the selected result branch. *)
Lemma audit_phi_query_probe_work N CN (enc : N -> positive * list CN) work key kept :
  audit_finset_source_work work (snd (audit_finset_mem enc key kept)) =
    2 + work (snd (enc key)) + audit_trie_get_source_work (fst (enc key)) kept +
    if audit_phi_operand_code_mem (fst (enc key)) kept then 4 else 2.
Proof.
  unfold audit_finset_mem, audit_phi_operand_code_mem, audit_map_code_get.
  destruct (enc key) as [code events].
  pose proof (audit_trie_get_trace_adequate (N * unit)%type code kept) as Htrace.
  pose proof (audit_trie_get_erases (N * unit)%type code kept) as Herase.
  destruct (audit_trie_get code kept) as [found calls].
  cbn in Htrace, Herase |- *.
  unfold Map.code_get; rewrite <- Herase.
  destruct found as [[stored value]|]; cbn; lia.
Qed.

(** The optional body pays its executed callback and, when present, the actual map lookup. *)
Lemma audit_phi_query_optional_work I N E CV CE
    (enc : memory_version N E -> positive * list CV)
    (base : I -> option (memory_version N E) * list CE) version_work base_work reps input :
  audit_phi_closure_source_work version_work base_work
    (snd (audit_phi_output_optional_call enc base reps input)) =
  4 + base_work (snd (base input)) +
    match fst (base input) with
    | None => 0
    | Some v =>
        4 + 1 + version_work (snd (enc v)) + audit_trie_get_source_work (fst (enc v)) reps +
        match Map.code_get (fst (enc v)) reps with
        | None => 2
        | Some _ => 4
        end
    end.
Proof.
  unfold audit_phi_output_optional_call.
  destruct (base input) as [found body].
  destruct found as [v|]; [|reflexivity].
  unfold audit_map_get, audit_map_code_get.
  destruct (enc v) as [code events] eqn:Henc.
  pose proof (audit_trie_get_trace_adequate
    (memory_version N E * memory_version N E)%type code reps) as Htrace.
  pose proof (audit_trie_get_erases
    (memory_version N E * memory_version N E)%type code reps) as Herase.
  destruct (audit_trie_get code reps) as [result calls].
  cbn [fst snd audit_phi_closure_source_work audit_map_source_work] in Htrace, Herase |- *.
  rewrite Henc; cbn [fst snd].
  unfold Map.code_get; rewrite <- Herase.
  destruct result as [[key value]|]; cbn; lia.
Qed.

(** The recorded query work equals the direct account on every lookup branch. *)
Theorem audit_phi_operand_query_source_adequate : audit_phi_operand_query_source_adequate_statement.
Proof.
  intros N E CN CV CE node_enc version_enc base node_work version_work base_work reps kept input.
  pose proof (audit_phi_query_probe_work N CN node_enc node_work (fst input) kept) as Hprobe.
  pose proof (audit_phi_query_optional_work (N * option E)%type N E CV CE version_enc base
    version_work base_work reps input) as Hbody.
  unfold audit_phi_output_operand_call, audit_phi_operand_query_direct_work.
  destruct (audit_finset_mem node_enc (fst input) kept) as [retained probe] eqn:Hmem.
  cbn in Hprobe.
  assert (Hretained : retained = audit_phi_operand_code_mem (fst (node_enc (fst input))) kept).
  { unfold audit_finset_mem, audit_phi_operand_code_mem in Hmem.
    destruct (node_enc (fst input)) as [code events] eqn:Henc.
    pose proof (audit_map_code_get_erases N unit code kept) as Herase.
    destruct (audit_map_code_get code kept) as [found calls].
    cbn [fst snd] in Herase, Hmem |- *; inversion Hmem; subst retained.
    unfold audit_phi_operand_code_mem; now rewrite <- Herase. }
  rewrite <- Hretained in Hprobe |- *.
  destruct retained.
  - destruct (audit_phi_output_optional_call version_enc base reps input) as [result calls].
    cbn [snd audit_phi_operand_query_source_work] in Hbody |- *.
    unfold audit_phi_operand_guard_frames; cbn [audit_work List.length]. lia.
  - cbn [snd audit_phi_operand_query_source_work].
    unfold audit_phi_operand_guard_frames; cbn [audit_work List.length]. lia.
Qed.

(** Actual callback budgets and trie widths bound the optional-body work. *)
Lemma audit_phi_query_optional_bound : audit_phi_closure_whole_input_bound_statement.
Proof.
  intros I N E CV CE enc base version_work base_work version_budget base_budget reps input
    Hversion Hbase.
  pose proof (Hbase input) as Hcall.
  unfold audit_phi_output_optional_call, audit_phi_closure_input_budget.
  destruct (base input) as [found body].
  destruct found as [v|].
  - pose proof (audit_map_get_source_work_bound (memory_version N E) (memory_version N E)
      CV enc version_work v reps) as Hmap.
    pose proof (Hversion v) as Henc.
    destruct (audit_map_get enc v reps) as [result calls].
    cbn [snd audit_phi_closure_source_work] in *.
    unfold audit_phi_get_input_budget; cbn [fst]; lia.
  - cbn [snd audit_phi_closure_source_work] in *; lia.
Qed.

(** Input budgets cover malformed sets and maps without extra client premises. *)
Theorem audit_phi_operand_query_whole_input_bound :
    audit_phi_operand_query_whole_input_bound_statement.
Proof.
  intros N E CN CV CE node_enc version_enc base node_work version_work base_work
    node_budget version_budget base_budget reps kept input Hnode Hversion Hbase.
  pose proof (audit_phi_operand_query_source_adequate N E CN CV CE node_enc version_enc base
    node_work version_work base_work reps kept input) as Hwork.
  pose proof (audit_phi_query_optional_bound (N * option E)%type N E CV CE version_enc base
    version_work base_work version_budget base_budget reps input Hversion Hbase) as Hbody.
  pose proof (audit_phi_query_optional_work (N * option E)%type N E CV CE version_enc base
    version_work base_work reps input) as Hbodyeq.
  pose proof (audit_trie_get_source_work_bound (N * unit)%type (fst (node_enc (fst input))) kept)
    as Htrie.
  pose proof (Hnode (fst input)) as Henc.
  unfold audit_phi_operand_query_direct_work in Hwork.
  unfold audit_phi_operand_query_input_budget.
  rewrite Hwork.
  destruct (audit_phi_operand_code_mem (fst (node_enc (fst input))) kept); lia.
Qed.

(** One captured set bounds the sum of all queries without rebuilding it. *)
Theorem audit_phi_operand_saved_queries_bound : audit_phi_operand_saved_queries_bound_statement.
Proof.
  intros N E CN CV CE node_enc version_enc base node_work version_work base_work
    node_budget version_budget base_budget reps captured Hnode Hversion Hbase.
  cbn zeta; intro inputs.
  induction inputs as [|input rest IH].
  - reflexivity.
  - cbn [fold_right audit_phi_operand_saved_query].
    pose proof (audit_phi_operand_query_whole_input_bound N E CN CV CE node_enc version_enc base
      node_work version_work base_work node_budget version_budget base_budget reps captured input
      Hnode Hversion Hbase) as Hquery.
    unfold audit_phi_operand_saved_query in *; lia.
Qed.

(** * Callback provenance *)

(** Concrete version encoding records only the node or edge callback it actually executes. *)
Lemma audit_phi_query_version_callbacks N E CN CE
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    node_work edge_work node_source edge_source node_budget edge_budget v :
  audit_external_callback_adapter node_enc node_work node_source node_budget ->
  audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
  Forall (audit_phi_operand_version_sources node_work edge_work node_source edge_source)
    (snd (audit_memory_version_encode node_enc edge_enc v)).
Proof.
  intros Hnode Hedge.
  destruct v as [|node|edge index].
  - cbn [audit_memory_version_encode]. repeat constructor.
  - cbn [audit_memory_version_encode].
    destruct (node_enc node) as [code body] eqn:Hcall.
    cbn [snd]. constructor; [|constructor].
    cbn [audit_phi_operand_version_sources].
    eapply audit_external_callback_source; eassumption.
  - cbn [audit_memory_version_encode audit_pair_encode].
    destruct (edge_enc edge) as [ecode ebody] eqn:Hedgecall.
    destruct (audit_nat_encode index) as [ncode nbody].
    destruct (audit_emit_code ncode []) as [bits nframes].
    destruct (audit_emit_code ecode bits) as [stream eframes].
    destruct (audit_stream_positive stream) as [code frames].
    cbn [snd]. constructor; [|constructor].
    cbn [audit_phi_operand_version_sources].
    constructor.
    + eapply audit_external_callback_source; eassumption.
    + constructor; [exact I|].
      apply Forall_forall; intros item Hin.
      apply in_map_iff in Hin; destruct Hin as [frame [Heq Hin]]; subst item.
      exact I.
Qed.

(** Each callback event in the guarded query witnesses its actual source call. *)
Lemma audit_phi_query_callbacks N E CN CE B
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (base : (N * option E) -> option (memory_version N E) * list B)
    node_work edge_work base_work node_source edge_source base_source
    node_budget edge_budget base_budget reps kept input :
  audit_external_callback_adapter node_enc node_work node_source node_budget ->
  audit_external_callback_adapter edge_enc edge_work edge_source edge_budget ->
  audit_external_callback_adapter base base_work base_source base_budget ->
  audit_phi_operand_query_callbacks node_work edge_work base_work node_source edge_source
    base_source (snd (audit_phi_output_operand_call node_enc
      (audit_memory_version_encode node_enc edge_enc) kept base reps input)).
Proof.
  intros Hnode Hedge Hbase.
  unfold audit_phi_output_operand_call, audit_finset_mem.
  destruct (node_enc (fst input)) as [code body] eqn:Hnodecall.
  destruct (audit_map_code_get code kept) as [found probe].
  destruct found as [present|]; cbn [snd audit_phi_operand_query_callbacks].
  - unfold audit_phi_output_optional_call.
    destruct (base input) as [value calls] eqn:Hbasecall.
    destruct value as [v|].
    + unfold audit_map_get.
      destruct (audit_memory_version_encode node_enc edge_enc v) as [vcode vbody]
        eqn:Hversion.
      destruct (audit_map_code_get vcode reps) as [representative read].
      cbn [snd audit_phi_operand_query_callbacks].
      constructor.
      * constructor; [|constructor].
        eapply audit_external_callback_source; eassumption.
      * constructor; [|constructor]. constructor.
        -- eapply audit_external_callback_source; eassumption.
        -- constructor.
           ++ constructor; [|constructor].
              pose proof (audit_phi_query_version_callbacks N E CN CE node_enc edge_enc
                node_work edge_work node_source edge_source node_budget edge_budget v Hnode Hedge)
                as Hcallbacks.
              rewrite Hversion in Hcallbacks; exact Hcallbacks.
           ++ constructor.
    + cbn [snd audit_phi_operand_query_callbacks].
      constructor.
      * constructor; [|constructor].
        eapply audit_external_callback_source; eassumption.
      * constructor; [|constructor]. constructor; [|constructor].
        eapply audit_external_callback_source; eassumption.
  - constructor.
    + constructor; [|constructor].
      eapply audit_external_callback_source; eassumption.
    + constructor; [exact I|constructor].
Qed.

(** Genuine adapters justify the executed callbacks and the same query's source-work bound. *)
Theorem audit_phi_operand_query_adapted_source : audit_phi_operand_query_adapted_source_statement.
Proof.
  intros N E CN CE B node_enc edge_enc base node_work edge_work base_work
    node_budget edge_budget base_budget node_source edge_source base_source reps kept input
    Hnode Hedge Hbase.
  cbn zeta.
  repeat split.
  - apply audit_phi_query_callbacks with (node_budget := node_budget) (edge_budget := edge_budget)
      (base_budget := base_budget); assumption.
  - apply audit_phi_operand_query_source_adequate.
  - apply audit_phi_operand_query_whole_input_bound.
    + intro n; destruct (node_enc n) as [code body] eqn:Hcall; cbn.
      eapply audit_external_callback_input_bound; eassumption.
    + intro v; apply audit_memory_version_input_bound.
      * intro n; destruct (node_enc n) as [code body] eqn:Hcall; cbn.
        eapply audit_external_callback_input_bound; eassumption.
      * intro e; destruct (edge_enc e) as [code body] eqn:Hcall; cbn.
        eapply audit_external_callback_input_bound; eassumption.
    + intro arg; destruct (base arg) as [result body] eqn:Hcall; cbn.
      eapply audit_external_callback_input_bound; eassumption.
Qed.
