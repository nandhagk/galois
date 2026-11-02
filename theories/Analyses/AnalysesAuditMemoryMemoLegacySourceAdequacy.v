(** * Adequacy of memo-threaded legacy source execution

    Actual query receipts preserve the exact persistent memo and the materialized load index.
    For example, a second load receives the first load's returned memo rather than the old cache.
    Builds on: complete legacy phases, public memo source adequacy and indexed map adequacy. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCallback CollectionsAuditMap CollectionsAuditMapAdequacy
  CollectionsAuditFinSet CollectionsAuditFinSetAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditBase
  GraphAuditBaseAdequacy GraphAuditDfs.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects ViewsGraph.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryEffects AnalysesAuditMemoryEffectsAdequacy
  AnalysesAuditMemoryLegacyGuard AnalysesAuditMemoryLegacyGuardAdequacy
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryMemo
  AnalysesAuditMemoryMemoWhole AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteBound
  AnalysesAuditMemoryMemoPublicSource AnalysesAuditMemoryMemoPublicSourceAdequacy
  AnalysesAuditMemoryMemoLegacyPlain AnalysesAuditMemoryMemoLegacySource
  AnalysesAuditMemoryIndex AnalysesAuditMemoryTable AnalysesAuditMemoryTableAdequacy
  AnalysesAuditMemoryLegacyCfg AnalysesAuditMemoryLegacyCfgAdequacy
  AnalysesAuditMemoryLegacySliceFull AnalysesAuditMemoryLegacySliceFullAdequacy
  AnalysesAuditMemoryLegacyChecker AnalysesAuditMemoryLegacyCheckerAdequacy
  AnalysesAuditMemoryLegacySuccessor AnalysesAuditMemoryLegacySuccessorAdequacy
  AnalysesAuditMemoryLegacyNoClobber AnalysesAuditMemoryLegacyNoClobberAdequacy
  AnalysesAuditMemoryLegacyProposalSource AnalysesAuditMemoryLegacyProposalSourceAdequacy
  AnalysesAuditMemoryLegacySetupSource AnalysesAuditMemoryLegacySetupSourceAdequacy
  AnalysesAuditMemoryLegacyProjectionSource AnalysesAuditMemoryLegacyProjectionSourceAdequacy
  AnalysesAuditMemoryLegacyInputBudget AnalysesAuditMemoryLegacyInputBudgetAdequacy
  AnalysesAuditMemoryGraphCallbacks.
Import List.ListNotations.

(** Returned load lookup pays its concrete encoder and one trie read, including missing keys. *)
Theorem audit_memo_legacy_lookup_source_bound : audit_memo_legacy_lookup_source_bound_statement.
Proof.
  intros F N CN node_enc node_work node_budget node_source pairs node Hadapter.
  pose proof (audit_map_get_source_work_bound N (option (mem_node F N)) CN node_enc node_work
    node pairs) as Hlookup.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hadapter node) as Hnode.
  unfold audit_memo_legacy_lookup_counted.
  destruct (audit_map_get node_enc node pairs) as [found body]; cbn [snd] in Hlookup |- *.
  lia.
Qed.

(** A materialized lookup returns precisely the plain option stored at that node. *)
Lemma audit_memo_legacy_lookup_erases F N CN (EN : encoding N)
    (node_enc : N -> positive * list CN) pairs node :
  fst (node_enc node) = encode EN node ->
  fst (@audit_memo_legacy_lookup_counted F N CN node_enc pairs node) =
    match Map.get EN node pairs with
    | Some candidate => candidate
    | None => None
    end.
Proof.
  intro Hnode.
  pose proof (audit_map_get_erases N (option (mem_node F N)) CN node_enc EN node pairs Hnode)
    as Hget.
  unfold audit_memo_legacy_lookup_counted.
  destruct (audit_map_get node_enc node pairs) as [found body]; cbn [fst] in Hget |- *.
  rewrite <- Hget; reflexivity.
Qed.

Section OneErasure.
  Context {F N E T CN CE CF SE XE OO TE OE BE LE RE WE : Type}.
  Context (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OO) (target : E -> N * list TE).
  Context (operand : N -> option E -> option (memory_version N E) * list OE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E).
  Hypothesis Hnode : forall n, fst (node_enc n) = encode EN n.
  Hypothesis Hedge : forall e, fst (edge_enc e) = encode EE e.
  Hypothesis Hfunction : forall f, fst (function_enc f) = encode EF f.
  Hypothesis Hsite : forall t, fst (site_enc t) = encode ET t.
  Hypothesis Hsource : forall e, fst (source e) = Graph.source g e.
  Hypothesis Hoperand : forall n key, fst (operand n key) = memory_operand mg n key.
  Hypothesis Hbefore : forall e i, fst (before e i) = memory_before mg e i.

  (** The receipt stores exactly the public query value and its returned persistent cache. *)
  Lemma audit_memo_legacy_clobber_erases state scope start query_fuel :
    let '(result, receipt) := audit_memo_legacy_clobber_counted EN node_enc edge_enc site_enc
      operand before g effects mg state scope start query_fuel in
    (result, @MemoState N E T EN g effects mg (@memo_adjacency N E T EN g effects mg state)
      (@memo_effect_index N E T EN g effects mg state)
      (audit_memo_cache (audit_memo_legacy_execution receipt))) =
    audit_memory_memo_query EN EE ET g effects mg state scope start query_fuel.
  Proof.
    pose proof (audit_memory_memo_public_source_erases N E T CN CE SE OE BE EN EE ET node_enc
      edge_enc site_enc g effects mg state operand before scope start query_fuel Hnode Hedge Hsite
      Hoperand Hbefore) as Hquery.
    unfold audit_memo_legacy_clobber_counted.
    destruct (audit_memory_memo_public_source_counted node_enc edge_enc site_enc EN g effects mg
      state operand before scope start query_fuel) as [encoded run].
    cbn [snd] in Hquery; destruct Hquery as [Hvalue Hcache].
    cbn [audit_memo_legacy_execution].
    rewrite Hvalue, Hcache.
    unfold audit_memory_memo_query; reflexivity.
  Qed.

  (** Prefix branches recover the exact request and extract the first actual query receipt. *)
  Lemma audit_memo_legacy_occurrence_erases
      (setup : @audit_legacy_setup_run N E T CN CE OO TE unit EN) state (function : F)
        query_fuel node :
    let '(proposal, body) := audit_legacy_occurrence_source_with node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads
      (audit_memo_legacy_clobber_counted EN node_enc edge_enc site_enc operand before g effects mg
        state) function query_fuel node in
    (proposal, audit_memo_legacy_receipt_after EN g effects mg state body) =
    match audit_memo_legacy_request EN EE g mg (audit_legacy_setup_reached setup)
        (audit_legacy_setup_listed setup) (@memo_effect_index N E T EN g effects mg state)
        (fun n => fst (reads n)) (fun n => fst (load n)) node with
    | None => (None, state)
    | Some (scope, start) =>
        let '(result, next) := audit_memory_memo_query EN EE ET g effects mg state scope start
          query_fuel in
        (legacy_clobber_proposal function g result, next)
    end.
  Proof.
    unfold audit_legacy_occurrence_source_with, audit_memo_legacy_request.
    destruct (load node) as [occurrence load_body]; cbn [fst].
    destruct occurrence as [[edge index]|]; [|reflexivity].
    pose proof (audit_legacy_guard_erases N E CN CE XE EN EE g node_enc edge_enc source
      (audit_legacy_setup_reached setup) (audit_legacy_setup_listed setup) edge node Hnode Hedge
      Hsource) as Hguard.
    destruct (audit_legacy_guard node_enc edge_enc source (audit_legacy_setup_reached setup)
      (audit_legacy_setup_listed setup) edge node) as [guard guard_body]; cbn [fst] in Hguard.
    rewrite <- Hguard; destruct guard; [|reflexivity].
    pose proof (audit_memory_effect_get_erases E T CE edge_enc EE
      (@memo_effect_index N E T EN g effects mg state) edge index (Hedge edge)) as Heffect.
    destruct (audit_memory_effect_get edge_enc (@memo_effect_index N E T EN g effects mg state)
      edge index) as [effect effect_body]; cbn [fst] in Heffect; rewrite <- Heffect.
    destruct effect as [actual|]; [|destruct (memory_before mg edge index); reflexivity].
    pose proof (Hbefore edge index) as Hinput.
    destruct (before edge index) as [input before_body]; cbn [fst] in Hinput; rewrite <- Hinput.
    destruct input as [start|]; [|reflexivity].
    destruct (memory_effect_has_read actual); [|reflexivity].
    destruct (reads node) as [footprints read_body]; cbn [fst].
    pose proof (audit_memo_legacy_clobber_erases state (MemoryRegions footprints) start query_fuel)
      as Hquery.
    destruct (audit_memo_legacy_clobber_counted EN node_enc edge_enc site_enc operand before g
      effects mg state (MemoryRegions footprints) start query_fuel) as [result receipt].
    pose proof (audit_legacy_finish_proposal_erases F N E T CN CE XE BE LE RE
      (audit_memo_legacy_receipt N E T CN CE SE OE BE) source g function
      result Hsource) as Hfinish.
    destruct (@audit_legacy_finish_proposal F N E T CN CE XE BE LE RE
      (audit_memo_legacy_receipt N E T CN CE SE OE BE) source function result)
      as [answer finish_body]; cbn [fst] in Hfinish.
    rewrite <- Hquery; cbn [app audit_memo_legacy_receipt_after].
    rewrite Hfinish; reflexivity.
  Qed.

  (** One counted load returns the same retained candidate and full memo state as the plain load. *)
  Lemma audit_memo_legacy_one_erases
      (setup : @audit_legacy_setup_run N E T CN CE OO TE unit EN) state (function : F)
        query_fuel node :
    let '(candidate, next, _) := audit_memo_legacy_one_counted EN EF ET node_enc edge_enc
      function_enc
      site_enc source operand before load reads writes g effects mg setup state function query_fuel
      node in
    (candidate, next) = audit_memo_legacy_one EN EE EF ET function g effects mg state
      (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup)
      (audit_legacy_setup_reached setup) (audit_legacy_setup_listed setup)
      (fun n => fst (writes n)) (fun n => fst (reads n)) (fun n => fst (load n)) query_fuel node.
  Proof.
    pose proof (audit_memo_legacy_occurrence_erases setup state function query_fuel node)
      as Hproposal.
    unfold audit_memo_legacy_one_counted, audit_memo_legacy_one.
    destruct (audit_legacy_occurrence_source_with node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads
      (audit_memo_legacy_clobber_counted EN node_enc edge_enc site_enc operand before g effects mg
        state) function query_fuel node) as [proposal proposal_body].
    destruct (audit_memo_legacy_request EN EE g mg (audit_legacy_setup_reached setup)
      (audit_legacy_setup_listed setup) (@memo_effect_index N E T EN g effects mg state)
      (fun n => fst (reads n)) (fun n => fst (load n)) node) as [[scope start]|].
    - destruct (audit_memory_memo_query EN EE ET g effects mg state scope start query_fuel)
        as [result next].
      injection Hproposal as Hcandidate Hnext; rewrite Hnext, Hcandidate.
      unfold legacy_retain.
      destruct (legacy_clobber_proposal function g result) as [candidate|]; [|reflexivity].
      pose proof (audit_legacy_pair_check_erases F N (N * N)%type T CN CF SE
        (audit_legacy_successor_event N (N * N) CN) RE WE EN EF ET node_enc function_enc site_enc
        (audit_legacy_successors_counted EN node_enc (audit_legacy_setup_cfg setup)
          (audit_legacy_setup_prepared setup)) reads writes (fun n => fst (reads n))
        (fun n => fst (writes n)) (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup)
        (audit_legacy_setup_reached setup) node candidate function Hnode Hfunction Hsite
        (fun n => audit_legacy_successors_erases N (N * N)%type CN EN node_enc
          (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup) n Hnode)
        (fun _ => eq_refl) (fun _ => eq_refl)) as Hretain.
      destruct (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
        (audit_legacy_successors_counted EN node_enc (audit_legacy_setup_cfg setup)
          (audit_legacy_setup_prepared setup)) reads writes (audit_legacy_setup_cfg setup)
        (audit_legacy_setup_prepared setup) (audit_legacy_setup_reached setup) node candidate
          function)
        as [accepted body]; cbn [fst] in Hretain.
      rewrite Hretain; reflexivity.
    - injection Hproposal as Hcandidate Hnext; rewrite Hnext, Hcandidate; reflexivity.
  Qed.

  (** Sequential counted stores preserve the entire plain index and the returned memo endpoint. *)
  Lemma audit_memo_legacy_nodes_erases
      (setup : @audit_legacy_setup_run N E T CN CE OO TE unit EN) (function : F) query_fuel nodes
      state pairs :
    let '(final, next, _) := audit_memo_legacy_nodes_counted EN EF ET node_enc edge_enc function_enc
      site_enc source operand before load reads writes g effects mg function query_fuel setup nodes
      state pairs in
    (final, next) = audit_memo_legacy_nodes EN EE EF ET function g effects mg
      (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup)
      (audit_legacy_setup_reached setup) (audit_legacy_setup_listed setup)
      (fun n => fst (writes n)) (fun n => fst (reads n)) (fun n => fst (load n)) query_fuel nodes
      state pairs.
  Proof.
    revert state pairs; induction nodes as [|node rest IH]; intros state pairs; [reflexivity|].
    cbn [audit_memo_legacy_nodes_counted audit_memo_legacy_nodes].
    pose proof (audit_memo_legacy_one_erases setup state function query_fuel node) as Hone.
    destruct (audit_memo_legacy_one_counted EN EF ET node_enc edge_enc function_enc site_enc source
      operand before load reads writes g effects mg setup state function query_fuel node)
      as [[candidate next] body].
    rewrite <- Hone.
    pose proof (audit_map_set_erases N (option (mem_node F N)) CN node_enc EN node candidate pairs
      (Hnode node)) as Hstore.
    destruct (audit_map_set node_enc node candidate pairs) as [updated store_body]; cbn [fst] in
      Hstore.
    rewrite <- Hstore; specialize (IH next updated).
    destruct (audit_memo_legacy_nodes_counted EN EF ET node_enc edge_enc function_enc site_enc
      source
      operand before load reads writes g effects mg function query_fuel setup rest next updated)
      as [[final final_state] tail]; exact IH.
  Qed.
End OneErasure.

(** Memo setup shares the same normalized graph and listed edges without rebuilding its table. *)
Lemma audit_memo_legacy_setup_erases N E T CN CE OO TE (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OO) (target : E -> N * list TE) (g : Graph.t N E)
    (table : Map.t E (Map.t nat (memory_effect T))) :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall e, fst (edge_enc e) = encode EE e) ->
  (forall n, fst (out n) = Graph.out g n) ->
  (forall e, fst (target e) = Graph.target g e) ->
  let setup := audit_memo_legacy_setup_counted EN node_enc edge_enc out target g table in
  audit_legacy_setup_cfg setup = legacy_cfg EN g /\
  audit_legacy_setup_reached setup = legacy_reached (prepare EN (legacy_cfg EN g))
    (Graph.entries g) /\
  audit_legacy_setup_listed setup = FinSet.of_list EE (edges_of g) /\
  out_index (audit_legacy_setup_prepared setup) = out_index (prepare EN (legacy_cfg EN g)) /\
  in_index (audit_legacy_setup_prepared setup) = in_index (prepare EN (legacy_cfg EN g)) /\
  fuel (audit_legacy_setup_prepared setup) = fuel (prepare EN (legacy_cfg EN g)).
Proof.
  intros Hnode Hedge Hout Htarget.
  pose proof (audit_legacy_projection_setup_erases N E T CN CE OO TE unit EN EE node_enc edge_enc
    out target (fun _ => (@nil (memory_effect T), @nil unit)) g Hnode Hedge Hout Htarget) as Hsetup.
  unfold audit_memo_legacy_setup_counted, audit_legacy_projection_setup in *.
  destruct (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) as [rows ce].
  set (cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd) in *.
  destruct (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    as [prep pe].
  destruct (audit_legacy_reached_counted EN node_enc cfg prep (Graph.entries cfg)) as [reached re].
  destruct (audit_memory_edges out (Graph.nodes g)) as [edges ee].
  destruct (audit_finset_of_list edge_enc edges) as [listed le].
  destruct (audit_memory_effect_table edge_enc out (fun _ => (@nil (memory_effect T), @nil unit))
    (Graph.nodes g)) as [new_table te] in Hsetup.
  cbn [audit_legacy_setup_cfg audit_legacy_setup_prepared audit_legacy_setup_reached
    audit_legacy_setup_listed audit_legacy_setup_table] in Hsetup |- *.
  tauto.
Qed.

(** Counted materialization preserves the public memo endpoint, every load answer and acceptance. *)
Theorem audit_memory_memo_legacy_source_erases : audit_memory_memo_legacy_source_erases_statement.
Proof.
  intros F N E T CN CE CF SE XE OO TE OE BE LE RE WE EN EE EF ET node_enc edge_enc function_enc
    site_enc source out target operand before load reads writes g effects mg function query_fuel
    state Hnode Hedge Hfunction Hsite Hsource Hout Htarget Hoperand Hbefore.
  pose proof (audit_memo_legacy_setup_erases N E T CN CE OO TE EN EE node_enc edge_enc out target g
    (@memo_effect_index N E T EN g effects mg state) Hnode Hedge Hout Htarget) as Hsetup.
  pose proof (@audit_memo_legacy_nodes_erases F N E T CN CE CF SE XE OO TE OE BE LE RE WE
    EN EE EF ET node_enc edge_enc function_enc site_enc source operand before load reads writes
    g effects mg Hnode Hedge Hfunction Hsite Hsource Hoperand Hbefore
    (audit_memo_legacy_setup_counted EN node_enc edge_enc out target g
      (@memo_effect_index N E T EN g effects mg state)) function query_fuel (Graph.nodes g) state
    Map.empty) as Hnodes.
  unfold audit_memory_memo_legacy_source_erases_at, audit_memory_memo_legacy_project_counted.
  remember (audit_memo_legacy_setup_counted EN node_enc edge_enc out target g
    (@memo_effect_index N E T EN g effects mg state))
    as setup eqn:Hsetup_call.
  destruct setup as [cfg prep reached listed table ce pe re ee le te].
  cbn [audit_legacy_setup_cfg audit_legacy_setup_prepared audit_legacy_setup_reached
    audit_legacy_setup_listed] in Hsetup, Hnodes |- *.
  destruct Hsetup as [Hcfg [Hreached [Hlisted [Houtindex [Hinindex Hfuel]]]]].
  subst cfg reached listed.
  assert (Hprep : prep = prepare EN (legacy_cfg EN g)).
  { apply audit_legacy_prepared_equal; assumption. }
  subst prep.
  destruct (audit_memo_legacy_nodes_counted EN EF ET node_enc edge_enc function_enc site_enc source
    operand before load reads writes g effects mg function query_fuel
    (@AuditLegacySetupRun N E T CN CE OO TE unit EN (legacy_cfg EN g)
      (prepare EN (legacy_cfg EN g))
      (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
      (FinSet.of_list EE (edges_of g)) table ce pe re ee le te)
    (Graph.nodes g) state Map.empty) as [[pairs next] body] eqn:Hcounted.
  unfold audit_memory_memo_legacy_project.
  change (Graph.entries (legacy_cfg EN g)) with (Graph.entries g).
  rewrite <- Hnodes; cbn [fst snd].
  split; [reflexivity|split].
  - intro node; apply audit_memo_legacy_lookup_erases; apply Hnode.
  - unfold audit_memory_memo_legacy_check_counted, audit_memory_memo_legacy_project_counted.
    rewrite <- Hsetup_call.
    rewrite Hcounted.
    pose proof (audit_legacy_no_clobber_erases F N E T CN CF SE OO TE RE WE
      (CollectionsAuditMap.audit_map_event N (option (mem_node F N)) CN) EN EF ET node_enc
      function_enc site_enc out target reads writes function g
      (MemorySSA (fun node => match Map.get EN node pairs with
        | Some candidate => candidate
        | None => None
        end))
      (audit_memo_legacy_lookup_counted node_enc pairs) Hnode Hfunction Hsite Hout Htarget
      (fun n => audit_memo_legacy_lookup_erases F N CN EN node_enc pairs n (Hnode n))) as Hcheck.
    destruct (audit_legacy_no_clobber_counted EN EF ET node_enc function_enc site_enc out target
      reads writes function g (audit_memo_legacy_lookup_counted node_enc pairs)) as [accepted
        checks].
    exact Hcheck.
Qed.

Section OneBudget.
  Context {F N E T CN CE CF SE XE OO TE OE BE LE RE WE : Type}.
  Context (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE).
  Context (operand : N -> option E -> option (memory_version N E) * list OE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (node_work : list CN -> nat) (edge_work : list CE -> nat).
  Context (function_work : list CF -> nat) (site_work : list SE -> nat).
  Context (source_work : list XE -> nat) (operand_work : list OE -> nat).
  Context (before_work : list BE -> nat) (load_work : list LE -> nat).
  Context (read_work : list RE -> nat) (write_work : list WE -> nat).
  Context (node_budget load_budget read_budget write_budget : N -> nat).
  Context (edge_budget source_budget : E -> nat) (function_budget : F -> nat) (site_budget : T
    -> nat).
  Context (operand_budget : N -> option E -> nat) (before_budget : E -> nat -> nat).
  Context (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E).
  Context (function : F) (query_fuel : positive).
  Hypothesis Hnode : forall n, fst (node_enc n) = encode EN n.
  Hypothesis Hedge : forall e, fst (edge_enc e) = encode EE e.
  Hypothesis Hfunction : forall f, fst (function_enc f) = encode EF f.
  Hypothesis Hsite : forall t, fst (site_enc t) = encode ET t.
  Hypothesis Hsource : forall e, fst (source e) = Graph.source g e.
  Hypothesis Hoperand : forall n key, fst (operand n key) = memory_operand mg n key.
  Hypothesis Hbefore : forall e i, fst (before e i) = memory_before mg e i.
  Hypothesis Hnw : forall n, node_work (snd (node_enc n)) <= node_budget n.
  Hypothesis Hew : forall e, edge_work (snd (edge_enc e)) <= edge_budget e.
  Hypothesis Hfw : forall f, function_work (snd (function_enc f)) <= function_budget f.
  Hypothesis Hsw : forall t, site_work (snd (site_enc t)) <= site_budget t.
  Hypothesis Hxw : forall e, source_work (snd (source e)) <= source_budget e.
  Hypothesis Hpw : forall n key, operand_work (snd (operand n key)) <= operand_budget n key.
  Hypothesis Hbw : forall e i, before_work (snd (before e i)) <= before_budget e i.
  Hypothesis Hlw : forall n, load_work (snd (load n)) <= load_budget n.
  Hypothesis Hrw : forall n, read_work (snd (reads n)) <= read_budget n.
  Hypothesis Hww : forall n, write_work (snd (writes n)) <= write_budget n.

  Let State := memo_state EN g effects mg.
  Let Setup := @audit_legacy_setup_run N E T CN CE OO TE unit EN.
  Let ReceiptWork := @audit_memo_legacy_receipt_work N E T CN CE SE OE BE
    node_work edge_work site_work operand_work before_work.
  Let Clobbers (state : State) := audit_memo_legacy_clobber_counted EN node_enc edge_enc site_enc
    operand before g effects mg state.
  Let Prefix := @audit_memo_legacy_prefix_input_budget F N E T CN CE XE OO TE BE LE RE EN node_enc
    edge_enc source before load reads node_budget load_budget read_budget edge_budget source_budget
    before_budget g effects mg function query_fuel.
  Let Finish := @audit_memo_legacy_finish_input_budget F N E T CN CE CF SE OO TE RE WE EN node_enc
    function_enc site_enc reads writes node_budget read_budget write_budget source_budget
    function_budget site_budget g function.
  Let OneBudget := @audit_memo_legacy_one_input_budget F N E T CN CE CF SE XE OO TE OE BE LE RE WE
    EN EE EF ET node_enc edge_enc function_enc site_enc source operand before load reads writes
    node_budget load_budget read_budget write_budget edge_budget source_budget function_budget
    site_budget operand_budget before_budget g effects mg function query_fuel.
  Let NodesBudget := @audit_memo_legacy_nodes_input_budget F N E T CN CE CF SE XE OO TE OE BE LE
    RE WE
    EN EE EF ET node_enc edge_enc function_enc site_enc source operand before load reads writes
    node_budget load_budget read_budget write_budget edge_budget source_budget function_budget
    site_budget operand_budget before_budget g effects mg function query_fuel.

  (** A real query receipt supplies the input recurrence with its identical cache endpoint. *)
  Lemma audit_memo_legacy_query_work_input (state : State) scope start :
    let '(result, receipt) := Clobbers state scope start query_fuel in
    exists next cost,
      audit_memo_legacy_query_input_budget EN node_enc edge_enc site_enc operand before node_budget
        edge_budget site_budget operand_budget before_budget g effects mg query_fuel state scope
        start result next cost /\
      ReceiptWork receipt <= cost /\
      (result, next) = audit_memory_memo_query EN EE ET g effects mg state scope start query_fuel.
  Proof.
    pose proof (audit_memory_memo_public_whole_input_bound N E T CN CE SE OE BE EN node_enc edge_enc
      site_enc g effects mg state operand before node_work edge_work site_work operand_work
      before_work node_budget edge_budget site_budget operand_budget before_budget scope start
      query_fuel Hnw Hew Hsw Hpw Hbw) as Hbound.
    pose proof (audit_memo_legacy_clobber_erases EN EE ET node_enc edge_enc site_enc operand before
      g effects mg Hnode Hedge Hsite Hoperand Hbefore state scope start query_fuel) as Herases.
    unfold Clobbers, audit_memo_legacy_clobber_counted in Herases |- *.
    unfold audit_memo_legacy_query_input_budget.
    destruct (audit_memory_memo_public_source_counted node_enc edge_enc site_enc EN g effects mg
      state operand before scope start query_fuel) as [encoded run] eqn:Hrun.
    destruct Hbound as [budget [Hbudget Hwork]].
    exists (@MemoState N E T EN g effects mg (@memo_adjacency N E T EN g effects mg state)
      (@memo_effect_index N E T EN g effects mg state) (audit_memo_cache run)).
    exists (4 + audit_memory_scope_input_budget site_enc site_budget scope +
      16 * S (Pos.size_nat query_fuel) * budget).
    split.
    - exists (audit_memo_cache run), (audit_memo_credit run), budget.
      split; [|split; reflexivity].
      unfold audit_memory_memo_public_source_counted, audit_memory_memo_query_counted in Hrun.
      destruct (audit_memory_scope_encode site_enc scope) as [code scope_body] eqn:Hscope.
      injection Hrun as Hencoded Hexecute; subst encoded run.
      exact Hbudget.
    - split; [exact Hwork|exact Herases].
  Qed.

  (** Separating the fixed prefix leaves only the actual query body and singleton source call. *)
  Lemma audit_memo_legacy_occurrence_budget_split (setup : Setup) (state : State) node :
    audit_legacy_occurrence_with_input_budget node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads (Clobbers state)
      node_budget load_budget read_budget edge_budget source_budget before_budget
      (fun scope start fuel => ReceiptWork (snd (Clobbers state scope start fuel)))
      function query_fuel node =
    Prefix setup state node +
    match audit_memo_legacy_request EN EE g mg (audit_legacy_setup_reached setup)
      (audit_legacy_setup_listed setup) (@memo_effect_index N E T EN g effects mg state)
      (fun n => fst (reads n)) (fun n => fst (load n)) node with
    | None => 0
    | Some (scope, start) =>
        ReceiptWork (snd (Clobbers state scope start query_fuel)) +
        match clobber_roots (fst (Clobbers state scope start query_fuel)) with
        | [MemoryDef edge _] => source_budget edge
        | _ => 0
        end
    end.
  Proof.
    unfold Prefix, audit_memo_legacy_prefix_input_budget,
      audit_legacy_occurrence_with_input_budget, audit_memo_legacy_request.
    destruct (fst (load node)) as [[edge index]|]; [|lia].
    rewrite (audit_legacy_guard_erases N E CN CE XE EN EE g node_enc edge_enc source
      (audit_legacy_setup_reached setup) (audit_legacy_setup_listed setup) edge node Hnode Hedge
      Hsource).
    destruct (Pos.eqb (encode EN (Graph.source g edge)) (encode EN node) &&
      FinSet.mem EN (Graph.source g edge) (audit_legacy_setup_reached setup) &&
      FinSet.mem EE edge (audit_legacy_setup_listed setup))%bool; [|lia].
    rewrite (audit_memory_effect_get_erases E T CE edge_enc EE
      (@memo_effect_index N E T EN g effects mg state) edge index (Hedge edge)).
    destruct (memory_walk_effect_get EE (@memo_effect_index N E T EN g effects mg state) edge index)
      as [actual|]; [|destruct (memory_before mg edge index); lia].
    rewrite Hbefore; destruct (memory_before mg edge index) as [start|]; [|lia].
    destruct (memory_effect_has_read actual); [|lia].
    cbn [fst clobber_roots]; lia.
  Qed.

  (** The actual counted node supplies its independent branch budget at identical endpoints. *)
  Lemma audit_memo_legacy_one_work_input (setup : Setup) (state : State) node :
    let '(candidate, next, body) := audit_memo_legacy_one_counted EN EF ET node_enc edge_enc
      function_enc site_enc source operand before load reads writes g effects mg setup state
      function query_fuel node in
    exists cost, OneBudget setup state node candidate next cost /\
      audit_memo_legacy_one_source_work EN node_work edge_work function_work site_work source_work
        operand_work before_work load_work read_work write_work body <= cost.
  Proof.
    pose proof (audit_legacy_occurrence_with_input_bound F N E T CN CE XE BE LE RE
      (audit_memo_legacy_receipt N E T CN CE SE OE BE) node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads (Clobbers state)
      node_work edge_work source_work before_work load_work read_work ReceiptWork node_budget
      load_budget read_budget edge_budget source_budget before_budget
      (fun scope start fuel => ReceiptWork (snd (Clobbers state scope start fuel)))
      function query_fuel node Hnw Hew Hxw Hbw Hlw Hrw (fun _ _ _ => Nat.le_refl _)) as Hoccurrence.
    rewrite audit_memo_legacy_occurrence_budget_split in Hoccurrence.
    pose proof (audit_memo_legacy_occurrence_erases EN EE ET node_enc edge_enc site_enc source
      operand
      before load reads g effects mg Hnode Hedge Hsite Hsource Hoperand Hbefore setup state
      function query_fuel node) as Herases.
    pose proof (audit_memo_legacy_one_erases EN EE EF ET node_enc edge_enc function_enc site_enc
      source operand before load reads writes g effects mg Hnode Hedge Hfunction Hsite Hsource
      Hoperand Hbefore setup state function query_fuel node) as Honeerase.
    unfold audit_memo_legacy_one_counted, audit_memo_legacy_one in Honeerase.
    fold (Clobbers state) in Honeerase.
    unfold audit_memo_legacy_one_counted; fold (Clobbers state).
    fold (Clobbers state) in Herases.
    destruct (audit_legacy_occurrence_source_with node_enc edge_enc source
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (@memo_effect_index N E T EN g effects mg state) before load reads (Clobbers state)
      function query_fuel node) as [proposal proposal_body].
    cbn [snd] in Hoccurrence.
    destruct (audit_memo_legacy_request EN EE g mg (audit_legacy_setup_reached setup)
      (audit_legacy_setup_listed setup) (@memo_effect_index N E T EN g effects mg state)
      (fun n => fst (reads n)) (fun n => fst (load n)) node) as [[scope start]|] eqn:Hrequest.
    - pose proof (audit_memo_legacy_query_work_input state scope start) as Hquery.
      destruct (Clobbers state scope start query_fuel) as [result receipt].
      destruct Hquery as [next [query_cost [Hquerybudget [Hquerywork Hqueryerase]]]].
      rewrite <- Hqueryerase in Herases, Honeerase.
      injection Herases as Hproposal Hnext; rewrite Hproposal, Hnext.
      rewrite Hproposal, Hnext in Honeerase; cbn [fst snd] in Honeerase.
      assert (Honebudget : OneBudget setup state node
        (legacy_retain EN EF ET function (audit_legacy_setup_cfg setup)
          (audit_legacy_setup_prepared setup) (audit_legacy_setup_reached setup)
          (fun n => fst (writes n)) (fun n => fst (reads n)) node
          (legacy_clobber_proposal function g result)) next
        (5 + Prefix setup state node + query_cost + Finish setup node result)).
      { unfold OneBudget, Prefix, Finish.
        eapply AuditMemoLegacyBudgetQuery; eassumption. }
      destruct (legacy_clobber_proposal function g result) as [candidate|] eqn:Hproposal_result.
      + pose proof (audit_legacy_pair_input_bound F N (N * N)%type T CN CF SE
            (audit_legacy_successor_event N (N * N) CN) RE WE EN EF ET node_enc function_enc
              site_enc
            (audit_legacy_successors_counted EN node_enc (audit_legacy_setup_cfg setup)
              (audit_legacy_setup_prepared setup)) reads writes node_work function_work site_work
            (audit_legacy_successor_source_work node_work) read_work write_work node_budget
            function_budget site_budget
            (audit_legacy_successors_input_budget node_enc node_budget
              (out_index (audit_legacy_setup_prepared setup))) read_budget write_budget
            (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup)
            (audit_legacy_setup_reached setup) node candidate function Hnode Hnw Hfw Hsw
            (fun n => audit_legacy_successors_input_bound N (N * N)%type CN EN node_enc node_work
              node_budget (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup) n
              (Hnw n)) Hrw Hww) as Hretain.
          destruct (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
            (audit_legacy_successors_counted EN node_enc (audit_legacy_setup_cfg setup)
              (audit_legacy_setup_prepared setup)) reads writes (audit_legacy_setup_cfg setup)
            (audit_legacy_setup_prepared setup) (audit_legacy_setup_reached setup) node candidate
            function) as [accepted retain_body]; cbn [snd] in Hretain |- *.
          exists (5 + Prefix setup state node + query_cost + Finish setup node result).
          split.
        * cbn [fst snd] in Honeerase.
             pose proof (f_equal fst Honeerase) as Hactual; cbn [fst] in Hactual.
             rewrite Hactual.
             exact Honebudget.
        * unfold Finish, audit_memo_legacy_finish_input_budget; rewrite Hproposal_result.
             cbn [audit_memo_legacy_one_source_work].
          cbn [fst snd] in Hoccurrence; unfold ReceiptWork in Hoccurrence, Hquerywork; lia.
      + exists (5 + Prefix setup state node + query_cost + Finish setup node result).
          split.
        * cbn [fst snd] in Honeerase.
             pose proof (f_equal fst Honeerase) as Hactual; cbn [fst] in Hactual.
             rewrite Hactual.
             exact Honebudget.
        * unfold Finish, audit_memo_legacy_finish_input_budget; rewrite Hproposal_result.
             cbn [snd audit_memo_legacy_one_source_work].
          cbn [fst snd] in Hoccurrence; unfold ReceiptWork in Hoccurrence, Hquerywork; lia.
    - injection Herases as Hproposal Hnext; rewrite Hproposal, Hnext.
      exists (5 + Prefix setup state node); split.
      + unfold OneBudget, Prefix; apply AuditMemoLegacyBudgetNoQuery; exact Hrequest.
      + cbn [snd audit_memo_legacy_one_source_work]; unfold ReceiptWork in Hoccurrence.
        lia.
  Qed.

  (** Sequential stores sum the node witnesses and charge the actual encoded map update. *)
  Lemma audit_memo_legacy_nodes_work_input (setup : Setup) nodes (state : State) pairs :
    let '(final, next, body) := audit_memo_legacy_nodes_counted EN EF ET node_enc edge_enc
      function_enc
      site_enc source operand before load reads writes g effects mg function query_fuel setup nodes
      state pairs in
    exists cost, NodesBudget setup nodes state pairs final next cost /\
      audit_memo_legacy_nodes_source_work EN node_work edge_work function_work site_work source_work
        operand_work before_work load_work read_work write_work body <= cost.
  Proof.
    revert state pairs; induction nodes as [|node rest IH]; intros state pairs.
    - exists 2; split; [constructor|reflexivity].
    - cbn [audit_memo_legacy_nodes_counted].
      pose proof (audit_memo_legacy_one_work_input setup state node) as Hone.
      destruct (audit_memo_legacy_one_counted EN EF ET node_enc edge_enc function_enc site_enc
        source
        operand before load reads writes g effects mg setup state function query_fuel node)
        as [[candidate next] one_body].
      destruct Hone as [one_cost [Honebudget Honework]].
      pose proof (audit_map_set_source_work_bound N (option (mem_node F N)) CN node_enc node_work
        node candidate pairs) as Hstorework.
      pose proof (audit_map_set_erases N (option (mem_node F N)) CN node_enc EN node candidate pairs
        (Hnode node)) as Hstore.
      pose proof (Hnw node) as Hnodework.
      destruct (audit_map_set node_enc node candidate pairs) as [updated store_body];
        cbn [fst snd] in Hstore, Hstorework.
      specialize (IH next updated).
      destruct (audit_memo_legacy_nodes_counted EN EF ET node_enc edge_enc function_enc site_enc
        source operand before load reads writes g effects mg function query_fuel setup rest next
        updated) as [[final final_state] tail].
      destruct IH as [tail_cost [Htailbudget Htailwork]].
      exists (6 + one_cost + 2 + node_budget node + 16 * Pos.size_nat (fst (node_enc node)) +
        tail_cost).
      split.
      + unfold NodesBudget in *; eapply AuditMemoLegacyBudgetCons; [exact Honebudget|].
        rewrite <- Hstore; exact Htailbudget.
      + cbn [app audit_memo_legacy_nodes_source_work]; lia.
  Qed.
End OneBudget.

(** Reusing the saved effect table costs no more than the full input-derived setup budget. *)
Lemma audit_memo_legacy_setup_work_input N E T CN CE OO TE (EN : encoding N)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (out : N -> list E * list OO) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T)) (g : Graph.t N E)
    (table : Map.t E (Map.t nat (memory_effect T)))
    node_work edge_work out_work target_work node_budget edge_budget out_budget target_budget :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  (forall n, out_work (snd (out n)) <= out_budget n) ->
  (forall e, target_work (snd (target e)) <= target_budget e) ->
  audit_legacy_setup_source_work EN node_work edge_work out_work target_work (fun _ => 0)
    (audit_memo_legacy_setup_counted EN node_enc edge_enc out target g table) <=
  audit_legacy_setup_input_budget EN node_enc edge_enc out target (fun e => (effects e, @nil unit))
    node_budget out_budget edge_budget target_budget (fun _ => 0) g.
Proof.
  intros Hnode Hnw Hew How Htw.
  pose proof (audit_legacy_setup_whole_input_bound N E T CN CE OO TE unit EN node_enc edge_enc out
    target (fun e => (effects e, @nil unit)) node_work edge_work out_work target_work (fun _ => 0)
    node_budget edge_budget out_budget target_budget (fun _ => 0) g Hnode Hnw Hew How Htw
    (fun _ => Nat.le_refl 0)) as Hsetup.
  unfold audit_memo_legacy_setup_counted, audit_legacy_projection_setup in *.
  destruct (audit_legacy_cfg_rows EN node_enc out target (Graph.nodes g)) as [rows ce].
  set (cfg := Graph.Make (Graph.entries g) (Graph.nodes g) (index_edges EN rows) fst snd) in *.
  destruct (audit_prepare_source_counted EN cfg (audit_legacy_prepare_callbacks node_enc rows))
    as [prep pe].
  destruct (audit_legacy_reached_counted EN node_enc cfg prep (Graph.entries cfg)) as [reached re].
  destruct (audit_memory_edges out (Graph.nodes g)) as [edges ee].
  destruct (audit_finset_of_list edge_enc edges) as [listed le].
  destruct (audit_memory_effect_table edge_enc out (fun e => (effects e, @nil unit))
    (Graph.nodes g))
    as [new_table te] in Hsetup.
  unfold audit_legacy_setup_source_work in Hsetup |- *.
  cbn [audit_legacy_setup_cfg_events audit_legacy_setup_prepare_events
    audit_legacy_setup_reached_events audit_legacy_setup_edges_events
      audit_legacy_setup_listed_events
    audit_legacy_setup_table_events audit_memory_table_work] in Hsetup |- *.
  lia.
Qed.

(** Actual foreign budgets derive the producer recurrence and complete independent checker cost. *)
Theorem audit_memory_memo_legacy_whole_input_bound :
  audit_memory_memo_legacy_whole_input_bound_statement.
Proof.
  intros F N E T CN CE CF SE XE OO TE OE BE LE RE WE EN EE EF ET node_enc edge_enc function_enc
    site_enc source out target operand before load reads writes g effects mg function query_fuel
    state node_work edge_work function_work site_work source_work out_work target_work operand_work
    before_work load_work read_work write_work node_budget out_budget load_budget read_budget
    write_budget edge_budget source_budget target_budget function_budget site_budget operand_budget
    before_budget Hnode Hedge Hfunction Hsite Hsource Hout Htarget Hoperand Hbefore node_source
    edge_source function_source site_source source_source out_source target_source operand_source
    before_source load_source reads_source writes_source Hn He Hf Hs Hx Ho Ht Hp Hb Hl Hr Hw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hn) as Hnw.
  pose proof (audit_legacy_callback_bound _ _ _ _ He) as Hew.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hf) as Hfw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hs) as Hsw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hx) as Hxw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Ho) as How.
  pose proof (audit_legacy_callback_bound _ _ _ _ Ht) as Htw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hl) as Hlw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hr) as Hrw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hw) as Hww.
  assert (Hpw : forall n key, operand_work (snd (operand n key)) <= operand_budget n key).
  { intros n key; exact (audit_legacy_callback_bound _ _ _ _ Hp (n, key)). }
  assert (Hbw : forall e index, before_work (snd (before e index)) <= before_budget e index).
  { intros e index; exact (audit_legacy_callback_bound _ _ _ _ Hb (e, index)). }
  pose proof (audit_memo_legacy_setup_work_input N E T CN CE OO TE EN node_enc edge_enc out target
    effects g (@memo_effect_index N E T EN g effects mg state) node_work edge_work out_work
    target_work node_budget edge_budget out_budget target_budget Hnode Hnw Hew How Htw) as Hsetup.
  pose proof (@audit_memo_legacy_nodes_work_input F N E T CN CE CF SE XE OO TE OE BE LE RE WE
    EN EE EF ET node_enc edge_enc function_enc site_enc source operand before load reads writes
    node_work edge_work function_work site_work source_work operand_work before_work load_work
    read_work write_work node_budget load_budget read_budget write_budget edge_budget source_budget
    function_budget site_budget operand_budget before_budget g effects mg function query_fuel
    Hnode Hedge Hfunction Hsite Hsource Hoperand Hbefore Hnw Hew Hfw Hsw Hxw Hpw Hbw Hlw Hrw Hww
    (audit_memo_legacy_setup_counted EN node_enc edge_enc out target g
      (@memo_effect_index N E T EN g effects mg state)) (Graph.nodes g) state Map.empty) as Hnodes.
  unfold audit_memory_memo_legacy_project_counted.
  remember (audit_memo_legacy_setup_counted EN node_enc edge_enc out target g
    (@memo_effect_index N E T EN g effects mg state))
    as setup eqn:Hsetup_call.
  destruct (audit_memo_legacy_nodes_counted EN EF ET node_enc edge_enc function_enc site_enc source
    operand before load reads writes g effects mg function query_fuel setup (Graph.nodes g) state
    Map.empty) as [[pairs next] body] eqn:Hrun.
  destruct Hnodes as [budget [Hbudget Hwork]].
  exists budget; split; [exact Hbudget|].
  assert (Hproducer : audit_memory_memo_legacy_source_work EN EF ET node_enc edge_enc function_enc
      site_enc source out target operand before load reads writes g effects mg function query_fuel
      state node_work edge_work function_work site_work source_work out_work target_work
        operand_work
      before_work load_work read_work write_work <=
    4 + audit_legacy_setup_input_budget EN node_enc edge_enc out target
      (fun e => (effects e, @nil unit)) node_budget out_budget edge_budget target_budget (fun _
        => 0)
      g + budget).
  { unfold audit_memory_memo_legacy_source_work, audit_memory_memo_legacy_project_counted.
    rewrite <- Hsetup_call, Hrun.
    apply Nat.add_le_mono; [apply Nat.add_le_mono_l; exact Hsetup|exact Hwork]. }
  split; [exact Hproducer|].
  pose proof (audit_legacy_no_clobber_whole_input_bound F N E T CN CF SE OO TE RE WE
    (audit_map_event N (option (mem_node F N)) CN) EN EF ET node_enc function_enc site_enc out
      target
    reads writes (audit_memo_legacy_lookup_counted node_enc pairs) node_work function_work site_work
    out_work target_work read_work write_work (fun events => 4 + audit_map_source_work node_work
      events)
    node_budget function_budget site_budget out_budget target_budget read_budget write_budget
    (fun node => 9 + node_budget node + 5 * Pos.size_nat (fst (node_enc node))) g function Hnode Hnw
    Hfw Hsw How Htw Hrw Hww
    (fun node => audit_memo_legacy_lookup_source_bound F N CN node_enc node_work node_budget
      node_source pairs node Hn)) as Hcheck.
  unfold audit_memory_memo_legacy_check_source_work, audit_memory_memo_legacy_check_counted,
    audit_memory_memo_legacy_project_counted.
  rewrite <- Hsetup_call, Hrun.
  destruct (audit_legacy_no_clobber_counted EN EF ET node_enc function_enc site_enc out target reads
    writes function g (audit_memo_legacy_lookup_counted node_enc pairs)) as [accepted checks].
  cbn [snd] in Hcheck |- *.
  apply Nat.add_le_mono; assumption.
Qed.
