(** * Adequacy of the complete legacy producer and checker

    The producer retains the actual proposal and pair-check decisions through its outer checker.
    For example, a proposed singleton definition pays its retain check and the later consumer check.
    Builds on: complete occurrence, shared setup and all-walk checker adequacy. *)

From Stdlib Require Import List PArith Arith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCallback CollectionsAuditMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesAuditMemoryLegacyProjectionSource AnalysesAuditMemoryLegacyProposalSource
  AnalysesAuditMemoryLegacyProposalSourceAdequacy AnalysesAuditMemoryLegacySetupSource
  AnalysesAuditMemoryLegacySetupSourceAdequacy AnalysesAuditMemoryLegacyChecker
  AnalysesAuditMemoryLegacyCheckerAdequacy AnalysesAuditMemoryLegacySuccessor
  AnalysesAuditMemoryLegacySuccessorAdequacy AnalysesAuditMemoryLegacyNoClobber
  AnalysesAuditMemoryLegacyNoClobberAdequacy AnalysesAuditMemoryLegacyInputBudget
  AnalysesAuditMemoryLegacyInputBudgetAdequacy AnalysesAuditMemoryClobbersSource.
Import List.ListNotations.

(** The stored prepared indexes and fuel determine the complete prepared record. *)
Lemma audit_legacy_prepared_equal N E (EN : encoding N) (g : Graph.t N E)
    (left right : prepared EN g) :
  out_index left = out_index right -> in_index left = in_index right ->
  fuel left = fuel right -> left = right.
Proof.
  destruct left, right; cbn; intros Hout Hin Hfuel; subst; reflexivity.
Qed.

(** Each counted closure query equals the historical retained occurrence at that same node. *)
Theorem audit_legacy_projection_source_erases : audit_legacy_projection_source_erases_statement.
Proof.
  intros F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE EN EE EF ET node_enc edge_enc
    function_enc site_enc source out target effects operand before load reads writes g mg function
    query_fuel Hnode Hedge Hfunction Hsite Hsource Hout Htarget Hoperand Hbefore.
  pose proof (audit_legacy_projection_setup_erases N E T CN CE OE TE FE EN EE node_enc edge_enc
    out target effects g Hnode Hedge Hout Htarget) as Hsetup.
  unfold audit_legacy_projection_source_counted.
  remember (audit_legacy_projection_setup EN node_enc edge_enc out target effects g)
    as setup eqn:Hsetup_call.
  destruct setup as [cfg prep reached listed table ce pe re ee le te].
  cbn [audit_legacy_setup_cfg audit_legacy_setup_prepared audit_legacy_setup_reached
    audit_legacy_setup_listed audit_legacy_setup_table] in Hsetup.
  destruct Hsetup as [Hcfg [Hreached [Hlisted [Htable [Houtindex [Hinindex [Hfuel Hsucc]]]]]]].
  subst cfg; assert (Hprep : prep = prepare EN (legacy_cfg EN g)).
  { apply audit_legacy_prepared_equal; assumption. }
  subst prep reached listed table.
  intro node; unfold audit_legacy_projection_definition_source.
  pose proof (audit_legacy_occurrence_source_erases F N E T CN CE SE XE OE TE FE PE BE LE RE
    EN EE ET node_enc edge_enc site_enc source out target effects operand before load reads
    (FinSet.of_list EE (ViewsGraph.edges_of g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
    (memory_walk_effect_table EE g (fun e => fst (effects e))) g mg function query_fuel node
    Hnode Hedge Hsite Hsource Hout Htarget Hoperand Hbefore) as Hproposal.
  cbn [audit_legacy_setup_listed audit_legacy_setup_reached audit_legacy_setup_table
    audit_legacy_setup_cfg audit_legacy_setup_prepared].
  destruct (audit_legacy_occurrence_source EN node_enc edge_enc site_enc source out target effects
    operand before load reads (FinSet.of_list EE (ViewsGraph.edges_of g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
    (memory_walk_effect_table EE g (fun e => fst (effects e))) g mg function query_fuel node)
    as [proposal proposal_body]; cbn [fst] in Hproposal.
  unfold project_memory_legacy; cbn [def_of_load].
  change (Graph.entries (legacy_cfg EN g)) with (Graph.entries g).
  rewrite <- Hproposal.
  destruct proposal as [candidate|]; [|reflexivity].
  pose proof (audit_legacy_pair_check_erases F N (N * N)%type T CN CF SE
    (audit_legacy_successor_event N (N * N) CN) RE WE EN EF ET node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc (legacy_cfg EN g)
      (prepare EN (legacy_cfg EN g))) reads writes (fun n => fst (reads n))
    (fun n => fst (writes n)) (legacy_cfg EN g) (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g)) node candidate function
    Hnode Hfunction Hsite
    (fun n => audit_legacy_successors_erases N (N * N)%type CN EN node_enc (legacy_cfg EN g)
      (prepare EN (legacy_cfg EN g)) n Hnode) (fun _ => eq_refl) (fun _ => eq_refl)) as Hretain.
  destruct (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
    (audit_legacy_successors_counted EN node_enc (legacy_cfg EN g)
      (prepare EN (legacy_cfg EN g))) reads writes (legacy_cfg EN g)
    (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g)) node candidate function)
    as [accepted retain_body]; cbn [fst] in Hretain.
  unfold legacy_retain; rewrite <- Hretain; reflexivity.
Qed.

(** The independent checker consumes exactly the definitions returned by the fixed producer. *)
Theorem audit_legacy_projection_check_source_erases :
  audit_legacy_projection_check_source_erases_statement.
Proof.
  intros F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE EN EE EF ET node_enc edge_enc
    function_enc site_enc source out target effects operand before load reads writes g mg function
    query_fuel Hnode Hedge Hfunction Hsite Hsource Hout Htarget Hoperand Hbefore.
  pose proof (audit_legacy_projection_source_erases F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
    EN EE EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
    load reads writes g mg function query_fuel Hnode Hedge Hfunction Hsite Hsource Hout Htarget
    Hoperand Hbefore) as Hdefinitions.
  unfold audit_legacy_projection_check_source_counted.
  destruct (audit_legacy_projection_source_counted EN EF ET node_enc edge_enc function_enc site_enc
    source out target effects operand before load reads writes g mg function query_fuel)
    as [setup definitions]; cbn in Hdefinitions.
  pose proof (audit_legacy_no_clobber_erases F N E T CN CF SE OE TE RE WE _ EN EF ET
    node_enc function_enc site_enc out target reads writes function g
    (project_memory_legacy EN EE EF ET function g (fun e => fst (effects e))
      (fun n => fst (writes n)) (fun n => fst (reads n)) mg (fun n => fst (load n)) query_fuel)
    definitions Hnode Hfunction Hsite Hout Htarget Hdefinitions) as Hcheck.
  destruct (audit_legacy_no_clobber_counted EN EF ET node_enc function_enc site_enc out target
    reads writes function g definitions) as [accepted body]; exact Hcheck.
Qed.

Section DefinitionBound.
  Context {F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE : Type}.
  Context (EN : encoding N) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OE) (target : E -> N * list TE).
  Context (effects : E -> list (memory_effect T) * list FE).
  Context (operand : N -> option E -> option (memory_version N E) * list PE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (node_work : list CN -> nat) (edge_work : list CE -> nat).
  Context (function_work : list CF -> nat) (site_work : list SE -> nat).
  Context (source_work : list XE -> nat) (out_work : list OE -> nat).
  Context (target_work : list TE -> nat) (effect_work : list FE -> nat).
  Context (operand_work : list PE -> nat) (before_work : list BE -> nat).
  Context (load_work : list LE -> nat) (read_work : list RE -> nat) (write_work : list WE -> nat).
  Context (node_budget out_budget load_budget read_budget write_budget : N -> nat).
  Context (edge_budget source_budget target_budget effect_budget : E -> nat).
  Context (function_budget : F -> nat) (site_budget : T -> nat).
  Context (operand_budget : N -> option E -> nat) (before_budget : E -> nat -> nat).
  Context (g : Graph.t N E) (mg : memory_graph N E) (function : F) (query_fuel : positive).
  Hypothesis Hnode : forall n, fst (node_enc n) = encode EN n.
  Hypothesis Hout : forall n, fst (out n) = Graph.out g n.
  Hypothesis Htarget : forall e, fst (target e) = Graph.target g e.
  Hypothesis Hnw : forall n, node_work (snd (node_enc n)) <= node_budget n.
  Hypothesis Hew : forall e, edge_work (snd (edge_enc e)) <= edge_budget e.
  Hypothesis Hfnw : forall f, function_work (snd (function_enc f)) <= function_budget f.
  Hypothesis Hsw : forall t, site_work (snd (site_enc t)) <= site_budget t.
  Hypothesis Hxw : forall e, source_work (snd (source e)) <= source_budget e.
  Hypothesis How : forall n, out_work (snd (out n)) <= out_budget n.
  Hypothesis Htw : forall e, target_work (snd (target e)) <= target_budget e.
  Hypothesis Hfw : forall e, effect_work (snd (effects e)) <= effect_budget e.
  Hypothesis Hpw : forall n key, operand_work (snd (operand n key)) <= operand_budget n key.
  Hypothesis Hbw : forall e i, before_work (snd (before e i)) <= before_budget e i.
  Hypothesis Hlw : forall n, load_work (snd (load n)) <= load_budget n.
  Hypothesis Hrw : forall n, read_work (snd (reads n)) <= read_budget n.
  Hypothesis Hww : forall n, write_work (snd (writes n)) <= write_budget n.

  (** One definition body pays its full occurrence and its actual selected retain branch. *)
  Lemma audit_legacy_projection_definition_input_bound
      (setup : @audit_legacy_setup_run N E T CN CE OE TE FE EN) node :
    audit_legacy_projection_definition_source_work EN node_work edge_work function_work site_work
      source_work out_work target_work effect_work operand_work before_work load_work read_work
      write_work (snd (audit_legacy_projection_definition_source EN EF ET node_enc edge_enc
        function_enc site_enc source out target effects operand before load reads writes g mg
        function query_fuel setup node)) <=
    audit_legacy_projection_definition_input_budget EN node_enc edge_enc function_enc site_enc
      source out target effects operand before load reads writes node_budget out_budget load_budget
      read_budget write_budget edge_budget source_budget target_budget effect_budget function_budget
      site_budget operand_budget before_budget g mg function query_fuel setup node.
  Proof.
    pose proof (audit_legacy_occurrence_whole_input_bound F N E T CN CE SE XE OE TE FE PE BE LE RE
      EN node_enc edge_enc site_enc source out target effects operand before load reads node_work
      edge_work site_work source_work out_work target_work effect_work operand_work before_work
      load_work read_work node_budget edge_budget site_budget source_budget out_budget target_budget
      effect_budget operand_budget before_budget load_budget read_budget
      (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (audit_legacy_setup_table setup) g mg function query_fuel node Hnode Hout Htarget Hnw Hew Hsw
      Hxw How Htw Hfw Hpw Hbw Hlw Hrw) as Hproposal.
    unfold audit_legacy_projection_definition_source,
      audit_legacy_projection_definition_input_budget.
    destruct (audit_legacy_occurrence_source EN node_enc edge_enc site_enc source out target effects
      operand before load reads (audit_legacy_setup_listed setup) (audit_legacy_setup_reached setup)
      (audit_legacy_setup_table setup) g mg function query_fuel node) as [proposal proposal_body];
      cbn [fst snd] in Hproposal |- *.
    destruct proposal as [candidate|].
    - pose proof (audit_legacy_pair_input_bound F N (N * N)%type T CN CF SE
        (audit_legacy_successor_event N (N * N) CN) RE WE EN EF ET node_enc function_enc site_enc
        (audit_legacy_successors_counted EN node_enc (audit_legacy_setup_cfg setup)
          (audit_legacy_setup_prepared setup)) reads writes node_work function_work site_work
        (audit_legacy_successor_source_work node_work) read_work write_work node_budget
        function_budget site_budget
        (audit_legacy_successors_input_budget node_enc node_budget
          (out_index (audit_legacy_setup_prepared setup))) read_budget write_budget
        (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup)
        (audit_legacy_setup_reached setup) node candidate function Hnode Hnw Hfnw Hsw
        (fun n => audit_legacy_successors_input_bound N (N * N)%type CN EN node_enc node_work
          node_budget (audit_legacy_setup_cfg setup) (audit_legacy_setup_prepared setup) n (Hnw n))
        Hrw Hww) as Hretain.
      destruct (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc
        (audit_legacy_successors_counted EN node_enc (audit_legacy_setup_cfg setup)
          (audit_legacy_setup_prepared setup)) reads writes (audit_legacy_setup_cfg setup)
        (audit_legacy_setup_prepared setup) (audit_legacy_setup_reached setup) node candidate
          function)
        as [accepted body]; cbn [snd] in Hretain |- *.
      cbn [audit_legacy_projection_definition_source_work]; lia.
    - cbn [snd audit_legacy_projection_definition_source_work]; lia.
  Qed.
End DefinitionBound.

(** The whole producer and independent checker compose setup, proposal and retain costs. *)
Theorem audit_legacy_projection_check_whole_input_bound :
  audit_legacy_projection_check_whole_input_bound_statement.
Proof.
  intros F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE EN EF ET node_enc edge_enc function_enc
    site_enc source out target effects operand before load reads writes node_budget out_budget
    load_budget read_budget write_budget edge_budget source_budget target_budget effect_budget
    function_budget site_budget operand_budget before_budget g mg function query_fuel node_work
    edge_work function_work site_work source_work out_work target_work effect_work operand_work
    before_work load_work read_work write_work Hnode Hout Htarget Hnw Hew Hfnw Hsw Hxw How Htw
    Hfw Hpw Hbw Hlw Hrw Hww.
  pose proof (audit_legacy_setup_whole_input_bound N E T CN CE OE TE FE EN node_enc edge_enc out
    target effects node_work edge_work out_work target_work effect_work node_budget edge_budget
    out_budget target_budget effect_budget g Hnode Hnw Hew How Htw Hfw) as Hsetup.
  pose proof (audit_legacy_no_clobber_whole_input_bound F N E T CN CF SE OE TE RE WE _ EN EF ET
    node_enc function_enc site_enc out target reads writes
    (audit_legacy_projection_definition_source EN EF ET node_enc edge_enc function_enc site_enc
      source out target effects operand before load reads writes g mg function query_fuel
      (audit_legacy_projection_setup EN node_enc edge_enc out target effects g))
    node_work function_work site_work out_work target_work read_work write_work
    (audit_legacy_projection_definition_source_work EN node_work edge_work function_work site_work
      source_work out_work target_work effect_work operand_work before_work load_work read_work
      write_work) node_budget function_budget site_budget out_budget target_budget read_budget
    write_budget
    (audit_legacy_projection_definition_input_budget EN node_enc edge_enc function_enc
      site_enc source out target effects operand before load reads writes node_budget out_budget
      load_budget read_budget write_budget edge_budget source_budget target_budget effect_budget
      function_budget site_budget operand_budget before_budget g mg function query_fuel
      (audit_legacy_projection_setup EN node_enc edge_enc out target effects g)) g function Hnode
    Hnw Hfnw Hsw How Htw Hrw Hww) as Hcheck.
  specialize (Hcheck (fun n => audit_legacy_projection_definition_input_bound EN EF ET node_enc
    edge_enc function_enc site_enc source out target effects operand before load reads writes
    node_work edge_work function_work site_work source_work out_work target_work effect_work
    operand_work before_work load_work read_work write_work node_budget out_budget load_budget
    read_budget write_budget edge_budget source_budget target_budget effect_budget function_budget
    site_budget operand_budget before_budget g mg function query_fuel Hnode Hout Htarget Hnw Hew
    Hfnw Hsw Hxw How Htw Hfw Hpw Hbw Hlw Hrw Hww _ n)).
  unfold audit_legacy_projection_check_source_counted, audit_legacy_projection_source_counted,
    audit_legacy_projection_check_input_budget, audit_legacy_projection_check_source_work.
  destruct (audit_legacy_no_clobber_counted EN EF ET node_enc function_enc site_enc out target reads
    writes function g (audit_legacy_projection_definition_source EN EF ET node_enc edge_enc
      function_enc site_enc source out target effects operand before load reads writes g mg
      function query_fuel (audit_legacy_projection_setup EN node_enc edge_enc out target effects
        g)))
    as [accepted body]; cbn [snd] in Hcheck |- *; apply Nat.add_le_mono; assumption.
Qed.

(** The returned body obeys its actual foreign per-call adapter budget. *)
Lemma audit_legacy_callback_bound {A R B} (call : A -> R * list B) work source budget :
  audit_external_callback_adapter call work source budget ->
  forall argument, work (snd (call argument)) <= budget argument.
Proof.
  intros Hadapter argument; destruct (call argument) as [result body] eqn:Hcall; cbn [snd].
  eapply audit_external_callback_input_bound; eassumption.
Qed.

(** Actual foreign callback adapters supply only their exact per-call source bounds. *)
Theorem audit_legacy_projection_check_whole_input_bound_adapted :
  audit_legacy_projection_check_whole_input_bound_adapted_statement.
Proof.
  intros F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE EN EF ET node_enc edge_enc function_enc
    site_enc source out target effects operand before load reads writes node_budget out_budget
    load_budget read_budget write_budget edge_budget source_budget target_budget effect_budget
    function_budget site_budget operand_budget before_budget g mg function query_fuel node_work
    edge_work function_work site_work source_work out_work target_work effect_work operand_work
    before_work load_work read_work write_work node_source edge_source function_source site_source
    source_source out_source target_source effects_source operand_source before_source load_source
    reads_source writes_source Hnode Hout Htarget Hn He Hf Hs Hx Ho Ht Hef Hp Hb Hl Hr Hw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hn) as Hnw.
  pose proof (audit_legacy_callback_bound _ _ _ _ He) as Hew.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hf) as Hfw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hs) as Hsw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hx) as Hxw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Ho) as How.
  pose proof (audit_legacy_callback_bound _ _ _ _ Ht) as Htw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hef) as Hefw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hl) as Hlw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hr) as Hrw.
  pose proof (audit_legacy_callback_bound _ _ _ _ Hw) as Hww.
  apply audit_legacy_projection_check_whole_input_bound; try assumption.
  - intros n key; exact (audit_legacy_callback_bound _ _ _ _ Hp (n, key)).
  - intros e index; exact (audit_legacy_callback_bound _ _ _ _ Hb (e, index)).
Qed.
