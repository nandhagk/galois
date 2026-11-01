(** * Complete legacy producer and checking consumer

    Projection setup is shared by its returned definition closure, which executes full clobbers.
    For example, the outer checker pays the producer's retain slice and then checks the pair again.
    Builds on: full setup, occurrence construction and the independent all-walk checker. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacyProposalSource
  AnalysesAuditMemoryLegacySetupSource AnalysesAuditMemoryLegacyChecker
  AnalysesAuditMemoryLegacySuccessor AnalysesAuditMemoryLegacyNoClobber
  AnalysesAuditMemoryLegacyInputBudget AnalysesAuditMemoryClobbersSource.
Import List.ListNotations.

Inductive audit_legacy_projection_event (F N P R : Type) : Type :=
  | AuditLegacyProjectionProposal (body : list P)
  | AuditLegacyProjectionRetainNone
  | AuditLegacyProjectionRetain (candidate : mem_node F N) (accepted : bool) (body : list R).
Arguments AuditLegacyProjectionProposal {F N P R} _.
Arguments AuditLegacyProjectionRetainNone {F N P R}.
Arguments AuditLegacyProjectionRetain {F N P R} _ _ _.

(** A proposal event can carry the full counted clobber run for its selected occurrence. *)
Definition audit_legacy_projection_proposal_event (F N E T CN CE SE XE OE TE FE PE BE LE RE :
  Type) :=
  audit_legacy_source_proposal_event F N E T CN CE XE BE LE RE
    (audit_clobbers_source_run N E T CN CE SE OE TE FE PE BE).

(** A retain event can record a legacy pair check with counted successor operations. *)
Definition audit_legacy_projection_retain_event (F N T CN CF SE RE WE : Type) :=
  audit_legacy_pair_event F N (N * N) T CN CF SE
    (audit_legacy_successor_event N (N * N) CN) RE WE.

(** A definition event combines proposal and retain observations for a projected load. *)
Definition audit_legacy_projection_definition_event
    (F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE : Type) :=
  audit_legacy_projection_event F N
    (audit_legacy_projection_proposal_event F N E T CN CE SE XE OE TE FE PE BE LE RE)
    (audit_legacy_projection_retain_event F N T CN CF SE RE WE).

Section Projection.
  Context {F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE : Type}.
  Context (EN : encoding N) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OE).
  Context (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE).
  Context (operand : N -> option E -> option (memory_version N E) * list PE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (g : Graph.t N E) (mg : memory_graph N E) (function : F) (fuel : positive).

  Definition audit_legacy_projection_definition_source
      (setup : @audit_legacy_setup_run N E T CN CE OE TE FE EN) (node : N) :=
    let '(proposal, proposal_body) := audit_legacy_occurrence_source EN node_enc edge_enc site_enc
      source out target effects operand before load reads (audit_legacy_setup_listed setup)
      (audit_legacy_setup_reached setup) (audit_legacy_setup_table setup) g mg function fuel node in
    match proposal with
    | None => (None, [AuditLegacyProjectionProposal proposal_body; AuditLegacyProjectionRetainNone])
    | Some candidate =>
        let cfg := audit_legacy_setup_cfg setup in
        let prep := audit_legacy_setup_prepared setup in
        let '(accepted, body) := audit_legacy_pair_check_full EN EF ET node_enc function_enc
          site_enc
          (audit_legacy_successors_counted EN node_enc cfg prep) reads writes cfg prep
          (audit_legacy_setup_reached setup) node candidate function in
        (if accepted then Some candidate else None,
          [AuditLegacyProjectionProposal proposal_body; AuditLegacyProjectionRetain candidate
            accepted body])
    end.

  Definition audit_legacy_projection_source_counted :=
    let setup := audit_legacy_projection_setup EN node_enc edge_enc out target effects g in
    (setup, audit_legacy_projection_definition_source setup).

  Definition audit_legacy_projection_check_source_counted :=
    let '(setup, definitions) := audit_legacy_projection_source_counted in
    let '(accepted, body) := audit_legacy_no_clobber_counted EN EF ET node_enc function_enc site_enc
      out target reads writes function g definitions in
    (accepted, setup, body).
End Projection.

Section Work.
  Context {F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE : Type}.
  Context (EN : encoding N).
  Context (node_work : list CN -> nat) (edge_work : list CE -> nat).
  Context (function_work : list CF -> nat) (site_work : list SE -> nat).
  Context (source_work : list XE -> nat) (out_work : list OE -> nat) (target_work : list TE -> nat).
  Context (effect_work : list FE -> nat) (operand_work : list PE -> nat) (before_work : list BE
    -> nat).
  Context (load_work : list LE -> nat) (read_work : list RE -> nat) (write_work : list WE -> nat).

  Fixpoint audit_legacy_projection_definition_source_work
      (events : list (audit_legacy_projection_definition_event
        F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE)) : nat :=
    match events with
    | [] => 0
    | event :: rest =>
        (2 +
          match event with
          | AuditLegacyProjectionProposal body => audit_legacy_occurrence_source_work node_work
            edge_work
              source_work before_work load_work read_work
              (audit_memory_clobbers_full_source_work node_work edge_work site_work out_work
                target_work
                effect_work operand_work before_work) body
          | AuditLegacyProjectionRetainNone => 1
          | AuditLegacyProjectionRetain _ _ body => audit_legacy_pair_source_work EN node_work
              function_work site_work (audit_legacy_successor_source_work node_work) read_work
                write_work body
          end) + audit_legacy_projection_definition_source_work rest
    end.

  Definition audit_legacy_projection_check_source_work
      (pipeline : bool * @audit_legacy_setup_run N E T CN CE OE TE FE EN *
        audit_legacy_no_clobber_events F N E T CN CF SE OE TE RE WE
          (audit_legacy_projection_definition_event F N E T CN CE CF SE XE OE TE FE PE BE LE RE
            WE)) : nat :=
    let '(_, setup, body) := pipeline in
    audit_legacy_setup_source_work EN node_work edge_work out_work target_work effect_work setup +
    audit_legacy_no_clobber_source_work EN node_work function_work site_work out_work target_work
      read_work write_work audit_legacy_projection_definition_source_work body.
End Work.

Section Budget.
  Context {F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE : Type}.
  Context (EN : encoding N) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OE).
  Context (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE).
  Context (operand : N -> option E -> option (memory_version N E) * list PE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (node_budget out_budget load_budget read_budget write_budget : N -> nat).
  Context (edge_budget source_budget target_budget effect_budget : E -> nat).
  Context (function_budget : F -> nat) (site_budget : T -> nat).
  Context (operand_budget : N -> option E -> nat) (before_budget : E -> nat -> nat).
  Context (g : Graph.t N E) (mg : memory_graph N E) (function : F) (fuel : positive).

  Definition audit_legacy_projection_definition_input_budget
      (setup : @audit_legacy_setup_run N E T CN CE OE TE FE EN) (node : N) : nat :=
    let listed := audit_legacy_setup_listed setup in
    let reached := audit_legacy_setup_reached setup in
    let table := audit_legacy_setup_table setup in
    let clobbers := audit_legacy_full_clobbers EN node_enc edge_enc site_enc out target effects
      operand before g mg in
    let clobber_budget := audit_memory_clobbers_whole_input_budget EN node_enc edge_enc site_enc
      out target effects operand before node_budget out_budget edge_budget effect_budget
        target_budget
      site_budget operand_budget before_budget g mg in
    let proposal := fst (audit_legacy_occurrence_source EN node_enc edge_enc site_enc source out
      target effects operand before load reads listed reached table g mg function fuel node) in
    5 + audit_legacy_occurrence_with_input_budget node_enc edge_enc source listed reached table
      before
      load reads clobbers node_budget load_budget read_budget edge_budget source_budget
        before_budget
      clobber_budget function fuel node +
    match proposal with
    | None => 0
    | Some candidate =>
        let cfg := audit_legacy_setup_cfg setup in
        let prep := audit_legacy_setup_prepared setup in
        audit_legacy_pair_input_budget EN node_enc function_enc site_enc
          (audit_legacy_successors_counted EN node_enc cfg prep) reads writes node_budget
            function_budget
          site_budget (audit_legacy_successors_input_budget node_enc node_budget (out_index prep))
          read_budget write_budget cfg prep node candidate function
    end.

  Definition audit_legacy_projection_check_input_budget : nat :=
    let setup := audit_legacy_projection_setup EN node_enc edge_enc out target effects g in
    let definitions := audit_legacy_projection_definition_source EN EF ET node_enc edge_enc
      function_enc site_enc source out target effects operand before load reads writes g mg
      function fuel setup in
    audit_legacy_setup_input_budget EN node_enc edge_enc out target effects node_budget out_budget
      edge_budget target_budget effect_budget g +
    audit_legacy_no_clobber_input_budget EN node_enc function_enc site_enc out target reads writes
      definitions node_budget out_budget read_budget write_budget
      (audit_legacy_projection_definition_input_budget setup) function_budget site_budget
        target_budget
      g function.

  (** Matching node, outgoing and target callbacks and callback budgets bound the combined
      producer and checker, including repeated retain and consumer checks. *)
  Definition audit_legacy_projection_check_whole_input_bound_at : Prop :=
    forall node_work edge_work function_work site_work source_work out_work target_work effect_work
        operand_work before_work load_work read_work write_work,
      (forall n, fst (node_enc n) = encode EN n) ->
      (forall n, fst (out n) = Graph.out g n) ->
      (forall e, fst (target e) = Graph.target g e) ->
      (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
      (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
      (forall f, function_work (snd (function_enc f)) <= function_budget f) ->
      (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
      (forall e, source_work (snd (source e)) <= source_budget e) ->
      (forall n, out_work (snd (out n)) <= out_budget n) ->
      (forall e, target_work (snd (target e)) <= target_budget e) ->
      (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
      (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
      (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
      (forall n, load_work (snd (load n)) <= load_budget n) ->
      (forall n, read_work (snd (reads n)) <= read_budget n) ->
      (forall n, write_work (snd (writes n)) <= write_budget n) ->
      audit_legacy_projection_check_source_work EN node_work edge_work function_work site_work
        source_work out_work target_work effect_work operand_work before_work load_work read_work
        write_work (audit_legacy_projection_check_source_counted EN EF ET node_enc edge_enc
          function_enc site_enc source out target effects operand before load reads writes g mg
          function fuel) <= audit_legacy_projection_check_input_budget.

  (** Matching node, outgoing and target callbacks and adapter laws bound the combined producer
      and checker using source bodies tied to their actual operands. *)
  Definition audit_legacy_projection_check_whole_input_bound_adapted_at : Prop :=
    forall node_work edge_work function_work site_work source_work out_work target_work effect_work
        operand_work before_work load_work read_work write_work node_enc_source edge_enc_source
          function_enc_source site_enc_source source_source out_source target_source
          effects_source operand_source before_source load_source reads_source writes_source,
      (forall n, fst (node_enc n) = encode EN n) ->
      (forall n, fst (out n) = Graph.out g n) ->
      (forall e, fst (target e) = Graph.target g e) ->
      audit_external_callback_adapter node_enc node_work node_enc_source node_budget ->
      audit_external_callback_adapter edge_enc edge_work edge_enc_source edge_budget ->
      audit_external_callback_adapter function_enc function_work function_enc_source
        function_budget ->
      audit_external_callback_adapter site_enc site_work site_enc_source site_budget ->
      audit_external_callback_adapter source source_work source_source source_budget ->
      audit_external_callback_adapter out out_work out_source out_budget ->
      audit_external_callback_adapter target target_work target_source target_budget ->
      audit_external_callback_adapter effects effect_work effects_source effect_budget ->
      audit_external_callback_adapter
        (fun args => operand (fst args) (snd args)) operand_work operand_source
        (fun args => operand_budget (fst args) (snd args)) ->
      audit_external_callback_adapter
        (fun args => before (fst args) (snd args)) before_work before_source
        (fun args => before_budget (fst args) (snd args)) ->
      audit_external_callback_adapter load load_work load_source load_budget ->
      audit_external_callback_adapter reads read_work reads_source read_budget ->
      audit_external_callback_adapter writes write_work writes_source write_budget ->
      audit_legacy_projection_check_source_work EN node_work edge_work function_work site_work
        source_work out_work target_work effect_work operand_work before_work load_work read_work
        write_work (audit_legacy_projection_check_source_counted EN EF ET node_enc edge_enc
          function_enc site_enc source out target effects operand before load reads writes g mg
          function fuel) <= audit_legacy_projection_check_input_budget.

End Budget.

Section Erasure.
  Context {F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE : Type}.
  Context (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T).
  Context (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE).
  Context (function_enc : F -> positive * list CF) (site_enc : T -> positive * list SE).
  Context (source : E -> N * list XE) (out : N -> list E * list OE).
  Context (target : E -> N * list TE) (effects : E -> list (memory_effect T) * list FE).
  Context (operand : N -> option E -> option (memory_version N E) * list PE).
  Context (before : E -> nat -> option (memory_version N E) * list BE).
  Context (load : N -> option (E * nat) * list LE).
  Context (reads : N -> list (footprint T) * list RE) (writes : N -> list (footprint T) * list WE).
  Context (g : Graph.t N E) (mg : memory_graph N E) (function : F) (fuel : positive).

  (** With matching encoders and graph and memory callbacks, every produced definition agrees
      with the historical producer. *)
  Definition audit_legacy_projection_source_erases_at : Prop :=
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall f, fst (function_enc f) = encode EF f) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall e, fst (source e) = Graph.source g e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    let '(_, definitions) := audit_legacy_projection_source_counted EN EF ET node_enc edge_enc
      function_enc site_enc source out target effects operand before load reads writes g mg
      function fuel in
    forall node, fst (definitions node) =
      def_of_load (project_memory_legacy EN EE EF ET function g (fun e => fst (effects e))
        (fun n => fst (writes n)) (fun n => fst (reads n)) mg (fun n => fst (load n)) fuel) node.

  (** With matching encoders and graph and memory callbacks, the integrated checker agrees with
      the original checker over the produced definitions. *)
  Definition audit_legacy_projection_check_source_erases_at : Prop :=
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall f, fst (function_enc f) = encode EF f) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall e, fst (source e) = Graph.source g e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    let '(accepted, _, _) := audit_legacy_projection_check_source_counted EN EF ET node_enc edge_enc
      function_enc site_enc source out target effects operand before load reads writes g mg
      function fuel in
    accepted = no_clobber_check EN EF ET function g (fun n => fst (writes n))
      (fun n => fst (reads n))
      (project_memory_legacy EN EE EF ET function g (fun e => fst (effects e))
        (fun n => fst (writes n)) (fun n => fst (reads n)) mg (fun n => fst (load n)) fuel).
End Erasure.

(** Matching callbacks make each produced definition equal the original legacy projection. *)
Definition audit_legacy_projection_source_erases_statement : Prop :=
  forall F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EE EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes g mg function fuel,
    @audit_legacy_projection_source_erases_at F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EE EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes g mg function fuel.

(** Matching callbacks make the counted consumer agree with the original no-clobber checker. *)
Definition audit_legacy_projection_check_source_erases_statement : Prop :=
  forall F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EE EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes g mg function fuel,
    @audit_legacy_projection_check_source_erases_at F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EE EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes g mg function fuel.

(** Matching node, outgoing and target callbacks and callback budgets bound the combined legacy
    producer and checker source work. *)
Definition audit_legacy_projection_check_whole_input_bound_statement : Prop :=
  forall F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes node_budget out_budget load_budget read_budget write_budget edge_budget
      source_budget target_budget effect_budget function_budget site_budget operand_budget
        before_budget
      g mg function fuel,
    @audit_legacy_projection_check_whole_input_bound_at F N E T CN CE CF SE XE OE TE FE PE BE LE
      RE WE
      EN EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes node_budget out_budget load_budget read_budget write_budget edge_budget
      source_budget target_budget effect_budget function_budget site_budget operand_budget
        before_budget
      g mg function fuel.

(** Matching node, outgoing and target callbacks and adapter laws bound the combined producer
    and checker using actual foreign callback bodies. *)
Definition audit_legacy_projection_check_whole_input_bound_adapted_statement : Prop :=
  forall F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes node_budget out_budget load_budget read_budget write_budget edge_budget
      source_budget target_budget effect_budget function_budget site_budget operand_budget
        before_budget
      g mg function fuel,
    @audit_legacy_projection_check_whole_input_bound_adapted_at
      F N E T CN CE CF SE XE OE TE FE PE BE LE RE WE
      EN EF ET node_enc edge_enc function_enc site_enc source out target effects operand before
      load reads writes node_budget out_budget load_budget read_budget write_budget edge_budget
      source_budget target_budget effect_budget function_budget site_budget operand_budget
        before_budget
      g mg function fuel.
