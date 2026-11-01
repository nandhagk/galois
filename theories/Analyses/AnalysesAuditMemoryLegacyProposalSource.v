(** * Legacy proposal with complete clobber construction

    Each accepted read occurrence executes the whole original prepared clobber query.
    For example, a table miss skips before, whereas a valid read builds all adjacency rows.
    Builds on: strict legacy guards, full clobbers and the original occurrence proposal. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Analyses Require Import AnalysesAuditMemoryEffects AnalysesAuditMemoryLegacyGuard
  AnalysesAuditMemoryClobbersSource AnalysesAuditMemoryInputBudget AnalysesAuditMemoryWalkIndex.
Import List.ListNotations.

Inductive audit_legacy_source_proposal_event (F N E T CN CE XE BE LE RE CP : Type) : Type :=
  | AuditLegacySourceLoad (node : N) (result : option (E * nat)) (body : list LE)
  | AuditLegacySourceGuard (body : list (audit_legacy_guard_event N E CN CE XE))
  | AuditLegacySourceEffect (body : list (audit_memory_effect_get_event E T CE))
  | AuditLegacySourceBefore (edge : E) (index : nat)
      (result : option (memory_version N E)) (body : list BE)
  | AuditLegacySourceReadTest (effect : memory_effect T) (result : bool)
  | AuditLegacySourceReads (node : N) (footprints : list (footprint T)) (body : list RE)
  | AuditLegacySourceClobbers (result : memory_clobber_result N E) (body : CP)
  | AuditLegacySourceSource (edge : E) (node : N) (body : list XE)
  | AuditLegacySourceReturn (result : option (mem_node F N)).
Arguments AuditLegacySourceLoad {F N E T CN CE XE BE LE RE CP} _ _ _.
Arguments AuditLegacySourceGuard {F N E T CN CE XE BE LE RE CP} _.
Arguments AuditLegacySourceEffect {F N E T CN CE XE BE LE RE CP} _.
Arguments AuditLegacySourceBefore {F N E T CN CE XE BE LE RE CP} _ _ _ _.
Arguments AuditLegacySourceReadTest {F N E T CN CE XE BE LE RE CP} _ _.
Arguments AuditLegacySourceReads {F N E T CN CE XE BE LE RE CP} _ _ _.
Arguments AuditLegacySourceClobbers {F N E T CN CE XE BE LE RE CP} _ _.
Arguments AuditLegacySourceSource {F N E T CN CE XE BE LE RE CP} _ _ _.
Arguments AuditLegacySourceReturn {F N E T CN CE XE BE LE RE CP} _.

Definition audit_legacy_finish_proposal {F N E T CN CE XE BE LE RE CP}
    (source : E -> N * list XE) (function : F) (clobber : memory_clobber_result N E) :
    option (mem_node F N) * list (audit_legacy_source_proposal_event F N E T CN CE XE BE LE RE
      CP) :=
  match clobber_roots clobber with
  | [MemoryLive] => (Some (MLive function), [AuditLegacySourceReturn (Some (MLive function))])
  | [MemoryDef edge _] =>
      let '(node, body) := source edge in
      let candidate := Some (MDef function node) in
      (candidate, [AuditLegacySourceSource edge node body; AuditLegacySourceReturn candidate])
  | _ => (None, [AuditLegacySourceReturn None])
  end.

Definition audit_legacy_occurrence_source_with {F N E T CN CE XE BE LE RE CP}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (source : E -> N * list XE) (listed : FinSet.t E) (reached : FinSet.t N)
    (table : Map.t E (Map.t nat (memory_effect T)))
    (before : E -> nat -> option (memory_version N E) * list BE)
    (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
    (clobbers : memory_scope T -> memory_version N E -> positive -> memory_clobber_result N E * CP)
    (function : F) (fuel : positive) (node : N) :=
  let '(occurrence, load_body) := load node in
  let load_event := AuditLegacySourceLoad node occurrence load_body in
  match occurrence with
  | None => (None, [load_event; AuditLegacySourceReturn None])
  | Some (edge, index) =>
      let '(guard, guard_body) := audit_legacy_guard node_enc edge_enc source reached listed
        edge node in
      let prefix := [load_event; AuditLegacySourceGuard guard_body] in
      if guard then
        let '(effect, effect_body) := audit_memory_effect_get edge_enc table edge index in
        let prefix := prefix ++ [AuditLegacySourceEffect effect_body] in
        match effect with
        | None => (None, prefix ++ [AuditLegacySourceReturn None])
        | Some actual =>
            let '(input, before_body) := before edge index in
            let prefix := prefix ++ [AuditLegacySourceBefore edge index input before_body] in
            match input with
            | None => (None, prefix ++ [AuditLegacySourceReturn None])
            | Some start =>
                let has_read := memory_effect_has_read actual in
                let prefix := prefix ++ [AuditLegacySourceReadTest actual has_read] in
                if has_read then
                  let '(footprints, read_body) := reads node in
                  let '(clobber, clobber_body) := clobbers (MemoryRegions footprints) start fuel in
                  let '(answer, finish_body) := audit_legacy_finish_proposal source function
                    clobber in
                  (answer, prefix ++ [AuditLegacySourceReads node footprints read_body;
                    AuditLegacySourceClobbers clobber clobber_body] ++ finish_body)
                else (None, prefix ++ [AuditLegacySourceReturn None])
            end
        end
      else (None, prefix ++ [AuditLegacySourceReturn None])
  end.

Fixpoint audit_legacy_occurrence_source_work {F N E T CN CE XE BE LE RE CP}
    (node_work : list CN -> nat) (edge_work : list CE -> nat) (source_work : list XE -> nat)
    (before_work : list BE -> nat) (load_work : list LE -> nat) (read_work : list RE -> nat)
    (clobber_work : CP -> nat)
    (events : list (audit_legacy_source_proposal_event F N E T CN CE XE BE LE RE CP)) : nat :=
  match events with
  | [] => 0
  | event :: rest =>
      (2 +
        match event with
        | AuditLegacySourceLoad _ _ body => load_work body
        | AuditLegacySourceGuard body => audit_legacy_guard_source_work node_work edge_work
          source_work body
        | AuditLegacySourceEffect body => audit_memory_effect_get_work edge_work body
        | AuditLegacySourceBefore _ _ _ body => before_work body
        | AuditLegacySourceReadTest _ _ => 1
        | AuditLegacySourceReads _ _ body => read_work body
        | AuditLegacySourceClobbers _ body => clobber_work body
        | AuditLegacySourceSource _ _ body => source_work body
        | AuditLegacySourceReturn _ => 1
        end) + audit_legacy_occurrence_source_work node_work edge_work source_work before_work
        load_work read_work clobber_work rest
  end.

Definition audit_legacy_full_clobbers {N E T CN CE SE OE TE FE PE BE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (g : Graph.t N E) (mg : memory_graph N E) scope start fuel :=
  let run := audit_memory_clobbers_source_counted EN node_enc edge_enc site_enc out target effects
    operand before g mg scope start fuel in
  (audit_clobbers_source_result run, run).

Definition audit_legacy_occurrence_source {F N E T CN CE SE XE OE TE FE PE BE LE RE}
    (EN : encoding N) (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
    (source : E -> N * list XE) (out : N -> list E * list OE) (target : E -> N * list TE)
    (effects : E -> list (memory_effect T) * list FE)
    (operand : N -> option E -> option (memory_version N E) * list PE)
    (before : E -> nat -> option (memory_version N E) * list BE)
    (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
    listed reached table (g : Graph.t N E) (mg : memory_graph N E) (function : F) fuel node :=
  audit_legacy_occurrence_source_with node_enc edge_enc source listed reached table before load
    reads
    (audit_legacy_full_clobbers EN node_enc edge_enc site_enc out target effects operand before
      g mg)
    function fuel node.

(** Matching encoders and graph and memory callbacks make the full occurrence result agree with
    the original producer. *)
Definition audit_legacy_occurrence_source_erases_statement : Prop :=
  forall F N E T CN CE SE XE OE TE FE PE BE LE RE (EN : encoding N) (EE : encoding E)
      (ET : encoding T) (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE)
      (source : E -> N * list XE) (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
      listed reached table (g : Graph.t N E) (mg : memory_graph N E) (function : F) fuel node,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall e, fst (source e) = Graph.source g e) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n key, fst (operand n key) = memory_operand mg n key) ->
    (forall e i, fst (before e i) = memory_before mg e i) ->
    fst (audit_legacy_occurrence_source EN node_enc edge_enc site_enc source out target effects
      operand before load reads listed reached table g mg function fuel node) =
    legacy_occurrence_proposal EN EE ET function g (fun e => fst (effects e)) mg listed reached
      table (fun n => fst (reads n)) (fun n => fst (load n)) fuel node.

Definition audit_legacy_guard_input_budget {N E CN CE XE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (source : E -> N * list XE) (node_budget : N -> nat) (edge_budget source_budget : E -> nat)
    (edge : E) (node : N) : nat :=
  let origin := fst (source edge) in
  26 + 2 * source_budget edge + 2 * node_budget origin + node_budget node + edge_budget edge +
  2 * Nat.min (Pos.size_nat (fst (node_enc origin))) (Pos.size_nat (fst (node_enc node))) +
  5 * Pos.size_nat (fst (node_enc origin)) + 5 * Pos.size_nat (fst (edge_enc edge)).

Definition audit_legacy_occurrence_with_input_budget {F N E T CN CE XE BE LE RE CP}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (source : E -> N * list XE) (listed : FinSet.t E) (reached : FinSet.t N)
    (table : Map.t E (Map.t nat (memory_effect T)))
    (before : E -> nat -> option (memory_version N E) * list BE)
    (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
    (clobbers : memory_scope T -> memory_version N E -> positive -> memory_clobber_result N E * CP)
    (node_budget load_budget read_budget : N -> nat) (edge_budget source_budget : E -> nat)
    (before_budget : E -> nat -> nat)
    (clobber_budget : memory_scope T -> memory_version N E -> positive -> nat)
    (function : F) fuel node : nat :=
  30 + load_budget node +
  match fst (load node) with
  | None => 0
  | Some (edge, index) =>
      audit_legacy_guard_input_budget node_enc edge_enc source node_budget edge_budget source_budget
        edge node +
      if fst (audit_legacy_guard node_enc edge_enc source reached listed edge node) then
        audit_memory_effect_get_input_budget edge_enc edge_budget table edge index +
        match fst (audit_memory_effect_get edge_enc table edge index) with
        | None => 0
        | Some actual => before_budget edge index +
            match fst (before edge index) with
            | None => 0
            | Some start =>
                if memory_effect_has_read actual then
                  let scope := MemoryRegions (fst (reads node)) in
                  let result := fst (clobbers scope start fuel) in
                  read_budget node + clobber_budget scope start fuel +
                  match clobber_roots result with
                  | [MemoryDef source_edge _] => source_budget source_edge
                  | _ => 0
                  end
                else 0
            end
        end
      else 0
  end.

(** Matching node, outgoing and target callbacks and callback budgets bound occurrence work,
    including its full clobber call at the same scope and start. *)
Definition audit_legacy_occurrence_whole_input_bound_statement : Prop :=
  forall F N E T CN CE SE XE OE TE FE PE BE LE RE (EN : encoding N)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
      (site_enc : T -> positive * list SE) (source : E -> N * list XE)
      (out : N -> list E * list OE) (target : E -> N * list TE)
      (effects : E -> list (memory_effect T) * list FE)
      (operand : N -> option E -> option (memory_version N E) * list PE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      (load : N -> option (E * nat) * list LE) (reads : N -> list (footprint T) * list RE)
      node_work edge_work site_work source_work out_work target_work effect_work operand_work
      before_work load_work read_work node_budget edge_budget site_budget source_budget out_budget
      target_budget effect_budget operand_budget before_budget load_budget read_budget
      listed reached table (g : Graph.t N E) (mg : memory_graph N E) (function : F) fuel node,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall n, fst (out n) = Graph.out g n) ->
    (forall e, fst (target e) = Graph.target g e) ->
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall e, source_work (snd (source e)) <= source_budget e) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, target_work (snd (target e)) <= target_budget e) ->
    (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
    (forall n, load_work (snd (load n)) <= load_budget n) ->
    (forall n, read_work (snd (reads n)) <= read_budget n) ->
    audit_legacy_occurrence_source_work node_work edge_work source_work before_work load_work
      read_work
      (audit_memory_clobbers_full_source_work node_work edge_work site_work out_work target_work
        effect_work operand_work before_work)
      (snd (audit_legacy_occurrence_source EN node_enc edge_enc site_enc source out target effects
        operand before load reads listed reached table g mg function fuel node)) <=
    audit_legacy_occurrence_with_input_budget node_enc edge_enc source listed reached table before
      load reads (audit_legacy_full_clobbers EN node_enc edge_enc site_enc out target effects
        operand
        before g mg) node_budget load_budget read_budget edge_budget source_budget before_budget
      (audit_memory_clobbers_whole_input_budget EN node_enc edge_enc site_enc out target effects
        operand before node_budget out_budget edge_budget effect_budget target_budget site_budget
        operand_budget before_budget g mg) function fuel node.
