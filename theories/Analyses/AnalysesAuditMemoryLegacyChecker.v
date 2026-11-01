(** * Actual legacy pair and all-node checker composition

    This file composes owner/scope decisions with the counted full slice for each
    actual candidate. The outer checker retains every strict [forallb] operand; its calls preserve
    the exact reached-set and source callback traces.
    For example, a false candidate does not skip the remaining node traversal.
    Builds on: legacy slice and successor observers. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy.
From Galois.Collections Require Import CollectionsAuditPrimitive CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacySliceFull.
Import List.ListNotations.
Open Scope bool_scope.

Inductive audit_legacy_pair_event (F N E T CN CF CT CS CR CW : Type) : Type :=
  | AuditLegacyPairLoadProbe (load : N) (result : bool) (calls : list (audit_set_event N CN))
  | AuditLegacyPairOwnerCompare (owner function : F) (owner_code function_code : positive)
      (owner_body function_body : list CF) (result : bool) (calls : list audit_positive_eqb_event)
  | AuditLegacyPairDefinitionProbe (node : N) (result : bool) (calls : list (audit_set_event N CN))
  | AuditLegacyPairSuccessors (node : N) (result : list N) (calls : list CS)
  | AuditLegacyPairReads (node : N) (result : list (footprint T)) (calls : list CR)
  | AuditLegacyPairSlice (result : bool)
      (events : audit_legacy_slice_full_events N E T CN CT CW).
Arguments AuditLegacyPairLoadProbe {F N E T CN CF CT CS CR CW} _ _ _.
Arguments AuditLegacyPairOwnerCompare {F N E T CN CF CT CS CR CW} _ _ _ _ _ _ _ _.
Arguments AuditLegacyPairDefinitionProbe {F N E T CN CF CT CS CR CW} _ _ _.
Arguments AuditLegacyPairSuccessors {F N E T CN CF CT CS CR CW} _ _ _.
Arguments AuditLegacyPairReads {F N E T CN CF CT CS CR CW} _ _ _.
Arguments AuditLegacyPairSlice {F N E T CN CF CT CS CR CW} _ _.

Definition audit_legacy_pair_check_full {F N E T CN CF CT CS CR CW}
    (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT)
    (successors : N -> list N * list CS) (reads : N -> list (footprint T) * list CR)
    (writes : N -> list (footprint T) * list CW)
    (g : Graph.t N E) (p : prepared EN g) (reached : FinSet.t N)
    (load : N) (d : mem_node F N) (function : F)
    : bool * list (audit_legacy_pair_event F N E T CN CF CT CS CR CW) :=
  let '(load_ok, load_calls) := audit_finset_mem node_enc load reached in
  let '(owner, def_node) :=
    match d with
    | MDef owner n => (owner, Some n)
    | MLive owner => (owner, None)
    end in
  let '(owner_code, owner_body) := function_enc owner in
  let '(function_code, function_body) := function_enc function in
  let '(same_owner, owner_calls) := audit_positive_eqb owner_code function_code in
  let owner_event := AuditLegacyPairOwnerCompare owner function owner_code function_code
    owner_body function_body same_owner owner_calls in
  match def_node with
  | Some n =>
      let '(def_ok, def_calls) := audit_finset_mem node_enc n reached in
      let '(read, read_calls) := reads load in
      let '(roots, succ_calls) := successors n in
      let '(answer, slice_events) := audit_legacy_slice_full EN ET node_enc site_enc g p writes
        read roots load in
      (andb load_ok (andb same_owner (andb def_ok answer)),
        [AuditLegacyPairLoadProbe load load_ok load_calls; owner_event;
        AuditLegacyPairDefinitionProbe n def_ok def_calls;
        AuditLegacyPairSuccessors n roots succ_calls; AuditLegacyPairReads load read read_calls;
        AuditLegacyPairSlice answer slice_events])
  | None =>
      let roots := Graph.entries g in
      let '(read, read_calls) := reads load in
      let '(answer, slice_events) := audit_legacy_slice_full EN ET node_enc site_enc g p writes
        read roots load in
      (andb load_ok (andb same_owner answer), [AuditLegacyPairLoadProbe load load_ok load_calls;
        owner_event;
        AuditLegacyPairReads load read read_calls; AuditLegacyPairSlice answer slice_events])
  end.

Inductive audit_legacy_checker_event (F N E T CN CF CT CS CR CW CD : Type) : Type :=
  | AuditLegacyCheckerCase (remaining : list N)
  | AuditLegacyCheckerMissing (node : N) (definition_call : list CD)
  | AuditLegacyCheckerCandidate (node : N) (definition : mem_node F N) (result : bool)
      (definition_call : list CD)
      (events : list (audit_legacy_pair_event F N E T CN CF CT CS CR CW)).
Arguments AuditLegacyCheckerCase {F N E T CN CF CT CS CR CW CD} _.
Arguments AuditLegacyCheckerMissing {F N E T CN CF CT CS CR CW CD} _ _.
Arguments AuditLegacyCheckerCandidate {F N E T CN CF CT CS CR CW CD} _ _ _ _ _.

Fixpoint audit_legacy_check_nodes {F N E T CN CF CT CS CR CW CD}
    (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT)
    (successors : N -> list N * list CS) (reads : N -> list (footprint T) * list CR)
    (writes : N -> list (footprint T) * list CW)
    (g : Graph.t N E) (p : prepared EN g) (reached : FinSet.t N)
    (definitions : N -> option (mem_node F N) * list CD) (function : F) (nodes : list N)
    : bool * list (audit_legacy_checker_event F N E T CN CF CT CS CR CW CD) :=
  match nodes with
  | [] => (true, [AuditLegacyCheckerCase nodes])
  | n :: rest => let '(definition, definition_call) := definitions n in
      match definition with
      | None => let '(tail, events) := audit_legacy_check_nodes EN EF ET node_enc function_enc
        site_enc
          successors reads writes g p reached definitions function rest in
          (andb true tail, AuditLegacyCheckerCase nodes :: AuditLegacyCheckerMissing n
            definition_call :: events)
      | Some d =>
          let '(answer, pair_events) := audit_legacy_pair_check_full EN EF ET node_enc function_enc
            site_enc successors reads writes g p reached n d function in
          let '(tail, events) := audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc
            successors reads writes g p reached definitions function rest in
          (andb answer tail,
            AuditLegacyCheckerCase nodes :: AuditLegacyCheckerCandidate n d answer definition_call
              pair_events :: events)
      end
  end.

(** Matching encoders and callbacks recover the original legacy pair-check boolean. *)
Definition audit_legacy_pair_check_erases_statement : Prop :=
  forall F N E T CN CF CT CS CR CW (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT) (successors : N -> list N * list CS)
    (reads : N -> list (footprint T) * list CR) (writes : N -> list (footprint T) * list CW)
    (original_reads original_writes : N -> list (footprint T))
    (g : Graph.t N E) (p : prepared EN g) reached n d f,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall x, fst (function_enc x) = encode EF x) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n, fst (successors n) = legacy_successors EN g p n) ->
    (forall n, fst (reads n) = original_reads n) ->
    (forall n, fst (writes n) = original_writes n) ->
    fst (audit_legacy_pair_check_full EN EF ET node_enc function_enc site_enc successors reads
      writes
      g p reached n d f) =
      legacy_pair_check EN EF ET f g p reached original_writes original_reads n d.

Fixpoint audit_legacy_pair_primitive_work {F N E T CN CF CT CS CR CW}
    (EN : encoding N) (node_work : list CN -> nat) (function_work : list CF -> nat)
    (site_work : list CT -> nat) (successor_work : list CS -> nat)
    (read_work : list CR -> nat) (write_work : list CW -> nat)
    (events : list (audit_legacy_pair_event F N E T CN CF CT CS CR CW)) : nat :=
  match events with
  | [] => 0
  | AuditLegacyPairLoadProbe _ _ calls :: rest => audit_finset_source_work node_work calls +
      audit_legacy_pair_primitive_work EN node_work function_work site_work successor_work
        read_work write_work rest
  | AuditLegacyPairOwnerCompare _ _ _ _ left_body right_body _ calls :: rest =>
      function_work left_body + function_work right_body + audit_positive_eqb_source_work calls +
      audit_legacy_pair_primitive_work EN node_work function_work site_work successor_work
        read_work write_work rest
  | AuditLegacyPairDefinitionProbe _ _ calls :: rest => audit_finset_source_work node_work calls +
      audit_legacy_pair_primitive_work EN node_work function_work site_work successor_work
        read_work write_work rest
  | AuditLegacyPairSuccessors _ _ calls :: rest => successor_work calls +
      audit_legacy_pair_primitive_work EN node_work function_work site_work successor_work
        read_work write_work rest
  | AuditLegacyPairReads _ _ calls :: rest => read_work calls +
      audit_legacy_pair_primitive_work EN node_work function_work site_work successor_work
        read_work write_work rest
  | AuditLegacyPairSlice _ child :: rest =>
      audit_legacy_slice_full_source_work EN node_work site_work write_work child +
      audit_legacy_pair_primitive_work EN node_work function_work site_work successor_work
        read_work write_work rest
  end.

Definition audit_legacy_pair_source_work {F N E T CN CF CT CS CR CW}
    (EN : encoding N) (node_work : list CN -> nat) (function_work : list CF -> nat)
    (site_work : list CT -> nat) (successor_work : list CS -> nat)
    (read_work : list CR -> nat) (write_work : list CW -> nat)
    (events : list (audit_legacy_pair_event F N E T CN CF CT CS CR CW)) : nat :=
  2 * length events + audit_legacy_pair_primitive_work EN node_work function_work site_work
    successor_work read_work write_work events.

Fixpoint audit_legacy_checker_source_work {F N E T CN CF CT CS CR CW CD}
    (EN : encoding N) (node_work : list CN -> nat) (function_work : list CF -> nat)
    (site_work : list CT -> nat) (successor_work : list CS -> nat)
    (read_work : list CR -> nat) (write_work : list CW -> nat) (definition_work : list CD -> nat)
    (events : list (audit_legacy_checker_event F N E T CN CF CT CS CR CW CD)) : nat :=
  match events with
  | [] => 0
  | AuditLegacyCheckerCase _ :: rest => 2 + audit_legacy_checker_source_work EN node_work
    function_work
      site_work successor_work read_work write_work definition_work rest
  | AuditLegacyCheckerMissing _ calls :: rest => 2 + definition_work calls +
    audit_legacy_checker_source_work EN node_work function_work
      site_work successor_work read_work write_work definition_work rest
  | AuditLegacyCheckerCandidate _ _ _ calls child :: rest =>
      2 + audit_legacy_pair_source_work EN node_work function_work site_work successor_work
        read_work write_work child +
      definition_work calls +
      audit_legacy_checker_source_work EN node_work function_work site_work successor_work
        read_work write_work definition_work rest
  end.

(** Matching definitions and callbacks recover the original all-node checker result. *)
Definition audit_legacy_check_nodes_erases_statement : Prop :=
  forall F N E T CN CF CT CS CR CW CD (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (node_enc : N -> positive * list CN) (function_enc : F -> positive * list CF)
    (site_enc : T -> positive * list CT) (successors : N -> list N * list CS)
    (reads : N -> list (footprint T) * list CR) (writes : N -> list (footprint T) * list CW)
    (definitions : N -> option (mem_node F N) * list CD)
    (original_reads original_writes : N -> list (footprint T))
    (original_definitions : N -> option (mem_node F N))
    (g : Graph.t N E) (p : prepared EN g) reached f nodes,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall x, fst (function_enc x) = encode EF x) ->
    (forall t, fst (site_enc t) = encode ET t) ->
    (forall n, fst (successors n) = legacy_successors EN g p n) ->
    (forall n, fst (reads n) = original_reads n) ->
    (forall n, fst (writes n) = original_writes n) ->
    (forall n, fst (definitions n) = original_definitions n) ->
    fst (audit_legacy_check_nodes EN EF ET node_enc function_enc site_enc successors reads writes
      g p reached definitions f nodes) =
    forallb (fun n =>
      match original_definitions n with
      | None => true
      | Some d => legacy_pair_check EN EF ET f g p reached original_writes original_reads n d
      end) nodes.

(** Counterexamples to short-circuit models: even with a false first operand, the
    selected constructor branch still records its read/successor work and slice. *)
Definition audit_legacy_false_load_graph : Graph.t bool bool :=
  Graph.Make [false; true] [false; true] (fun _ => []) (fun e => e) (fun e => e).

Definition audit_legacy_false_load_pair_fixture :=
  audit_legacy_pair_check_full bool_encoding bool_encoding unit_encoding
    (fun n => (encode bool_encoding n, @nil unit))
    (fun f => (encode bool_encoding f, @nil unit))
    (fun _ => (encode unit_encoding tt, @nil unit))
    (fun n => ([negb n], [tt]))
    (fun _ => ([], [tt])) (fun _ => ([], [tt]))
    audit_legacy_false_load_graph (prepare bool_encoding audit_legacy_false_load_graph)
    FinSet.empty false (MDef true false) true.

(** A false load check still records the selected pair-check body. *)
Definition audit_legacy_false_load_fixture_retains_body_statement : Prop :=
  let '(result, events) := audit_legacy_false_load_pair_fixture in
  result = false /\
  (exists reads_trace, In (AuditLegacyPairReads false [] reads_trace) events) /\
  (exists slice_result slice_events, In (AuditLegacyPairSlice slice_result slice_events) events).

Definition audit_legacy_false_owner_pair_fixture :=
  audit_legacy_pair_check_full bool_encoding bool_encoding unit_encoding
    (fun n => (encode bool_encoding n, @nil unit))
    (fun f => (encode bool_encoding f, @nil unit))
    (fun _ => (encode unit_encoding tt, @nil unit))
    (fun n => ([negb n], [tt]))
    (fun _ => ([], [tt])) (fun _ => ([], [tt]))
    audit_legacy_false_load_graph (prepare bool_encoding audit_legacy_false_load_graph)
    (FinSet.add bool_encoding false FinSet.empty) false (MDef false true) true.

(** A false owner comparison still records the selected pair-check body. *)
Definition audit_legacy_false_owner_fixture_retains_body_statement : Prop :=
  let '(result, events) := audit_legacy_false_owner_pair_fixture in
  result = false /\
  (exists left right lc rc lb rb eq_events,
    In (AuditLegacyPairOwnerCompare left right lc rc lb rb false eq_events) events) /\
  (exists node reads_trace, In (AuditLegacyPairReads node [] reads_trace) events) /\
  (exists slice_result slice_events,
    In (AuditLegacyPairSlice slice_result slice_events) events).

(** The outer fixture has two false candidates and exposes both calls, proving the
    all-node traversal continues after a false first pair result. *)
Definition audit_legacy_false_head_two_nodes_fixture :=
  audit_legacy_check_nodes bool_encoding bool_encoding unit_encoding
    (fun n => (encode bool_encoding n, @nil unit))
    (fun f => (encode bool_encoding f, @nil unit))
    (fun _ => (encode unit_encoding tt, @nil unit))
    (fun n => ([negb n], [tt]))
    (fun _ => ([], [tt])) (fun _ => ([], [tt]))
    audit_legacy_false_load_graph (prepare bool_encoding audit_legacy_false_load_graph)
    FinSet.empty (fun _ => (Some (MDef true false), [tt])) true [false; true].

(** A false first node still retains the tail checker trace in this fixture. *)
Definition audit_legacy_false_head_two_nodes_fixture_retains_tail_statement : Prop :=
  let '(result, events) := audit_legacy_false_head_two_nodes_fixture in
  result = false /\
  (exists d calls pair_events,
    In (AuditLegacyCheckerCandidate false d false calls pair_events) events /\
    exists d' calls' pair_events',
      In (AuditLegacyCheckerCandidate true d' false calls' pair_events') events).
