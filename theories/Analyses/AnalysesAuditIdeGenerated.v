(** * Indexed IDE producer and source mirrors

    Defines the indexed producer and models its source and callback work.
    For example, a present summary entry invokes the supplied evaluation adapter.
    Builds on: AnalysesAuditIdeBase, AnalysesAuditIdeModels and AnalysesAuditSource. *)

From Stdlib Require Import Decimal Arith Bool List PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditIdeBase AnalysesAuditIdeModels AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap CollectionsTrie.
From Galois.Order Require Import OrderLattice.
Import List.ListNotations.

(* Definition source: IdeGeneratedWhole.v *)
(** * Generated IDE source composition without a carrier census

    Pure row/key iterations are instrumented explicitly; the fixed machine's typed actual
    primitive/callback events are composed on the same intermediate states.
    Builds on: the retained generated IDE declarations and private source combinators. *)

Definition ide_registry_solve {N P D A F} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F) start seed
    : ide_registry_summary N D F :=
  let rules := audit_ide_ground_rules EP r q weight (start,seed) in
  let keys := audit_ide_summary_keys q in
  let initial := audit_ide_machine_initial EN ED rules in
  let fuel := audit_ide_machine_fuel r keys rules in
  let final := audit_ide_machine_loop EN ED r fuel initial in
  IdeRegistrySummary (audit_ide_machine_values final) (rev (audit_ide_machine_probes_rev final)).

(** Generated-source calls distinguish generator, machine, map and external callback events. *)
Inductive ide_generated_source_call (N P D A F : Type) : Type :=
  | IdeSourceGenerator (events : list (audit_ide_generator_call N P D F))
  | IdeSourceInitial (events : list (audit_ide_initial_call N D F))
  | IdeSourceMachine (events : list (audit_ide_machine_call N D F))
  | IdeSourceFact (call : exact_map_call (IpTab.fact N D) F)
  | IdeSourceEval (transformer : F) (input output : A)
  | IdeSourceWeight (edge : ip_edge N P D) (source target : option D) (result : F)
  | IdeSourceOldWeight (edge : ip_edge N P D) (source target : option D) (input output : A)
  | IdeSourceLe (first second : A) (result : bool)
  | IdeSourceFuel (rule_count key_count rank_bound : nat) (result : positive).

Arguments IdeSourceGenerator {N P D A F}.

Arguments IdeSourceInitial {N P D A F}.

Arguments IdeSourceMachine {N P D A F}.

Arguments IdeSourceFact {N P D A F}.

Arguments IdeSourceEval {N P D A F}.

Arguments IdeSourceWeight {N P D A F}.

Arguments IdeSourceOldWeight {N P D A F}.

Arguments IdeSourceLe {N P D A F}.

Arguments IdeSourceFuel {N P D A F}.

Section Generated.

Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
  (weight : ip_edge N P D -> option D -> option D -> F).

Context (node_body : N -> nat) (site_body : P -> nat) (fact_body : D -> nat).

Let Call := ide_generated_source_call N P D A F.

Let fact_cost := ide_fact_body EN ED node_body fact_body.

Definition ide_source_vertices : exact_counted Call (list (IpTab.vertex N D)) :=
  exact_flat_map 1000 (fun n =>
    exact_bind 1001 (exact_map 1001 (fun d => exact_return 1001 (Some d)) (ip_facts q))
      (fun facts => exact_map 1002 (fun d => exact_return 1002 (n,d)) (None :: facts))) (ip_nodes
        q).

Definition ide_source_keys : exact_counted Call (list (IpTab.fact N D)) :=
  exact_bind 1003 ide_source_vertices (fun vertices =>
  exact_bind 1004 (exact_flat_map 1004 (fun v =>
    exact_map 1005 (fun w => exact_return 1005 (v,w)) vertices) vertices) (fun pairs =>
  exact_bind 1006 (exact_map 1006 (fun pair => exact_return 1006 (inl pair)) pairs) (fun summaries
    =>
  exact_bind 1007 (exact_map 1007 (fun vertex => exact_return 1007 (inr vertex)) vertices)
    (fun prefixes => exact_append 1008 summaries prefixes)))).

Definition ide_source_rows (vertices : list (IpTab.vertex N D))
    (arcs : list (audit_ide_arc N P D F))
    (matches : list (audit_ide_arc N P D F * audit_ide_arc N P D F)) (root : IpTab.vertex N D)
    : exact_counted Call (list (audit_ide_rule N D F)) :=
  exact_bind 1010 (exact_return 1010 (AuditIdeSeed (inr root) (audit_ide_id r))) (fun seed =>
  exact_bind 1011 (exact_map 1011 (fun v => exact_return 1011
    (AuditIdeSeed (inl (v,v)) (audit_ide_id r))) vertices) (fun identities =>
  exact_bind 1012 (exact_flat_map 1012 (fun arc => match audit_ide_arc_kind arc with
    | IpInternal => exact_case 1013 (exact_map 1014 (fun a => exact_return 1014
        (AuditIdeUnary (inl (a,audit_ide_arc_from arc)) (inl (a,audit_ide_arc_to arc))
          (audit_ide_arc_weight arc))) vertices)
    | _ => exact_case 1015 (exact_return 1015 [])
    end) arcs) (fun unary =>
  exact_bind 1016 (exact_flat_map 1016 (fun pair => let '(call,ret) := pair in
    exact_map 1017 (fun a => exact_return 1017
      (AuditIdeBinary (inl (a,audit_ide_arc_from call))
        (inl (audit_ide_arc_to call,audit_ide_arc_from ret)) (inl (a,audit_ide_arc_to ret))
        (audit_ide_arc_weight call) (audit_ide_arc_weight ret))) vertices) matches) (fun binary =>
  exact_bind 1018 (exact_flat_map 1018 (fun u => exact_map 1019 (fun v => exact_return 1019
    (AuditIdeBinary (inr u) (inl (u,v)) (inr v) (audit_ide_id r) (audit_ide_id r))) vertices)
    vertices) (fun prefixes =>
  exact_bind 1020 (exact_flat_map 1020 (fun call => match audit_ide_arc_kind call with
    | IpCall _ => exact_case 1021 (exact_return 1021
        [AuditIdeUnary (inr (audit_ide_arc_from call)) (inr (audit_ide_arc_to call))
          (audit_ide_arc_weight call)])
    | _ => exact_case 1022 (exact_return 1022 [])
    end) arcs) (fun calls =>
  exact_bind 1023 (exact_append 1023 prefixes calls) (fun tail1 =>
  exact_bind 1024 (exact_append 1024 binary tail1) (fun tail2 =>
  exact_bind 1025 (exact_append 1025 unary tail2) (fun tail3 =>
  exact_bind 1026 (exact_append 1026 identities tail3) (fun tail4 =>
    exact_return 1027 (seed :: tail4))))))))))).

Definition ide_generator_source_extra (event : audit_ide_generator_call N P D F) : nat :=
  match event with
  | IdeGeneratorIndexGet kind _ _ | IdeGeneratorIndexSet kind _ _ =>
      128 + 64 * Pos.size_nat (encode (IpTab.kind_encoding EP) kind) +
      match kind with
      | IpInternal => 0
      | IpCall p | IpReturn p => site_body p
      end
  | _ => 0
  end.

Definition ide_initial_source_extra (event : audit_ide_initial_call N D F) : nat :=
  match event with
  | IdeInitSeq _ count _ => 128 * S count
  | IdeInitTableSet id _ _ _ | IdeInitQueueAdd id _ _ =>
      64 * Pos.size_nat (encode nat_encoding id) + 2 * S id
  | IdeInitIndexGet _ key _ _ | IdeInitIndexSet _ key _ _ =>
      fact_cost key + 64 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) key)
  | _ => 0
  end.

Definition ide_machine_source_extra (event : audit_ide_machine_call N D F) : nat :=
  match event with
  | IdeMachineRuleRead id _ _ | IdeMachineQueueMember id _ _ |
      IdeMachineQueueRemove id _ _ | IdeMachineQueueAdd id _ _ =>
      64 * Pos.size_nat (encode nat_encoding id) + 2 * S id
  | IdeMachineFactRead key _ _ | IdeMachineFactWrite key _ _ _ | IdeMachineIncidenceRead key _ _ =>
      fact_cost key + 64 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) key)
  | _ => 0
  end.

Definition ide_generator_source_work (events : list (audit_ide_generator_call N P D F)) : nat :=
  audit_ide_generator_model_work EP events + fold_right (fun e n => ide_generator_source_extra e +
    n) 0 events.

Definition ide_initial_source_work (events : list (audit_ide_initial_call N D F)) : nat :=
  audit_ide_initial_model_work EN ED events + fold_right (fun e n => ide_initial_source_extra e + n)
    0 events.

Definition ide_machine_source_work (events : list (audit_ide_machine_call N D F)) : nat :=
  audit_ide_machine_model_work EN ED events + fold_right (fun e n => ide_machine_source_extra e + n)
    0 events.

Definition ide_generated_source_counted (start : N) (seed : option D)
    : exact_counted Call (ide_registry_summary N D F) :=
  exact_bind 1030 ide_source_vertices (fun vertices =>
  let '(arcs,arc_events) := audit_ide_generate_arcs_counted weight (ip_edges q) in
  exact_bind 1031 (exact_call (IdeSourceGenerator arc_events) (ide_generator_source_work arc_events)
    arcs)
    (fun arcs =>
  let '(index,index_events) := audit_ide_generate_index_counted EP arcs in
  exact_bind 1032 (exact_call (IdeSourceGenerator index_events) (ide_generator_source_work
    index_events) index)
    (fun index =>
  let '(matches,match_events) := audit_ide_generate_matches_counted EP index arcs in
  exact_bind 1033 (exact_call (IdeSourceGenerator match_events) (ide_generator_source_work
    match_events) matches)
    (fun matches =>
  exact_bind 1034 (ide_source_rows vertices arcs matches (start,seed)) (fun rules =>
  exact_bind 1035 ide_source_keys (fun keys =>
  let '(initial,initial_events) := audit_ide_initial_counted EN ED rules in
  exact_bind 1036 (exact_call (IdeSourceInitial initial_events) (ide_initial_source_work
    initial_events) initial)
    (fun initial =>
  let fuel := audit_ide_machine_fuel r keys rules in
  exact_bind 1037 (exact_call (IdeSourceFuel (length rules) (length keys) (audit_ide_bound r) fuel)
    (1024 + audit_ide_fuel_model r keys rules) fuel) (fun fuel =>
  let '(final,machine_events) := audit_ide_loop_counted EN ED r fuel initial in
  exact_bind 1038 (exact_call (IdeSourceMachine machine_events) (ide_machine_source_work
    machine_events) final)
    (fun final =>
  exact_bind 1039 (exact_rev 1039 (audit_ide_machine_probes_rev final)) (fun probes =>
    exact_return 1040 (IdeRegistrySummary (audit_ide_machine_values final) probes))))))))))).

Definition ide_generated_query_counted (summary : ide_registry_summary N D F) (initial : A)
    (n : N) (d : option D) : exact_counted Call (option A) :=
  exact_bind 1050 (exact_get IdeSourceFact (IpTab.fact_encoding EN ED) fact_cost
    (inr (n,d)) (ide_registry_summary_map summary)) (fun found => match found with
    | None => exact_case 1051 (exact_return 1051 None)
    | Some transformer =>
        let output := audit_ide_eval r transformer initial in
        exact_case 1052 (exact_bind 1053 (exact_call (IdeSourceEval transformer initial output) 0
          output)
          (fun value => exact_return 1054 (Some value)))
    end).

Definition ide_generated_extra_input (rules : list (audit_ide_rule N D F)) : nat :=
  1024 * S (length rules) + fold_right Nat.max 0
    (map (fun key => fact_cost key + 64 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) key))
      (flat_map audit_ide_rule_keys rules)).

Definition ide_generated_source_budget (start : N) (seed : option D) : nat :=
  let rules := audit_ide_rule_spec EP r q weight (start,seed) in
  let keys := audit_ide_summary_keys q in
  let initial := audit_ide_machine_initial EN ED rules in
  let fuel := audit_ide_machine_fuel r keys rules in
  let loop_events := (32 + 3 * audit_ide_incidence_size initial) * (2 * Pos.to_nat fuel + 1) in
  let vertices := length (IpTab.vertices q) in
  let gen_extra := fold_right Nat.max 0 (map (fun edge => match ip_action edge with
    | IpInternal => 128
    | IpCall p | IpReturn p => 256 + site_body p + 64 * Pos.size_nat (encode EP p)
    end) (ip_edges
      q)) in
  (Nat.of_num_uint 65536%uint) *
    Nat.pow (S (length (ip_nodes q) + length (ip_facts q) + vertices)) 4 +
  audit_ide_generator_input_budget EP q * S gen_extra +
  (Nat.of_num_uint 65536%uint) * Nat.pow (S (length rules + length keys)) 4 +
  audit_ide_initial_input_budget EN ED rules +
    (20 + 16 * length rules) * ide_generated_extra_input rules +
  1024 + audit_ide_fuel_model r keys rules +
  audit_ide_machine_input_budget EN ED fuel initial + loop_events * ide_generated_extra_input rules
    +
    1024 * Nat.pow (S loop_events) 2.

(** Under registry and graph premises, the generated source run returns the fixed producer within
    budget and bounds successful updates. *)
Definition audit_ide_generated_full_source_statement : Prop := forall start seed,
  ide_registry_laws L r -> ip_problem_wf q -> In start (ip_nodes q) ->
  (match seed with
  | None => True
  | Some d => In d (ip_facts q)
  end) ->
  let run := ide_generated_source_counted start seed in
  exact_value run = ide_registry_solve EN EP ED L r q weight start seed /\
  exact_units run <= ide_generated_source_budget start seed /\
  length (audit_ide_probe_updates (ide_registry_summary_probes (exact_value run))) <=
    length (audit_ide_summary_keys q) * S (audit_ide_bound r).

(** The counted query returns the fixed query within its input budget. *)
Definition audit_ide_generated_query_source_statement : Prop := forall summary initial n d,
  let run := ide_generated_query_counted summary initial n d in
  exact_value run = ide_registry_query EN ED r summary initial n d /\
  exact_units run <= 4096 + 4 * fact_cost (inr (n,d)) +
    1024 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) (inr (n,d))).

End Generated.

(* Definition source: IdeGeneratedAdequacy.v *)
(** * Concrete implementation-primitive bridge for the generated IDE stages

    Card: AUD-IDE. The propositions bind fixed source recurrences on retained actual maps.
    Work is at the published source-block granularity, not kernel or native steps. *)
Definition ide_generator_literal_event_work {N P D F} (EP : encoding P)
    (body : P -> nat) (event : audit_ide_generator_call N P D F) : nat :=
  let E := IpTab.kind_encoding EP in
  64 + match event with
  | IdeGeneratorIndexGet kind before _ =>
      16 + (match kind with
      | IpInternal => 0
      | IpCall p | IpReturn p => body p
      end) +
        16 * Pos.size_nat (encode E kind) + audit_trie_get_source_work (encode E kind) before
  | IdeGeneratorIndexSet kind before after =>
      16 + (match kind with
      | IpInternal => 0
      | IpCall p | IpReturn p => body p
      end) +
        16 * Pos.size_nat (encode E kind) +
        audit_trie_update_source_work (encode E kind) (Trie.get (encode E kind) after) before
  | _ => 0
  end.

Definition ide_initial_literal_event_work {N D F} (EN : encoding N) (ED : encoding D)
    (node_body : N -> nat) (fact_body : D -> nat)
    (event : audit_ide_initial_call N D F) : nat :=
  let E := IpTab.fact_encoding EN ED in
  let body := ide_fact_body EN ED node_body fact_body in
  64 + match event with
  | IdeInitSeq _ count _ => 64 * S count
  | IdeInitTableSet id rule before _ =>
      8 + 2 * S id + audit_trie_update_source_work (encode nat_encoding id) (Some (id,rule)) before
  | IdeInitQueueAdd id before _ =>
      8 + 2 * S id + audit_trie_update_source_work (encode nat_encoding id) (Some (id,tt)) before
  | IdeInitIndexGet _ key before _ =>
      8 + body key + audit_trie_get_source_work (encode E key) before
  | IdeInitIndexSet _ key before after =>
      8 + body key + audit_trie_update_source_work (encode E key) (Trie.get (encode E key) after)
        before
  | _ => 0
  end.

Definition ide_machine_literal_event_work {N D F} (EN : encoding N) (ED : encoding D)
    (node_body : N -> nat) (fact_body : D -> nat)
    (event : audit_ide_machine_call N D F) : nat :=
  let E := IpTab.fact_encoding EN ED in
  let body := ide_fact_body EN ED node_body fact_body in
  64 + match event with
  | IdeMachineRuleRead id before _ =>
      8 + 2 * S id + audit_trie_get_source_work (encode nat_encoding id) before
  | IdeMachineQueueMember id before _ =>
      8 + 2 * S id + audit_trie_get_source_work (encode nat_encoding id) before
  | IdeMachineQueueRemove id before _ =>
      8 + 2 * S id + audit_trie_update_source_work (encode nat_encoding id) None before
  | IdeMachineQueueAdd id before _ =>
      8 + 2 * S id + audit_trie_update_source_work (encode nat_encoding id) (Some (id,tt)) before
  | IdeMachineFactRead key before _ =>
      8 + body key + audit_trie_get_source_work (encode E key) before
  | IdeMachineIncidenceRead key before _ =>
      8 + body key + audit_trie_get_source_work (encode E key) before
  | IdeMachineFactWrite key value before _ =>
      8 + body key + audit_trie_update_source_work (encode E key) (Some (key,value)) before
  | _ => 0
  end.

(** Trace-output administration is an explicit quadratic allowance for all append/reversal
    traversals. Recursive source iterations are separately represented by their case events. *)
(** Literal generator, initialization and machine event work is bounded by their source totals. *)
Definition ide_generated_primitive_adequacy_statement : Prop :=
  forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (node_body : N -> nat) (site_body : P -> nat) (fact_body : D -> nat)
    (r : ide_registry A F) (q : ip_problem N P D) weight start seed,
  let arcs := audit_ide_generate_arcs_counted weight (ip_edges q) in
  let index := audit_ide_generate_index_counted EP (fst arcs) in
  let matches := audit_ide_generate_matches_counted EP (fst index) (fst arcs) in
  let rules := audit_ide_rule_spec EP r q weight (start,seed) in
  let init := audit_ide_initial_counted EN ED rules in
  forall fuel,
  let machine := audit_ide_loop_counted EN ED r fuel (fst init) in
  fold_right (fun e n => ide_generator_literal_event_work EP site_body e + n) 0
    (snd arcs ++ snd index ++ snd matches) <=
    ide_generator_source_work EP site_body (snd arcs ++ snd index ++ snd matches) /\
  fold_right (fun e n => ide_initial_literal_event_work EN ED node_body fact_body e + n) 0 (snd
    init) <=
    ide_initial_source_work EN ED node_body fact_body (snd init) /\
  fold_right (fun e n => ide_machine_literal_event_work EN ED node_body fact_body e + n) 0 (snd
    machine) <=
    ide_machine_source_work EN ED node_body fact_body (snd machine).

(** * Generated IDE machine with real per-invocation dictionary bodies

    Card: AUD-IDE-GEN. Each external callback is executed by its supplied counted adapter
    once, and its actual typed call/body pair survives every bind and recursive iteration. *)
Section Bodies.

Context {N D A F : Type} (EN : encoding N) (ED : encoding D) (r : ide_registry A F)
  (adapters : audit_ide_registry_adapters r) (node_body : N -> nat) (fact_body : D -> nat).

Let Call := audit_ide_machine_call N D F.

Let Key := IpTab.fact_encoding EN ED.

Definition ide_body_internal (event : Call) {X} (value : X) : exact_counted Call X :=
  exact_call event (audit_ide_machine_model_event EN ED event +
    ide_machine_source_extra EN ED node_body fact_body event) value.

Definition ide_body_read (state : Map.t (IpTab.fact N D) F) key : exact_counted Call (option F) :=
  let result := Map.get Key key state in ide_body_internal (IdeMachineFactRead key state result)
    result.

Definition ide_rule_with_bodies_counted (state : Map.t (IpTab.fact N D) F)
    (rule : audit_ide_rule N D F) : exact_counted Call (option (IpTab.fact N D * F)) :=
  match rule with
  | AuditIdeSeed dst value => exact_case 2100 (exact_return 2100 (Some (dst,value)))
  | AuditIdeUnary source dst suffix => exact_case 2101
      (exact_bind 2102 (ide_body_read state source) (fun found => match found with
      | None => exact_case 2103 (exact_return 2103 None)
      | Some value => exact_case 2104
          (exact_bind 2105 (exact_external_call (ide_compose_adapter adapters) (value,suffix)
            (fun out => IdeMachineCompose value suffix out))
            (fun out => exact_return 2106 (Some (dst,out))))
      end))
  | AuditIdeBinary first second dst between after => exact_case 2107
      (exact_bind 2108 (ide_body_read state first) (fun left => match left with
      | None => exact_case 2109 (exact_return 2109 None)
      | Some x => exact_case 2110 (exact_bind 2111 (ide_body_read state second) (fun right =>
        match right with
        | None => exact_case 2112 (exact_return 2112 None)
        | Some y => exact_case 2113
            (exact_bind 2114 (exact_external_call (ide_compose_adapter adapters) (x,between)
              (fun out => IdeMachineCompose x between out)) (fun one =>
            exact_bind 2115 (exact_external_call (ide_compose_adapter adapters) (one,y)
              (fun out => IdeMachineCompose one y out)) (fun two =>
            exact_bind 2116 (exact_external_call (ide_compose_adapter adapters) (two,after)
              (fun out => IdeMachineCompose two after out))
              (fun three => exact_return 2117 (Some (dst,three))))))
        end))
      end))
  end.

Definition ide_enqueue_with_bodies_counted ids pending queued
    : exact_counted Call (list nat * FinSet.t nat) :=
  let '(result,events) := @audit_ide_enqueue_counted N D F ids pending queued in
  ExactCounted result (fold_right (fun event rest => audit_ide_machine_model_event EN ED event +
    ide_machine_source_extra EN ED node_body fact_body event + rest) 64 events)
    (map AuditCall events) [].

Definition ide_update_with_bodies_counted (rule : audit_ide_rule N D F)
    (values : Map.t (IpTab.fact N D) F) (derived : option (IpTab.fact N D * F))
    : exact_counted Call (Map.t (IpTab.fact N D) F * audit_ide_probe N D F) :=
  match derived with
  | None => exact_case 2120 (exact_return 2120 (values,AuditIdeProbe rule None false false))
  | Some (dst,incoming) => exact_case 2121
      (exact_bind 2122 (ide_body_read values dst) (fun old => match old with
      | None => exact_case 2123
          (let next := Map.set Key dst incoming values in
          exact_bind 2124 (ide_body_internal (IdeMachineFactWrite dst incoming values next) next)
            (fun next => exact_return 2125 (next,AuditIdeProbe rule (Some dst) true false)))
      | Some previous => exact_case 2126
          (exact_bind 2127 (exact_external_call (ide_join_adapter adapters) (previous,incoming)
            (fun out => IdeMachineJoin previous incoming out)) (fun joined =>
          exact_bind 2128 (exact_external_call (ide_equal_adapter adapters) (joined,previous)
            (fun out => IdeMachineEqual joined previous out)) (fun equal =>
          if equal then exact_case 2129
            (exact_return 2129 (values,AuditIdeProbe rule (Some dst) false true))
          else exact_case 2130
            (let next := Map.set Key dst joined values in
            exact_bind 2131 (ide_body_internal (IdeMachineFactWrite dst joined values next) next)
              (fun next => exact_return 2132 (next,AuditIdeProbe rule (Some dst) true true))))))
      end))
  end.

Definition ide_step_with_bodies_counted (state : audit_ide_machine N D F)
    : exact_counted Call (option (audit_ide_machine N D F)) :=
  match audit_ide_machine_pending state with
  | [] => exact_case 2140 (exact_return 2140 None)
  | id :: rest => exact_case 2141
      (let queued := FinSet.remove nat_encoding id (audit_ide_machine_queued state) in
      exact_bind 2142 (ide_body_internal (IdeMachineQueueRemove id (audit_ide_machine_queued state)
        queued)
        queued) (fun queued =>
      let rule := Map.get nat_encoding id (audit_ide_machine_table state) in
      exact_bind 2143 (ide_body_internal (IdeMachineRuleRead id (audit_ide_machine_table state)
        rule) rule)
        (fun rule => match rule with
      | None => exact_case 2144 (exact_return 2144 (Some (AuditIdeMachine
          (audit_ide_machine_rules state) (audit_ide_machine_table state)
          (audit_ide_machine_incidence state) rest queued (audit_ide_machine_values state)
          (audit_ide_machine_probes_rev state))))
      | Some rule => exact_case 2145
          (exact_bind 2146 (ide_rule_with_bodies_counted (audit_ide_machine_values state) rule) (fun
            derived =>
          exact_bind 2147 (ide_update_with_bodies_counted rule (audit_ide_machine_values state)
            derived)
            (fun update => let '(values,probe) := update in
          exact_bind 2148 (match audit_ide_probe_key probe, audit_ide_probe_changed probe with
            | Some dst,true => exact_case 2148
                (let found := Map.get Key dst (audit_ide_machine_incidence state) in
                exact_bind 2149 (ide_body_internal
                  (IdeMachineIncidenceRead dst (audit_ide_machine_incidence state) found) found)
                  (fun found => ide_enqueue_with_bodies_counted
                    (match found with
                    | Some xs => xs
                    | None => []
                    end) rest queued))
            | _,_ => exact_case 2150 (exact_return 2150 (rest,queued))
            end) (fun todo =>
          exact_return 2151 (Some (AuditIdeMachine (audit_ide_machine_rules state)
            (audit_ide_machine_table state) (audit_ide_machine_incidence state)
            (fst todo) (snd todo) values (probe :: audit_ide_machine_probes_rev state)))))))
      end)))
  end.

Fixpoint ide_loop_with_bodies_counted fuel (state : audit_ide_machine N D F)
    : exact_counted Call (audit_ide_machine N D F) :=
  match audit_ide_machine_pending state with
  | [] => exact_case 2160 (exact_return 2160 state)
  | _ => match fuel with
    | xH => exact_case 2161 (exact_bind 2161 (ide_step_with_bodies_counted state)
        (fun next => exact_return 2161 (match next with
        | Some next => next
        | None => state
        end)))
    | xO p => exact_case 2162 (exact_bind 2162 (ide_loop_with_bodies_counted p state)
        (ide_loop_with_bodies_counted p))
    | xI p => exact_case 2163 (exact_bind 2163 (ide_loop_with_bodies_counted p state) (fun middle =>
        exact_bind 2163 (ide_loop_with_bodies_counted p middle) (fun last =>
        exact_bind 2163 (ide_step_with_bodies_counted last)
          (fun next => exact_return 2163 (match next with
          | Some next => next
          | None => last
          end)))))
    end
  end.

(** A machine callback receipt matches the adapter invoked by its event. *)
Definition ide_machine_body_valid (pair : Call * list audit_external_frame) : Prop :=
  match fst pair with
  | IdeMachineCompose x y out => audit_external_body (ide_compose_adapter adapters) (x,y) out (snd
    pair)
  | IdeMachineJoin x y out => audit_external_body (ide_join_adapter adapters) (x,y) out (snd pair)
  | IdeMachineEqual x y out => audit_external_body (ide_equal_adapter adapters) (x,y) out (snd pair)
  | _ => False
  end.

Definition ide_machine_body_input_budget (pair : Call * list audit_external_frame) : nat :=
  match fst pair with
  | IdeMachineCompose x y _ => external_input_budget (ide_compose_adapter adapters) (x,y)
  | IdeMachineJoin x y _ => external_input_budget (ide_join_adapter adapters) (x,y)
  | IdeMachineEqual x y _ => external_input_budget (ide_equal_adapter adapters) (x,y)
  | _ => 0
  end.

(** The counted loop retains valid callback bodies whose total work is bounded by their budgets. *)
Definition audit_ide_machine_with_bodies_statement : Prop :=
  audit_ide_registry_adapter_laws adapters -> forall fuel state,
  let run := ide_loop_with_bodies_counted fuel state in
  exact_value run = fst (audit_ide_loop_counted EN ED r fuel state) /\
  Forall ide_machine_body_valid (exact_bodies run) /\
  fold_right (fun body rest => audit_external_trace_work (snd body) + rest) 0 (exact_bodies run) <=
    fold_right (fun body rest => ide_machine_body_input_budget body + rest) 0 (exact_bodies run).

End Bodies.

(** * Whole generated IDE source execution with genuine callback bodies

    Card: AUD-IDE-GEN. Base encoder allowances come from their individual certified input
    budgets; internal derived encoders have the fixed library composition duties. Dictionary
    and weight callbacks execute their counted adapters once and retain actual body receipts. *)
Section GeneratedBodies.

Context {N P D A F : Type} (EN : encoding N) (EP : encoding P) (ED : encoding D)
  (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
  (weight : ip_edge N P D -> option D -> option D -> F)
  (encoders : audit_ide_graph_encoding_adapters EN EP ED)
  (dictionary : audit_ide_registry_adapters r) (weighted : audit_ide_weight_adapter weight).

Let nb := external_input_budget (ide_node_encoding_adapter encoders).

Let pb := external_input_budget (ide_site_encoding_adapter encoders).

Let db := external_input_budget (ide_fact_encoding_adapter encoders).

Let Call := ide_generated_source_call N P D A F.

Definition ide_generate_arcs_with_bodies_counted : exact_counted Call (list (audit_ide_arc N P D F))
  :=
  exact_flat_map 2200 (fun edge => exact_map 2201 (fun pair =>
    let '(x,y) := pair in
    exact_bind 2202 (exact_external_call weighted (edge,(x,y))
      (fun out => IdeSourceWeight edge x y out)) (fun out =>
    exact_return 2203 (AuditIdeArc (ip_action edge) (ip_source edge,x) (ip_target edge,y) out)))
      (ip_pairs edge)) (ip_edges q).

Definition ide_generated_with_bodies_counted start seed
    : exact_counted Call (ide_registry_summary N D F) :=
  exact_bind 2210 (ide_source_vertices (A:=A) (F:=F) q) (fun vertices =>
  exact_bind 2211 ide_generate_arcs_with_bodies_counted (fun arcs =>
  let '(index,index_events) := audit_ide_generate_index_counted EP arcs in
  exact_bind 2212 (exact_call (IdeSourceGenerator index_events)
    (ide_generator_source_work EP pb index_events) index) (fun index =>
  let '(matches,match_events) := audit_ide_generate_matches_counted EP index arcs in
  exact_bind 2213 (exact_call (IdeSourceGenerator match_events)
    (ide_generator_source_work EP pb match_events) matches) (fun matches =>
  exact_bind 2214 (ide_source_rows r vertices arcs matches (start,seed)) (fun rules =>
  exact_bind 2215 (ide_source_keys (A:=A) (F:=F) q) (fun keys =>
  let '(initial,initial_events) := audit_ide_initial_counted EN ED rules in
  exact_bind 2216 (exact_call (IdeSourceInitial initial_events)
    (ide_initial_source_work EN ED nb db initial_events) initial) (fun initial =>
  let fuel := audit_ide_machine_fuel r keys rules in
  exact_bind 2217 (exact_call (IdeSourceFuel (length rules) (length keys) (audit_ide_bound r) fuel)
    (1024 + audit_ide_fuel_model r keys rules) fuel) (fun fuel =>
  exact_bind 2218 (exact_lift (fun call => IdeSourceMachine [call])
    (ide_loop_with_bodies_counted EN ED r dictionary nb db fuel initial)) (fun final =>
  exact_bind 2219 (exact_rev 2219 (audit_ide_machine_probes_rev final)) (fun probes =>
    exact_return 2220 (IdeRegistrySummary (audit_ide_machine_values final) probes))))))))))).

Definition ide_generated_query_with_bodies_counted summary initial n d
    : exact_counted Call (option A) :=
  exact_bind 2230 (exact_get IdeSourceFact (IpTab.fact_encoding EN ED)
    (ide_fact_body EN ED nb db) (inr (n,d)) (ide_registry_summary_map summary)) (fun found =>
  match found with
  | None => exact_case 2231 (exact_return 2231 None)
  | Some f => exact_case 2232
      (exact_bind 2233 (exact_external_call (ide_eval_adapter dictionary) (f,initial)
        (fun out => IdeSourceEval f initial out)) (fun out => exact_return 2234 (Some out)))
  end).

(** A generated callback receipt matches its actual external adapter. *)
Definition ide_generated_external_body_valid (body : Call * list audit_external_frame) : Prop :=
  match fst body with
  | IdeSourceWeight edge x y out => audit_external_body weighted (edge,(x,y)) out (snd body)
  | IdeSourceEval f x out => audit_external_body (ide_eval_adapter dictionary) (f,x) out (snd body)
  | IdeSourceMachine [IdeMachineCompose x y out] =>
      audit_external_body (ide_compose_adapter dictionary) (x,y) out (snd body)
  | IdeSourceMachine [IdeMachineJoin x y out] =>
      audit_external_body (ide_join_adapter dictionary) (x,y) out (snd body)
  | IdeSourceMachine [IdeMachineEqual x y out] =>
      audit_external_body (ide_equal_adapter dictionary) (x,y) out (snd body)
  | _ => False
  end.

Definition ide_generated_external_body_budget (body : Call * list audit_external_frame) : nat :=
  match fst body with
  | IdeSourceWeight edge x y _ => external_input_budget weighted (edge,(x,y))
  | IdeSourceEval f x _ => external_input_budget (ide_eval_adapter dictionary) (f,x)
  | IdeSourceMachine [IdeMachineCompose x y _] => external_input_budget (ide_compose_adapter
    dictionary) (x,y)
  | IdeSourceMachine [IdeMachineJoin x y _] => external_input_budget (ide_join_adapter dictionary)
    (x,y)
  | IdeSourceMachine [IdeMachineEqual x y _] => external_input_budget (ide_equal_adapter dictionary)
    (x,y)
  | _ => 0
  end.

Definition ide_generated_external_allowance bodies :=
  fold_right (fun body rest => ide_generated_external_body_budget body + rest) 0 bodies.

(** The generated run retains valid callbacks and their allowances. *)
Definition audit_ide_generated_with_bodies_statement : Prop :=
  audit_ide_graph_encoding_laws encoders -> audit_ide_registry_adapter_laws dictionary ->
  audit_external_adapter_laws weighted -> forall start seed,
    ide_registry_laws L r -> ip_problem_wf q -> In start (ip_nodes q) ->
    (match seed with
    | None => True
    | Some d => In d (ip_facts q)
    end) ->
    let run := ide_generated_with_bodies_counted start seed in
    exact_value run = ide_registry_solve EN EP ED L r q weight start seed /\
    Forall ide_generated_external_body_valid (exact_bodies run) /\
    exact_units run <= 16 * ide_generated_source_budget EN EP ED r q weight nb pb db start seed +
      ide_generated_external_allowance (exact_bodies run).

(** The generated query preserves the result, validates recorded bodies and charges their
    budgets. *)
Definition audit_ide_generated_query_with_bodies_statement : Prop :=
  audit_ide_graph_encoding_laws encoders -> audit_ide_registry_adapter_laws dictionary ->
  forall summary initial n d,
    let run := ide_generated_query_with_bodies_counted summary initial n d in
    exact_value run = ide_registry_query EN ED r summary initial n d /\
    Forall ide_generated_external_body_valid (exact_bodies run) /\
    exact_units run <= (Nat.of_num_uint 8192%uint) + 4 * ide_fact_body EN ED nb db (inr (n,d)) +
      1024 * Pos.size_nat (encode (IpTab.fact_encoding EN ED) (inr (n,d))) +
      ide_generated_external_allowance (exact_bodies run).

End GeneratedBodies.
