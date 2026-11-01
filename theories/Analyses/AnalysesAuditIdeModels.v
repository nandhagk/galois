(** * Concrete IDE generator and machine models

    Records generated rules, indexed machine steps and compatibility checks.
    For example, a generated internal edge retains its source and target in an arc.
    Builds on: AnalysesAuditIdeBase, AnalysesAuditSource and CollectionsMap. *)

From Stdlib Require Import Arith Bool Lia List NArith PArith ZArith.
From Galois.Analyses Require Export AnalysesAuditIdeBase AnalysesAuditSource.
From Galois.Analyses Require Import AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditPrimitive CollectionsAuditTrie
  CollectionsAuditUnion CollectionsEncoding CollectionsFinSet CollectionsMap.
From Galois.Fixpoint Require Import FixpointIndex.
From Galois.Order Require Import OrderLattice.
Import List.ListNotations.

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-generator-model.md *)
(** Generator events retain input edges, indexed lookups and writes, matches and emitted rules. *)
Inductive audit_ide_generator_call (N P D F : Type) : Type :=
  | IdeGeneratorCase (site : nat)
  | IdeGeneratorEdge (edge : ip_edge N P D)
  | IdeGeneratorWeight (edge : ip_edge N P D) (source target : option D) (result : F)
  | IdeGeneratorIndexGet (kind : ip_kind P)
      (before : Map.t (ip_kind P) (list (audit_ide_arc N P D F)))
      (result : option (list (audit_ide_arc N P D F)))
  | IdeGeneratorIndexSet (kind : ip_kind P)
      (before after : Map.t (ip_kind P) (list (audit_ide_arc N P D F)))
  | IdeGeneratorMatch (call ret : audit_ide_arc N P D F)
  | IdeGeneratorRule (rule : audit_ide_rule N D F).

Arguments IdeGeneratorCase {N P D F} _.

Arguments IdeGeneratorEdge {N P D F} _.

Arguments IdeGeneratorWeight {N P D F} _ _ _ _.

Arguments IdeGeneratorIndexGet {N P D F} _ _ _.

Arguments IdeGeneratorIndexSet {N P D F} _ _ _.

Arguments IdeGeneratorMatch {N P D F} _ _.

Arguments IdeGeneratorRule {N P D F} _.

Fixpoint audit_ide_generate_pairs_counted {N P D F}
    (weight : ip_edge N P D -> option D -> option D -> F) (edge : ip_edge N P D)
    (pairs : list (option D * option D))
    : list (audit_ide_arc N P D F) * list (audit_ide_generator_call N P D F) :=
  match pairs with
  | [] => ([], [IdeGeneratorCase 0])
  | (source, target) :: rest =>
      let value := weight edge source target in
      let arc := AuditIdeArc (ip_action edge) (ip_source edge, source) (ip_target edge, target)
        value in
      let '(later, events) := audit_ide_generate_pairs_counted weight edge rest in
      (arc :: later, IdeGeneratorCase 1 :: IdeGeneratorWeight edge source target value :: events)
  end.

Fixpoint audit_ide_generate_arcs_counted {N P D F}
    (weight : ip_edge N P D -> option D -> option D -> F) (edges : list (ip_edge N P D))
    : list (audit_ide_arc N P D F) * list (audit_ide_generator_call N P D F) :=
  match edges with
  | [] => ([], [IdeGeneratorCase 2])
  | edge :: rest =>
      let '(arcs, pair_events) := audit_ide_generate_pairs_counted weight edge (ip_pairs edge) in
      let '(later, tail_events) := audit_ide_generate_arcs_counted weight rest in
      (arcs ++ later, IdeGeneratorCase 3 :: IdeGeneratorEdge edge :: pair_events ++ tail_events)
  end.

Fixpoint audit_ide_generate_index_counted {N P D F} (EP : encoding P)
    (arcs : list (audit_ide_arc N P D F))
    : Map.t (ip_kind P) (list (audit_ide_arc N P D F)) * list (audit_ide_generator_call N P D F) :=
  match arcs with
  | [] => (Map.empty, [IdeGeneratorCase 4])
  | arc :: rest =>
      let '(before, tail_events) := audit_ide_generate_index_counted EP rest in
      let kind := audit_ide_arc_kind arc in
      let found := Map.get (IpTab.kind_encoding EP) kind before in
      let row := match found with
      | Some xs => xs
      | None => []
      end in
      let after := Map.set (IpTab.kind_encoding EP) kind (arc :: row) before in
      (after, IdeGeneratorCase 5 :: tail_events ++
        [IdeGeneratorIndexGet kind before found; IdeGeneratorIndexSet kind before after])
  end.

Fixpoint audit_ide_generate_matches_counted {N P D F} (EP : encoding P)
    (index : Map.t (ip_kind P) (list (audit_ide_arc N P D F)))
    (arcs : list (audit_ide_arc N P D F))
    : list (audit_ide_arc N P D F * audit_ide_arc N P D F) *
      list (audit_ide_generator_call N P D F) :=
  match arcs with
  | [] => ([], [IdeGeneratorCase 6])
  | call :: rest =>
      match audit_ide_arc_kind call with
      | IpCall site =>
          let kind := IpReturn site in
          let found := Map.get (IpTab.kind_encoding EP) kind index in
          let returns := match found with
          | Some xs => xs
          | None => []
          end in
          let pairs := map (fun ret => (call, ret)) returns in
          let match_calls := map (fun ret => IdeGeneratorMatch call ret) returns in
          let '(later, events) := audit_ide_generate_matches_counted EP index rest in
          (pairs ++ later,
            IdeGeneratorCase 7 :: IdeGeneratorIndexGet kind index found ::
              match_calls ++ events)
      | _ =>
          let '(later, events) := audit_ide_generate_matches_counted EP index rest in
          (later, IdeGeneratorCase 8 :: events)
      end
  end.

Definition audit_ide_indexed_rows {N P D A F} (r : audit_ide_registry A F)
    (vertices : list (IpTab.vertex N D)) (arcs : list (audit_ide_arc N P D F))
    (matches : list (audit_ide_arc N P D F * audit_ide_arc N P D F))
    (root : IpTab.vertex N D) : list (audit_ide_rule N D F) :=
  AuditIdeSeed (inr root) (audit_ide_id r) ::
  map (fun v => AuditIdeSeed (inl (v, v)) (audit_ide_id r)) vertices ++
  flat_map (fun arc => match audit_ide_arc_kind arc with
    | IpInternal => map (fun a => AuditIdeUnary (inl (a, audit_ide_arc_from arc))
        (inl (a, audit_ide_arc_to arc)) (audit_ide_arc_weight arc)) vertices
    | _ => []
    end) arcs ++
  flat_map (fun pair => let '(call, ret) := pair in
    map (fun a => AuditIdeBinary (inl (a, audit_ide_arc_from call))
      (inl (audit_ide_arc_to call, audit_ide_arc_from ret))
      (inl (a, audit_ide_arc_to ret)) (audit_ide_arc_weight call)
      (audit_ide_arc_weight ret)) vertices) matches ++
  flat_map (fun u => map (fun v => AuditIdeBinary (inr u) (inl (u, v)) (inr v)
    (audit_ide_id r) (audit_ide_id r)) vertices) vertices ++
  flat_map (fun call => match audit_ide_arc_kind call with
    | IpCall _ => [AuditIdeUnary (inr (audit_ide_arc_from call))
        (inr (audit_ide_arc_to call)) (audit_ide_arc_weight call)]
    | _ => []
    end) arcs.

Definition audit_ide_generator_counted {N P D A F} (EP : encoding P)
    (r : audit_ide_registry A F) (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F) (root : IpTab.vertex N D)
    : list (audit_ide_rule N D F) * list (audit_ide_generator_call N P D F) :=
  let vertices := IpTab.vertices q in
  let '(arcs, arc_events) := audit_ide_generate_arcs_counted weight (ip_edges q) in
  let '(index, index_events) := audit_ide_generate_index_counted EP arcs in
  let '(matches, match_events) := audit_ide_generate_matches_counted EP index arcs in
  let rules := audit_ide_indexed_rows r vertices arcs matches root in
  (rules, arc_events ++ index_events ++ match_events ++ map IdeGeneratorRule rules).

Definition audit_ide_generator_model_event {N P D F} (EP : encoding P)
    (event : audit_ide_generator_call N P D F) : nat :=
  let EK := IpTab.kind_encoding EP in
  let emission code := audit_encoding_weight (audit_key_bits_weight code) in
  64 + match event with
  | IdeGeneratorIndexGet kind _ _ => audit_get_weight (encode EK kind) + emission (encode EK kind)
  | IdeGeneratorIndexSet kind _ _ => audit_set_weight (encode EK kind) + emission (encode EK kind)
  | _ => 0
  end.

Definition audit_ide_generator_model_work {N P D F} (EP : encoding P)
    (events : list (audit_ide_generator_call N P D F)) : nat :=
  64 * S (length events) * S (length events) +
  fold_right (fun event n => audit_ide_generator_model_event EP event + n) 0 events.

Definition audit_ide_generator_model_budget {N P D F} (EP : encoding P)
    (events : list (audit_ide_generator_call N P D F)) : nat :=
  64 * S (length events) * S (length events) + 64 * length events + fold_right
    (fun event n => (audit_ide_generator_model_event EP event - 64) + n) 0 events.

Definition audit_ide_generator_input_width {N P D} (EP : encoding P) (q : ip_problem N P D) : nat :=
  fold_right (fun edge width =>
    let action := ip_action edge in
    let action_width := audit_key_bits_weight (encode (IpTab.kind_encoding EP) action) in
    let return_width := match action with
      | IpCall site => audit_key_bits_weight (encode (IpTab.kind_encoding EP) (IpReturn site))
      | _ => 0
      end in
    Nat.max action_width (Nat.max return_width width)) 0 (ip_edges q).

Definition audit_ide_generator_input_budget {N P D} (EP : encoding P) (q : ip_problem N P D)
    : nat :=
  let bound := 16 * (1 + length (ip_edges q) + length (IpTab.vertices q) +
    audit_ide_arc_count q + audit_ide_matching_occurrences EP q + audit_ide_occurrence_rule_count EP
      q) in
  64 * S bound * S bound + bound * (66 + 3 * audit_ide_generator_input_width EP q).

(** Counted generation returns the reference rules and respects event budgets. *)
Definition audit_ide_generator_counted_statement : Prop :=
  forall N P D A F (EP : encoding P) (r : audit_ide_registry A F)
      (q : ip_problem N P D) weight root,
    let '(rules, events) := audit_ide_generator_counted EP r q weight root in
    rules = audit_ide_rule_spec EP r q weight root /\
    length events <= 16 * (1 + length (ip_edges q) + length (IpTab.vertices q) +
      audit_ide_arc_count q + audit_ide_matching_occurrences EP q + length rules) /\
    audit_ide_generator_model_work EP events <= audit_ide_generator_model_budget EP events /\
    audit_ide_generator_model_work EP events <= audit_ide_generator_input_budget EP q /\
    64 * length events <= audit_ide_generator_model_work EP events.

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-initial-model.md *)
(** Initialization events retain sequence construction and table, index and queue updates. *)
Inductive audit_ide_initial_call (N D F : Type) : Type :=
  | IdeInitCase (site : nat)
  | IdeInitSeq (site count : nat) (result : list nat)
  | IdeInitTableSet (id : nat) (rule : audit_ide_rule N D F)
      (before after : Map.t nat (audit_ide_rule N D F))
  | IdeInitIndexGet (id : nat) (key : IpTab.fact N D)
      (before : Map.t (IpTab.fact N D) (list nat)) (result : option (list nat))
  | IdeInitIndexSet (id : nat) (key : IpTab.fact N D)
      (before after : Map.t (IpTab.fact N D) (list nat))
  | IdeInitQueueAdd (id : nat) (before after : FinSet.t nat).

Arguments IdeInitCase {N D F} _.

Arguments IdeInitSeq {N D F} _ _ _.

Arguments IdeInitTableSet {N D F} _ _ _ _.

Arguments IdeInitIndexGet {N D F} _ _ _ _.

Arguments IdeInitIndexSet {N D F} _ _ _ _.

Arguments IdeInitQueueAdd {N D F} _ _ _.

Fixpoint audit_ide_initial_table_counted {N D F}
    (rows : list (nat * audit_ide_rule N D F)) (state : Map.t nat (audit_ide_rule N D F))
    : Map.t nat (audit_ide_rule N D F) * list (audit_ide_initial_call N D F) :=
  match rows with
  | [] => (state, [IdeInitCase 0])
  | (id, rule) :: rest =>
      let next := Map.set nat_encoding id rule state in
      let '(result, events) := audit_ide_initial_table_counted rest next in
      (result, IdeInitCase 1 :: IdeInitTableSet id rule state next :: events)
  end.

Fixpoint audit_ide_initial_keys_counted {N D F} (EN : encoding N) (ED : encoding D)
    (id : nat) (keys : list (IpTab.fact N D)) (state : Map.t (IpTab.fact N D) (list nat))
    : Map.t (IpTab.fact N D) (list nat) * list (audit_ide_initial_call N D F) :=
  match keys with
  | [] => (state, [IdeInitCase 2])
  | key :: rest =>
      let '(middle, tail_events) := @audit_ide_initial_keys_counted N D F EN ED id rest state in
      let found := Map.get (IpTab.fact_encoding EN ED) key middle in
      let row := match found with
      | Some ids => ids
      | None => []
      end in
      let next := Map.set (IpTab.fact_encoding EN ED) key (id :: row) middle in
      (next, IdeInitCase 3 :: tail_events ++
        [IdeInitIndexGet id key middle found; IdeInitIndexSet id key middle next])
  end.

Fixpoint audit_ide_initial_index_counted {N D F} (EN : encoding N) (ED : encoding D)
    (rows : list (nat * audit_ide_rule N D F)) (state : Map.t (IpTab.fact N D) (list nat))
    : Map.t (IpTab.fact N D) (list nat) * list (audit_ide_initial_call N D F) :=
  match rows with
  | [] => (state, [IdeInitCase 4])
  | (id, rule) :: rest =>
      let '(middle, tail_events) := audit_ide_initial_index_counted EN ED rest state in
      let '(next, key_events) := @audit_ide_initial_keys_counted N D F EN ED id
        (audit_ide_rule_sources rule) middle in
      (next, IdeInitCase 5 :: tail_events ++ key_events)
  end.

Fixpoint audit_ide_initial_pending_counted {N D F} (ids : list nat) (state : FinSet.t nat)
    : FinSet.t nat * list (audit_ide_initial_call N D F) :=
  match ids with
  | [] => (state, [IdeInitCase 6])
  | id :: rest =>
      let next := FinSet.add nat_encoding id state in
      let '(result, events) := @audit_ide_initial_pending_counted N D F rest next in
      (result, IdeInitCase 7 :: IdeInitQueueAdd id state next :: events)
  end.

Definition audit_ide_initial_counted {N D F} (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F))
    : audit_ide_machine N D F * list (audit_ide_initial_call N D F) :=
  let count := length rules in
  let ids := seq 0 count in
  let table_ids := seq 0 (length rules) in
  let '(table, table_events) := audit_ide_initial_table_counted (combine table_ids rules) Map.empty
    in
  let index_ids := seq 0 (length rules) in
  let '(index, index_events) := audit_ide_initial_index_counted EN ED (combine index_ids rules)
    Map.empty in
  let '(queued, queue_events) := @audit_ide_initial_pending_counted N D F ids FinSet.empty in
  (AuditIdeMachine rules table index ids queued Map.empty [],
    IdeInitSeq 0 count ids :: IdeInitSeq 1 count table_ids :: table_events ++
    IdeInitSeq 2 count index_ids :: index_events ++ queue_events).

Definition audit_ide_initial_model_event {N D F} (EN : encoding N) (ED : encoding D)
    (event : audit_ide_initial_call N D F) : nat :=
  let fact_key := IpTab.fact_encoding EN ED in
  let emission code := audit_encoding_weight (audit_key_bits_weight code) in
  let nat_work id := audit_unary_conversion_weight id + id * audit_key_bits_weight (encode
    nat_encoding id) in
  64 + match event with
  | IdeInitSeq _ count _ => 1 + count
  | IdeInitTableSet id _ _ _ | IdeInitQueueAdd id _ _ =>
      audit_set_weight (encode nat_encoding id) + emission (encode nat_encoding id) + nat_work id
  | IdeInitIndexGet _ key _ _ => audit_get_weight (encode fact_key key) + emission (encode fact_key
    key)
  | IdeInitIndexSet _ key _ _ => audit_set_weight (encode fact_key key) + emission (encode fact_key
    key)
  | _ => 0
  end.

Definition audit_ide_initial_model_work {N D F} (EN : encoding N) (ED : encoding D)
    (events : list (audit_ide_initial_call N D F)) : nat :=
  64 * S (length events) * S (length events) +
  fold_right (fun event n => audit_ide_initial_model_event EN ED event + n) 0 events.

Definition audit_ide_initial_model_budget {N D F} (EN : encoding N) (ED : encoding D)
    (events : list (audit_ide_initial_call N D F)) : nat :=
  64 * S (length events) * S (length events) + 64 * length events +
    fold_right (fun event n => (audit_ide_initial_model_event EN ED event - 64) + n) 0 events.

Definition audit_ide_initial_fact_width {N D F} (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F)) : nat :=
  fold_right Nat.max 0 (map (fun key => audit_key_bits_weight (encode (IpTab.fact_encoding EN ED)
    key))
    (flat_map audit_ide_rule_keys rules)).

Definition audit_ide_initial_input_budget {N D F} (EN : encoding N) (ED : encoding D)
    (rules : list (audit_ide_rule N D F)) : nat :=
  let count := length rules in
  let event_bound := 20 + 16 * count in
  let nat_width := audit_key_bits_weight (encode nat_encoding count) in
  let width := Nat.max nat_width (audit_ide_initial_fact_width EN ED rules) in
  64 * S event_bound * S event_bound +
    event_bound * (66 + 3 * width + 2 * S count + count * nat_width).

(** Counted initialization returns the original state and respects event budgets. *)
Definition audit_ide_initial_counted_statement : Prop :=
  forall N D F (EN : encoding N) (ED : encoding D) (rules : list (audit_ide_rule N D F)),
    let '(result, events) := audit_ide_initial_counted EN ED rules in
    result = audit_ide_machine_initial EN ED rules /\
    length events <= 20 + 16 * length rules /\
    audit_ide_initial_model_work EN ED events <= audit_ide_initial_model_budget EN ED events /\
    audit_ide_initial_model_work EN ED events <= audit_ide_initial_input_budget EN ED rules /\
    64 * length events <= audit_ide_initial_model_work EN ED events.

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-machine-model.md *)
(** Machine events retain actual map, queue, incidence and transformer operation operands. *)
Inductive audit_ide_machine_call (N D F : Type) : Type :=
  | IdeMachineCase (site : nat)
  | IdeMachineRuleRead (id : nat) (table : Map.t nat (audit_ide_rule N D F))
      (answer : option (audit_ide_rule N D F))
  | IdeMachineFactRead (key : IpTab.fact N D) (state : Map.t (IpTab.fact N D) F)
      (answer : option F)
  | IdeMachineFactWrite (key : IpTab.fact N D) (value : F)
      (before after : Map.t (IpTab.fact N D) F)
  | IdeMachineQueueRemove (id : nat) (before after : FinSet.t nat)
  | IdeMachineQueueMember (id : nat) (before : FinSet.t nat) (answer : bool)
  | IdeMachineQueueAdd (id : nat) (before after : FinSet.t nat)
  | IdeMachineIncidenceRead (key : IpTab.fact N D)
      (index : Map.t (IpTab.fact N D) (list nat)) (answer : option (list nat))
  | IdeMachineCompose (first second result : F)
  | IdeMachineJoin (first second result : F)
  | IdeMachineEqual (first second : F) (result : bool).

Arguments IdeMachineCase {N D F} _.

Arguments IdeMachineRuleRead {N D F} _ _ _.

Arguments IdeMachineFactRead {N D F} _ _ _.

Arguments IdeMachineFactWrite {N D F} _ _ _ _.

Arguments IdeMachineQueueRemove {N D F} _ _ _.

Arguments IdeMachineQueueMember {N D F} _ _ _.

Arguments IdeMachineQueueAdd {N D F} _ _ _.

Arguments IdeMachineIncidenceRead {N D F} _ _ _.

Arguments IdeMachineCompose {N D F} _ _ _.

Arguments IdeMachineJoin {N D F} _ _ _.

Arguments IdeMachineEqual {N D F} _ _ _.

Definition audit_ide_rule_counted {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (state : Map.t (IpTab.fact N D) F)
    (rule : audit_ide_rule N D F)
    : option (IpTab.fact N D * F) * list (audit_ide_machine_call N D F) :=
  let key := IpTab.fact_encoding EN ED in
  match rule with
  | AuditIdeSeed dst value => (Some (dst, value), [IdeMachineCase 0])
  | AuditIdeUnary source dst suffix =>
      let found := Map.get key source state in
      match found with
      | None => (None, [IdeMachineCase 1; IdeMachineFactRead source state found])
      | Some value =>
          let output := audit_ide_compose r value suffix in
          (Some (dst, output), [IdeMachineCase 2; IdeMachineFactRead source state found;
              IdeMachineCompose value suffix output])
      end
  | AuditIdeBinary first second dst between after =>
      let left := Map.get key first state in
      match left with
      | None => (None, [IdeMachineCase 3; IdeMachineFactRead first state left])
      | Some a =>
          let right := Map.get key second state in
          match right with
          | None => (None, [IdeMachineCase 4; IdeMachineFactRead first state left;
              IdeMachineFactRead second state right])
          | Some b =>
              let one := audit_ide_compose r a between in
              let two := audit_ide_compose r one b in
              let three := audit_ide_compose r two after in
              (Some (dst, three), [IdeMachineCase 5; IdeMachineFactRead first state left;
                IdeMachineFactRead second state right; IdeMachineCompose a between one;
                IdeMachineCompose one b two; IdeMachineCompose two after three])
          end
      end
  end.

Fixpoint audit_ide_enqueue_counted {N D F} (ids : list nat) (pending : list nat)
    (queued : FinSet.t nat) : (list nat * FinSet.t nat) * list (audit_ide_machine_call N D F) :=
  match ids with
  | [] => ((pending, queued), [IdeMachineCase 6])
  | id :: rest =>
      let present := FinSet.mem nat_encoding id queued in
      if present then
        let '(result, events) := audit_ide_enqueue_counted rest pending queued in
        (result, IdeMachineCase 7 :: IdeMachineQueueMember id queued present :: events)
      else
        let next := FinSet.add nat_encoding id queued in
        let '(result, events) := audit_ide_enqueue_counted rest (id :: pending) next in
        (result, IdeMachineCase 8 :: IdeMachineQueueMember id queued present ::
          IdeMachineQueueAdd id queued next :: events)
  end.

Definition audit_ide_step_counted {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (st : audit_ide_machine N D F)
    : option (audit_ide_machine N D F) * list (audit_ide_machine_call N D F) :=
  match audit_ide_machine_pending st with
  | [] => (None, [IdeMachineCase 9])
  | id :: rest =>
      let queued := FinSet.remove nat_encoding id (audit_ide_machine_queued st) in
      let rule := Map.get nat_encoding id (audit_ide_machine_table st) in
      let prefix := [IdeMachineCase 10;
        IdeMachineQueueRemove id (audit_ide_machine_queued st) queued;
        IdeMachineRuleRead id (audit_ide_machine_table st) rule] in
      match rule with
      | None =>
          (Some (AuditIdeMachine (audit_ide_machine_rules st) (audit_ide_machine_table st)
            (audit_ide_machine_incidence st) rest queued (audit_ide_machine_values st)
            (audit_ide_machine_probes_rev st)), prefix ++ [IdeMachineCase 11])
      | Some rule_value =>
          let key := IpTab.fact_encoding EN ED in
          let values := audit_ide_machine_values st in
          let '(derived, rule_events) := audit_ide_rule_counted EN ED r values rule_value in
          let '(next_values, probe, update_events) :=
            match derived with
            | None => (values, AuditIdeProbe rule_value None false false, [IdeMachineCase 12])
            | Some (dst, incoming) =>
                let old := Map.get key dst values in
                match old with
                | None =>
                    let new_values := Map.set key dst incoming values in
                    (new_values, AuditIdeProbe rule_value (Some dst) true false,
                      [IdeMachineCase 13; IdeMachineFactRead dst values old;
                      IdeMachineFactWrite dst incoming values new_values])
                | Some previous =>
                    let joined := audit_ide_join r previous incoming in
                    let equal := audit_ide_equal r joined previous in
                    if equal then
                      (values, AuditIdeProbe rule_value (Some dst) false true,
                        [IdeMachineCase 14; IdeMachineFactRead dst values old;
                        IdeMachineJoin previous incoming joined; IdeMachineEqual joined previous
                          equal])
                    else
                      let new_values := Map.set key dst joined values in
                      (new_values, AuditIdeProbe rule_value (Some dst) true true,
                        [IdeMachineCase 15; IdeMachineFactRead dst values old;
                        IdeMachineJoin previous incoming joined; IdeMachineEqual joined previous
                          equal;
                        IdeMachineFactWrite dst joined values new_values])
                end
            end in
          let '(todo, seen, enqueue_events) :=
            match audit_ide_probe_key probe, audit_ide_probe_changed probe with
            | Some dst, true =>
                let lookup := Map.get key dst (audit_ide_machine_incidence st) in
                let ids := match lookup with
                | Some xs => xs
                | None => []
                end in
                let '(result, events) := audit_ide_enqueue_counted ids rest queued in
                (fst result, snd result,
                  IdeMachineIncidenceRead dst (audit_ide_machine_incidence st) lookup :: events)
            | _, _ => (rest, queued, [IdeMachineCase 16])
            end in
          (Some (AuditIdeMachine (audit_ide_machine_rules st) (audit_ide_machine_table st)
            (audit_ide_machine_incidence st) todo seen next_values
            (probe :: audit_ide_machine_probes_rev st)),
            prefix ++ rule_events ++ update_events ++ enqueue_events)
      end
  end.

Fixpoint audit_ide_loop_counted {N D A F} (EN : encoding N) (ED : encoding D)
    (r : audit_ide_registry A F) (fuel : positive) (st : audit_ide_machine N D F)
    : audit_ide_machine N D F * list (audit_ide_machine_call N D F) :=
  match audit_ide_machine_pending st with
  | [] => (st, [IdeMachineCase 17])
  | _ => match fuel with
    | xH => let '(result, events) := audit_ide_step_counted EN ED r st in
        (match result with
        | Some next => next
        | None => st
        end, IdeMachineCase 18 :: events)
    | xO p => let '(middle, first_events) := audit_ide_loop_counted EN ED r p st in
        let '(result, second_events) := audit_ide_loop_counted EN ED r p middle in
        (result, IdeMachineCase 19 :: first_events ++ second_events)
    | xI p => let '(middle, first_events) := audit_ide_loop_counted EN ED r p st in
        let '(last, second_events) := audit_ide_loop_counted EN ED r p middle in
        let '(result, step_events) := audit_ide_step_counted EN ED r last in
        (match result with
        | Some next => next
        | None => last
        end,
          IdeMachineCase 20 :: first_events ++ second_events ++ step_events)
    end
  end.

Definition audit_ide_machine_model_event {N D F} (EN : encoding N) (ED : encoding D)
    (event : audit_ide_machine_call N D F) : nat :=
  let fact_key := IpTab.fact_encoding EN ED in
  let emission code := audit_encoding_weight (audit_key_bits_weight code) in
  let nat_work id := audit_unary_conversion_weight id +
    id * audit_key_bits_weight (encode nat_encoding id) in
  64 + match event with
  | IdeMachineRuleRead id _ _ | IdeMachineQueueMember id _ _ =>
      audit_get_weight (encode nat_encoding id) + emission (encode nat_encoding id) + nat_work id
  | IdeMachineQueueRemove id _ _ =>
      audit_remove_weight (encode nat_encoding id) + emission (encode nat_encoding id) + nat_work id
  | IdeMachineQueueAdd id _ _ =>
      audit_set_weight (encode nat_encoding id) + emission (encode nat_encoding id) + nat_work id
  | IdeMachineFactRead key _ _ | IdeMachineIncidenceRead key _ _ =>
      audit_get_weight (encode fact_key key) + emission (encode fact_key key)
  | IdeMachineFactWrite key _ _ _ =>
      audit_set_weight (encode fact_key key) + emission (encode fact_key key)
  | _ => 0
  end.

Definition audit_ide_machine_model_work {N D F} (EN : encoding N) (ED : encoding D)
    (events : list (audit_ide_machine_call N D F)) : nat :=
  64 * S (length events) * S (length events) +
  fold_right (fun event n => audit_ide_machine_model_event EN ED event + n) 0 events.

Definition audit_ide_machine_model_budget {N D F} (EN : encoding N) (ED : encoding D)
    (events : list (audit_ide_machine_call N D F)) : nat :=
  64 * S (length events) * S (length events) + 64 * length events +
    fold_right (fun event n => (audit_ide_machine_model_event EN ED event - 64) + n) 0 events.

Definition audit_ide_incidence_size {N D F} (state : audit_ide_machine N D F) : nat :=
  fold_right (fun row n => length (snd row) + n) 0
    (Map.elements (audit_ide_machine_incidence state)).

Definition audit_ide_machine_nat_keys {N D F} (state : audit_ide_machine N D F) : list nat :=
  audit_ide_machine_pending state ++ FinSet.elements (audit_ide_machine_queued state) ++
  map fst (Map.elements (audit_ide_machine_table state)) ++
  flat_map snd (Map.elements (audit_ide_machine_incidence state)).

Definition audit_ide_machine_fact_keys {N D F} (state : audit_ide_machine N D F)
    : list (IpTab.fact N D) :=
  flat_map (fun row => audit_ide_rule_keys (snd row)) (Map.elements (audit_ide_machine_table state))
    ++
  map fst (Map.elements (audit_ide_machine_values state)) ++
  map fst (Map.elements (audit_ide_machine_incidence state)).

Definition audit_ide_machine_nat_width {N D F} (state : audit_ide_machine N D F) : nat :=
  fold_right Nat.max 0 (map (fun id => audit_key_bits_weight (encode nat_encoding id))
    (audit_ide_machine_nat_keys state)).

Definition audit_ide_machine_fact_width {N D F} (EN : encoding N) (ED : encoding D)
    (state : audit_ide_machine N D F) : nat :=
  fold_right Nat.max 0 (map (fun key => audit_key_bits_weight (encode (IpTab.fact_encoding EN ED)
    key))
    (audit_ide_machine_fact_keys state)).

Definition audit_ide_machine_input_budget {N D F} (EN : encoding N) (ED : encoding D)
    (fuel : positive) (state : audit_ide_machine N D F) : nat :=
  let event_bound := (32 + 3 * audit_ide_incidence_size state) * (2 * Pos.to_nat fuel + 1) in
  let nat_max := fold_right Nat.max 0 (audit_ide_machine_nat_keys state) in
  let nat_width := audit_ide_machine_nat_width state in
  let width := Nat.max (audit_ide_machine_nat_width state) (audit_ide_machine_fact_width EN ED
    state) in
  64 * S event_bound * S event_bound +
    event_bound * (66 + 3 * width + S nat_max + nat_max * nat_width).

(** The counted rule returns the same result as the plain rule. *)
Definition audit_ide_rule_counted_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F) state rule,
    fst (audit_ide_rule_counted EN ED r state rule) = audit_ide_rule_result EN ED r state rule.

(** Counted enqueue returns the same queue as plain enqueue. *)
Definition audit_ide_enqueue_counted_statement : Prop :=
  forall N D F ids pending queued,
    fst (@audit_ide_enqueue_counted N D F ids pending queued) = audit_ide_enqueue ids pending
      queued.

(** The counted scheduler step returns the plain step result. *)
Definition audit_ide_step_counted_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F) state,
    fst (audit_ide_step_counted EN ED r state) = audit_ide_machine_step EN ED r state.

(** The counted loop returns the plain loop result. *)
Definition audit_ide_loop_counted_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F) fuel state,
    fst (audit_ide_loop_counted EN ED r fuel state) = audit_ide_machine_loop EN ED r fuel state.

(** The counted loop records bounded events and returns the plain state. *)
Definition audit_ide_machine_model_bound_statement : Prop :=
  forall N D A F (EN : encoding N) (ED : encoding D) (r : audit_ide_registry A F) fuel state,
    let '(result, events) := audit_ide_loop_counted EN ED r fuel state in
    result = audit_ide_machine_loop EN ED r fuel state /\
    length events <= (32 + 3 * audit_ide_incidence_size state) * (2 * Pos.to_nat fuel + 1) /\
    audit_ide_machine_model_work EN ED events <= audit_ide_machine_model_budget EN ED events /\
    audit_ide_machine_model_work EN ED events <= audit_ide_machine_input_budget EN ED fuel state /\
    64 * length events <= audit_ide_machine_model_work EN ED events.

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-producer-model.md *)
(** The run stores generated rules, keys, machine states and each stage's event sequence. *)
Record audit_ide_generated_run (N P D F : Type) : Type := AuditIdeGeneratedRun {
  audit_ide_run_rules : list (audit_ide_rule N D F);
  audit_ide_run_keys : list (IpTab.fact N D);
  audit_ide_run_initial : audit_ide_machine N D F;
  audit_ide_run_final : audit_ide_machine N D F;
  audit_ide_run_generator_events : list (audit_ide_generator_call N P D F);
  audit_ide_run_initial_events : list (audit_ide_initial_call N D F);
  audit_ide_run_loop_events : list (audit_ide_machine_call N D F)
}.

Arguments AuditIdeGeneratedRun {N P D F}.

Arguments audit_ide_run_rules {N P D F}.

Arguments audit_ide_run_keys {N P D F}.

Arguments audit_ide_run_initial {N P D F}.

Arguments audit_ide_run_final {N P D F}.

Arguments audit_ide_run_generator_events {N P D F}.

Arguments audit_ide_run_initial_events {N P D F}.

Arguments audit_ide_run_loop_events {N P D F}.

Definition audit_ide_producer_counted {N P D A F} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D)
    (weight : ip_edge N P D -> option D -> option D -> F) (start : N) (seed : option D)
    : ide_registry_summary N D F * audit_ide_generated_run N P D F :=
  let '(rules, generator_events) := audit_ide_generator_counted EP r q weight (start, seed) in
  let keys := audit_ide_summary_keys q in
  let '(initial, initial_events) := audit_ide_initial_counted EN ED rules in
  let fuel := audit_ide_machine_fuel r keys rules in
  let '(final, loop_events) := audit_ide_loop_counted EN ED r fuel initial in
  (IdeRegistrySummary (audit_ide_machine_values final) (rev (audit_ide_machine_probes_rev final)),
    AuditIdeGeneratedRun rules keys initial final generator_events initial_events loop_events).

Definition audit_ide_generate_index_plain {N P D F} (EP : encoding P)
    (arcs : list (audit_ide_arc N P D F)) :=
  fold_right (fun arc index =>
    let kind := audit_ide_arc_kind arc in
    let row := match Map.get (IpTab.kind_encoding EP) kind index with
      | Some xs => xs
      | None => []
      end in
    Map.set (IpTab.kind_encoding EP) kind (arc :: row) index) Map.empty arcs.

Definition audit_ide_generate_matches_plain {N P D F} (EP : encoding P)
    (index : Map.t (ip_kind P) (list (audit_ide_arc N P D F)))
    (arcs : list (audit_ide_arc N P D F)) :=
  flat_map (fun call => match audit_ide_arc_kind call with
    | IpCall site =>
        let returns := match Map.get (IpTab.kind_encoding EP) (IpReturn site) index with
          | Some xs => xs
          | None => []
          end in
        map (fun ret => (call,ret)) returns
    | _ => []
    end) arcs.

Definition audit_ide_ground_rules {N P D A F} (EP : encoding P) (r : ide_registry A F)
    (q : ip_problem N P D) (weight : ip_edge N P D -> option D -> option D -> F)
    (root : IpTab.vertex N D) : list (audit_ide_rule N D F) :=
  let vertices := IpTab.vertices q in
  let arcs := audit_ide_arcs q weight in
  let index := audit_ide_generate_index_plain EP arcs in
  let matches := audit_ide_generate_matches_plain EP index arcs in
  audit_ide_indexed_rows r vertices arcs matches root.

Definition audit_ide_fuel_model {N D A F} (r : ide_registry A F)
    (keys : list (IpTab.fact N D)) (rules : list (audit_ide_rule N D F)) : nat :=
  let nr := length rules in
  let nk := length keys in
  let rank := S (audit_ide_bound r) in
  64 + audit_unary_conversion_weight nr + audit_unary_conversion_weight nk +
  audit_unary_conversion_weight rank +
  nr * Pos.size_nat (Pos.of_succ_nat nr) + nk * Pos.size_nat (Pos.of_succ_nat nk) +
  rank * Pos.size_nat (Pos.of_succ_nat rank) +
  audit_multiply_weight 2 (Z.of_nat nk) +
  audit_multiply_weight (2 * Z.of_nat nk) (Z.of_nat rank) +
  audit_binary_weight 1 (2 * Z.of_nat nk * Z.of_nat rank) +
  audit_multiply_weight (Z.of_nat nr) (1 + 2 * Z.of_nat nk * Z.of_nat rank).

Definition audit_ide_producer_model_work {N P D A F} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (r : ide_registry A F) (run : audit_ide_generated_run N P D F) : nat :=
  let keys := audit_ide_run_keys run in
  let rules := audit_ide_run_rules run in
  let output := audit_ide_machine_probes_rev (audit_ide_run_final run) in
  audit_ide_generator_model_work EP (audit_ide_run_generator_events run) +
  audit_ide_initial_model_work EN ED (audit_ide_run_initial_events run) +
  audit_ide_machine_model_work EN ED (audit_ide_run_loop_events run) +
  audit_ide_fuel_model r keys rules +
  64 * S (length keys) * S (length keys) +
  64 * S (length output) * S (length output).

Definition audit_ide_producer_model_budget {N P D A F} (EN : encoding N) (EP : encoding P)
    (ED : encoding D) (r : ide_registry A F) (q : ip_problem N P D)
    (run : audit_ide_generated_run N P D F) : nat :=
  let keys := audit_ide_run_keys run in
  let rules := audit_ide_run_rules run in
  let initial := audit_ide_run_initial run in
  let fuel := audit_ide_machine_fuel r keys rules in
  let output_bound := (32 + 3 * audit_ide_incidence_size initial) * (2 * Pos.to_nat fuel + 1) in
  audit_ide_generator_input_budget EP q +
  audit_ide_initial_input_budget EN ED rules +
  audit_ide_machine_input_budget EN ED fuel initial +
  audit_ide_fuel_model r keys rules +
  64 * S (length keys) * S (length keys) +
  64 * S output_bound * S output_bound.

Section IdeProducerContract.

  Variable solve : forall {N P D A F : Type}, encoding N -> encoding P -> encoding D ->
    lattice A -> ide_registry A F -> ip_problem N P D ->
    (ip_edge N P D -> option D -> option D -> F) -> N -> option D -> ide_registry_summary N D F.

  (** Under the stated premises, the counted producer agrees with the supplied solver and bounds
      its stage events and work. *)
  Definition audit_ide_producer_counted_statement : Prop :=
    forall N P D A F (EN : encoding N) (EP : encoding P) (ED : encoding D)
      (L : lattice A) (r : ide_registry A F) (q : ip_problem N P D) weight start seed,
      ide_registry_laws L r -> ip_problem_wf q -> In start (ip_nodes q) ->
      (match seed with
      | None => True
      | Some d => In d (ip_facts q)
      end) ->
      let '(result, run) := audit_ide_producer_counted EN EP ED L r q weight start seed in
      let rules := audit_ide_run_rules run in
      let keys := audit_ide_run_keys run in
      let initial := audit_ide_run_initial run in
      let final := audit_ide_run_final run in
      result = solve EN EP ED L r q weight start seed /\
      rules = audit_ide_rule_spec EP r q weight (start, seed) /\
      keys = audit_ide_summary_keys q /\
      initial = audit_ide_machine_initial EN ED rules /\
      final = audit_ide_machine_loop EN ED r (audit_ide_machine_fuel r keys rules) initial /\
      ide_registry_summary_map result = audit_ide_machine_values final /\
      ide_registry_summary_probes result = rev (audit_ide_machine_probes_rev final) /\
      length (audit_ide_run_generator_events run) <=
        16 * (1 + length (ip_edges q) + length (IpTab.vertices q) +
          audit_ide_arc_count q + audit_ide_matching_occurrences EP q + length rules) /\
      length (audit_ide_run_initial_events run) <= 20 + 16 * length rules /\
      length (audit_ide_run_loop_events run) <=
        (32 + 3 * audit_ide_incidence_size initial) *
          (2 * Pos.to_nat (audit_ide_machine_fuel r keys rules) + 1) /\
      length (audit_ide_probe_updates (ide_registry_summary_probes result)) <=
        length keys * S (audit_ide_bound r) /\
      audit_ide_producer_model_work EN EP ED r run <= audit_ide_producer_model_budget EN EP ED r q
        run /\
      64 * length (audit_ide_run_loop_events run) <= audit_ide_producer_model_work EN EP ED r run.

End IdeProducerContract.

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-check-types.md *)
(** Compatibility events retain the visited graph inputs and comparison operands. *)
Inductive audit_ide_check_event (N P D A F : Type) : Type :=
  | IdeCheckEdge (edge : ip_edge N P D)
  | IdeCheckPair (edge : ip_edge N P D) (x y : option D)
  | IdeCheckWeight (edge : ip_edge N P D) (x y : option D)
  | IdeCheckEval (f : F) (a : A)
  | IdeCheckOldWeight (edge : ip_edge N P D) (x y : option D) (a : A)
  | IdeCheckLe (left right : A).

Arguments IdeCheckEdge {N P D A F}.

Arguments IdeCheckPair {N P D A F}.

Arguments IdeCheckWeight {N P D A F}.

Arguments IdeCheckEval {N P D A F}.

Arguments IdeCheckOldWeight {N P D A F}.

Arguments IdeCheckLe {N P D A F}.

(** Compatibility counts distinguish visited edges, pairs, values and order comparisons. *)
Record audit_ide_check_counts : Type := AuditIdeCheckCounts {
  audit_ide_check_edges : nat;
  audit_ide_check_pairs : nat;
  audit_ide_check_values : nat;
  audit_ide_check_comparisons : nat
}.

Definition audit_ide_check_zero : audit_ide_check_counts := AuditIdeCheckCounts 0 0 0 0.

Definition audit_ide_check_add (a b : audit_ide_check_counts) : audit_ide_check_counts :=
  AuditIdeCheckCounts (audit_ide_check_edges a + audit_ide_check_edges b)
    (audit_ide_check_pairs a + audit_ide_check_pairs b)
    (audit_ide_check_values a + audit_ide_check_values b)
    (audit_ide_check_comparisons a + audit_ide_check_comparisons b).

Definition audit_ide_check_event_counts {N P D A F} (event : audit_ide_check_event N P D A F)
    : audit_ide_check_counts :=
  match event with
  | IdeCheckEdge _ => AuditIdeCheckCounts 1 0 0 0
  | IdeCheckPair _ _ _ => AuditIdeCheckCounts 0 1 0 0
  | IdeCheckWeight _ _ _ => AuditIdeCheckCounts 0 0 1 0
  | IdeCheckLe _ _ => AuditIdeCheckCounts 0 0 0 1
  | _ => audit_ide_check_zero
  end.

Definition audit_ide_check_trace_counts {N P D A F} (events : list (audit_ide_check_event N P D A
  F))
    : audit_ide_check_counts :=
  fold_right (fun event total => audit_ide_check_add (audit_ide_check_event_counts event) total)
    audit_ide_check_zero events.

(** Source: run/reports/AUD-API-final-20261101/graph-ssa/ide-strict-check.md *)
Fixpoint audit_ide_strict_all {X Event : Type}
    (f : X -> bool * list Event) (xs : list X) : bool * list Event :=
  match xs with
  | [] => (true, [])
  | x :: rest =>
      let '(ok, here) := f x in
      let '(later_ok, later) := audit_ide_strict_all f rest in
      (ok && later_ok, here ++ later)
  end.

Definition audit_ide_strict_value {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (edge : ip_edge N P D) (x y : option D) (a : A)
    : bool * list (audit_ide_check_event N P D A F) :=
  let L := ide_lattice old in
  let f := weight edge x y in
  let new := audit_ide_eval r f a in
  let prior := ide_weight old edge x y a in
  let forward := OrderLattice.leb L new prior in
  let reverse := OrderLattice.leb L prior new in
  (forward && reverse,
    [IdeCheckWeight edge x y; IdeCheckEval f a;
    IdeCheckOldWeight edge x y a; IdeCheckLe new prior; IdeCheckLe prior new]).

Definition audit_ide_strict_pair {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (edge : ip_edge N P D) (xy : option D * option D)
    : bool * list (audit_ide_check_event N P D A F) :=
  let '(ok, events) := audit_ide_strict_all
    (audit_ide_strict_value old r weight edge (fst xy) (snd xy)) (ide_values old) in
  (ok, IdeCheckPair edge (fst xy) (snd xy) :: events).

Definition audit_ide_strict_edge {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (edge : ip_edge N P D)
    : bool * list (audit_ide_check_event N P D A F) :=
  let '(ok, events) := audit_ide_strict_all
    (audit_ide_strict_pair old r weight edge) (ip_pairs edge) in
  (ok, IdeCheckEdge edge :: events).

Definition audit_ide_check_strict_traced {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    : bool * list (audit_ide_check_event N P D A F) :=
  audit_ide_strict_all (audit_ide_strict_edge old r weight)
    (ip_edges (ide_graph old)).

(** A strict traversal relates each element's result and events to the combined result and trace. *)
Inductive audit_ide_strict_all_execution {X Event : Type}
    (step : X -> bool -> list Event -> Prop) : list X -> bool -> list Event -> Prop :=
  | AuditIdeStrictAllNil : audit_ide_strict_all_execution step [] true []
  | AuditIdeStrictAllCons x rest here_ok here later_ok later :
      step x here_ok here ->
      audit_ide_strict_all_execution step rest later_ok later ->
      audit_ide_strict_all_execution step (x :: rest) (here_ok && later_ok) (here ++ later).

(** A value execution records both comparison directions and the actual callback operands. *)
Inductive audit_ide_strict_value_execution {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (edge : ip_edge N P D) (x y : option D)
    : A -> bool -> list (audit_ide_check_event N P D A F) -> Prop :=
  | AuditIdeStrictValueRun a :
      audit_ide_strict_value_execution old r weight edge x y a
        (let new := audit_ide_eval r (weight edge x y) a in
          let prior := ide_weight old edge x y a in
          OrderLattice.leb (ide_lattice old) new prior && OrderLattice.leb (ide_lattice old) prior
            new)
        [IdeCheckWeight edge x y; IdeCheckEval (weight edge x y) a;
          IdeCheckOldWeight edge x y a;
          IdeCheckLe (audit_ide_eval r (weight edge x y) a) (ide_weight old edge x y a);
          IdeCheckLe (ide_weight old edge x y a) (audit_ide_eval r (weight edge x y) a)].

(** A pair execution traverses every old value and prefixes the pair event. *)
Inductive audit_ide_strict_pair_execution {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F) (edge : ip_edge N P D)
    : option D * option D -> bool -> list (audit_ide_check_event N P D A F) -> Prop :=
  | AuditIdeStrictPairRun x y result events :
      audit_ide_strict_all_execution (audit_ide_strict_value_execution old r weight edge x y)
        (ide_values old) result events ->
      audit_ide_strict_pair_execution old r weight edge (x, y) result
        (IdeCheckPair edge x y :: events).

(** An edge execution traverses its pairs and prefixes the edge event. *)
Inductive audit_ide_strict_edge_execution {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    : ip_edge N P D -> bool -> list (audit_ide_check_event N P D A F) -> Prop :=
  | AuditIdeStrictEdgeRun edge result events :
      audit_ide_strict_all_execution (audit_ide_strict_pair_execution old r weight edge)
        (ip_pairs edge) result events ->
      audit_ide_strict_edge_execution old r weight edge result (IdeCheckEdge edge :: events).

(** The strict compatibility execution traverses every edge of the old graph. *)
Definition audit_ide_check_strict_execution {N P D A F}
    (old : ide_problem N P D A) (r : audit_ide_registry A F)
    (weight : ip_edge N P D -> option D -> option D -> F)
    (result : bool) (events : list (audit_ide_check_event N P D A F)) : Prop :=
  audit_ide_strict_all_execution (audit_ide_strict_edge_execution old r weight)
    (ip_edges (ide_graph old)) result events.

(** The strict traversal has an execution with the compatibility result. *)
Definition audit_ide_check_strict_execution_exists_statement : Prop :=
  forall N P D A F (old : ide_problem N P D A) (r : audit_ide_registry A F) weight,
    exists result events, audit_ide_check_strict_execution old r weight result events /\
      result = audit_ide_finite_compatible_check old r weight.

Definition audit_ide_strict_pair_count {N P D A}
    (old : ide_problem N P D A) : nat :=
  fold_right (fun edge n => length (ip_pairs edge) + n) 0
    (ip_edges (ide_graph old)).

(** The strict traversal agrees with the compatibility check and records the specified counts. *)
Definition audit_ide_strict_check_contract : Prop :=
  forall N P D A F (old : ide_problem N P D A)
      (r : audit_ide_registry A F) weight,
    let '(answer, events) := audit_ide_check_strict_traced old r weight in
    let edges := length (ip_edges (ide_graph old)) in
    let pairs := audit_ide_strict_pair_count old in
    let values := pairs * length (ide_values old) in
    audit_ide_check_strict_execution old r weight answer events /\
    answer = audit_ide_finite_compatible_check old r weight /\
    audit_ide_check_trace_counts events =
      AuditIdeCheckCounts edges pairs values (2 * values) /\
    length events = edges + pairs + 5 * values.
