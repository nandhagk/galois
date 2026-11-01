(** * RewriteAuditQueueReference

    This module defines pending queues, their rebuild projection, and audited queue operations.
    For example, popping the empty pending queue returns None.
    Builds on: RewriteIndex and
    RewriteRebuild. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
Import List.ListNotations.

Record rw_pending_queue : Type := RwPendingQueue {
  rw_pending_sequence : list rw_pair;
  rw_pending_members : FinSet.t rw_pair
}.

Definition rw_pending_pair_encoding : encoding rw_pair :=
  pair_encoding positive_encoding positive_encoding.

Definition rw_pending_pair_key_bits (p : rw_pair) : nat :=
  Pos.size_nat (encode rw_pending_pair_encoding p).

(** A pending pair key has one plus twice the sum of its positive operand bit lengths. *)
Definition rw_pending_pair_key_bits_exact_contract : Prop :=
  forall n m, rw_pending_pair_key_bits (n, m) = S (2 * Pos.size_nat n + 2 * Pos.size_nat m).

(** A pending queue has no duplicate pairs and its well-formed member set matches its sequence. *)
Definition rw_pending_valid (q : rw_pending_queue) : Prop :=
  NoDup (rw_pending_sequence q) /\
  FinSet.wf rw_pending_pair_encoding (rw_pending_members q) /\
  forall p, FinSet.mem rw_pending_pair_encoding p (rw_pending_members q) = true <->
    In p (rw_pending_sequence q).

Definition rw_pending_empty : rw_pending_queue :=
  RwPendingQueue nil FinSet.empty.

Definition rw_pending_insert (p : rw_pair) (q : rw_pending_queue) : rw_pending_queue :=
  if FinSet.mem rw_pending_pair_encoding p (rw_pending_members q) then q
  else RwPendingQueue (p :: rw_pending_sequence q)
    (FinSet.add rw_pending_pair_encoding p (rw_pending_members q)).

Definition rw_pending_prepend (ps : list rw_pair) (q : rw_pending_queue) : rw_pending_queue :=
  fold_right rw_pending_insert q ps.

Definition rw_pending_pop (q : rw_pending_queue) : option (rw_pair * rw_pending_queue) :=
  match rw_pending_sequence q with
  | nil => None
  | p :: ps => Some (p, RwPendingQueue ps
      (FinSet.remove rw_pending_pair_encoding p (rw_pending_members q)))
  end.

Definition rw_pending_initial {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t positive (list rw_id)) :
    rw_pending_queue :=
  fold_right (fun n q => fold_right (fun m acc => rw_pending_insert (n, m) acc) q
    (rw_partners EK EN base ix vars n)) rw_pending_empty (rw_nodes_in base).

Definition rw_pending_initial_with_count {K Sort V} (EK : encoding K)
    (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)) : rw_pending_queue * nat :=
  fold_right (fun n state =>
    fold_right (fun m acc =>
      let '(q, count) := acc in (rw_pending_insert (n, m) q, S count))
      state (rw_partners EK EN base ix vars n))
    (rw_pending_empty, 0) (rw_nodes_in base).

Record rw_queue_state (K Sort V : Type) : Type := RwQueueState {
  rw_queue_graph : rw_graph K Sort V;
  rw_queue_index : rw_index K;
  rw_queue_pending : rw_pending_queue
}.
Arguments RwQueueState {K Sort V}.
Arguments rw_queue_graph {K Sort V}.
Arguments rw_queue_index {K Sort V}.
Arguments rw_queue_pending {K Sort V}.

Definition rw_queue_project {K Sort V} (state : rw_queue_state K Sort V) :
    rw_rebuild_state K Sort V :=
  RwRebuildState (rw_queue_graph state) (rw_queue_index state) (rw_pending_sequence
    (rw_queue_pending state)).

Definition rw_queue_step {K Sort V} (EK : encoding K) (ES : encoding Sort) (EN : encoding (rw_node K
    Sort V)) (base : rw_graph K Sort V) (baseix : rw_index K) (vars : Map.t positive (list rw_id))
    (state : rw_queue_state K Sort V) : rw_queue_state K Sort V :=
  let g := rw_queue_graph state in
  let ix := rw_queue_index state in
  match rw_pending_pop (rw_queue_pending state) with
  | None => state
  | Some ((n, m), rest) =>
    let dropped := RwQueueState g ix rest in
    match rw_node_at g n, rw_node_at g m with
    | Some (a, node), Some (b, other) =>
      match rw_find g a, rw_find g b with
      | Some ra, Some rb =>
        if Pos.eq_dec (encode EN (rw_canonical_node g node))
              (encode EN (rw_canonical_node g other)) then
          if Pos.eq_dec ra rb then dropped
          else
            match rw_union ES g a b with
            | Some g' =>
              RwQueueState g' (rw_index_after_union g g' ix a b)
                (rw_pending_prepend
                  (flat_map (rw_pairs_for EK EN base baseix vars)
                    (rw_parent_nodes g ix a ++ rw_parent_nodes g ix b)) rest)
            | None => dropped
            end
        else dropped
      | _, _ => dropped
      end
    | _, _ => dropped
    end
  end.

Definition rw_pending_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_graph K Sort V :=
  let EN := rw_node_encoding EK ES EV in
  let ix := rw_build_index EK g in
  let vars := rw_build_table positive_encoding g (RewriteRebuild.rw_variable_keys EN) in
  let '(pending, pair_count) := rw_pending_initial_with_count EK EN g ix vars in
  let initial := RwQueueState g ix pending in
  let fuel := length (rw_roots g) * S pair_count + length (rw_pending_sequence pending) in
  let done := fun state => rw_rebuild_done (rw_queue_project state) in
  let final := rw_repeat done (rw_queue_step EK ES EN g ix vars) (Pos.of_succ_nat fuel) initial in
  fst (rw_canonicalize_all EK (rw_nodes_in (rw_queue_graph final))
    (rw_queue_graph final) (rw_queue_index final)).

(** Counted pending initialization returns the plain queue and the pair-universe length. *)
Definition rw_pending_initial_with_count_correct_contract : Prop :=
  forall K Sort V (EK : encoding K) (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V)
    (ix : rw_index K) (vars : Map.t positive (list rw_id)), rw_pending_initial_with_count EK EN base
    ix vars = (rw_pending_initial EK EN base ix vars, length (rw_pair_universe EK EN base ix vars)).

(** A queue step from a valid pending queue preserves validity and projects to the
    corresponding rebuild step. *)
Definition rw_queue_step_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EN : encoding (rw_node K Sort V)) base
    baseix vars (state : rw_queue_state K Sort V),
    rw_pending_valid (rw_queue_pending state) ->
    rw_pending_valid (rw_queue_pending (rw_queue_step EK ES EN base baseix vars state)) /\
    rw_queue_project (rw_queue_step EK ES EN base baseix vars state) =
      rw_rebuild_step EK ES EN base baseix vars (rw_queue_project state).

(** The empty pending queue is valid and has an empty sequence. *)
Definition rw_pending_empty_valid_contract : Prop :=
  rw_pending_valid rw_pending_empty /\ rw_pending_sequence rw_pending_empty = nil.

(** Inserting into a valid pending queue leaves an existing pair in place or prepends
    a pair not already present. *)
Definition rw_pending_insert_order_contract : Prop :=
  forall q p, rw_pending_valid q ->
    rw_pending_sequence (rw_pending_insert p q) =
      if in_dec rw_pair_dec p (rw_pending_sequence q) then
        rw_pending_sequence q else p :: rw_pending_sequence q.

(** Inserting into a valid pending queue preserves validity and adds exactly the new pair
    to its sequence membership. *)
Definition rw_pending_membership_contract : Prop :=
  forall q p x, rw_pending_valid q ->
    rw_pending_valid (rw_pending_insert p q) /\
    (In x (rw_pending_sequence (rw_pending_insert p q)) <-> x = p \/ In x (rw_pending_sequence q)).

(** Popping a valid queue returns None for an empty sequence, otherwise its head and
    a valid queue with exactly the remaining sequence. *)
Definition rw_pending_pop_agrees_contract : Prop :=
  forall q, rw_pending_valid q ->
    match rw_pending_sequence q, rw_pending_pop q with
    | nil, None => True
    | p :: rest, Some (p', q') =>
      p' = p /\ rw_pending_valid q' /\ rw_pending_sequence q' = rest
    | _, _ => False
    end.

(** Prepending pairs to a valid queue preserves validity and yields the deduplicated
    concatenation of pairs and the original sequence. *)
Definition rw_pending_prepend_agrees_contract : Prop :=
  forall ps q, rw_pending_valid q ->
    rw_pending_valid (rw_pending_prepend ps q) /\
    rw_pending_sequence (rw_pending_prepend ps q) = nodup rw_pair_dec (ps ++ rw_pending_sequence q).

(** Initial pending construction yields a valid queue whose sequence is the deduplicated
    pair universe. *)
Definition rw_pair_universe_refines_contract : Prop :=
  forall K Sort V (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)),
    let q := rw_pending_initial EK EN base ix vars in
    rw_pending_valid q /\
    rw_pending_sequence q = nodup rw_pair_dec (rw_pair_universe EK EN base ix vars).

(** The pending-queue rebuild returns the same graph as the original rebuild. *)
Definition rw_pending_rebuild_agrees_contract : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (g : rw_graph K Sort V),
    rw_pending_rebuild EK ES EV g = rw_rebuild EK ES EV g.

Record rw_pending_charge := RwPendingCharge {
  rw_pending_probes : nat;
  rw_pending_updates : nat;
  rw_pending_key_steps : nat
}.

Definition rw_pending_charge_insert (p : rw_pair) (state : rw_pending_queue * rw_pending_charge) :
    rw_pending_queue * rw_pending_charge :=
  let '(q, charge) := state in
  let bits := rw_pending_pair_key_bits p in
  if FinSet.mem rw_pending_pair_encoding p (rw_pending_members q) then
    (q, RwPendingCharge (S (rw_pending_probes charge)) (rw_pending_updates charge)
      (bits + rw_pending_key_steps charge))
  else
    (RwPendingQueue (p :: rw_pending_sequence q)
      (FinSet.add rw_pending_pair_encoding p (rw_pending_members q)),
      RwPendingCharge (S (rw_pending_probes charge)) (S (rw_pending_updates charge))
        (2 * bits + rw_pending_key_steps charge)).

Definition rw_pending_initial_counted {K Sort V} (EK : encoding K)
    (EN : encoding (rw_node K Sort V)) (base : rw_graph K Sort V) (ix : rw_index K)
    (vars : Map.t positive (list rw_id)) : rw_pending_queue * rw_pending_charge :=
  fold_right (fun n st => fold_right (fun m acc => rw_pending_charge_insert (n, m) acc) st
    (rw_partners EK EN base ix vars n)) (rw_pending_empty, RwPendingCharge 0 0 0)
    (rw_nodes_in base).

Definition rw_pending_key_budget (pairs : list rw_pair) : nat :=
  fold_right (fun p n => 2 * rw_pending_pair_key_bits p + n) 0 pairs.

(** Counted initialization yields the plain pending queue, one probe per candidate,
    and bounded updates and key steps. *)
Definition rw_pending_initial_counted_correct_contract : Prop :=
  forall K Sort V (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K) (vars : Map.t positive (list rw_id)),
    let '(pending, charge) := rw_pending_initial_counted EK EN base ix vars in
    pending = rw_pending_initial EK EN base ix vars /\
    rw_pending_probes charge = length (rw_pair_universe EK EN base ix vars) /\
    rw_pending_updates charge <= length (rw_pair_universe EK EN base ix vars) /\
    rw_pending_key_steps charge <= rw_pending_key_budget (rw_pair_universe EK EN base ix vars).

Inductive rw_queue_insert_call : Type :=
  | RWQueuePairCode : rw_pair -> positive -> rw_queue_insert_call
  | RWQueueGet : rw_pair -> FinSet.t rw_pair -> option unit -> rw_queue_insert_call
  | RWQueueSet : rw_pair -> FinSet.t rw_pair -> FinSet.t rw_pair -> rw_queue_insert_call
  | RWQueueRemove : rw_pair -> FinSet.t rw_pair -> FinSet.t rw_pair -> rw_queue_insert_call.

Definition rw_queue_insert_event_cost (event : audit_event rw_queue_insert_call) : nat :=
  match event with
  | AuditCall (RWQueuePairCode _ code) => audit_encoding_weight (Pos.size_nat code)
  | AuditCall (RWQueueGet p _ _) =>
    audit_get_weight (encode rw_pending_pair_encoding p)
  | AuditCall (RWQueueSet p _ _) =>
    audit_set_weight (encode rw_pending_pair_encoding p)
  | AuditCall (RWQueueRemove p _ _) =>
    audit_remove_weight (encode rw_pending_pair_encoding p)
  | _ => 1
  end.

Definition rw_queue_insert_model_cost (trace : audit_trace rw_queue_insert_call) : nat :=
  fold_right (fun event total => rw_queue_insert_event_cost event + total) 0 trace.

Definition rw_queue_insert_atomic (p : rw_pair) (q : rw_pending_queue) : rw_pending_queue *
    audit_trace rw_queue_insert_call :=
  let code := encode rw_pending_pair_encoding p in
  let members := rw_pending_members q in
  let found := Map.code_get code members in
  match found with
  | Some _ =>
    (q, [AuditCase 0 []; AuditCall (RWQueuePairCode p code);
      AuditCall (RWQueueGet p members found); AuditCase 1 []])
  | None =>
    let code' := encode rw_pending_pair_encoding p in
    let updated := Trie.set code' (p, tt) members in
    (RwPendingQueue (p :: rw_pending_sequence q) updated,
      [AuditCase 0 []; AuditCall (RWQueuePairCode p code);
        AuditCall (RWQueueGet p members found); AuditCase 2 [];
        AuditCall (RWQueuePairCode p code'); AuditCall (RWQueueSet p members updated);
        AuditConstruct 3 []; AuditConstruct 4 []])
  end.

Record rw_queue_encoder_adapter (A : Type) : Type := RwQueueEncoderAdapter {
  rw_queue_encoder_run : A -> positive * nat
}.
Arguments RwQueueEncoderAdapter {A}.
Arguments rw_queue_encoder_run {A}.

(** The adapter returns the specified encoding and has an external execution witness
    for its actual result and work on every input. *)
Record rw_queue_encoder_adapter_laws {A} (E : encoding A)
    (external_execution : A -> positive -> nat -> Prop)
    (adapter : rw_queue_encoder_adapter A) : Prop := {
  (** The adapter's returned code is the specified encoding of the input. *)
  rw_queue_encoder_agrees : forall input,
    fst (rw_queue_encoder_run adapter input) = encode E input;
  (** The external execution relation holds for the adapter's actual code and work. *)
  rw_queue_encoder_adequate : forall input,
    let '(result, work) := rw_queue_encoder_run adapter input in
    external_execution input result work
}.

Definition rw_queue_pop_atomic (q : rw_pending_queue) : option (rw_pair * rw_pending_queue) *
    audit_trace rw_queue_insert_call :=
  match rw_pending_sequence q with
  | nil => (None, [AuditCase 20 []; AuditConstruct 22 []])
  | p :: rest =>
    let code := encode rw_pending_pair_encoding p in
    let updated := Trie.remove code (rw_pending_members q) in
    (Some (p, RwPendingQueue rest updated),
      [AuditCase 21 []; AuditCall (RWQueuePairCode p code);
        AuditCall (RWQueueRemove p (rw_pending_members q) updated);
        AuditConstruct 23 []; AuditConstruct 24 []; AuditConstruct 25 []])
  end.

Fixpoint rw_queue_prepend_atomic (pairs : list rw_pair) (q : rw_pending_queue) : rw_pending_queue *
    audit_trace rw_queue_insert_call :=
  match pairs with
  | nil => (q, [AuditCase 10 []])
  | p :: rest =>
    let '(after_rest, rest_trace) := rw_queue_prepend_atomic rest q in
    let '(out, insert_trace) := rw_queue_insert_atomic p after_rest in
    (out, AuditCase 11 [] :: rest_trace ++ insert_trace)
  end.

Fixpoint rw_queue_append_atomic {A} (first second : list A) : list A * audit_trace unit :=
  match first with
  | nil => (second, [AuditCase 195 []])
  | item :: rest =>
    let '(tail, trace) := rw_queue_append_atomic rest second in
    (item :: tail, [AuditCase 196 []] ++ trace ++ [AuditConstruct 197 []])
  end.

Fixpoint rw_fuel_length {A} (xs : list A) : nat * audit_trace unit :=
  match xs with
  | nil => (0, [AuditCase 410 []; AuditConstruct 411 []])
  | _ :: rest =>
    let '(n, trace) := rw_fuel_length rest in
    (S n, [AuditCase 412 []; AuditArithmetic 440 []] ++ trace ++ [AuditConstruct 413 []])
  end.

Fixpoint rw_fuel_add (n m : nat) : nat * audit_trace unit :=
  match n with
  | 0 => (m, [AuditCase 414 []])
  | S n' =>
    let '(out, trace) := rw_fuel_add n' m in
    (S out, [AuditCase 415 []; AuditArithmetic 441 []] ++ trace ++ [AuditConstruct 416 []])
  end.

Fixpoint rw_fuel_mul (n m : nat) : nat * audit_trace unit :=
  match n with
  | 0 => (0, [AuditCase 417 []; AuditConstruct 418 []])
  | S n' =>
    let '(tail, tail_trace) := rw_fuel_mul n' m in
    let '(out, add_trace) := rw_fuel_add m tail in
    (out, [AuditCase 419 []; AuditArithmetic 442 []] ++ tail_trace ++
      [AuditArithmetic 443 []] ++ add_trace)
  end.

Fixpoint rw_fuel_pos_succ (p : positive) : positive * audit_trace unit :=
  match p with
  | xH => (xO xH, [AuditCase 420 []; AuditConstruct 421 []])
  | xO rest => (xI rest, [AuditCase 422 []; AuditConstruct 423 []])
  | xI rest =>
    let '(out, trace) := rw_fuel_pos_succ rest in
    (xO out, [AuditCase 424 []; AuditArithmetic 444 []] ++ trace ++ [AuditConstruct 425 []])
  end.

Fixpoint rw_fuel_to_positive (n : nat) : positive * audit_trace unit :=
  match n with
  | 0 => (xH, [AuditCase 426 []; AuditConstruct 427 []])
  | S rest =>
    let '(p, tail_trace) := rw_fuel_to_positive rest in
    let '(out, succ_trace) := rw_fuel_pos_succ p in
    (out, [AuditCase 428 []; AuditArithmetic 445 []] ++ tail_trace ++
        [AuditArithmetic 446 []] ++ succ_trace)
  end.

Definition rw_rebuild_fuel_atomic {K Sort V} (g : rw_graph K Sort V) (pair_count : nat)
    (queue : rw_pending_queue) : positive * audit_trace unit :=
  let roots := rw_roots g in
  let '(root_count, root_trace) := rw_fuel_length roots in
  let width := S pair_count in
  let '(product, mul_trace) := rw_fuel_mul root_count width in
  let pending := rw_pending_sequence queue in
  let '(pending_count, pending_trace) := rw_fuel_length pending in
  let '(total, add_trace) := rw_fuel_add product pending_count in
  let '(fuel, conversion_trace) := rw_fuel_to_positive total in
  (fuel, [AuditCase 430 []; AuditArithmetic 447 []] ++ root_trace ++
    [AuditConstruct 429 []; AuditArithmetic 448 []] ++ mul_trace ++
    [AuditCase 431 []; AuditArithmetic 449 []] ++ pending_trace ++
    [AuditArithmetic 450 []] ++ add_trace ++ [AuditArithmetic 451 []] ++ conversion_trace).

Definition rw_rebuild_fuel_work (roots pair_count pending : nat) : nat :=
  let product := roots * S pair_count in
  let total := product + pending in
  30 + 3 * roots + 3 * pending + roots * (4 + 3 * S pair_count) +
    3 * product + (S total) * (5 + 3 * Pos.size_nat (Pos.of_succ_nat total)).

Definition rw_node_encode_atomic {K Sort V KE SE VE} (op : K -> positive * list KE)
    (sort : Sort -> positive * list SE) (value : V -> positive * list VE)
    (node : rw_node K Sort V) :=
  audit_sum_encode (audit_pair_encode sort value)
    (audit_pair_encode sort (audit_pair_encode op (audit_list_encode audit_positive_encode)))
    (rw_node_key node).

Definition rw_node_encode_trace_cost {K Sort V KE SE VE} (op_work : list KE -> nat)
    (sort_work : list SE -> nat) (value_work : list VE -> nat)
    (trace : list (audit_sum_event (Sort * V) (Sort * (K * list rw_id))
      (audit_pair_event Sort V SE VE)
      (audit_pair_event Sort (K * list rw_id) SE
        (audit_pair_event K (list rw_id) KE (audit_list_event rw_id (audit_basic_encoding_event
          positive)))))) : nat :=
  audit_sum_events_work (audit_pair_events_work sort_work value_work)
    (audit_pair_events_work sort_work
      (audit_pair_events_work op_work (audit_list_events_work (@length
        (audit_basic_encoding_event positive))))) trace.

Definition rw_external_encoding_events {A} (adapter : rw_queue_encoder_adapter A) (x : A) : positive
    * list nat :=
  let '(code, work) := rw_queue_encoder_run adapter x in (code, [work]).

Definition rw_external_events_work (events : list nat) : nat :=
  fold_right Nat.add 0 events.

Definition rw_queue_insert_trie_work (event : audit_event rw_queue_insert_call) : nat :=
  match event with
  | AuditCall (RWQueueGet p before _) =>
    audit_trie_get_source_work (encode rw_pending_pair_encoding p) before
  | AuditCall (RWQueueSet p before _) =>
    audit_trie_update_source_work (encode rw_pending_pair_encoding p) (Some (p, tt)) before
  | AuditCall (RWQueueRemove p before _) =>
    audit_trie_update_source_work (encode rw_pending_pair_encoding p) None before
  | _ => 0
  end.

Definition rw_queue_insert_trie_trace_work (trace : audit_trace rw_queue_insert_call) : nat :=
  fold_right (fun event total => rw_queue_insert_trie_work event + total) 0 trace.

Definition rw_queue_insert_expanded_work (trace : audit_trace rw_queue_insert_call) : nat :=
  rw_queue_insert_model_cost trace + rw_queue_insert_trie_trace_work trace.

Definition rw_queue_prepend_expanded_budget (pairs : list rw_pair) : nat :=
  S (length pairs) + fold_right (fun p total => 8 + 26 * rw_pending_pair_key_bits p + total) 0
    pairs.
