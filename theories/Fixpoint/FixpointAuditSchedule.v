(** * Reverse postorder scheduler observations

    Counted graph and scheduler operations retain their source events and budgets.
    For example, a position assignment records its map write and successor operation.
    Builds on: FixpointSchedule and the counted graph and collection models. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphDfs GraphAuditBase.
From Galois.Fixpoint Require Import FixpointSchedule.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditCompare
  CollectionsAuditEncoding.
Import List.ListNotations.

Inductive audit_rpo_schedule_event (V B : Type) : Type :=
  | RpoScheduleCase : nat -> audit_rpo_schedule_event V B
  | RpoScheduleNext : positive -> positive -> list audit_nat_encoding_event ->
    audit_rpo_schedule_event V B
  | RpoScheduleMap : audit_map_event V positive B -> audit_rpo_schedule_event V B
  | RpoScheduleSet : audit_set_event V B -> audit_rpo_schedule_event V B.

Arguments RpoScheduleCase {V B} _.

Arguments RpoScheduleNext {V B} _ _ _.

Arguments RpoScheduleMap {V B} _.

Arguments RpoScheduleSet {V B} _.

Fixpoint audit_rpo_schedule_positions {V B} (enc : V -> positive * list B) (vertices : list V) (next
  : positive)
    : Map.t V positive * list (audit_rpo_schedule_event V B) :=
  match vertices with
  | [] => (Map.empty, [RpoScheduleCase 0])
  | v :: rest => let '(next', successor_events) := audit_positive_succ next in
      let '(middle, events) := audit_rpo_schedule_positions enc rest next' in
      let '(result, writes) := audit_map_set enc v next middle in
      (result, [RpoScheduleCase 1; RpoScheduleNext next next' successor_events] ++ events ++ map
        RpoScheduleMap writes)
  end.

Definition audit_rpo_schedule_priority {V B} (enc : V -> positive * list B) (positions : Map.t V
  positive) (v : V)
    : positive * list (audit_rpo_schedule_event V B) :=
  let '(found, reads) := audit_map_get enc v positions in
  (
    match found with
    | Some rank => rank
    | None => 1%positive
    end, map RpoScheduleMap reads).

Definition audit_rpo_schedule_widening {V B} (enc : V -> positive * list B) (heads : FinSet.t V) (v
  : V)
    : bool * list (audit_rpo_schedule_event V B) :=
  let '(result, events) := audit_finset_mem enc v heads in (result, map RpoScheduleSet events).

(** If modeled encodings agree with the original, counted position assignment returns the
    original map. *)
Definition audit_rpo_schedule_positions_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) vertices next,
    (forall v, fst (enc v) = encode EV v) ->
    fst (audit_rpo_schedule_positions enc vertices next) = schedule_positions EV vertices next.

(** If modeled encodings agree, counted priority and widening-point queries return the original
    answers. *)
Definition audit_rpo_schedule_callbacks_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) positions heads v,
    (forall x, fst (enc x) = encode EV x) ->
    fst (audit_rpo_schedule_priority enc positions v) = schedule_priority EV positions v /\
    fst (audit_rpo_schedule_widening enc heads v) = FinSet.mem EV v heads.

Record audit_rpo_graph_callbacks (V E B : Type) : Type := AuditRpoGraphCallbacks {
  audit_rpo_graph_encode : V -> positive * list B;
  audit_rpo_graph_out : V -> list E * list B;
  audit_rpo_graph_source : E -> V * list B;
  audit_rpo_graph_target : E -> V * list B
}.

Arguments audit_rpo_graph_encode {V E B} _ _.

Arguments audit_rpo_graph_out {V E B} _ _.

Arguments audit_rpo_graph_source {V E B} _ _.

Arguments audit_rpo_graph_target {V E B} _ _.

Inductive audit_rpo_graph_event (V E B : Type) : Type :=
  | RpoGraphCase : nat -> audit_rpo_graph_event V E B
  | RpoGraphOut : V -> list E -> list B -> audit_rpo_graph_event V E B
  | RpoGraphSource : E -> V -> list B -> audit_rpo_graph_event V E B
  | RpoGraphTarget : E -> V -> list B -> audit_rpo_graph_event V E B
  | RpoGraphRank : audit_map_event V positive B -> audit_rpo_graph_event V E B
  | RpoGraphSet : audit_set_event V B -> audit_rpo_graph_event V E B
  | RpoGraphCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
    audit_rpo_graph_event V E B.

Arguments RpoGraphCase {V E B} _.

Arguments RpoGraphOut {V E B} _ _ _.

Arguments RpoGraphSource {V E B} _ _ _.

Arguments RpoGraphTarget {V E B} _ _ _.

Arguments RpoGraphRank {V E B} _.

Arguments RpoGraphSet {V E B} _.

Arguments RpoGraphCompare {V E B} _ _ _ _.

Definition audit_rpo_graph_ancestor {V E B} (enc : V -> positive * list B) (r : dfs_result V E) (u v
  : V)
    : bool * list (audit_rpo_graph_event V E B) :=
  let '(a, ea) := audit_map_get enc u (pre_num r) in
  match a with
  | None => (false, map RpoGraphRank ea)
  | Some av =>
    let '(b, eb) := audit_map_get enc v (pre_num r) in
    match b with
    | None => (false, map RpoGraphRank (ea ++ eb))
    | Some bv =>
      let '(c, ec) := audit_map_get enc u (post_num r) in
      match c with
      | None => (false, map RpoGraphRank (ea ++ eb ++ ec))
      | Some cv =>
        let '(d, ed) := audit_map_get enc v (post_num r) in
        match d with
        | None => (false, map RpoGraphRank (ea ++ eb ++ ec ++ ed))
        | Some dv =>
          let '(first, ef) := audit_positive_leb av bv in let '(second, es) := audit_positive_leb dv
            cv in
          (first && second, map RpoGraphRank (ea ++ eb ++ ec ++ ed) ++
            [RpoGraphCompare av bv first ef; RpoGraphCompare dv cv second es])
        end
      end
    end
  end.

Fixpoint audit_rpo_graph_filter {V E B} (cb : audit_rpo_graph_callbacks V E B) (r : dfs_result V E)
  (edges : list E)
    : list E * list (audit_rpo_graph_event V E B) :=
  match edges with
  | [] => ([], [RpoGraphCase 0])
  | edge :: rest => let '(target, tb) := audit_rpo_graph_target cb edge in
      let '(source, sb) := audit_rpo_graph_source cb edge in
      let '(keep, checks) := audit_rpo_graph_ancestor (audit_rpo_graph_encode cb) r target source in
      let '(later, events) := audit_rpo_graph_filter cb r rest in
      (if keep then edge :: later else later,
        [RpoGraphCase 1; RpoGraphTarget edge target tb; RpoGraphSource edge source sb] ++ checks ++
          events)
  end.

Fixpoint audit_rpo_graph_targets {V E B} (cb : audit_rpo_graph_callbacks V E B) (edges : list E)
    : list V * list (audit_rpo_graph_event V E B) :=
  match edges with
  | [] => ([], [RpoGraphCase 2])
  | edge :: rest => let '(target, body) := audit_rpo_graph_target cb edge in
      let '(later, events) := audit_rpo_graph_targets cb rest in
      (target :: later, RpoGraphCase 3 :: RpoGraphTarget edge target body :: events)
  end.

Fixpoint audit_rpo_graph_collect {V E B} (cb : audit_rpo_graph_callbacks V E B) (r : dfs_result V E)
  (vertices : list V)
    : list V * list (audit_rpo_graph_event V E B) :=
  match vertices with
  | [] => ([], [RpoGraphCase 4])
  | v :: rest => let '(outgoing, body) := audit_rpo_graph_out cb v in
      let '(retreats, checks) := audit_rpo_graph_filter cb r outgoing in
      let '(targets, target_events) := audit_rpo_graph_targets cb retreats in
      let '(later, events) := audit_rpo_graph_collect cb r rest in
      (targets ++ later, [RpoGraphCase 5; RpoGraphOut v outgoing body] ++ checks ++ target_events ++
        events)
  end.

Fixpoint audit_rpo_graph_add_all {V E B} (enc : V -> positive * list B) (vertices : list V) (heads :
  FinSet.t V)
    : FinSet.t V * list (audit_rpo_graph_event V E B) :=
  match vertices with
  | [] => (heads, [RpoGraphCase 6])
  | v :: rest => let '(next, events) := audit_finset_add enc v heads in
      let '(result, later) := audit_rpo_graph_add_all enc rest next in
      (result, RpoGraphCase 7 :: map RpoGraphSet events ++ later)
  end.

Definition audit_rpo_schedule_retreats {V E B} (cb : audit_rpo_graph_callbacks V E B)
    (g : Graph.t V E) (r : dfs_result V E) : FinSet.t V * list (audit_rpo_graph_event V E B) :=
  let '(vertices, events) := audit_rpo_graph_collect cb r (Graph.nodes g) in
  let '(result, adds) := audit_rpo_graph_add_all (audit_rpo_graph_encode cb) vertices FinSet.empty
    in
  (result, events ++ adds).

(** Modeled graph encodings, outgoing edges and endpoints agree with the supplied graph
    operations. *)
Definition audit_rpo_graph_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_rpo_graph_callbacks V E B) : Prop :=
  (forall v, fst (audit_rpo_graph_encode cb v) = encode EV v) /\
  (forall v, fst (audit_rpo_graph_out cb v) = Graph.out g v) /\
  (forall e, fst (audit_rpo_graph_source cb e) = Graph.source g e) /\
  (forall e, fst (audit_rpo_graph_target cb e) = Graph.target g e).

(** If graph callbacks erase correctly, counted retreat detection returns the original retreat
    set. *)
Definition audit_rpo_schedule_retreats_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (cb :
    audit_rpo_graph_callbacks V E B),
    audit_rpo_graph_callbacks_erase EV g cb -> fst (audit_rpo_schedule_retreats cb g r) =
      schedule_retreats EV g r.

Definition audit_rpo_schedule_event_work {V B} (weight : B -> nat) (event : audit_rpo_schedule_event
  V B) : nat :=
  let body := fun es => fold_right (fun item n => weight item + n) 0 es in
  64 +
    match event with
    | RpoScheduleMap item => audit_map_source_work body [item]
    | RpoScheduleSet item => audit_finset_source_work body [item]
    | RpoScheduleNext _ _ events => 2 * length events
    | RpoScheduleCase _ => 0
    end.

Definition audit_rpo_graph_event_work {V E B} (weight : B -> nat) (event : audit_rpo_graph_event V E
  B) : nat :=
  let body := fun es => fold_right (fun item n => weight item + n) 0 es in
  64 +
    match event with
    | RpoGraphOut _ _ es
    | RpoGraphSource _ _ es
    | RpoGraphTarget _ _ es => body es
    | RpoGraphRank item => audit_map_source_work body [item]
    | RpoGraphSet item => audit_finset_source_work body [item]
    | RpoGraphCompare _ _ _ events => audit_positive_order_source_work events
    | RpoGraphCase _ => 0
    end.

Definition audit_rpo_schedule_event_body {V B} (weight : B -> nat) (event : audit_rpo_schedule_event
  V B) : nat :=
  match event with
  | RpoScheduleMap (AuditMapGet _ _ _ _ body _)
  | RpoScheduleMap (AuditMapSet _ _ _ _ _ body _)
  | RpoScheduleMap (AuditMapRemove _ _ _ _ body _)
  | RpoScheduleSet (AuditSetMem _ _ _ _ body _)
  | RpoScheduleSet (AuditSetAdd _ _ _ _ body _)
  | RpoScheduleSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | RpoScheduleSet (AuditSetFold _ _)
  | RpoScheduleNext _ _ _
  | RpoScheduleCase _ => 0
  end.

Definition audit_rpo_graph_event_body {V E B} (weight : B -> nat) (event : audit_rpo_graph_event V E
  B) : nat :=
  match event with
  | RpoGraphOut _ _ body
  | RpoGraphSource _ _ body
  | RpoGraphTarget _ _ body
  | RpoGraphRank (AuditMapGet _ _ _ _ body _) | RpoGraphRank (AuditMapSet _ _ _ _ _ body _)
  | RpoGraphRank (AuditMapRemove _ _ _ _ body _)
  | RpoGraphSet (AuditSetMem _ _ _ _ body _)
  | RpoGraphSet (AuditSetAdd _ _ _ _ body _)
  | RpoGraphSet (AuditSetRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | RpoGraphSet (AuditSetFold _ _)
  | RpoGraphCompare _ _ _ _
  | RpoGraphCase _ => 0
  end.

Definition audit_rpo_schedule_work {V B} (weight : B -> nat) (events : list
  (audit_rpo_schedule_event V B)) : nat :=
  fold_right (fun event n => audit_rpo_schedule_event_work weight event + n) 0 events.

Definition audit_rpo_schedule_body_work {V B} (weight : B -> nat) (events : list
  (audit_rpo_schedule_event V B)) : nat :=
  fold_right (fun event n => audit_rpo_schedule_event_body weight event + n) 0 events.

Definition audit_rpo_graph_work {V E B} (weight : B -> nat) (events : list (audit_rpo_graph_event V
  E B)) : nat :=
  fold_right (fun event n => audit_rpo_graph_event_work weight event + n) 0 events.

Definition audit_rpo_graph_body_work {V E B} (weight : B -> nat) (events : list
  (audit_rpo_graph_event V E B)) : nat :=
  fold_right (fun event n => audit_rpo_graph_event_body weight event + n) 0 events.

Definition audit_rpo_positions_budget {V} (EV : encoding V) (vertices : list V) (next : positive) :
  nat :=
  let width := fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices) in
  256 * S (length vertices) * (128 + 32 * width + Pos.size_nat next + length vertices).

Definition audit_rpo_graph_budget {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) :
  nat :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  let vertices := Graph.nodes g ++ map (Graph.source g) edges ++ map (Graph.target g) edges ++
    map fst (Map.elements (pre_num r)) ++ map fst (Map.elements (post_num r)) in
  let numbers := map snd (Map.elements (pre_num r)) ++ map snd (Map.elements (post_num r)) in
  let width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map Pos.size_nat numbers)) in
  4096 * S (length (Graph.nodes g) + length edges) * S (length (Graph.nodes g) + length edges) *
    (128 + 32 * width).

(** With correct encodings, position assignment returns the original map and meets its
    recorded-work bound. *)
Definition audit_rpo_positions_bound_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) vertices next,
    (forall v, fst (enc v) = encode EV v) ->
    let '(result, events) := audit_rpo_schedule_positions enc vertices next in
    result = schedule_positions EV vertices next /\
    audit_rpo_schedule_work weight events <= audit_rpo_positions_budget EV vertices next +
      audit_rpo_schedule_body_work weight events.

(** With correct graph callbacks, retreat detection returns the original set and meets its
    recorded-work bound. *)
Definition audit_rpo_retreats_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (cb : audit_rpo_graph_callbacks V E B) (weight : B -> nat),
    audit_rpo_graph_callbacks_erase EV g cb ->
    let '(result, events) := audit_rpo_schedule_retreats cb g r in
    result = schedule_retreats EV g r /\
    audit_rpo_graph_work weight events <= audit_rpo_graph_budget EV g r + audit_rpo_graph_body_work
      weight events.

(** With correct encodings, priority and widening queries return the original answers and their
    combined work fits the stated bound. *)
Definition audit_rpo_schedule_query_bound_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat) positions heads v,
    (forall x, fst (enc x) = encode EV x) ->
    let '(priority, priority_events) := audit_rpo_schedule_priority enc positions v in
    let '(widening, widening_events) := audit_rpo_schedule_widening enc heads v in
    priority = schedule_priority EV positions v /\ widening = FinSet.mem EV v heads /\
    audit_rpo_schedule_work weight priority_events + audit_rpo_schedule_work weight widening_events
      <=
      512 + 32 * Pos.size_nat (encode EV v) + audit_rpo_schedule_body_work weight priority_events +
        audit_rpo_schedule_body_work weight widening_events.

(** One generic adapter applies to each genuinely external callback signature. *)

Definition audit_rpo_schedule_event_budget {V B} (budget : V -> nat) (event :
    audit_rpo_schedule_event V B) : nat :=
  match event with
  | RpoScheduleMap (AuditMapGet key _ _ _ _ _)
  | RpoScheduleMap (AuditMapSet key _ _ _ _ _ _)
  | RpoScheduleMap (AuditMapRemove key _ _ _ _ _)
  | RpoScheduleSet (AuditSetMem key _ _ _ _ _)
  | RpoScheduleSet (AuditSetAdd key _ _ _ _ _)
  | RpoScheduleSet (AuditSetRemove key _ _ _ _ _) =>
      budget key
  | RpoScheduleSet (AuditSetFold _ _)
  | RpoScheduleNext _ _ _
  | RpoScheduleCase _ => 0
  end.

Definition audit_rpo_graph_event_budget {V E B} (encode_budget : V -> nat) (out_budget : V -> nat)
    (source_budget target_budget : E -> nat) (event : audit_rpo_graph_event V E B) : nat :=
  match event with
  | RpoGraphOut v _ _ => out_budget v
  | RpoGraphSource e _ _ => source_budget e
  | RpoGraphTarget e _ _ => target_budget e
  | RpoGraphRank (AuditMapGet key _ _ _ _ _)
  | RpoGraphRank (AuditMapSet key _ _ _ _ _ _)
  | RpoGraphRank (AuditMapRemove key _ _ _ _ _) | RpoGraphSet (AuditSetMem key _ _ _ _ _)
  | RpoGraphSet (AuditSetAdd key _ _ _ _ _)
  | RpoGraphSet (AuditSetRemove key _ _ _ _ _) =>
      encode_budget key
  | RpoGraphSet (AuditSetFold _ _)
  | RpoGraphCompare _ _ _ _
  | RpoGraphCase _ => 0
  end.

(** With encoder erasure and an adequate source adapter, position assignment has its original
    result and stated work bound. *)
Definition audit_rpo_positions_adapted_statement : Prop :=
  forall V B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat)
    source budget vertices next,
    (forall v, fst (enc v) = encode EV v) -> audit_graph_external_callback_adapter enc weight source
      budget ->
    let '(result, events) := audit_rpo_schedule_positions enc vertices next in
    result = schedule_positions EV vertices next /\
    audit_rpo_schedule_work weight events <= audit_rpo_positions_budget EV vertices next +
      fold_right (fun event n => audit_rpo_schedule_event_budget budget event + n) 0 events.

(** With graph callback erasure and adequate source adapters, retreat detection has its original
    result and stated work bound. *)
Definition audit_rpo_retreats_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (cb : audit_rpo_graph_callbacks V E B) (weight : B -> nat)
    encode_source out_source source_source target_source encode_budget out_budget source_budget
      target_budget,
    audit_rpo_graph_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_rpo_graph_encode cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_rpo_graph_out cb) weight out_source out_budget ->
    audit_graph_external_callback_adapter (audit_rpo_graph_source cb) weight source_source
      source_budget ->
    audit_graph_external_callback_adapter (audit_rpo_graph_target cb) weight target_source
      target_budget ->
    let '(result, events) := audit_rpo_schedule_retreats cb g r in
    result = schedule_retreats EV g r /\
    audit_rpo_graph_work weight events <= audit_rpo_graph_budget EV g r +
      fold_right (fun event n => audit_rpo_graph_event_budget encode_budget out_budget source_budget
        target_budget event + n) 0 events.

(** Every positive input has a successor run, and each run agrees with the counted successor and
    has twice the event count as work, bounded by twice the input bit size. *)
Definition audit_rpo_successor_source_obligations : Prop :=
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement.
