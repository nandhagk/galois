(** * Depth-first search audit model

    Models source-level events, work, and associated contract statements.
    For example, discovering a vertex records its set and map operations.

    Builds on: the graph and collections interfaces imported below. *)

From Galois.Collections Require Import CollectionsAuditCost CollectionsTrie.
From Galois.Graph Require Import GraphAuditBase.
From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditEncoding.
Import List.ListNotations.

Inductive audit_dfs_call (V E : Type) : Type :=
  | AuditDfsCase (site : nat)
  | AuditDfsTarget (edge : E) (target : V)
  | AuditDfsMember (vertex : V) (set : FinSet.t V) (result : bool)
  | AuditDfsSuccessors (vertex : V) (index : Map.t V (list E)) (result : option (list E))
  | AuditDfsDiscover (vertex : V) (via : option E) (before after : DfsState.t V E)
  | AuditDfsFinish (vertex : V) (before after : DfsState.t V E).
Arguments AuditDfsCase {V E} _.
Arguments AuditDfsTarget {V E} _ _.
Arguments AuditDfsMember {V E} _ _ _.
Arguments AuditDfsSuccessors {V E} _ _ _.
Arguments AuditDfsDiscover {V E} _ _ _ _.
Arguments AuditDfsFinish {V E} _ _ _.

Definition audit_dfs_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_call V E) :=
  let '(stack, st) := work in
  match stack with
  | [] => (([], st), [AuditDfsCase 0])
  | (v, []) :: rest =>
      let next := dfs_finish EV v st in
      ((rest, next), [AuditDfsCase 1; AuditDfsFinish v st next])
  | (v, e :: es) :: rest =>
      let target := Graph.target g e in
      let is_blocked := FinSet.mem EV target blocked in
      let is_seen := FinSet.mem EV target (DfsState.seen st) in
      if is_blocked || is_seen then
        (((v, es) :: rest, st), [AuditDfsTarget e target;
          AuditDfsMember target blocked is_blocked; AuditDfsMember target (DfsState.seen st)
            is_seen; AuditDfsCase 2])
      else
        let outgoing := Map.get EV target (out_index p) in
        let edges :=
          match outgoing with
          | Some xs => xs
          | None => []
          end in
        let next := dfs_discover EV target (Some e) st in
        (((target, edges) :: (v, es) :: rest, next),
         [AuditDfsTarget e target; AuditDfsMember target blocked is_blocked;
          AuditDfsMember target (DfsState.seen st) is_seen; AuditDfsCase 3; AuditDfsSuccessors
            target (out_index p) outgoing;
          AuditDfsDiscover target (Some e) st next])
  end.

Fixpoint audit_dfs_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (fuel : positive)
    (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_call V E) :=
  match fst work with
  | [] => (work, [AuditDfsCase 4])
  | _ :: _ =>
    match fuel with
    | xH => let '(result, events) := audit_dfs_step_counted p blocked work in
        (result, AuditDfsCase 5 :: events)
    | xO rest => let '(middle, first) := audit_dfs_run_counted p blocked rest work in
        let '(result, second) := audit_dfs_run_counted p blocked rest middle in
        (result, AuditDfsCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_dfs_run_counted p blocked rest work in
        let '(last, second) := audit_dfs_run_counted p blocked rest middle in
        let '(result, step_events) := audit_dfs_step_counted p blocked last in
        (result, AuditDfsCase 7 :: first ++ second ++ step_events)
    end
  end.

Definition audit_dfs_root_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (st : DfsState.t V E) (v : V)
    : DfsState.t V E * list (audit_dfs_call V E) :=
  let is_blocked := FinSet.mem EV v blocked in
  let is_seen := FinSet.mem EV v (DfsState.seen st) in
  if is_blocked || is_seen then
    (st, [AuditDfsMember v blocked is_blocked; AuditDfsMember v (DfsState.seen st) is_seen;
      AuditDfsCase 8])
  else
    let outgoing := Map.get EV v (out_index p) in
    let edges :=
      match outgoing with
      | Some xs => xs
      | None => []
      end in
    let discovered := dfs_discover EV v None st in
    let '(result, events) := audit_dfs_run_counted p blocked (fuel p) ([(v, edges)], discovered) in
    (snd result, [AuditDfsMember v blocked is_blocked;
      AuditDfsMember v (DfsState.seen st) is_seen; AuditDfsCase 9; AuditDfsSuccessors v (out_index
        p) outgoing;
      AuditDfsDiscover v None st discovered] ++ events).

Fixpoint audit_dfs_roots_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_call V E) :=
  match roots with
  | [] => (st, [AuditDfsCase 10])
  | root :: rest =>
      let '(next, here) := audit_dfs_root_counted p blocked st root in
      let '(result, later) := audit_dfs_roots_counted p blocked rest next in
      (result, AuditDfsCase 11 :: here ++ later)
  end.

Definition audit_dfs_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V)
    : dfs_result V E * list (audit_dfs_call V E) :=
  let '(st, events) := audit_dfs_roots_counted p blocked roots dfs_initial in
  (DfsResult (rev (DfsState.pre st)) (rev (DfsState.post st)) (DfsState.parent st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st), events).

Definition audit_dfs_model_event {V E} (EV : encoding V) (event : audit_dfs_call V E) : nat :=
  let read v := audit_get_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
    (encode EV v)) in
  let write v := audit_set_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
    (encode EV v)) in
  64 +
  match event with
  | AuditDfsMember v _ _
  | AuditDfsSuccessors v _ _ => read v
  | AuditDfsDiscover v via st _ =>
      (
        match via with
        | Some _ => 3
        | None => 2
        end) * write v +
      audit_binary_weight (Z.pos (DfsState.pre_clock st)) 1
  | AuditDfsFinish v st _ => write v + audit_binary_weight (Z.pos (DfsState.post_clock st)) 1
  | _ => 0
  end.

Definition audit_dfs_model_work {V E} (EV : encoding V) (events : list (audit_dfs_call V E)) : nat
  :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_dfs_model_event EV event + n) 0 events.

Definition audit_dfs_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let rows := Map.elements (out_index p) in
  let vertices := roots ++ Graph.nodes g ++ map fst rows ++
    flat_map (fun row => map (Graph.target g) (snd row)) rows in
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices).

Definition audit_dfs_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (roots : list V) : nat :=
  2 + length roots * (16 * S (Pos.to_nat (fuel p))).

Definition audit_dfs_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let events := audit_dfs_input_event_bound p roots in
  let clock_width := audit_key_bits_weight (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat
    (fuel p)))) in
  let width := Nat.max (audit_dfs_input_width EV g p roots) clock_width in
  256 * S events * S events + events * (80 + 12 * width).

(** Counted DFS returns DFS with bounded events and work. *)

Definition audit_dfs_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) blocked roots,
    let '(result, events) := audit_dfs_counted p blocked roots in
    result = dfs p blocked roots /\
    length events <= audit_dfs_input_event_bound p roots /\
    audit_dfs_model_work EV events <= audit_dfs_input_budget EV g p roots.

Inductive audit_dfs_detail (V E : Type) : Type :=
  | AuditDfsParentSet (v : V) (e : E) (m : Map.t V E)
  | AuditDfsNumSet (v : V) (number : positive) (m : Map.t V positive)
  | AuditDfsSeenAdd (v : V) (s : FinSet.t V)
  | AuditDfsClock (before after : positive).
Arguments AuditDfsParentSet {V E} _ _ _.
Arguments AuditDfsNumSet {V E} _ _ _.
Arguments AuditDfsSeenAdd {V E} _ _.
Arguments AuditDfsClock {V E} _ _.

Definition audit_dfs_discover_counted {V E} (EV : encoding V) (v : V) (via : option E)
    (st : DfsState.t V E) : DfsState.t V E * list (audit_dfs_detail V E) :=
  let '(parent, parent_events) :=
    match via with
    | Some e => (Map.set EV v e (DfsState.parent st), [AuditDfsParentSet v e (DfsState.parent st)])
    | None => (DfsState.parent st, [])
    end in
  let index := Map.set EV v (DfsState.pre_clock st) (DfsState.pre_index st) in
  let seen := FinSet.add EV v (DfsState.seen st) in
  let clock := Pos.succ (DfsState.pre_clock st) in
  (DfsState.Make (v :: DfsState.pre st) (DfsState.post st) parent index
    (DfsState.post_index st) seen clock (DfsState.post_clock st),
   parent_events ++ [AuditDfsNumSet v (DfsState.pre_clock st) (DfsState.pre_index st);
     AuditDfsSeenAdd v (DfsState.seen st); AuditDfsClock (DfsState.pre_clock st) clock]).

Definition audit_dfs_finish_counted {V E} (EV : encoding V) (v : V) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_detail V E) :=
  let index := Map.set EV v (DfsState.post_clock st) (DfsState.post_index st) in
  let clock := Pos.succ (DfsState.post_clock st) in
  (DfsState.Make (DfsState.pre st) (v :: DfsState.post st) (DfsState.parent st)
    (DfsState.pre_index st) index (DfsState.seen st) (DfsState.pre_clock st) clock,
   [AuditDfsNumSet v (DfsState.post_clock st) (DfsState.post_index st);
    AuditDfsClock (DfsState.post_clock st) clock]).

Definition audit_dfs_detail_work {V E} (EV : encoding V) (event : audit_dfs_detail V E) : nat :=
  64 +
  match event with
  | AuditDfsParentSet v _ _
  | AuditDfsNumSet v _ _
  | AuditDfsSeenAdd v _ =>
      audit_set_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight (encode EV v))
  | AuditDfsClock before _ => audit_binary_weight (Z.pos before) 1
  end.

(** Counted discovery and finish erase to their helpers with bounded events. *)
Definition audit_dfs_helpers_statement : Prop :=
  (forall V E (EV : encoding V) v via (st : DfsState.t V E),
    let '(result, events) := audit_dfs_discover_counted EV v via st in
    result = dfs_discover EV v via st /\ length events <= 4) /\
  (forall V E (EV : encoding V) v (st : DfsState.t V E),
    let '(result, events) := audit_dfs_finish_counted EV v st in
    result = dfs_finish EV v st /\ length events = 2).

Inductive audit_dfs_full_call (V E : Type) : Type :=
  | AuditDfsFullCase (site : nat)
  | AuditDfsFullTarget (edge : E) (target : V)
  | AuditDfsFullMember (vertex : V) (set : FinSet.t V) (result : bool)
  | AuditDfsFullSuccessors (vertex : V) (index : Map.t V (list E)) (result : option (list E))
  | AuditDfsFullDiscover (vertex : V) (via : option E) (before after : DfsState.t V E)
  | AuditDfsFullFinish (vertex : V) (before after : DfsState.t V E)
  | AuditDfsFullDetail (detail : audit_dfs_detail V E)
  | AuditDfsFullOutput (pre post : nat).
Arguments AuditDfsFullCase {V E} _.
Arguments AuditDfsFullTarget {V E} _ _.
Arguments AuditDfsFullMember {V E} _ _ _.
Arguments AuditDfsFullSuccessors {V E} _ _ _.
Arguments AuditDfsFullDiscover {V E} _ _ _ _.
Arguments AuditDfsFullFinish {V E} _ _ _.
Arguments AuditDfsFullDetail {V E} _.
Arguments AuditDfsFullOutput {V E} _ _.

Definition audit_dfs_full_step_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_full_call V E) :=
  let '(stack, st) := work in
  match stack with
  | [] => (([], st), [AuditDfsFullCase 0])
  | (v, []) :: rest =>
      let '(next, detail) := audit_dfs_finish_counted EV v st in
      ((rest, next), AuditDfsFullCase 1 :: map AuditDfsFullDetail detail ++ [AuditDfsFullFinish v
        st next])
  | (v, e :: es) :: rest =>
      let target := Graph.target g e in
      let is_blocked := FinSet.mem EV target blocked in
      let is_seen := FinSet.mem EV target (DfsState.seen st) in
      if is_blocked || is_seen then
        (((v, es) :: rest, st), [AuditDfsFullTarget e target;
          AuditDfsFullMember target blocked is_blocked; AuditDfsFullMember target (DfsState.seen
            st) is_seen; AuditDfsFullCase 2])
      else
        let outgoing := Map.get EV target (out_index p) in
        let edges :=
          match outgoing with
          | Some xs => xs
          | None => []
          end in
        let '(next, detail) := audit_dfs_discover_counted EV target (Some e) st in
        (((target, edges) :: (v, es) :: rest, next),
         [AuditDfsFullTarget e target; AuditDfsFullMember target blocked is_blocked;
          AuditDfsFullMember target (DfsState.seen st) is_seen; AuditDfsFullCase 3;
            AuditDfsFullSuccessors target (out_index p) outgoing] ++
          map AuditDfsFullDetail detail ++ [AuditDfsFullDiscover target (Some e) st next])
  end.

Fixpoint audit_dfs_full_run_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (fuel : positive)
    (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_full_call V E) :=
  match fst work with
  | [] => (work, [AuditDfsFullCase 4])
  | _ :: _ =>
    match fuel with
    | xH => let '(result, events) := audit_dfs_full_step_counted p blocked work in
        (result, AuditDfsFullCase 5 :: events)
    | xO rest => let '(middle, first) := audit_dfs_full_run_counted p blocked rest work in
        let '(result, second) := audit_dfs_full_run_counted p blocked rest middle in
        (result, AuditDfsFullCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_dfs_full_run_counted p blocked rest work in
        let '(last, second) := audit_dfs_full_run_counted p blocked rest middle in
        let '(result, step_events) := audit_dfs_full_step_counted p blocked last in
        (result, AuditDfsFullCase 7 :: first ++ second ++ step_events)
    end
  end.

Definition audit_dfs_full_root_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (st : DfsState.t V E) (v : V)
    : DfsState.t V E * list (audit_dfs_full_call V E) :=
  let is_blocked := FinSet.mem EV v blocked in
  let is_seen := FinSet.mem EV v (DfsState.seen st) in
  if is_blocked || is_seen then
    (st, [AuditDfsFullMember v blocked is_blocked; AuditDfsFullMember v (DfsState.seen st)
      is_seen; AuditDfsFullCase 8])
  else
    let outgoing := Map.get EV v (out_index p) in
    let edges :=
      match outgoing with
      | Some xs => xs
      | None => []
      end in
    let '(discovered, detail) := audit_dfs_discover_counted EV v None st in
    let '(result, events) := audit_dfs_full_run_counted p blocked (fuel p) ([(v, edges)],
      discovered) in
    (snd result, [AuditDfsFullMember v blocked is_blocked;
      AuditDfsFullMember v (DfsState.seen st) is_seen; AuditDfsFullCase 9; AuditDfsFullSuccessors
        v (out_index p) outgoing] ++
      map AuditDfsFullDetail detail ++ [AuditDfsFullDiscover v None st discovered] ++ events).

Fixpoint audit_dfs_full_roots_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_full_call V E) :=
  match roots with
  | [] => (st, [AuditDfsFullCase 10])
  | root :: rest =>
      let '(next, here) := audit_dfs_full_root_counted p blocked st root in
      let '(result, later) := audit_dfs_full_roots_counted p blocked rest next in
      (result, AuditDfsFullCase 11 :: here ++ later)
  end.

Definition audit_dfs_full_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (roots : list V)
    : dfs_result V E * list (audit_dfs_full_call V E) :=
  let '(st, events) := audit_dfs_full_roots_counted p blocked roots dfs_initial in
  (DfsResult (rev (DfsState.pre st)) (rev (DfsState.post st)) (DfsState.parent st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st),
    events ++ [AuditDfsFullOutput (length (DfsState.pre st)) (length (DfsState.post st))]).

Definition audit_dfs_full_model_event {V E} (EV : encoding V) (event : audit_dfs_full_call V E) :
  nat :=
  let read v := audit_get_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
    (encode EV v)) in
  let write v := audit_set_weight (encode EV v) + audit_encoding_weight (audit_key_bits_weight
    (encode EV v)) in
  64 +
  match event with
  | AuditDfsFullMember v _ _
  | AuditDfsFullSuccessors v _ _ => read v
  | AuditDfsFullDetail detail => audit_dfs_detail_work EV detail
  | AuditDfsFullOutput before after => before + after
  | _ => 0
  end.

Definition audit_dfs_full_model_work {V E} (EV : encoding V) (events : list (audit_dfs_full_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_dfs_full_model_event EV event + n) 0 events.

Definition audit_dfs_full_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let rows := Map.elements (out_index p) in
  let vertices := roots ++ Graph.nodes g ++ map fst rows ++
    flat_map (fun row => map (Graph.target g) (snd row)) rows in
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices).

Definition audit_dfs_full_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (roots : list V) : nat :=
  3 + length roots * (40 * S (Pos.to_nat (fuel p))).

Definition audit_dfs_full_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let events := audit_dfs_full_input_event_bound p roots in
  let clock_width := audit_key_bits_weight (Pos.of_succ_nat (2 + length roots * S (Pos.to_nat
    (fuel p)))) in
  let width := Nat.max (audit_dfs_full_input_width EV g p roots) clock_width in
  512 * S events * S events + events * (140 + 12 * width).

(** Full counted DFS returns DFS with bounded events and work. *)
Definition audit_dfs_full_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) blocked roots,
    let '(result, events) := audit_dfs_full_counted p blocked roots in
    result = dfs p blocked roots /\
    length events <= audit_dfs_full_input_event_bound p roots /\
    audit_dfs_full_model_work EV events <= audit_dfs_full_input_budget EV g p roots.

Record audit_dfs_callback_model (V E B : Type) : Type := AuditDfsCallbackModel {
  audit_dfs_target_model : E -> V * list B;
  audit_dfs_encode_model : V -> positive * list B
}.
Arguments audit_dfs_target_model {V E B} _ _.
Arguments audit_dfs_encode_model {V E B} _ _.

(** DFS callbacks return the original target and encoding values. *)
Definition audit_dfs_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_dfs_callback_model V E B) : Prop :=
  (forall e, fst (audit_dfs_target_model cb e) = Graph.target g e) /\
  (forall v, fst (audit_dfs_encode_model cb v) = encode EV v).

Definition audit_dfs_nested_event (V E B : Type) : Type := audit_dfs_full_call V E * list B.

Definition audit_dfs_nested_get {V A E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (m : Map.t V A) : option A * list B :=
  let '(code, body) := audit_dfs_encode_model cb v in (Map.code_get code m, body).

Definition audit_dfs_nested_set {V A E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (value : A) (m : Map.t V A) : Map.t V A * list B :=
  let '(code, body) := audit_dfs_encode_model cb v in (Trie.set code (v, value) m, body).

Definition audit_dfs_nested_discover {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (via : option E) (st : DfsState.t V E)
    : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  let '(parent, parent_events) :=
    match via with
    | Some e => let '(next, body) := audit_dfs_nested_set cb v e (DfsState.parent st) in
        (next, [(AuditDfsFullDetail (AuditDfsParentSet v e (DfsState.parent st)), body)])
    | None => (DfsState.parent st, [])
    end in
  let '(index, index_body) := audit_dfs_nested_set cb v (DfsState.pre_clock st)
    (DfsState.pre_index st) in
  let '(seen, seen_body) := audit_dfs_nested_set cb v tt (DfsState.seen st) in
  let clock := Pos.succ (DfsState.pre_clock st) in
  (DfsState.Make (v :: DfsState.pre st) (DfsState.post st) parent index
    (DfsState.post_index st) seen clock (DfsState.post_clock st),
   parent_events ++ [(AuditDfsFullDetail (AuditDfsNumSet v (DfsState.pre_clock st)
     (DfsState.pre_index st)), index_body);
     (AuditDfsFullDetail (AuditDfsSeenAdd v (DfsState.seen st)), seen_body);
     (AuditDfsFullDetail (AuditDfsClock (DfsState.pre_clock st) clock), [])]).

Definition audit_dfs_nested_finish {V E B} (cb : audit_dfs_callback_model V E B)
    (v : V) (st : DfsState.t V E) : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  let '(index, body) := audit_dfs_nested_set cb v (DfsState.post_clock st) (DfsState.post_index
    st) in
  let clock := Pos.succ (DfsState.post_clock st) in
  (DfsState.Make (DfsState.pre st) (v :: DfsState.post st) (DfsState.parent st)
    (DfsState.pre_index st) index (DfsState.seen st) (DfsState.pre_clock st) clock,
   [(AuditDfsFullDetail (AuditDfsNumSet v (DfsState.post_clock st) (DfsState.post_index st)), body);
    (AuditDfsFullDetail (AuditDfsClock (DfsState.post_clock st) clock), [])]).

Definition audit_dfs_nested_step {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_nested_event V E B) :=
  let '(stack, st) := work in
  match stack with
  | [] => (([], st), [(AuditDfsFullCase 0, [])])
  | (v, []) :: rest => let '(next, detail) := audit_dfs_nested_finish cb v st in
      ((rest, next), (AuditDfsFullCase 1, []) :: detail ++ [(AuditDfsFullFinish v st next, [])])
  | (v, e :: es) :: rest =>
      let '(target, target_body) := audit_dfs_target_model cb e in
      let '(blocked_value, blocked_body) := audit_dfs_nested_get cb target blocked in
      let is_blocked :=
        match blocked_value with
        | Some _ => true
        | None => false
        end in
      let '(seen_value, seen_body) := audit_dfs_nested_get cb target (DfsState.seen st) in
      let is_seen :=
        match seen_value with
        | Some _ => true
        | None => false
        end in
      if is_blocked || is_seen then
        (((v, es) :: rest, st), [(AuditDfsFullTarget e target, target_body);
          (AuditDfsFullMember target blocked is_blocked, blocked_body);
          (AuditDfsFullMember target (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 2,
            [])])
      else let '(outgoing, outgoing_body) := audit_dfs_nested_get cb target (out_index p) in
        let edges :=
          match outgoing with
          | Some xs => xs
          | None => []
          end in
        let '(next, details) := audit_dfs_nested_discover cb target (Some e) st in
        (((target, edges) :: (v, es) :: rest, next),
          [(AuditDfsFullTarget e target, target_body); (AuditDfsFullMember target blocked
            is_blocked, blocked_body);
           (AuditDfsFullMember target (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 3,
             []);
           (AuditDfsFullSuccessors target (out_index p) outgoing, outgoing_body)] ++ details ++
           [(AuditDfsFullDiscover target (Some e) st next, [])])
  end.

Fixpoint audit_dfs_nested_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (fuel : positive) (work : dfs_stack V E * DfsState.t V E)
    : (dfs_stack V E * DfsState.t V E) * list (audit_dfs_nested_event V E B) :=
  match fst work with
  | [] => (work, [(AuditDfsFullCase 4, [])])
  | _ :: _ =>
    match fuel with
    | xH => let '(result, events) := audit_dfs_nested_step p cb blocked work in
        (result, (AuditDfsFullCase 5, []) :: events)
    | xO rest => let '(middle, first) := audit_dfs_nested_run p cb blocked rest work in
        let '(result, second) := audit_dfs_nested_run p cb blocked rest middle in
        (result, (AuditDfsFullCase 6, []) :: first ++ second)
    | xI rest => let '(middle, first) := audit_dfs_nested_run p cb blocked rest work in
        let '(last, second) := audit_dfs_nested_run p cb blocked rest middle in
        let '(result, step_events) := audit_dfs_nested_step p cb blocked last in
        (result, (AuditDfsFullCase 7, []) :: first ++ second ++ step_events)
    end
  end.

Definition audit_dfs_nested_root {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (st : DfsState.t V E) (v : V) : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  let '(blocked_value, blocked_body) := audit_dfs_nested_get cb v blocked in
  let is_blocked :=
    match blocked_value with
    | Some _ => true
    | None => false
    end in
  let '(seen_value, seen_body) := audit_dfs_nested_get cb v (DfsState.seen st) in
  let is_seen :=
    match seen_value with
    | Some _ => true
    | None => false
    end in
  if is_blocked || is_seen then
    (st, [(AuditDfsFullMember v blocked is_blocked, blocked_body);
      (AuditDfsFullMember v (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 8, [])])
  else let '(outgoing, outgoing_body) := audit_dfs_nested_get cb v (out_index p) in
    let edges :=
      match outgoing with
      | Some xs => xs
      | None => []
      end in
    let '(discovered, details) := audit_dfs_nested_discover cb v None st in
    let '(result, events) := audit_dfs_nested_run p cb blocked (fuel p) ([(v, edges)], discovered)
      in
    (snd result, [(AuditDfsFullMember v blocked is_blocked, blocked_body);
      (AuditDfsFullMember v (DfsState.seen st) is_seen, seen_body); (AuditDfsFullCase 9, []);
      (AuditDfsFullSuccessors v (out_index p) outgoing, outgoing_body)] ++ details ++
      [(AuditDfsFullDiscover v None st discovered, [])] ++ events).

Fixpoint audit_dfs_nested_roots {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V)
    (roots : list V) (st : DfsState.t V E) : DfsState.t V E * list (audit_dfs_nested_event V E B) :=
  match roots with
  | [] => (st, [(AuditDfsFullCase 10, [])])
  | root :: rest => let '(next, here) := audit_dfs_nested_root p cb blocked st root in
      let '(result, later) := audit_dfs_nested_roots p cb blocked rest next in
      (result, (AuditDfsFullCase 11, []) :: here ++ later)
  end.

Definition audit_dfs_nested_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) (blocked : FinSet.t V) (roots : list
      V)
    : dfs_result V E * list (audit_dfs_nested_event V E B) :=
  let '(st, events) := audit_dfs_nested_roots p cb blocked roots dfs_initial in
  (DfsResult (rev (DfsState.pre st)) (rev (DfsState.post st)) (DfsState.parent st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st),
   events ++ [(AuditDfsFullOutput (length (DfsState.pre st)) (length (DfsState.post st)), [])]).

Definition audit_dfs_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd event) + total)
    0 events.

(** Nested DFS erases to the full trace and obeys its event and work bounds. *)
Definition audit_dfs_nested_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
      (cb : audit_dfs_callback_model V E B) blocked roots,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_dfs_nested_counted p cb blocked roots in
    result = dfs p blocked roots /\ map fst events = snd (audit_dfs_full_counted p blocked roots) /\
    length events <= audit_dfs_full_input_event_bound p roots /\
    audit_dfs_full_model_work EV (map fst events) <= audit_dfs_full_input_budget EV g p roots.

Definition audit_dfs_nested_total_work {V E B} (EV : encoding V) (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E B)) : nat :=
  audit_dfs_full_model_work EV (map fst events) + audit_dfs_nested_body_work weight events.

Inductive audit_graph_callback_capture (V E B : Type) : Type :=
  | AuditGraphTargetCapture : E -> V -> list B -> audit_graph_callback_capture V E B
  | AuditGraphEncodeCapture : V -> positive -> list B -> audit_graph_callback_capture V E B.

Definition audit_graph_capture_callbacks {V E B} (cb : audit_dfs_callback_model V E B)
    : audit_dfs_callback_model V E (audit_graph_callback_capture V E B) :=
  AuditDfsCallbackModel V E (audit_graph_callback_capture V E B)
    (fun edge => let '(value, body) := audit_dfs_target_model cb edge in
      (value, [AuditGraphTargetCapture V E B edge value body]))
    (fun vertex => let '(code, body) := audit_dfs_encode_model cb vertex in
      (code, [AuditGraphEncodeCapture V E B vertex code body])).

(** Capturing erasing graph callbacks preserves their erasure. *)
Definition audit_graph_capture_callbacks_erases_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (cb : audit_dfs_callback_model V E B),
    audit_dfs_callbacks_erase EV g cb ->
    audit_dfs_callbacks_erase EV g (audit_graph_capture_callbacks cb).

Definition audit_graph_capture_work {V E B} (weight : B -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphTargetCapture _ _ _ _ _ body
  | AuditGraphEncodeCapture _ _ _ _ _ body =>
      fold_right (fun item total => weight item + total) 0 body
  end.

Definition audit_dfs_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (cb : audit_dfs_callback_model V E B) blocked roots :=
  let '(st, events) := audit_dfs_nested_roots p (audit_graph_capture_callbacks cb) blocked roots
    dfs_initial in
  (DfsResult (rev_append (DfsState.pre st) []) (rev_append (DfsState.post st) []) (DfsState.parent
    st)
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st),
   events ++ [(AuditDfsFullOutput (length (DfsState.pre st)) (length (DfsState.post st)), [])]).

Definition audit_dfs_source_code {V E B} (body : list (audit_graph_callback_capture V E B)) :
  positive :=
  match body with
  | [AuditGraphEncodeCapture _ _ _ _ code _] => code
  | _ => 1%positive
  end.

Definition audit_dfs_source_event_work {V E B} (weight : B -> nat)
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : nat :=
  let '(event, body) := item in let code := audit_dfs_source_code body in
  let callback_work := fold_right (fun item n => audit_graph_capture_work weight item + n) 0 body in
  64 + callback_work +
  match event with
  | AuditDfsFullMember _ set _ => 5 + audit_trie_get_source_work code set
  | AuditDfsFullSuccessors _ input _ => 5 + audit_trie_get_source_work code input
  | AuditDfsFullDetail (AuditDfsParentSet v edge input) =>
      2 + audit_trie_update_source_work code (Some (v, edge)) input
  | AuditDfsFullDetail (AuditDfsNumSet v number input) =>
      2 + audit_trie_update_source_work code (Some (v, number)) input
  | AuditDfsFullDetail (AuditDfsSeenAdd v input) =>
      2 + audit_trie_update_source_work code (Some (v, tt)) input
  | AuditDfsFullDetail (AuditDfsClock before _) => 2 * Pos.size_nat before
  | AuditDfsFullOutput pre post => audit_graph_reverse_fast_work pre +
    audit_graph_reverse_fast_work post
  | _ => 0
  end.

Definition audit_dfs_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_graph_capture_work weight event + k)
    0 (snd item) + n) 0 events.

Definition audit_dfs_source_work {V E B} (weight : B -> nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => audit_dfs_source_event_work weight item + n) 0 events.

(** A DFS source event carries the matching callback capture. *)
Definition audit_dfs_source_event_wellformed {V E B}
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  let '(event, body) := item in
  match event with
  | AuditDfsFullMember v _ _
  | AuditDfsFullSuccessors v _ _ =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditDfsFullDetail (AuditDfsParentSet v _ _)
  | AuditDfsFullDetail (AuditDfsNumSet v _ _)
  | AuditDfsFullDetail (AuditDfsSeenAdd v _) =>
      exists code trace, body = [AuditGraphEncodeCapture V E B v code trace]
  | AuditDfsFullTarget e v => exists trace, body = [AuditGraphTargetCapture V E B e v trace]
  | _ => body = []
  end.

Definition audit_dfs_source_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) : nat :=
  let count := audit_dfs_full_input_event_bound p roots in
  let width := Nat.max (audit_dfs_full_input_width EV g p roots)
    (Pos.size_nat (Pos.of_succ_nat (S (length roots) * S (Pos.to_nat (fuel p))))) in
  1024 * S count * S count + count * (512 + 64 * width).

(** Source DFS returns DFS with well-formed events and bounded work. *)
Definition audit_dfs_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) blocked roots,
    audit_dfs_callbacks_erase EV g cb ->
    let '(result, events) := audit_dfs_source_counted p cb blocked roots in
    result = dfs p blocked roots /\ Forall audit_dfs_source_event_wellformed events /\
    length events <= audit_dfs_full_input_event_bound p roots /\
    audit_dfs_source_work weight events <= audit_dfs_source_budget EV g p roots +
      audit_dfs_source_body_work weight events.

(** DFS requires the legacy and tail-recursive reverse contracts. *)
Definition audit_dfs_source_reverse_obligations : Prop :=
  audit_graph_reverse_run_statement /\ audit_graph_reverse_fast_run_statement /\
  audit_graph_reverse_fast_counted_statement.

(** A clock event agrees with the positive successor model. *)
Definition audit_dfs_source_successor_event {V E B}
    (item : audit_dfs_nested_event V E (audit_graph_callback_capture V E B)) : Prop :=
  match fst item with
  | AuditDfsFullDetail (AuditDfsClock before after) => fst (audit_positive_succ before) = after
  | _ => True
  end.

(** Every source DFS event satisfies the successor correspondence. *)
Definition audit_dfs_source_successor_correspondence_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) blocked roots,
    audit_dfs_callbacks_erase EV g cb ->
    Forall audit_dfs_source_successor_event (snd (audit_dfs_source_counted p cb blocked roots)).

(** DFS requires successor totality, correctness and event correspondence. *)
Definition audit_dfs_source_successor_obligations : Prop :=
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement /\
  audit_dfs_source_successor_correspondence_statement.

Definition audit_dfs_capture_budget {V E B} (encode_budget : V -> nat) (target_budget : E -> nat)
    (event : audit_graph_callback_capture V E B) : nat :=
  match event with
  | AuditGraphEncodeCapture _ _ _ vertex _ _ => encode_budget vertex
  | AuditGraphTargetCapture _ _ _ edge _ _ => target_budget edge
  end.

Definition audit_dfs_source_external_budget {V E B} (encode_budget : V -> nat) (target_budget : E
  -> nat)
    (events : list (audit_dfs_nested_event V E (audit_graph_callback_capture V E B))) : nat :=
  fold_right (fun item n => fold_right (fun event k => audit_dfs_capture_budget encode_budget
    target_budget event + k)
    0 (snd item) + n) 0 events.

(** Adapted DFS bounds external callback work by the supplied budgets. *)
Definition audit_dfs_source_adapted_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_dfs_callback_model V E B) (weight : B -> nat) blocked roots
    encode_source target_source encode_budget target_budget,
    audit_dfs_callbacks_erase EV g cb ->
    audit_graph_external_callback_adapter (audit_dfs_encode_model cb) weight encode_source
      encode_budget ->
    audit_graph_external_callback_adapter (audit_dfs_target_model cb) weight target_source
      target_budget ->
    let '(result, events) := audit_dfs_source_counted p cb blocked roots in
    result = dfs p blocked roots /\
    audit_dfs_source_work weight events <= audit_dfs_source_budget EV g p roots +
      audit_dfs_source_external_budget encode_budget target_budget events.

(** The DFS source contract combines its primitive and source obligations. *)
Definition audit_dfs_source_contract_statement : Prop :=
  audit_dfs_source_statement /\ audit_dfs_source_adapted_statement /\
  audit_dfs_source_reverse_obligations /\ audit_dfs_source_successor_obligations /\
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement.
