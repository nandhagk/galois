(** * Semi-NCA source contracts

    Record each ancestor walk and its actual map and comparison bodies.
    For example, a missing parent stops the walk without consulting later ranks.
    Builds on: semidominator and graph source models. *)

From Stdlib Require Import List Bool PArith NArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditCost CollectionsAuditTrie CollectionsAuditMap
    CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditPrimitive
      CollectionsAuditCompare CollectionsAuditEncoding.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators GraphSemiNca
  GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditSemiDominators.
Import List.ListNotations.

Inductive audit_nca_walk_run {V E} (EV : encoding V) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) : V -> V -> list (audit_semi_call V) -> Prop :=
  | AuditNcaThreshold v rank events :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = true ->
    audit_nca_walk_run EV r limit parents v v (events ++ [AuditSemiLe rank limit true;
      AuditSemiCase 20])
  | AuditNcaNoParent v rank events :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = false ->
    Map.get EV v parents = None ->
    audit_nca_walk_run EV r limit parents v v
      (events ++ [AuditSemiLe rank limit false; AuditSemiCase 21; AuditSemiGet v parents None;
        AuditSemiCase 22])
  | AuditNcaStop v rank events a ra rv ea ev :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = false ->
    Map.get EV v parents = Some a -> audit_semi_rank_counted EV r a = (ra, ea) ->
    audit_semi_rank_counted EV r v = (rv, ev) -> Pos.ltb ra rv = false ->
    audit_nca_walk_run EV r limit parents v v
      (events ++ [AuditSemiLe rank limit false; AuditSemiCase 21; AuditSemiGet v parents (Some a)]
        ++
        ea ++ ev ++ [AuditSemiLess ra rv false; AuditSemiCase 23])
  | AuditNcaRecur v rank events a ra rv ea ev result inner :
    audit_semi_rank_counted EV r v = (rank, events) -> Pos.leb rank limit = false ->
    Map.get EV v parents = Some a -> audit_semi_rank_counted EV r a = (ra, ea) ->
    audit_semi_rank_counted EV r v = (rv, ev) -> Pos.ltb ra rv = true ->
    audit_nca_walk_run EV r limit parents a result inner ->
    audit_nca_walk_run EV r limit parents v result
      (events ++ [AuditSemiLe rank limit false; AuditSemiCase 21; AuditSemiGet v parents (Some a)]
        ++
        ea ++ ev ++ [AuditSemiLess ra rv true; AuditSemiCase 24] ++ inner).

Definition audit_nca_walk_width {V E} (EV : encoding V) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) (v : V) : nat :=
  let pairs := Map.elements parents in
  let vertices := v :: map fst pairs ++ map snd pairs ++ map fst (Map.elements (pre_num r)) in
  Nat.max (audit_key_bits_weight limit)
    (Nat.max (fold_right Nat.max 0 (map (fun x => audit_key_bits_weight (encode EV x)) vertices))
      (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements
        (pre_num r))))).

Definition audit_nca_walk_event_bound {V E} (EV : encoding V) (r : dfs_result V E) (v : V) : nat :=
  12 * S (Pos.to_nat (semi_rank EV r v)).

Definition audit_nca_walk_budget {V E} (EV : encoding V) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) (v : V) : nat :=
  let count := audit_nca_walk_event_bound EV r v in
  let width := audit_nca_walk_width EV r limit parents v in
  128 * S count * S count + count * (80 + 6 * width).

(** NCA walking admits a run with the original result and bounded events and work. *)
Definition audit_nca_walk_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) limit parents v,
    exists result events, audit_nca_walk_run EV r limit parents v result events /\
      result = nca_walk EV (semi_rank EV r) limit parents v /\
      length events <= audit_nca_walk_event_bound EV r v /\
      audit_semi_compress_work EV events <= audit_nca_walk_budget EV r limit parents v.

(** NCA walking runs have unique results and event traces. *)
Definition audit_nca_walk_unique_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) limit parents v x y ex ey,
    audit_nca_walk_run EV r limit parents v x ex -> audit_nca_walk_run EV r limit parents v y ey ->
    x = y /\ ex = ey.

Inductive audit_nca_call (V E : Type) : Type :=
  | AuditNcaCase (site : nat)
  | AuditNcaTreeGet (v : V) (m : Map.t V E) (result : option E)
  | AuditNcaSource (e : E) (v : V)
  | AuditNcaInner (event : audit_semi_call V).
Arguments AuditNcaCase {V E} _.
Arguments AuditNcaTreeGet {V E} _ _ _.
Arguments AuditNcaSource {V E} _ _.
Arguments AuditNcaInner {V E} _.

Inductive audit_nca_step_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V -> V -> Map.t V V ->
    list (audit_nca_call V E) -> Prop :=
  | AuditNcaStepRoot m v : Map.get EV v (tree_edge r) = None ->
    audit_nca_step_run EV g r semis m v m [AuditNcaTreeGet v (tree_edge r) None; AuditNcaCase 0]
  | AuditNcaStepNode m v e value value_events limit limit_events source result walk_events :
    Map.get EV v (tree_edge r) = Some e -> audit_semi_value_counted EV semis v = (value,
      value_events) ->
    audit_semi_rank_counted EV r value = (limit, limit_events) -> source = Graph.source g e ->
    audit_nca_walk_run EV r limit m source result walk_events ->
    audit_nca_step_run EV g r semis m v (Map.set EV v result m)
      ([AuditNcaTreeGet v (tree_edge r) (Some e); AuditNcaCase 1] ++ map AuditNcaInner
        value_events ++
       map AuditNcaInner limit_events ++ [AuditNcaSource e source] ++ map AuditNcaInner
         walk_events ++
       [AuditNcaInner (AuditSemiSet v result m)]).

Inductive audit_nca_steps_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : list V -> Map.t V V -> Map.t V V ->
    list (audit_nca_call V E) -> Prop :=
  | AuditNcaStepsNil m : audit_nca_steps_run EV g r semis [] m m [AuditNcaCase 2]
  | AuditNcaStepsCons v rest initial middle result here later :
    audit_nca_step_run EV g r semis initial v middle here ->
    audit_nca_steps_run EV g r semis rest middle result later ->
    audit_nca_steps_run EV g r semis (v :: rest) initial result (AuditNcaCase 3 :: here ++ later).

(** An NCA computation run relates its inputs, result and event trace. *)
Definition audit_nca_compute_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) (result : Map.t V V) (events : list (audit_nca_call V
      E)) : Prop :=
  audit_nca_steps_run EV g r semis (preorder r) Map.empty result events.

Definition audit_nca_event_work {V E} (EV : encoding V) (event : audit_nca_call V E) : nat :=
  64 +
  match event with
  | AuditNcaTreeGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_get_weight (encode EV v)
  | AuditNcaInner inner => audit_semi_call_work EV inner
  | _ => 0
  end.

Definition audit_nca_compute_work {V E} (EV : encoding V) (events : list (audit_nca_call V E)) :
  nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_nca_event_work EV event + total) 0 events.

Definition audit_nca_compute_event_bound {V E} (r : dfs_result V E) : nat :=
  64 * S (length (preorder r)) * S (audit_semi_compute_rank_bound r).

Definition audit_nca_compute_width {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge
    r)) ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
      r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
      r)))).

Definition audit_nca_compute_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let count := audit_nca_compute_event_bound r in
  let width := audit_nca_compute_width EV g r semis in
  512 * S count * S count + count * (256 + 12 * width).

(** NCA computation admits a run with the original result and bounded events and work. *)
Definition audit_nca_compute_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis,
    exists result events, audit_nca_compute_run EV g r semis result events /\
      result = nca_compute EV g r semis /\ length events <= audit_nca_compute_event_bound r /\
      audit_nca_compute_work EV events <= audit_nca_compute_budget EV g r semis.

(** NCA computation runs have unique results and event traces. *)
Definition audit_nca_compute_unique_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis a b ea eb,
    audit_nca_compute_run EV g r semis a ea -> audit_nca_compute_run EV g r semis b eb -> a = b /\
      ea = eb.

Inductive audit_nca_source_event (V E B : Type) : Type :=
  | NcaSourceCase : nat -> audit_nca_source_event V E B
  | NcaSourceTree : audit_map_event V E B -> audit_nca_source_event V E B
  | NcaSourceSource : E -> V -> list B -> audit_nca_source_event V E B
  | NcaSourceInner : audit_semi_nested_event V B -> audit_nca_source_event V E B.
Arguments NcaSourceCase {V E B} _.
Arguments NcaSourceTree {V E B} _.
Arguments NcaSourceSource {V E B} _ _ _.
Arguments NcaSourceInner {V E B} _.

Inductive audit_nca_source_walk_run {V E B} (enc : V -> positive * list B) (r : dfs_result V E)
    (limit : positive) (parents : Map.t V V) : V -> V -> list (audit_semi_nested_event V B) ->
      Prop :=
  | NcaSourceThreshold v rank events cmp :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (true, cmp)
      ->
    audit_nca_source_walk_run enc r limit parents v v (events ++ [SemiNestedCompare rank limit
      true cmp; SemiNestedCase 20])
  | NcaSourceNoParent v rank events cmp reads :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (false,
      cmp) ->
    audit_map_get enc v parents = (None, reads) ->
    audit_nca_source_walk_run enc r limit parents v v
      (events ++ [SemiNestedCompare rank limit false cmp; SemiNestedCase 21] ++
        map SemiNestedVertexMap reads ++ [SemiNestedCase 22])
  | NcaSourceStop v rank events cmp a reads ra rv ea ev cmp2 :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (false,
      cmp) ->
    audit_map_get enc v parents = (Some a, reads) -> audit_semi_nested_rank enc r a = (ra, ea) ->
    audit_semi_nested_rank enc r v = (rv, ev) -> audit_positive_ltb ra rv = (false, cmp2) ->
    audit_nca_source_walk_run enc r limit parents v v
      (events ++ [SemiNestedCompare rank limit false cmp; SemiNestedCase 21] ++ map
        SemiNestedVertexMap reads ++
        ea ++ ev ++ [SemiNestedCompare ra rv false cmp2; SemiNestedCase 23])
  | NcaSourceRecur v rank events cmp a reads ra rv ea ev cmp2 result inner :
    audit_semi_nested_rank enc r v = (rank, events) -> audit_positive_leb rank limit = (false,
      cmp) ->
    audit_map_get enc v parents = (Some a, reads) -> audit_semi_nested_rank enc r a = (ra, ea) ->
    audit_semi_nested_rank enc r v = (rv, ev) -> audit_positive_ltb ra rv = (true, cmp2) ->
    audit_nca_source_walk_run enc r limit parents a result inner ->
    audit_nca_source_walk_run enc r limit parents v result
      (events ++ [SemiNestedCompare rank limit false cmp; SemiNestedCase 21] ++ map
        SemiNestedVertexMap reads ++
        ea ++ ev ++ [SemiNestedCompare ra rv true cmp2; SemiNestedCase 24] ++ inner).

Inductive audit_nca_source_step_run {V E B} (enc : V -> positive * list B) (source : E -> V * list
  B)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V -> V -> Map.t V V -> list
      (audit_nca_source_event V E B) -> Prop :=
  | NcaSourceRoot m v reads : audit_map_get enc v (tree_edge r) = (None, reads) ->
    audit_nca_source_step_run enc source r semis m v m (map NcaSourceTree reads ++ [NcaSourceCase
      0])
  | NcaSourceNode m v edge reads value values limit ranks origin body result walk output writes :
    audit_map_get enc v (tree_edge r) = (Some edge, reads) ->
    audit_map_get enc v semis = (value, values) ->
    audit_semi_nested_rank enc r (
      match value with
      | Some x => x
      | None => v
      end) = (limit, ranks) ->
    source edge = (origin, body) -> audit_nca_source_walk_run enc r limit m origin result walk ->
    audit_map_set enc v result m = (output, writes) ->
    audit_nca_source_step_run enc source r semis m v output
      (map NcaSourceTree reads ++ [NcaSourceCase 1] ++
       map (fun item => NcaSourceInner (SemiNestedVertexMap item)) values ++ map NcaSourceInner
         ranks ++
       [NcaSourceSource edge origin body] ++ map NcaSourceInner walk ++
       map (fun item => NcaSourceInner (SemiNestedVertexMap item)) writes).

Inductive audit_nca_source_steps_run {V E B} (enc : V -> positive * list B) (source : E -> V *
  list B)
    (r : dfs_result V E) (semis : Map.t V V) : list V -> Map.t V V -> Map.t V V -> list
      (audit_nca_source_event V E B) -> Prop :=
  | NcaSourceStepsNil m : audit_nca_source_steps_run enc source r semis [] m m [NcaSourceCase 2]
  | NcaSourceStepsCons v rest initial middle result here later :
    audit_nca_source_step_run enc source r semis initial v middle here ->
    audit_nca_source_steps_run enc source r semis rest middle result later ->
    audit_nca_source_steps_run enc source r semis (v :: rest) initial result (NcaSourceCase 3 ::
      here ++ later).

(** An NCA source run relates callback operations, result and event trace. *)
Definition audit_nca_source_run {V E B} (enc : V -> positive * list B) (source : E -> V * list B)
    (r : dfs_result V E) (semis : Map.t V V) (result : Map.t V V) (events : list
      (audit_nca_source_event V E B)) : Prop :=
  audit_nca_source_steps_run enc source r semis (preorder r) Map.empty result events.

Definition audit_nca_source_event_work {V E B} (weight : B -> nat) (event : audit_nca_source_event
  V E B) : nat :=
  64 +
  match event with
  | NcaSourceInner item => audit_semi_nested_event_work weight item
  | NcaSourceTree item => audit_map_source_work (fun es => fold_right (fun x n => weight x + n) 0
    es) [item]
  | NcaSourceSource _ _ es => fold_right (fun x n => weight x + n) 0 es
  | NcaSourceCase _ => 0
  end.

Definition audit_nca_source_event_body {V E B} (weight : B -> nat) (event : audit_nca_source_event
  V E B) : nat :=
  match event with
  | NcaSourceInner item => audit_semi_nested_body_event_work weight item
  | NcaSourceTree (AuditMapGet _ _ _ _ body _)
  | NcaSourceTree (AuditMapSet _ _ _ _ _ body _)
  | NcaSourceTree (AuditMapRemove _ _ _ _ body _)
  | NcaSourceSource _ _ body =>
      fold_right (fun x n => weight x + n) 0 body
  | NcaSourceCase _ => 0
  end.

Definition audit_nca_source_work {V E B} (weight : B -> nat) (events : list
  (audit_nca_source_event V E B)) : nat :=
  fold_right (fun item n => audit_nca_source_event_work weight item + n) 0 events.

Definition audit_nca_source_body_work {V E B} (weight : B -> nat) (events : list
  (audit_nca_source_event V E B)) : nat :=
  fold_right (fun item n => audit_nca_source_event_body weight item + n) 0 events.

Definition audit_nca_source_input_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge
    r)) ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
      r)) in
  let width := Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))) in
  let count := 64 * S (length (preorder r)) * S (audit_semi_producer_input_rank r) in
  512 * S count * S count + count * (512 + 64 * width).

(** Source NCA computation admits the original result with bounded total work. *)
Definition audit_nca_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis
    (enc : V -> positive * list B) (source : E -> V * list B) (weight : B -> nat),
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    exists result events, audit_nca_source_run enc source r semis result events /\ result =
      nca_compute EV g r semis /\
      audit_nca_source_work weight events <= audit_nca_source_input_bound EV g r semis +
        audit_nca_source_body_work weight events.

(** Source NCA computation runs have unique results and event traces. *)
Definition audit_nca_source_unique_statement : Prop :=
  forall V E B enc source (r : dfs_result V E) semis a ea b eb,
    audit_nca_source_run (B := B) enc source r semis a ea -> audit_nca_source_run enc source r
      semis b eb ->
    a = b /\ ea = eb.
