(** * Semidominator audit model

    Models source-level events, work, and associated contract statements.
    For example, compressing a path records its rank and map operations.

    Builds on: the graph and collections interfaces imported below. *)

From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditVirtual.
From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsTrie
  CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphSemiDominators GraphDominance.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditCompare.
Import List.ListNotations.

Inductive audit_semi_call (V : Type) : Type :=
  | AuditSemiCase (site : nat)
  | AuditSemiGet (v : V) (m : Map.t V V) (result : option V)
  | AuditSemiRankGet (v : V) (m : Map.t V positive) (result : option positive)
  | AuditSemiLess (a b : positive) (result : bool)
  | AuditSemiLe (a b : positive) (result : bool)
  | AuditSemiSet (v value : V) (m : Map.t V V).
Arguments AuditSemiCase {V} _.
Arguments AuditSemiGet {V} _ _ _.
Arguments AuditSemiRankGet {V} _ _ _.
Arguments AuditSemiLess {V} _ _ _.
Arguments AuditSemiLe {V} _ _ _.
Arguments AuditSemiSet {V} _ _ _.

Definition audit_semi_rank_counted {V E} (EV : encoding V) (r : dfs_result V E) (v : V)
    : positive * list (audit_semi_call V) :=
  let found := Map.get EV v (pre_num r) in
  (
    match found with
    | Some p => p
    | None => 1%positive
    end, [AuditSemiRankGet v (pre_num r) found]).

Definition audit_semi_score_counted {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (v : V) : positive * list (audit_semi_call V) :=
  let found := Map.get EV v semis in
  let value :=
    match found with
    | Some u => u
    | None => v
    end in
  let '(score, events) := audit_semi_rank_counted EV r value in
  (score, AuditSemiGet v semis found :: events).

Definition audit_semi_label_counted {V} (EV : encoding V) (st : SemiLinks.t V) (v : V)
    : V * list (audit_semi_call V) :=
  let found := Map.get EV v (SemiLinks.labels st) in
  (
    match found with
    | Some u => u
    | None => v
    end, [AuditSemiGet v (SemiLinks.labels st) found]).

Inductive audit_semi_compress_run {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) : V -> semi_query_result V -> list (audit_semi_call
      V) -> Prop :=
  | AuditSemiCompressRoot v :
    Map.get EV v (SemiLinks.shortcut st) = None ->
    audit_semi_compress_run EV r semis st v (st, (v, None))
      [AuditSemiGet v (SemiLinks.shortcut st) None; AuditSemiCase 0]
  | AuditSemiCompressStopped v a ra rv ea ev :
    Map.get EV v (SemiLinks.shortcut st) = Some a ->
    audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
    Pos.ltb ra rv = false ->
    audit_semi_compress_run EV r semis st v (st, (v, None))
      ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
        [AuditSemiLess ra rv false; AuditSemiCase 1])
  | AuditSemiCompressRecurNone v a ra rv ea ev st' root inner label label_events :
    Map.get EV v (SemiLinks.shortcut st) = Some a ->
    audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
    Pos.ltb ra rv = true -> audit_semi_compress_run EV r semis st a (st', (root, None)) inner ->
    audit_semi_label_counted EV st v = (label, label_events) ->
    audit_semi_compress_run EV r semis st v
      (semi_shortcut_set EV st' v root label, (root, Some label))
      ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
        [AuditSemiLess ra rv true; AuditSemiCase 2] ++ inner ++ [AuditSemiCase 3] ++ label_events ++
        [AuditSemiSet v root (SemiLinks.shortcut st'); AuditSemiSet v label (SemiLinks.labels st')])
  | AuditSemiCompressRecurSome v a ra rv ea ev st' root u inner label label_events sl su el eu
  choose :
    Map.get EV v (SemiLinks.shortcut st) = Some a ->
    audit_semi_rank_counted EV r a = (ra, ea) -> audit_semi_rank_counted EV r v = (rv, ev) ->
    Pos.ltb ra rv = true -> audit_semi_compress_run EV r semis st a (st', (root, Some u)) inner ->
    audit_semi_label_counted EV st v = (label, label_events) ->
    audit_semi_score_counted EV r semis label = (sl, el) ->
    audit_semi_score_counted EV r semis u = (su, eu) -> choose = Pos.leb sl su ->
    let best := if choose then label else u in
    audit_semi_compress_run EV r semis st v
      (semi_shortcut_set EV st' v root best, (root, Some best))
      ([AuditSemiGet v (SemiLinks.shortcut st) (Some a)] ++ ea ++ ev ++
        [AuditSemiLess ra rv true; AuditSemiCase 2] ++ inner ++ [AuditSemiCase 4] ++ label_events ++
        el ++ eu ++ [AuditSemiLe sl su choose; AuditSemiSet v root (SemiLinks.shortcut st');
          AuditSemiSet v best (SemiLinks.labels st')]).

Definition audit_semi_call_work {V} (EV : encoding V) (event : audit_semi_call V) : nat :=
  64 +
  match event with
  | AuditSemiGet v _ _
  | AuditSemiRankGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditSemiSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v)
  | AuditSemiLess a b _
  | AuditSemiLe a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditSemiCase _ => 0
  end.

Definition audit_semi_compress_work {V} (EV : encoding V) (events : list (audit_semi_call V)) :
  nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event total => audit_semi_call_work EV event + total) 0 events.

Definition audit_semi_compress_width {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let pairs := Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
    Map.elements semis in
  let vertices := v :: map fst pairs ++ map snd pairs ++ map fst (Map.elements (pre_num r)) in
  Nat.max (fold_right Nat.max 0 (map (fun x => audit_key_bits_weight (encode EV x)) vertices))
    (fold_right Nat.max 0 (map (fun pair => audit_key_bits_weight (snd pair)) (Map.elements
      (pre_num r)))).

Definition audit_semi_compress_event_bound {V E} (EV : encoding V) (r : dfs_result V E) (v : V) :
  nat :=
  20 * S (Pos.to_nat (semi_rank EV r v)).

Definition audit_semi_compress_budget {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let count := audit_semi_compress_event_bound EV r v in
  let width := audit_semi_compress_width EV r semis st v in
  128 * S count * S count + count * (80 + 6 * width).

(** Semidominator compression admits a run with the original result and bounded events and work. *)

Definition audit_semi_compress_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) semis st v,
    exists result events, audit_semi_compress_run EV r semis st v result events /\
      result = semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x))
        st v /\
      length events <= audit_semi_compress_event_bound EV r v /\
      audit_semi_compress_work EV events <= audit_semi_compress_budget EV r semis st v.

(** Semidominator compression runs have unique results and event traces. *)
Definition audit_semi_compress_unique_statement : Prop :=
  forall V E (EV : encoding V) (r : dfs_result V E) semis st v result1 events1 result2 events2,
    audit_semi_compress_run EV r semis st v result1 events1 ->
    audit_semi_compress_run EV r semis st v result2 events2 -> result1 = result2 /\ events1 =
      events2.

Inductive audit_semi_outer_call (V E : Type) : Type :=
  | AuditSemiOuterCase (site : nat)
  | AuditSemiOuterSource (edge : E) (source : V)
  | AuditSemiOuterInner (event : audit_semi_call V)
  | AuditSemiOuterTreeGet (v : V) (m : Map.t V E) (result : option E)
  | AuditSemiOuterPredGet (v : V) (m : Map.t V (list E)) (result : option (list E))
  | AuditSemiOuterResultSet (v value : V) (m : Map.t V V)
  | AuditSemiOuterLink (v parent : V) (st : SemiLinks.t V)
  | AuditSemiOuterOutput (size : nat).
Arguments AuditSemiOuterCase {V E} _.
Arguments AuditSemiOuterSource {V E} _ _.
Arguments AuditSemiOuterInner {V E} _.
Arguments AuditSemiOuterTreeGet {V E} _ _ _.
Arguments AuditSemiOuterPredGet {V E} _ _ _.
Arguments AuditSemiOuterResultSet {V E} _ _ _.
Arguments AuditSemiOuterLink {V E} _ _ _.
Arguments AuditSemiOuterOutput {V E} _.

Definition audit_semi_value_counted {V} (EV : encoding V) (semis : Map.t V V) (v : V)
    : V * list (audit_semi_call V) :=
  let found := Map.get EV v semis in
  (
    match found with
    | Some u => u
    | None => v
    end, [AuditSemiGet v semis found]).

Inductive audit_semi_predecessor_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) :
    SemiLinks.t V * V -> E -> SemiLinks.t V * V -> list (audit_semi_outer_call V E) -> Prop :=
  | AuditSemiPredUnnumbered st best edge v :
    v = Graph.source g edge -> Map.get EV v (pre_num r) = None ->
    audit_semi_predecessor_run EV g r semis (st, best) edge (st, best)
      [AuditSemiOuterSource edge v; AuditSemiOuterInner (AuditSemiRankGet v (pre_num r) None);
        AuditSemiOuterCase 0]
  | AuditSemiPredNumbered st best edge v number st' root part inner u value value_events
    best_rank selected_rank eb es choose :
    v = Graph.source g edge -> Map.get EV v (pre_num r) = Some number ->
    audit_semi_compress_run EV r semis st v (st', (root, part)) inner ->
    u =
      match part with
      | Some chosen => chosen
      | None => v
      end ->
    audit_semi_value_counted EV semis u = (value, value_events) ->
    audit_semi_rank_counted EV r best = (best_rank, eb) ->
    audit_semi_rank_counted EV r value = (selected_rank, es) -> choose = Pos.leb best_rank
      selected_rank ->
    audit_semi_predecessor_run EV g r semis (st, best) edge
      (st', if choose then best else value)
      ([AuditSemiOuterSource edge v; AuditSemiOuterInner (AuditSemiRankGet v (pre_num r) (Some
        number)); AuditSemiOuterCase 1] ++
       map AuditSemiOuterInner inner ++ [AuditSemiOuterCase 2] ++ map AuditSemiOuterInner
         value_events ++
       map AuditSemiOuterInner eb ++ map AuditSemiOuterInner es ++ [AuditSemiOuterInner
         (AuditSemiLe best_rank selected_rank choose)]).

Inductive audit_semi_predecessors_run {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : list E -> SemiLinks.t V * V ->
    SemiLinks.t V * V -> list (audit_semi_outer_call V E) -> Prop :=
  | AuditSemiPredsNil acc :
      audit_semi_predecessors_run EV g r semis [] acc acc [AuditSemiOuterCase 3]
  | AuditSemiPredsCons edge rest initial middle result here later :
    audit_semi_predecessor_run EV g r semis initial edge middle here ->
    audit_semi_predecessors_run EV g r semis rest middle result later ->
    audit_semi_predecessors_run EV g r semis (edge :: rest) initial result
      (AuditSemiOuterCase 4 :: here ++ later).

Inductive audit_semi_settle_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : SemiState.t V -> V -> SemiState.t V ->
    list (audit_semi_outer_call V E) -> Prop :=
  | AuditSemiSettleRoot st w : Map.get EV w (tree_edge r) = None ->
    audit_semi_settle_run p r st w st [AuditSemiOuterTreeGet w (tree_edge r) None;
      AuditSemiOuterCase 5]
  | AuditSemiSettleNode st w edge parent incoming edges links' best events :
    Map.get EV w (tree_edge r) = Some edge -> parent = Graph.source g edge ->
    incoming = Map.get EV w (in_index p) ->
    edges =
            match incoming with
            | Some xs => xs
            | None => []
            end ->
    audit_semi_predecessors_run EV g r (SemiState.result st) edges (SemiState.links st, parent)
      (links', best) events ->
    audit_semi_settle_run p r st w
      (SemiState.Make (Map.set EV w best (SemiState.result st)) (semi_link EV links' w parent))
      ([AuditSemiOuterTreeGet w (tree_edge r) (Some edge); AuditSemiOuterCase 6;
        AuditSemiOuterSource edge parent; AuditSemiOuterPredGet w (in_index p) incoming] ++ events
          ++
       [AuditSemiOuterResultSet w best (SemiState.result st); AuditSemiOuterLink w parent links']).

Inductive audit_semi_settles_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : list V -> SemiState.t V -> SemiState.t V ->
    list (audit_semi_outer_call V E) -> Prop :=
  | AuditSemiSettlesNil st : audit_semi_settles_run p r [] st st [AuditSemiOuterCase 7]
  | AuditSemiSettlesCons v rest initial middle result here later :
    audit_semi_settle_run p r initial v middle here -> audit_semi_settles_run p r rest middle
      result later ->
    audit_semi_settles_run p r (v :: rest) initial result (AuditSemiOuterCase 8 :: here ++ later).

(** A semidominator computation run relates its inputs, result and trace. *)
Definition audit_semi_compute_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) (result : SemiState.t V)
    (events : list (audit_semi_outer_call V E)) : Prop :=
  exists inner, audit_semi_settles_run p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty) result inner /\
    events = AuditSemiOuterOutput (length (preorder r)) :: inner.

Definition audit_semi_outer_event_work {V E} (EV : encoding V) (event : audit_semi_outer_call V E)
  : nat :=
  64 +
  match event with
  | AuditSemiOuterInner item => audit_semi_call_work EV item
  | AuditSemiOuterTreeGet v _ _
  | AuditSemiOuterPredGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditSemiOuterResultSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v)
  | AuditSemiOuterLink v _ _ => 3 * (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v))
  | AuditSemiOuterOutput size => S size
  | _ => 0
  end.

Definition audit_semi_compute_work {V E} (EV : encoding V) (events : list (audit_semi_outer_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_semi_outer_event_work EV event + total) 0 events.

Definition audit_semi_compute_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  fold_right (fun v total => length (pred_edges p v) + total) 0 (preorder r).

Definition audit_semi_compute_rank_bound {V E} (r : dfs_result V E) : nat :=
  fold_right Nat.max 1 (map (fun row => Pos.to_nat (snd row)) (Map.elements (pre_num r))).

Definition audit_semi_compute_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let pred_edges_all := flat_map snd (Map.elements (in_index p)) in
  let tree_edges := map snd (Map.elements (tree_edge r)) in
  let vertices := preorder r ++ map fst (Map.elements (pre_num r)) ++
    map fst (Map.elements (tree_edge r)) ++ map fst (Map.elements (in_index p)) ++
    map (Graph.source g) (pred_edges_all ++ tree_edges) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
      r)))).

Definition audit_semi_compute_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  100 * S (length (preorder r)) * S (audit_semi_compute_input_edges p r) * S
    (audit_semi_compute_rank_bound r).

Definition audit_semi_compute_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let events := audit_semi_compute_event_bound p r in
  let width := audit_semi_compute_width EV g p r in
  512 * S events * S events + events * (512 + 16 * width).

(** Semidominator computation admits a run with the original result and bounded events and work. *)
Definition audit_semi_compute_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E),
    exists result events, audit_semi_compute_run p r result events /\ result = semi_compute p r /\
      length events <= audit_semi_compute_event_bound p r /\
      audit_semi_compute_work EV events <= audit_semi_compute_input_budget EV g p r.

(** Semidominator computation runs have unique results and event traces. *)
Definition audit_semi_compute_unique_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E) a b ea eb,
    audit_semi_compute_run p r a ea -> audit_semi_compute_run p r b eb -> a = b /\ ea = eb.

Inductive audit_semi_nested_event (V B : Type) : Type :=
  | SemiNestedCase : nat -> audit_semi_nested_event V B
  | SemiNestedVertexMap : audit_map_event V V B -> audit_semi_nested_event V B
  | SemiNestedRankMap : audit_map_event V positive B -> audit_semi_nested_event V B
  | SemiNestedCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
    audit_semi_nested_event V B.
Arguments SemiNestedCase {V B} _.
Arguments SemiNestedVertexMap {V B} _.
Arguments SemiNestedRankMap {V B} _.
Arguments SemiNestedCompare {V B} _ _ _ _.

Definition audit_semi_nested_rank {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (v : V) : positive * list (audit_semi_nested_event V B) :=
  let '(found, events) := audit_map_get enc v (pre_num r) in
  (
    match found with
    | Some x => x
    | None => 1%positive
    end, map SemiNestedRankMap events).

Definition audit_semi_nested_score {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (v : V)
    : positive * list (audit_semi_nested_event V B) :=
  let '(found, events) := audit_map_get enc v semis in
  let next :=
    match found with
    | Some x => x
    | None => v
    end in
  let '(score, rank_events) := audit_semi_nested_rank enc r next in
  (score, map SemiNestedVertexMap events ++ rank_events).

Definition audit_semi_nested_label {V B} (enc : V -> positive * list B)
    (st : SemiLinks.t V) (v : V) : V * list (audit_semi_nested_event V B) :=
  let '(found, events) := audit_map_get enc v (SemiLinks.labels st) in
  (
    match found with
    | Some x => x
    | None => v
    end, map SemiNestedVertexMap events).

Definition audit_semi_nested_shortcut_set {V B} (enc : V -> positive * list B)
    (st : SemiLinks.t V) (v root best : V) : SemiLinks.t V * list (audit_semi_nested_event V B) :=
  let '(shortcuts, first) := audit_map_set enc v root (SemiLinks.shortcut st) in
  let '(labels, second) := audit_map_set enc v best (SemiLinks.labels st) in
  (SemiLinks.Make (SemiLinks.original st) shortcuts labels,
    map SemiNestedVertexMap first ++ map SemiNestedVertexMap second).

Inductive audit_semi_nested_compress_run {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (st : SemiLinks.t V)
    : V -> semi_query_result V -> list (audit_semi_nested_event V B) -> Prop :=
  | SemiNestedRoot v get_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (None, get_events) ->
    audit_semi_nested_compress_run enc r semis st v (st, (v, None))
      (map SemiNestedVertexMap get_events ++ [SemiNestedCase 0])
  | SemiNestedStopped v a get_events ra rv ea ev compare_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
    audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
    audit_positive_ltb ra rv = (false, compare_events) ->
    audit_semi_nested_compress_run enc r semis st v (st, (v, None))
      (map SemiNestedVertexMap get_events ++ ea ++ ev ++
        [SemiNestedCompare ra rv false compare_events; SemiNestedCase 1])
  | SemiNestedRecurNone v a get_events ra rv ea ev compare_events st' root inner
    label label_events final set_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
    audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
    audit_positive_ltb ra rv = (true, compare_events) ->
    audit_semi_nested_compress_run enc r semis st a (st', (root, None)) inner ->
    audit_semi_nested_label enc st v = (label, label_events) ->
    audit_semi_nested_shortcut_set enc st' v root label = (final, set_events) ->
    audit_semi_nested_compress_run enc r semis st v (final, (root, Some label))
      (map SemiNestedVertexMap get_events ++ ea ++ ev ++
        [SemiNestedCompare ra rv true compare_events; SemiNestedCase 2] ++ inner ++
        [SemiNestedCase 3] ++ label_events ++ set_events)
  | SemiNestedRecurSome v a get_events ra rv ea ev compare_events st' root u inner
    label label_events sl su el eu choose choose_events final set_events :
    audit_map_get enc v (SemiLinks.shortcut st) = (Some a, get_events) ->
    audit_semi_nested_rank enc r a = (ra, ea) -> audit_semi_nested_rank enc r v = (rv, ev) ->
    audit_positive_ltb ra rv = (true, compare_events) ->
    audit_semi_nested_compress_run enc r semis st a (st', (root, Some u)) inner ->
    audit_semi_nested_label enc st v = (label, label_events) ->
    audit_semi_nested_score enc r semis label = (sl, el) ->
    audit_semi_nested_score enc r semis u = (su, eu) ->
    audit_positive_leb sl su = (choose, choose_events) ->
    audit_semi_nested_shortcut_set enc st' v root (if choose then label else u) = (final,
      set_events) ->
    audit_semi_nested_compress_run enc r semis st v (final, (root, Some (if choose then label else
      u)))
      (map SemiNestedVertexMap get_events ++ ea ++ ev ++
        [SemiNestedCompare ra rv true compare_events; SemiNestedCase 2] ++ inner ++
        [SemiNestedCase 4] ++ label_events ++ el ++ eu ++
        [SemiNestedCompare sl su choose choose_events] ++ set_events).

(** Nested compression admits a run yielding the ordinary compression result. *)
Definition audit_semi_nested_compress_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (enc : V -> positive * list B) (r : dfs_result V E) semis st v,
    (forall x, fst (enc x) = encode EV x) ->
    exists result events, audit_semi_nested_compress_run enc r semis st v result events /\
      result = semi_compress EV (semi_rank EV r) (fun x => semi_rank EV r (semi_value EV semis x))
        st v.

(** Nested compression runs have unique results and event traces. *)
Definition audit_semi_nested_compress_unique_statement : Prop :=
  forall V E B enc (r : dfs_result V E) semis st v first first_events second second_events,
    audit_semi_nested_compress_run (B := B) enc r semis st v first first_events ->
    audit_semi_nested_compress_run enc r semis st v second second_events ->
    first = second /\ first_events = second_events.

Definition audit_semi_nested_event_work {V B} (weight : B -> nat)
    (event : audit_semi_nested_event V B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 +
  match event with
  | SemiNestedVertexMap map_event => audit_map_source_work body [map_event]
  | SemiNestedRankMap map_event => audit_map_source_work body [map_event]
  | SemiNestedCompare _ _ _ events => audit_positive_order_source_work events
  | SemiNestedCase _ => 0
  end.

Definition audit_semi_nested_body_event_work {V B} (weight : B -> nat)
    (event : audit_semi_nested_event V B) : nat :=
  match event with
  | SemiNestedVertexMap (AuditMapGet _ _ _ _ body _)
  | SemiNestedVertexMap (AuditMapSet _ _ _ _ _ body _)
  | SemiNestedVertexMap (AuditMapRemove _ _ _ _ body _)
  | SemiNestedRankMap (AuditMapGet _ _ _ _ body _)
  | SemiNestedRankMap (AuditMapSet _ _ _ _ _ body _)
  | SemiNestedRankMap (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | SemiNestedCase _
  | SemiNestedCompare _ _ _ _ => 0
  end.

Definition audit_semi_nested_work {V B} (weight : B -> nat)
    (events : list (audit_semi_nested_event V B)) : nat :=
  fold_right (fun event n => audit_semi_nested_event_work weight event + n) 0 events.

Definition audit_semi_nested_body_work {V B} (weight : B -> nat)
    (events : list (audit_semi_nested_event V B)) : nat :=
  fold_right (fun event n => audit_semi_nested_body_event_work weight event + n) 0 events.

Definition audit_semi_nested_width {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let rows := Map.elements (SemiLinks.shortcut st) ++ Map.elements (SemiLinks.labels st) ++
    Map.elements semis in
  let vertices := v :: map fst rows ++ map snd rows ++ map fst (Map.elements (pre_num r)) in
  Nat.max (fold_right Nat.max 0 (map (fun x => Pos.size_nat (encode EV x)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))).

Definition audit_semi_nested_input_budget {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (st : SemiLinks.t V) (v : V) : nat :=
  let count := 20 * S (Pos.to_nat (semi_rank EV r v)) in
  128 * S count * S count + count * (256 + 32 * audit_semi_nested_width EV r semis st v).

(** Nested compression runs obey their event and total-work bounds. *)
Definition audit_semi_nested_compress_bound_statement : Prop :=
  forall V E B (EV : encoding V) (enc : V -> positive * list B) (weight : B -> nat)
    (r : dfs_result V E) semis st v result events,
    (forall x, fst (enc x) = encode EV x) ->
    audit_semi_nested_compress_run enc r semis st v result events ->
    length events <= 20 * S (Pos.to_nat (semi_rank EV r v)) /\
    audit_semi_nested_work weight events <=
      audit_semi_nested_input_budget EV r semis st v + audit_semi_nested_body_work weight events.

Inductive audit_semi_producer_nested_event (V E B : Type) : Type :=
  | SemiProducerCase : nat -> audit_semi_producer_nested_event V E B
  | SemiProducerSource : E -> V -> list B -> audit_semi_producer_nested_event V E B
  | SemiProducerInner : audit_semi_nested_event V B -> audit_semi_producer_nested_event V E B
  | SemiProducerTreeMap : audit_map_event V E B -> audit_semi_producer_nested_event V E B
  | SemiProducerPredMap : audit_map_event V (list E) B -> audit_semi_producer_nested_event V E B
  | SemiProducerOutput : nat -> audit_semi_producer_nested_event V E B.
Arguments SemiProducerCase {V E B} _.
Arguments SemiProducerSource {V E B} _ _ _.
Arguments SemiProducerInner {V E B} _.
Arguments SemiProducerTreeMap {V E B} _.
Arguments SemiProducerPredMap {V E B} _.
Arguments SemiProducerOutput {V E B} _.

Definition audit_semi_producer_link {V E B} (enc : V -> positive * list B)
    (st : SemiLinks.t V) (v parent : V)
    : SemiLinks.t V * list (audit_semi_producer_nested_event V E B) :=
  let '(original, a) := audit_map_set enc v parent (SemiLinks.original st) in
  let '(shortcut, b) := audit_map_set enc v parent (SemiLinks.shortcut st) in
  let '(labels, c) := audit_map_set enc v v (SemiLinks.labels st) in
  (SemiLinks.Make original shortcut labels,
    map (fun item => SemiProducerInner (SemiNestedVertexMap item)) (a ++ b ++ c)).

Inductive audit_semi_producer_pred_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) :
    SemiLinks.t V * V -> E -> SemiLinks.t V * V -> list (audit_semi_producer_nested_event V E B)
      -> Prop :=
  | SemiProducerPredMissing st best edge vertex source_body rank_events :
    source edge = (vertex, source_body) -> audit_map_get enc vertex (pre_num r) = (None,
      rank_events) ->
    audit_semi_producer_pred_run enc source r semis (st, best) edge (st, best)
      ([SemiProducerSource edge vertex source_body] ++
       map (fun item => SemiProducerInner (SemiNestedRankMap item)) rank_events ++
         [SemiProducerCase 0])
  | SemiProducerPredNumbered st best edge vertex source_body number rank_events st' root part inner
    u value value_events best_rank value_rank best_events value_rank_events choose compare_events :
    source edge = (vertex, source_body) -> audit_map_get enc vertex (pre_num r) = (Some number,
      rank_events) ->
    audit_semi_nested_compress_run enc r semis st vertex (st', (root, part)) inner ->
    u =
      match part with
      | Some chosen => chosen
      | None => vertex
      end ->
    audit_map_get enc u semis = (value, value_events) ->
    audit_semi_nested_rank enc r best = (best_rank, best_events) ->
    audit_semi_nested_rank enc r (
      match value with
      | Some x => x
      | None => u
      end) = (value_rank,
      value_rank_events) ->
    audit_positive_leb best_rank value_rank = (choose, compare_events) ->
    audit_semi_producer_pred_run enc source r semis (st, best) edge
      (st', if choose then best else
        match value with
        | Some x => x
        | None => u
        end)
      ([SemiProducerSource edge vertex source_body] ++
       map (fun item => SemiProducerInner (SemiNestedRankMap item)) rank_events ++
         [SemiProducerCase 1] ++
       map SemiProducerInner inner ++ [SemiProducerCase 2] ++
       map (fun item => SemiProducerInner (SemiNestedVertexMap item)) value_events ++
       map SemiProducerInner best_events ++ map SemiProducerInner value_rank_events ++
       [SemiProducerInner (SemiNestedCompare best_rank value_rank choose compare_events)]).

Inductive audit_semi_producer_preds_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) :
    list E -> SemiLinks.t V * V -> SemiLinks.t V * V -> list (audit_semi_producer_nested_event V E
      B) -> Prop :=
  | SemiProducerPredsNil acc : audit_semi_producer_preds_run enc source r semis [] acc acc
  [SemiProducerCase 3]
  | SemiProducerPredsCons edge rest initial middle result here later :
    audit_semi_producer_pred_run enc source r semis initial edge middle here ->
    audit_semi_producer_preds_run enc source r semis rest middle result later ->
    audit_semi_producer_preds_run enc source r semis (edge :: rest) initial result
      (SemiProducerCase 4 :: here ++ later).

Inductive audit_semi_producer_settle_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (source : E -> V * list B) (p : prepared EV g) (r : dfs_result
      V E) :
    SemiState.t V -> V -> SemiState.t V -> list (audit_semi_producer_nested_event V E B) -> Prop :=
  | SemiProducerSettleRoot st v tree_events : audit_map_get enc v (tree_edge r) = (None,
  tree_events) ->
    audit_semi_producer_settle_run enc source p r st v st
      (map SemiProducerTreeMap tree_events ++ [SemiProducerCase 5])
  | SemiProducerSettleNode st v edge tree_events parent source_body incoming pred_events edges
    links' best pred_steps result_map result_events links'' link_events :
    audit_map_get enc v (tree_edge r) = (Some edge, tree_events) -> source edge = (parent,
      source_body) ->
    audit_map_get enc v (in_index p) = (incoming, pred_events) ->
    edges =
      match incoming with
      | Some xs => xs
      | None => []
      end ->
    audit_semi_producer_preds_run enc source r (SemiState.result st) edges
      (SemiState.links st, parent) (links', best) pred_steps ->
    audit_map_set enc v best (SemiState.result st) = (result_map, result_events) ->
    audit_semi_producer_link enc links' v parent = (links'', link_events) ->
    audit_semi_producer_settle_run enc source p r st v (SemiState.Make result_map links'')
      (map SemiProducerTreeMap tree_events ++ [SemiProducerCase 6; SemiProducerSource edge parent
        source_body] ++
       map SemiProducerPredMap pred_events ++ pred_steps ++
       map (fun item => SemiProducerInner (SemiNestedVertexMap item)) result_events ++ link_events).

Inductive audit_semi_producer_settles_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (source : E -> V * list B) (p : prepared EV g) (r : dfs_result
      V E) :
    list V -> SemiState.t V -> SemiState.t V -> list (audit_semi_producer_nested_event V E B) ->
      Prop :=
  | SemiProducerSettlesNil st : audit_semi_producer_settles_run enc source p r [] st st
  [SemiProducerCase 7]
  | SemiProducerSettlesCons v rest initial middle result here later :
    audit_semi_producer_settle_run enc source p r initial v middle here ->
    audit_semi_producer_settles_run enc source p r rest middle result later ->
    audit_semi_producer_settles_run enc source p r (v :: rest) initial result
      (SemiProducerCase 8 :: here ++ later).

(** A nested semidominator run relates callback operations, result and trace. *)
Definition audit_semi_producer_nested_run {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (source : E -> V * list B) (p : prepared EV g) (r : dfs_result
      V E)
    (result : SemiState.t V) (events : list (audit_semi_producer_nested_event V E B)) : Prop :=
  exists inner, audit_semi_producer_settles_run enc source p r (rev (preorder r))
    (SemiState.Make Map.empty semi_links_empty) result inner /\
    events = SemiProducerOutput (length (preorder r)) :: inner.

(** Nested semidominator production admits the ordinary computation result. *)
Definition audit_semi_producer_nested_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E)
    (enc : V -> positive * list B) (source : E -> V * list B),
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    exists result events, audit_semi_producer_nested_run enc source p r result events /\
      result = semi_compute p r.

(** Nested semidominator production has unique results and event traces. *)
Definition audit_semi_producer_nested_unique_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E)
    (enc : V -> positive * list B) (source : E -> V * list B) a ea b eb,
    audit_semi_producer_nested_run enc source p r a ea -> audit_semi_producer_nested_run enc
      source p r b eb ->
    a = b /\ ea = eb.

Definition audit_semi_producer_nested_event_work {V E B} (weight : B -> nat)
    (event : audit_semi_producer_nested_event V E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 +
  match event with
  | SemiProducerSource _ _ events => body events
  | SemiProducerInner item => audit_semi_nested_event_work weight item
  | SemiProducerTreeMap item => audit_map_source_work body [item]
  | SemiProducerPredMap item => audit_map_source_work body [item]
  | SemiProducerOutput size => S size
  | SemiProducerCase _ => 0
  end.

Definition audit_semi_producer_nested_body_event_work {V E B} (weight : B -> nat)
    (event : audit_semi_producer_nested_event V E B) : nat :=
  match event with
  | SemiProducerSource _ _ body => fold_right (fun item n => weight item + n) 0 body
  | SemiProducerInner item => audit_semi_nested_body_event_work weight item
  | SemiProducerTreeMap (AuditMapGet _ _ _ _ body _)
  | SemiProducerTreeMap (AuditMapSet _ _ _ _ _ body _)
  | SemiProducerTreeMap (AuditMapRemove _ _ _ _ body _)
  | SemiProducerPredMap (AuditMapGet _ _ _ _ body _)
  | SemiProducerPredMap (AuditMapSet _ _ _ _ _ body _)
  | SemiProducerPredMap (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | SemiProducerCase _
  | SemiProducerOutput _ => 0
  end.

Definition audit_semi_producer_nested_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event V E B)) : nat :=
  fold_right (fun item n => audit_semi_producer_nested_event_work weight item + n) 0 events.

Definition audit_semi_producer_nested_body_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event V E B)) : nat :=
  fold_right (fun item n => audit_semi_producer_nested_body_event_work weight item + n) 0 events.

Definition audit_semi_producer_input_rank {V E} (r : dfs_result V E) : nat :=
  fold_right Nat.max 1 (map (fun row => Pos.to_nat (snd row)) (Map.elements (pre_num r))).

Definition audit_semi_producer_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  fold_right (fun v n => length (pred_edges p v) + n) 0 (preorder r).

Definition audit_semi_producer_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let edges := flat_map snd (Map.elements (in_index p)) ++ map snd (Map.elements (tree_edge r)) in
  let vertices := preorder r ++ map fst (Map.elements (pre_num r)) ++
    map fst (Map.elements (tree_edge r)) ++ map fst (Map.elements (in_index p)) ++ map
      (Graph.source g) edges in
  Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))).

Definition audit_semi_producer_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  100 * S (length (preorder r)) * S (audit_semi_producer_input_edges p r) *
    S (audit_semi_producer_input_rank r).

Definition audit_semi_producer_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (r : dfs_result V E) : nat :=
  let count := audit_semi_producer_event_bound p r in
  512 * S count * S count + count * (512 + 64 * audit_semi_producer_input_width EV g p r).

(** Nested semidominator production obeys its event and total-work bounds. *)
Definition audit_semi_producer_nested_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (r : dfs_result V E)
    (enc : V -> positive * list B) (source : E -> V * list B) (weight : B -> nat) result events,
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    audit_semi_producer_nested_run enc source p r result events ->
    length events <= audit_semi_producer_event_bound p r /\
    audit_semi_producer_nested_work weight events <=
      audit_semi_producer_input_budget EV g p r + audit_semi_producer_nested_body_work weight
        events.
(** A virtual semidominator run applies the producer to the virtual search. *)
Definition audit_virtual_semi_run {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (result : SemiState.t (V + unit))
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V
      E B)))
    : Prop :=
  let '(p, (search, _)) := audit_virtual_full_search_with_prepared EV g cb in
  audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
    p search result events.

(** Virtual semidominator production admits the ordinary virtual computation result. *)
Definition audit_virtual_semi_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists result events, audit_virtual_semi_run EV g cb source result events /\
      result = semi_compute (virtual_prepared p) (virtual_dfs p).

Definition audit_virtual_semi_stage_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V
      E B))) : nat :=
  audit_semi_producer_nested_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event)
    events.

Definition audit_virtual_semi_external_work {V E B} (weight : B -> nat)
    (events : list (audit_semi_producer_nested_event (V + unit) (E + V) (audit_virtual_full_call V
      E B))) : nat :=
  audit_semi_producer_nested_body_work (audit_virtual_full_body_event_work weight) events.
