(** * Dominance frontier audit model

    Models source-level events, work, and associated contract statements.
    For example, processing an edge records its set operations.

    Builds on: the graph and collections interfaces imported below. *)

From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Graph Require Import GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditDominators.
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators GraphFrontier.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditCompare.
Import List.ListNotations.

Inductive audit_frontier_dom_call (N : Type) : Type :=
  | AuditFrontierDomGet (n : N) (m : Map.t N positive) (r : option positive)
  | AuditFrontierDomLe (a b : positive) (r : bool).
Arguments AuditFrontierDomGet {N} _ _ _.
Arguments AuditFrontierDomLe {N} _ _ _.

Definition audit_frontier_dom_counted {N} (EN : encoding N) (tree : dom_tree N) (d t : N)
    : bool * list (audit_frontier_dom_call N) :=
  let a := Map.get EN d (tin tree) in
  match a with
  | None => (false, [AuditFrontierDomGet d (tin tree) a])
  | Some av => let b := Map.get EN t (tin tree) in
    match b with
    | None => (false, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b])
    | Some bv => let c := Map.get EN d (tout tree) in
      match c with
      | None => (false, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b;
          AuditFrontierDomGet d (tout tree) c])
      | Some cv => let e := Map.get EN t (tout tree) in
        match e with
        | None => (false, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b;
            AuditFrontierDomGet d (tout tree) c; AuditFrontierDomGet t (tout tree) e])
        | Some ev => let first := Pos.leb av bv in let second := Pos.leb ev cv in
          (first && second, [AuditFrontierDomGet d (tin tree) a; AuditFrontierDomGet t (tin tree) b;
            AuditFrontierDomGet d (tout tree) c; AuditFrontierDomGet t (tout tree) e;
            AuditFrontierDomLe av bv first; AuditFrontierDomLe ev cv second])
        end
      end
    end
  end.

Definition audit_frontier_dom_event_work {N} (EN : encoding N) (event : audit_frontier_dom_call N)
  : nat :=
  64 +
  match event with
  | AuditFrontierDomGet n _ _ => audit_get_weight (encode EN n) + audit_encoding_weight
    (audit_key_bits_weight (encode EN n))
  | AuditFrontierDomLe a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  end.

(** Counted dominance testing returns the boolean result with at most six events. *)

Definition audit_frontier_dom_statement : Prop :=
  forall N (EN : encoding N) tree d t,
    let '(result, events) := audit_frontier_dom_counted EN tree d t in
    result = dominates_b EN tree d t /\ length events <= 6.

Inductive audit_frontier_call (V E : Type) : Type :=
  | AuditFrontierCase (site : nat)
  | AuditFrontierDom (event : audit_frontier_dom_call V)
  | AuditFrontierParent (v : V) (m : Map.t V V) (result : option V)
  | AuditFrontierDfs (event : audit_dfs_full_call V E)
  | AuditFrontierSource (e : E) (v : V)
  | AuditFrontierTarget (e : E) (v : V)
  | AuditFrontierPred (v : V) (m : Map.t V (list E)) (result : option (list E))
  | AuditFrontierMem (v : V) (s : FinSet.t V) (result : bool)
  | AuditFrontierGet (v : V) (m : Map.t V (FinSet.t V)) (result : option (FinSet.t V))
  | AuditFrontierSetMember (v : V) (s : FinSet.t V)
  | AuditFrontierSetRow (v : V) (row : FinSet.t V) (m : Map.t V (FinSet.t V))
  | AuditFrontierOutput (size : nat).
Arguments AuditFrontierCase {V E} _.
Arguments AuditFrontierDom {V E} _.
Arguments AuditFrontierParent {V E} _ _ _.
Arguments AuditFrontierDfs {V E} _.
Arguments AuditFrontierSource {V E} _ _.
Arguments AuditFrontierTarget {V E} _ _.
Arguments AuditFrontierPred {V E} _ _ _.
Arguments AuditFrontierMem {V E} _ _ _.
Arguments AuditFrontierGet {V E} _ _ _.
Arguments AuditFrontierSetMember {V E} _ _.
Arguments AuditFrontierSetRow {V E} _ _ _.
Arguments AuditFrontierOutput {V E} _.

Definition audit_frontier_step_counted {V E} (EV : encoding V) (t : dom_tree V)
    (stop : option V) (state : option V * list V)
    : (option V * list V) * list (audit_frontier_call V E) :=
  let '(current, seen) := state in
  match current with
  | None => ((None, seen), [AuditFrontierCase 0])
  | Some v =>
      let '(blocked, detail) :=
        match stop with
        | None => (false, [])
        | Some q => audit_frontier_dom_counted EV t v q
        end in
      if blocked then ((None, seen), AuditFrontierCase 1 :: map AuditFrontierDom detail ++
        [AuditFrontierCase 2])
      else let parent := Map.get EV v (idom t) in
        ((parent, v :: seen), AuditFrontierCase 1 :: map AuditFrontierDom detail ++
          [AuditFrontierCase 3; AuditFrontierParent v (idom t) parent])
  end.

Fixpoint audit_frontier_run_counted {V E} (EV : encoding V) (t : dom_tree V) (stop : option V)
    (fuel : positive) (state : option V * list V)
    : (option V * list V) * list (audit_frontier_call V E) :=
  match fst state with
  | None => (state, [AuditFrontierCase 4])
  | Some _ =>
    match fuel with
    | xH => let '(result, events) := audit_frontier_step_counted EV t stop state in
        (result, AuditFrontierCase 5 :: events)
    | xO rest => let '(middle, first) := audit_frontier_run_counted EV t stop rest state in
        let '(result, second) := audit_frontier_run_counted EV t stop rest middle in
        (result, AuditFrontierCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_frontier_run_counted EV t stop rest state in
        let '(last, second) := audit_frontier_run_counted EV t stop rest middle in
        let '(result, events) := audit_frontier_step_counted EV t stop last in
        (result, AuditFrontierCase 7 :: first ++ second ++ events)
    end
  end.

Definition audit_frontier_runner_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (start : V) (stop : option V)
    : list V * list (audit_frontier_call V E) :=
  let '(result, events) := audit_frontier_run_counted EV t stop (fuel p) (Some start, []) in
  (snd result, events).

Definition audit_frontier_event_work {V E} (EV : encoding V) (event : audit_frontier_call V E) :
  nat :=
  64 +
  match event with
  | AuditFrontierDom item => audit_frontier_dom_event_work EV item
  | AuditFrontierDfs item => audit_dfs_full_model_event EV item
  | AuditFrontierParent v _ _
  | AuditFrontierPred v _ _
  | AuditFrontierMem v _ _
  | AuditFrontierGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditFrontierSetMember v _
  | AuditFrontierSetRow v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_set_weight (encode EV v)
  | AuditFrontierOutput size => S size
  | _ => 0
  end.

Definition audit_frontier_model_work {V E} (EV : encoding V) (events : list (audit_frontier_call V
  E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_frontier_event_work EV event + total) 0 events.

Definition audit_frontier_runner_width {V} (EV : encoding V) (t : dom_tree V) (start : V) (stop :
  option V) : nat :=
  let parent_rows := Map.elements (idom t) in
  let vertices := start :: (
    match stop with
    | Some v => [v]
    | None => []
    end) ++
    map fst parent_rows ++ map snd parent_rows ++ map fst (Map.elements (tin t)) ++ map fst
      (Map.elements (tout t)) in
  let numbers := map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_frontier_runner_event_bound (fuel : positive) : nat := 3 + 12 * S (Pos.to_nat
  fuel).

Definition audit_frontier_runner_budget {V} (EV : encoding V) (t : dom_tree V)
    (fuel : positive) (start : V) (stop : option V) : nat :=
  let count := audit_frontier_runner_event_bound fuel in let width := audit_frontier_runner_width
    EV t start stop in
  512 * S count * S count + count * (256 + 12 * width).

(** Counted frontier walking returns the runner result with bounded events and work. *)
Definition audit_frontier_runner_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V) start stop,
    let '(result, events) := audit_frontier_runner_counted p t start stop in
    result = frontier_runner p t start stop /\ length events <= audit_frontier_runner_event_bound
      (fuel p) /\
    audit_frontier_model_work EV events <= audit_frontier_runner_budget EV t (fuel p) start stop.

Fixpoint audit_frontier_collect_pred {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (nodes : list V) : list E * list (audit_frontier_call V E) :=
  match nodes with
  | [] => ([], [AuditFrontierCase 10])
  | v :: rest => let found := Map.get EV v (in_index p) in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(later, events) := audit_frontier_collect_pred p rest in
      (row ++ later, AuditFrontierCase 11 :: AuditFrontierPred v (in_index p) found :: events ++
        [AuditFrontierOutput (length row)])
  end.

Fixpoint audit_frontier_live_filter {V E} (EV : encoding V) (g : Graph.t V E)
    (live : FinSet.t V) (edges : list E) : list E * list (audit_frontier_call V E) :=
  match edges with
  | [] => ([], [AuditFrontierCase 12])
  | e :: rest => let source := Graph.source g e in let keep := FinSet.mem EV source live in
      let '(later, events) := audit_frontier_live_filter EV g live rest in
      (if keep then e :: later else later, AuditFrontierCase 13 :: AuditFrontierSource e source ::
        AuditFrontierMem source live keep :: AuditFrontierCase (if keep then 14 else 15) :: events)
  end.

Fixpoint audit_frontier_targets {V E} (g : Graph.t V E) (e : E) (vertices : list V)
    : list (V * V) * list (audit_frontier_call V E) :=
  match vertices with
  | [] => ([], [AuditFrontierCase 16])
  | v :: rest => let target := Graph.target g e in let '(later, events) := audit_frontier_targets
    g e rest in
      ((v, target) :: later, AuditFrontierCase 17 :: AuditFrontierTarget e target :: events)
  end.

Fixpoint audit_frontier_edge_events {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (edges : list E)
    : list (V * V) * list (audit_frontier_call V E) :=
  match edges with
  | [] => ([], [AuditFrontierCase 18])
  | e :: rest => let source := Graph.source g e in let target := Graph.target g e in
      let stop := Map.get EV target (idom t) in
      let '(chain, walk_events) := audit_frontier_runner_counted p t source stop in
      let '(pairs, pair_events) := audit_frontier_targets g e chain in
      let '(later, events) := audit_frontier_edge_events p t rest in
      (pairs ++ later, AuditFrontierCase 19 :: AuditFrontierSource e source :: AuditFrontierTarget
        e target ::
        AuditFrontierParent target (idom t) stop :: walk_events ++ pair_events ++ events ++
        [AuditFrontierOutput (length pairs)])
  end.

Fixpoint audit_frontier_rows_counted {V E} (EV : encoding V) (pairs : list (V * V))
    (rows : Map.t V (FinSet.t V)) : Map.t V (FinSet.t V) * list (audit_frontier_call V E) :=
  match pairs with
  | [] => (rows, [AuditFrontierCase 20])
  | (d, n) :: rest => let found := Map.get EV d rows in
      let old :=
        match found with
        | Some s => s
        | None => FinSet.empty
        end in
      let row := FinSet.add EV n old in let next := Map.set EV d row rows in
      let '(result, events) := audit_frontier_rows_counted EV rest next in
      (result, AuditFrontierCase 21 :: AuditFrontierGet d rows found :: AuditFrontierSetMember n
        old ::
        AuditFrontierSetRow d row rows :: events)
  end.

Definition audit_frontier_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) : Map.t V (FinSet.t V) * list (audit_frontier_call V E) :=
  let '(search, dfs_events) := audit_dfs_full_counted p FinSet.empty (Graph.entries g) in
  let '(incoming, pred_events) := audit_frontier_collect_pred p (Graph.nodes g) in
  let '(live_edges, filter_events) := audit_frontier_live_filter EV g (visited search) incoming in
  let '(pairs, pair_events) := audit_frontier_edge_events p t live_edges in
  let '(result, row_events) := audit_frontier_rows_counted EV pairs Map.empty in
  (result, map AuditFrontierDfs dfs_events ++ pred_events ++ filter_events ++ pair_events ++
    row_events).

Definition audit_frontier_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list E := flat_map (pred_edges p) (Graph.nodes g).

Definition audit_frontier_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let edges := audit_frontier_input_edges p in let parent_rows := Map.elements (idom t) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map
    (Graph.target g) edges ++
    map fst parent_rows ++ map snd parent_rows ++ map fst (Map.elements (tin t)) ++ map fst
      (Map.elements (tout t)) in
  let numbers := map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  let callback_width := fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v))
    vertices) in
  Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Nat.max callback_width (Nat.max (fold_right Nat.max 0 (map audit_key_bits_weight numbers))
      (audit_key_bits_weight (Pos.of_succ_nat (2 + length (Graph.entries g) * S (Pos.to_nat (fuel
        p))))))).

Definition audit_frontier_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  let nodes := length (Graph.nodes g) in let edges := length (audit_frontier_input_edges p) in
  let f := S (Pos.to_nat (fuel p)) in
  100 * S (nodes + edges) * f * f + audit_dfs_full_input_event_bound p (Graph.entries g).

Definition audit_frontier_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let count := audit_frontier_input_event_bound p in let width := audit_frontier_input_width EV g
    p t in
  1024 * S count * S count + count * (512 + 24 * width).

(** Counted frontier construction returns the frontier with bounded events and work. *)
Definition audit_frontier_counted_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) t,
    let '(result, events) := audit_frontier_counted p t in
    result = dominance_frontier p t /\ length events <= audit_frontier_input_event_bound p /\
    audit_frontier_model_work EV events <= audit_frontier_input_budget EV g p t.

Inductive audit_ifrontier_body (V : Type) : Type :=
  | AuditIfCase (site : nat)
  | AuditIfGet (v : V) (m : Map.t V (FinSet.t V)) (result : option (FinSet.t V))
  | AuditIfElements (set : FinSet.t V) (result : list V)
  | AuditIfMap (size : nat)
  | AuditIfTarget (v : V)
  | AuditIfEncode (v : V) (code : positive).
Arguments AuditIfCase {V} _.
Arguments AuditIfGet {V} _ _ _.
Arguments AuditIfElements {V} _ _.
Arguments AuditIfMap {V} _.
Arguments AuditIfTarget {V} _.
Arguments AuditIfEncode {V} _ _.

Definition audit_ifrontier_successors_counted {V} (EV : encoding V) (df : Map.t V (FinSet.t V)) (v
  : V)
    : list V * list (audit_ifrontier_body V) :=
  let found := Map.get EV v df in
  match found with
  | None => ([], [AuditIfGet v df found; AuditIfCase 0])
  | Some set => let values := FinSet.elements set in
      (values, [AuditIfGet v df found; AuditIfCase 1; AuditIfElements set values])
  end.

Fixpoint audit_ifrontier_entries_counted {V} (EV : encoding V) (df : Map.t V (FinSet.t V)) (defs :
  list V)
    : list V * list (audit_ifrontier_body V) :=
  match defs with
  | [] => ([], [AuditIfCase 2])
  | v :: rest => let '(first, here) := audit_ifrontier_successors_counted EV df v in
      let '(later, events) := audit_ifrontier_entries_counted EV df rest in
      (first ++ later, AuditIfCase 3 :: here ++ events ++ [AuditIfMap (length first)])
  end.

Definition audit_ifrontier_out_counted {V} (EV : encoding V) (df : Map.t V (FinSet.t V)) (v : V)
    : list (V * V) * list (audit_ifrontier_body V) :=
  let '(values, events) := audit_ifrontier_successors_counted EV df v in
  (map (fun n => (v, n)) values, events ++ [AuditIfMap (length values)]).

Definition audit_ifrontier_target_counted {V} (edge : V * V) : V * list (audit_ifrontier_body V) :=
  (snd edge, [AuditIfTarget (snd edge)]).

Definition audit_ifrontier_encode_counted {V} (EV : encoding V) (v : V) : positive * list
  (audit_ifrontier_body V) :=
  let code := encode EV v in (code, [AuditIfEncode v code]).

Definition audit_ifrontier_prepare_callbacks {V} (EV : encoding V) (df : Map.t V (FinSet.t V))
    : audit_prepare_callback_model V (V * V) (audit_ifrontier_body V) :=
  AuditPrepareCallbackModel _ _ _ (audit_ifrontier_out_counted EV df)
    audit_ifrontier_target_counted (audit_ifrontier_encode_counted EV).

Definition audit_ifrontier_dfs_callbacks {V} (EV : encoding V)
    : audit_dfs_callback_model V (V * V) (audit_ifrontier_body V) :=
  AuditDfsCallbackModel _ _ _ audit_ifrontier_target_counted (audit_ifrontier_encode_counted EV).

Definition audit_ifrontier_counted {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) :=
  let '(entries, entry_events) := audit_ifrontier_entries_counted EV df defs in
  let fg := Graph.Make entries (Graph.nodes g)
    (fun v => map (fun n => (v, n)) (frontier_successors EV df v)) fst snd in
  let '(fp, prep_events) := audit_graph_prepare_nested_counted EV fg
    (audit_ifrontier_prepare_callbacks EV df) in
  let '(search, dfs_events) := audit_dfs_nested_counted fp (audit_ifrontier_dfs_callbacks EV)
    FinSet.empty entries in
  (visited search, (entry_events, (prep_events, dfs_events))).

Definition audit_ifrontier_body_work {V} (EV : encoding V) (event : audit_ifrontier_body V) : nat :=
  64 +
  match event with
  | AuditIfGet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_get_weight (encode EV v)
  | AuditIfElements set _ => 64 * Nat.pow (S (audit_erase_nodes set)) 3
  | AuditIfMap size => S size
  | AuditIfEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | _ => 0
  end.

Definition audit_ifrontier_work {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  let '(_, (entry_events, (prep_events, dfs_events))) := audit_ifrontier_counted p df defs in
  fold_right (fun event n => audit_ifrontier_body_work EV event + n) 0 entry_events +
    audit_graph_prepare_nested_total_work (audit_ifrontier_body_work EV) prep_events +
    audit_dfs_nested_total_work EV (audit_ifrontier_body_work EV) dfs_events.

Definition audit_ifrontier_scale {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  1 + length (Graph.nodes g) + length defs + audit_erase_nodes df +
    fold_right (fun row n => audit_erase_nodes (snd row) + n) 0 (Map.elements df).

Definition audit_ifrontier_width {V E} (EV : encoding V) (g : Graph.t V E)
    (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  let rows := Map.elements df in
  let vertices := Graph.nodes g ++ defs ++ map fst rows ++ flat_map (fun row => FinSet.elements
    (snd row)) rows in
  fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices).

Definition audit_ifrontier_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : nat :=
  let scale := audit_ifrontier_scale p df defs in let width := audit_ifrontier_width EV g df defs in
  (128 * 64)%nat * Nat.pow (S scale) 12 * Nat.pow (S width) 2.

(** Counted iterated frontier returns the frontier and obeys its work budget. *)
Definition audit_ifrontier_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) df defs,
    fst (audit_ifrontier_counted p df defs) = iterated_frontier p df defs /\
    audit_ifrontier_work p df defs <= audit_ifrontier_budget EV g p df defs.

Record audit_frontier_source_callbacks (V E B : Type) : Type := AuditFrontierSourceCallbacks {
  audit_frontier_source_encode : V -> positive * list B;
  audit_frontier_source_source : E -> V * list B;
  audit_frontier_source_target : E -> V * list B
}.
Arguments audit_frontier_source_encode {V E B} _ _.
Arguments audit_frontier_source_source {V E B} _ _.
Arguments audit_frontier_source_target {V E B} _ _.

Inductive audit_frontier_source_event (V E B : Type) : Type :=
  | FrontierSourceCase : nat -> audit_frontier_source_event V E B
  | FrontierSourceDfs : audit_dfs_nested_event V E (audit_graph_callback_capture V E B) ->
  audit_frontier_source_event V E B
  | FrontierSourceSource : E -> V -> list B -> audit_frontier_source_event V E B
  | FrontierSourceTarget : E -> V -> list B -> audit_frontier_source_event V E B
  | FrontierSourceParent : audit_map_event V V B -> audit_frontier_source_event V E B
  | FrontierSourceRank : audit_map_event V positive B -> audit_frontier_source_event V E B
  | FrontierSourcePred : audit_map_event V (list E) B -> audit_frontier_source_event V E B
  | FrontierSourceRows : audit_map_event V (FinSet.t V) B -> audit_frontier_source_event V E B
  | FrontierSourceSet : audit_set_event V B -> audit_frontier_source_event V E B
  | FrontierSourceCompare : positive -> positive -> bool -> list audit_positive_compare_event ->
  audit_frontier_source_event V E B
  | FrontierSourceOutput : nat -> audit_frontier_source_event V E B.
Arguments FrontierSourceCase {V E B} _.
Arguments FrontierSourceDfs {V E B} _.
Arguments FrontierSourceSource {V E B} _ _ _.
Arguments FrontierSourceTarget {V E B} _ _ _.
Arguments FrontierSourceParent {V E B} _.
Arguments FrontierSourceRank {V E B} _.
Arguments FrontierSourcePred {V E B} _.
Arguments FrontierSourceRows {V E B} _.
Arguments FrontierSourceSet {V E B} _.
Arguments FrontierSourceCompare {V E B} _ _ _ _.
Arguments FrontierSourceOutput {V E B} _.

Definition audit_frontier_source_dom {V E B} (enc : V -> positive * list B) (t : dom_tree V) (d n
  : V)
    : bool * list (audit_frontier_source_event V E B) :=
  let '(a, ea) := audit_map_get enc d (tin t) in
  match a with
  | None => (false, map FrontierSourceRank ea)
  | Some av =>
    let '(b, eb) := audit_map_get enc n (tin t) in
    match b with
    | None => (false, map FrontierSourceRank (ea ++ eb))
    | Some bv =>
      let '(c, ec) := audit_map_get enc d (tout t) in
      match c with
      | None => (false, map FrontierSourceRank (ea ++ eb ++ ec))
      | Some cv =>
        let '(z, ez) := audit_map_get enc n (tout t) in
        match z with
        | None => (false, map FrontierSourceRank (ea ++ eb ++ ec ++ ez))
        | Some zv =>
          let '(first, ef) := audit_positive_leb av bv in let '(second, es) := audit_positive_leb
            zv cv in
          (first && second, map FrontierSourceRank (ea ++ eb ++ ec ++ ez) ++
            [FrontierSourceCompare av bv first ef; FrontierSourceCompare zv cv second es])
        end
      end
    end
  end.

Definition audit_frontier_source_step {V E B} (enc : V -> positive * list B) (t : dom_tree V)
    (stop : option V) (state : option V * list V) : (option V * list V) * list
      (audit_frontier_source_event V E B) :=
  let '(current, seen) := state in
  match current with
  | None => ((None, seen), [FrontierSourceCase 0])
  | Some v => let '(blocked, details) :=
        match stop with
        | None => (false, [])
        | Some q => audit_frontier_source_dom enc t v q
        end in
      if blocked then ((None, seen), FrontierSourceCase 1 :: details ++ [FrontierSourceCase 2])
      else let '(parent, reads) := audit_map_get enc v (idom t) in
        ((parent, v :: seen), FrontierSourceCase 1 :: details ++ [FrontierSourceCase 3] ++ map
          FrontierSourceParent reads)
  end.

Fixpoint audit_frontier_source_walk {V E B} (enc : V -> positive * list B) (t : dom_tree V)
    (stop : option V) (fuel : positive) (state : option V * list V)
    : (option V * list V) * list (audit_frontier_source_event V E B) :=
  match fst state with
  | None => (state, [FrontierSourceCase 4])
  | Some _ =>
    match fuel with
    | xH => let '(result, events) := audit_frontier_source_step enc t stop state in (result,
      FrontierSourceCase 5 :: events)
    | xO rest => let '(middle, first) := audit_frontier_source_walk enc t stop rest state in
        let '(result, second) := audit_frontier_source_walk enc t stop rest middle in (result,
          FrontierSourceCase 6 :: first ++ second)
    | xI rest => let '(middle, first) := audit_frontier_source_walk enc t stop rest state in
        let '(last, second) := audit_frontier_source_walk enc t stop rest middle in
        let '(result, events) := audit_frontier_source_step enc t stop last in (result,
          FrontierSourceCase 7 :: first ++ second ++ events)
    end
  end.

Fixpoint audit_frontier_source_incoming {V E B} {EV : encoding V} {g : Graph.t V E}
    (enc : V -> positive * list B) (p : prepared EV g) (nodes : list V)
    : list E * list (audit_frontier_source_event V E B) :=
  match nodes with
  | [] => ([], [FrontierSourceCase 10])
  | v :: rest => let '(found, reads) := audit_map_get enc v (in_index p) in
      let row :=
        match found with
        | Some xs => xs
        | None => []
        end in
      let '(later, events) := audit_frontier_source_incoming enc p rest in
      (row ++ later, FrontierSourceCase 11 :: map FrontierSourcePred reads ++ events ++
        [FrontierSourceOutput (length row)])
  end.

Fixpoint audit_frontier_source_filter {V E B} (cb : audit_frontier_source_callbacks V E B)
    (live : FinSet.t V) (edges : list E) : list E * list (audit_frontier_source_event V E B) :=
  match edges with
  | [] => ([], [FrontierSourceCase 12])
  | edge :: rest => let '(vertex, body) := audit_frontier_source_source cb edge in
      let '(keep, reads) := audit_finset_mem (audit_frontier_source_encode cb) vertex live in
      let '(later, events) := audit_frontier_source_filter cb live rest in
      (if keep then edge :: later else later, [FrontierSourceCase 13; FrontierSourceSource edge
        vertex body] ++
        map FrontierSourceSet reads ++ [FrontierSourceCase (if keep then 14 else 15)] ++ events)
  end.

Fixpoint audit_frontier_source_targets {V E B} (cb : audit_frontier_source_callbacks V E B)
    (edge : E) (vertices : list V) : list (V * V) * list (audit_frontier_source_event V E B) :=
  match vertices with
  | [] => ([], [FrontierSourceCase 16])
  | v :: rest => let '(target, body) := audit_frontier_source_target cb edge in
      let '(later, events) := audit_frontier_source_targets cb edge rest in
      ((v, target) :: later, FrontierSourceCase 17 :: FrontierSourceTarget edge target body ::
        events)
  end.

Fixpoint audit_frontier_source_edges {V E B} {EV : encoding V} {g : Graph.t V E}
    (cb : audit_frontier_source_callbacks V E B) (p : prepared EV g) (t : dom_tree V) (edges :
      list E)
    : list (V * V) * list (audit_frontier_source_event V E B) :=
  match edges with
  | [] => ([], [FrontierSourceCase 18])
  | edge :: rest => let '(source, sb) := audit_frontier_source_source cb edge in
      let '(target, tb) := audit_frontier_source_target cb edge in
      let '(stop, reads) := audit_map_get (audit_frontier_source_encode cb) target (idom t) in
      let '(walk, we) := audit_frontier_source_walk (audit_frontier_source_encode cb) t stop (fuel
        p) (Some source, []) in
      let '(pairs, pe) := audit_frontier_source_targets cb edge (snd walk) in
      let '(later, events) := audit_frontier_source_edges cb p t rest in
      (pairs ++ later, [FrontierSourceCase 19; FrontierSourceSource edge source sb;
        FrontierSourceTarget edge target tb] ++
        map FrontierSourceParent reads ++ we ++ pe ++ events ++ [FrontierSourceOutput (length
          pairs)])
  end.

Fixpoint audit_frontier_source_rows {V E B} (enc : V -> positive * list B) (pairs : list (V * V))
    (rows : Map.t V (FinSet.t V)) : Map.t V (FinSet.t V) * list (audit_frontier_source_event V E
      B) :=
  match pairs with
  | [] => (rows, [FrontierSourceCase 20])
  | (d, n) :: rest => let '(found, reads) := audit_map_get enc d rows in
      let old :=
        match found with
        | Some s => s
        | None => FinSet.empty
        end in
      let '(row, adds) := audit_finset_add enc n old in let '(next, writes) := audit_map_set enc d
        row rows in
      let '(result, events) := audit_frontier_source_rows enc rest next in
      (result, FrontierSourceCase 21 :: map FrontierSourceRows reads ++ map FrontierSourceSet adds
        ++ map FrontierSourceRows writes ++ events)
  end.

Definition audit_frontier_source_counted {V E B} {EV : encoding V} {g : Graph.t V E}
    (cb : audit_frontier_source_callbacks V E B) (p : prepared EV g) (t : dom_tree V)
    : Map.t V (FinSet.t V) * list (audit_frontier_source_event V E B) :=
  let dfs_cb := AuditDfsCallbackModel V E B (audit_frontier_source_target cb)
    (audit_frontier_source_encode cb) in
  let '(search, dfs_events) := audit_dfs_source_counted p dfs_cb FinSet.empty (Graph.entries g) in
  let '(incoming, pred_events) := audit_frontier_source_incoming (audit_frontier_source_encode cb)
    p (Graph.nodes g) in
  let '(live, filter_events) := audit_frontier_source_filter cb (visited search) incoming in
  let '(pairs, pair_events) := audit_frontier_source_edges cb p t live in
  let '(result, row_events) := audit_frontier_source_rows (audit_frontier_source_encode cb) pairs
    Map.empty in
  (result, map FrontierSourceDfs dfs_events ++ pred_events ++ filter_events ++ pair_events ++
    row_events).

(** Frontier callbacks return the original graph and encoding values. *)
Definition audit_frontier_source_callbacks_erase {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_frontier_source_callbacks V E B) : Prop :=
  (forall v, fst (audit_frontier_source_encode cb v) = encode EV v) /\
  (forall e, fst (audit_frontier_source_source cb e) = Graph.source g e) /\
  (forall e, fst (audit_frontier_source_target cb e) = Graph.target g e).

Definition audit_frontier_source_event_work {V E B} (weight : B -> nat)
    (event : audit_frontier_source_event V E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 +
  match event with
  | FrontierSourceDfs item => audit_dfs_source_event_work weight item
  | FrontierSourceSource _ _ events
  | FrontierSourceTarget _ _ events => body events
  | FrontierSourceParent item => audit_map_source_work body [item]
  | FrontierSourceRank item => audit_map_source_work body [item]
  | FrontierSourcePred item => audit_map_source_work body [item]
  | FrontierSourceRows item => audit_map_source_work body [item]
  | FrontierSourceSet item => audit_finset_source_work body [item]
  | FrontierSourceCompare _ _ _ events => audit_positive_order_source_work events
  | FrontierSourceOutput n => S n
  | FrontierSourceCase _ => 0
  end.

Definition audit_frontier_source_body_event_work {V E B} (weight : B -> nat)
    (event : audit_frontier_source_event V E B) : nat :=
  match event with
  | FrontierSourceDfs item => audit_dfs_source_body_work weight [item]
  | FrontierSourceSource _ _ body
  | FrontierSourceTarget _ _ body
  | FrontierSourceParent (AuditMapGet _ _ _ _ body _)
  | FrontierSourceParent (AuditMapSet _ _ _ _
      _ body _) |
    FrontierSourceParent (AuditMapRemove _ _ _ _ body _) | FrontierSourceRank (AuditMapGet _ _ _ _
      body _) |
    FrontierSourceRank (AuditMapSet _ _ _ _ _ body _) | FrontierSourceRank (AuditMapRemove _ _ _ _
      body _) |
    FrontierSourcePred (AuditMapGet _ _ _ _ body _) | FrontierSourcePred (AuditMapSet _ _ _ _ _
      body _) |
    FrontierSourcePred (AuditMapRemove _ _ _ _ body _) | FrontierSourceRows (AuditMapGet _ _ _ _
      body _) |
    FrontierSourceRows (AuditMapSet _ _ _ _ _ body _) | FrontierSourceRows (AuditMapRemove _ _ _ _
      body _) |
    FrontierSourceSet (AuditSetMem _ _ _ _ body _) | FrontierSourceSet (AuditSetAdd _ _ _ _ body
      _) |
    FrontierSourceSet (AuditSetRemove _ _ _ _ body _) => fold_right (fun item n => weight item +
      n) 0 body
  | FrontierSourceSet (AuditSetFold _ _)
  | FrontierSourceCompare _ _ _ _
  | FrontierSourceOutput _
  | FrontierSourceCase _ => 0
  end.

Definition audit_frontier_source_work {V E B} (weight : B -> nat)
    (events : list (audit_frontier_source_event V E B)) : nat :=
  fold_right (fun item n => audit_frontier_source_event_work weight item + n) 0 events.

Definition audit_frontier_source_body_work {V E B} (weight : B -> nat)
    (events : list (audit_frontier_source_event V E B)) : nat :=
  fold_right (fun item n => audit_frontier_source_body_event_work weight item + n) 0 events.

Definition audit_frontier_source_input_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list E := flat_map (pred_edges p) (Graph.nodes g).

Definition audit_frontier_source_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let edges := audit_frontier_source_input_edges p in let parents := Map.elements (idom t) in
  let vertices := Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map
    (Graph.target g) edges ++
    map fst parents ++ map snd parents ++ map fst (Map.elements (tin t)) ++ map fst (Map.elements
      (tout t)) in
  let numbers := map snd (Map.elements (tin t)) ++ map snd (Map.elements (tout t)) in
  Nat.max (audit_dfs_full_input_width EV g p (Graph.entries g))
    (Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
      (Nat.max (fold_right Nat.max 0 (map Pos.size_nat numbers))
        (Pos.size_nat (Pos.of_succ_nat (2 + length (Graph.entries g) * S (Pos.to_nat (fuel p))))))).

Definition audit_frontier_source_input_event_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : nat :=
  let size := length (Graph.nodes g) + length (audit_frontier_source_input_edges p) in
  let f := S (Pos.to_nat (fuel p)) in
  1024 * S size * f * f + audit_dfs_full_input_event_bound p (Graph.entries g).

Definition audit_frontier_source_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) : nat :=
  let count := audit_frontier_source_input_event_bound p in
  let width := audit_frontier_source_input_width EV g p t in
  1024 * S count * S count + count * (1024 + 128 * width).

(** Source frontier construction preserves the result and satisfies its source work bound. *)
Definition audit_frontier_source_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) (t : dom_tree V)
    (cb : audit_frontier_source_callbacks V E B) (weight : B -> nat),
    audit_frontier_source_callbacks_erase EV g cb ->
    let '(result, events) := audit_frontier_source_counted cb p t in
    result = dominance_frontier p t /\ length events <= audit_frontier_source_input_event_bound p /\
    audit_frontier_source_work weight events <=
      audit_frontier_source_input_budget EV g p t + audit_frontier_source_body_work weight events.
