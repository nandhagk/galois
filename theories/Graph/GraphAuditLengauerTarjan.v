(** * Lengauer-Tarjan audit model

    Models source-level events, work, and associated contract statements.
    For example, processing a predecessor records its map and comparison operations.

    Builds on: the graph and collections interfaces imported below. *)

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost CollectionsEncoding CollectionsMap
  CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphAuditBase GraphAuditDfs GraphAuditVirtual GraphAuditSemiDominators
    GraphLengauerTarjan.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditPrimitive
  CollectionsAuditCompare.
Import List.ListNotations.

Inductive audit_lt_call (V E : Type) : Type :=
  | AuditLtCase (site : nat)
  | AuditLtInner (event : audit_semi_call V)
  | AuditLtBucketGet (v : V) (m : Map.t V (list V)) (result : option (list V))
  | AuditLtBucketSet (v : V) (value : list V) (m : Map.t V (list V))
  | AuditLtTreeGet (v : V) (m : Map.t V E) (result : option E)
  | AuditLtSource (e : E) (v : V)
  | AuditLtLink (v parent : V) (st : SemiLinks.t V)
  | AuditLtEncode (v : V) (code : positive)
  | AuditLtEq (a b : positive) (result : bool)
  | AuditLtOutput (size : nat).
Arguments AuditLtCase {V E} _.
Arguments AuditLtInner {V E} _.
Arguments AuditLtBucketGet {V E} _ _ _.
Arguments AuditLtBucketSet {V E} _ _ _.
Arguments AuditLtTreeGet {V E} _ _ _.
Arguments AuditLtSource {V E} _ _.
Arguments AuditLtLink {V E} _ _ _.
Arguments AuditLtEncode {V E} _ _.
Arguments AuditLtEq {V E} _ _ _.
Arguments AuditLtOutput {V E} _.

Fixpoint audit_lt_buckets_counted {V E} (EV : encoding V) (semis : Map.t V V)
    (order : list V) (buckets : Map.t V (list V)) : Map.t V (list V) * list (audit_lt_call V E) :=
  match order with
  | [] => (buckets, [AuditLtCase 0])
  | v :: rest => let found := Map.get EV v semis in
    match found with
    | None => let '(result, events) := audit_lt_buckets_counted EV semis rest buckets in
        (result, AuditLtCase 1 :: AuditLtInner (AuditSemiGet v semis None) :: AuditLtCase 2 ::
          events)
    | Some s => let old := Map.get EV s buckets in
        let row :=
          match old with
          | Some xs => xs
          | None => []
          end in
        let next := Map.set EV s (v :: row) buckets in
        let '(result, events) := audit_lt_buckets_counted EV semis rest next in
        (result, AuditLtCase 1 :: AuditLtInner (AuditSemiGet v semis (Some s)) :: AuditLtCase 3 ::
          AuditLtBucketGet s buckets old :: AuditLtBucketSet s (v :: row) buckets :: events)
    end
  end.

Inductive audit_lt_member_run {V E} (EV : encoding V) (r : dfs_result V E) (semis : Map.t V V)
    (s : V) : LtState.t V -> V -> LtState.t V -> list (audit_lt_call V E) -> Prop :=
  | AuditLtMember st v links' root part inner u score score_events rank rank_events choose :
    audit_semi_compress_run EV r semis (LtState.links st) v (links', (root, part)) inner ->
    u =
      match part with
      | Some best => best
      | None => v
      end ->
    audit_semi_score_counted EV r semis u = (score, score_events) ->
    audit_semi_rank_counted EV r s = (rank, rank_events) -> choose = Pos.ltb score rank ->
    let parent := if choose then u else s in
    audit_lt_member_run EV r semis s st v (LtState.Make links' (Map.set EV v parent
      (LtState.parents st)))
      (map AuditLtInner inner ++ [AuditLtCase 4] ++ map AuditLtInner score_events ++
       map AuditLtInner rank_events ++ [AuditLtInner (AuditSemiLess score rank choose);
         AuditLtInner (AuditSemiSet v parent (LtState.parents st))]).

Inductive audit_lt_members_run {V E} (EV : encoding V) (r : dfs_result V E) (semis : Map.t V V) (s
  : V) :
    list V -> LtState.t V -> LtState.t V -> list (audit_lt_call V E) -> Prop :=
  | AuditLtMembersNil st : audit_lt_members_run EV r semis s [] st st [AuditLtCase 5]
  | AuditLtMembersCons v rest initial middle result here later :
    audit_lt_member_run EV r semis s initial v middle here ->
    audit_lt_members_run EV r semis s rest middle result later ->
    audit_lt_members_run EV r semis s (v :: rest) initial result (AuditLtCase 6 :: here ++ later).

Inductive audit_lt_reverse_run {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (buckets : Map.t V (list V)) : LtState.t V -> V -> LtState.t V -> list
      (audit_lt_call V E) -> Prop :=
  | AuditLtReverseRoot st s bucket members settled events :
    bucket = Map.get EV s buckets -> members =
      match bucket with
      | Some xs => xs
      | None => []
      end ->
    audit_lt_members_run EV r semis s members st settled events -> Map.get EV s (tree_edge r) =
      None ->
    audit_lt_reverse_run EV g r semis buckets st s settled
      ([AuditLtBucketGet s buckets bucket] ++ events ++ [AuditLtTreeGet s (tree_edge r) None;
        AuditLtCase 7])
  | AuditLtReverseNode st s bucket members settled events edge parent :
    bucket = Map.get EV s buckets -> members =
      match bucket with
      | Some xs => xs
      | None => []
      end ->
    audit_lt_members_run EV r semis s members st settled events -> Map.get EV s (tree_edge r) =
      Some edge ->
    parent = Graph.source g edge ->
    audit_lt_reverse_run EV g r semis buckets st s
      (LtState.Make (semi_link EV (LtState.links settled) s parent) (LtState.parents settled))
      ([AuditLtBucketGet s buckets bucket] ++ events ++
        [AuditLtTreeGet s (tree_edge r) (Some edge); AuditLtCase 8; AuditLtSource edge parent;
         AuditLtLink s parent (LtState.links settled)]).

Inductive audit_lt_reverse_fold_run {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (buckets : Map.t V (list V)) : list V -> LtState.t V -> LtState.t V ->
      list (audit_lt_call V E) -> Prop :=
  | AuditLtReverseNil st : audit_lt_reverse_fold_run EV g r semis buckets [] st st [AuditLtCase 9]
  | AuditLtReverseCons v rest initial middle result here later :
    audit_lt_reverse_run EV g r semis buckets initial v middle here ->
    audit_lt_reverse_fold_run EV g r semis buckets rest middle result later ->
    audit_lt_reverse_fold_run EV g r semis buckets (v :: rest) initial result (AuditLtCase 10 ::
      here ++ later).

Definition audit_lt_correct_counted {V E} (EV : encoding V) (semis provisional corrected : Map.t V
  V)
    (v : V) : Map.t V V * list (audit_lt_call V E) :=
  let found := Map.get EV v provisional in
  match found with
  | None => (corrected, [AuditLtInner (AuditSemiGet v provisional found); AuditLtCase 11])
  | Some u => let a := encode EV u in let '(value, value_events) := audit_semi_value_counted EV
    semis v in
      let b := encode EV value in let equal := Pos.eqb a b in
      let '(parent, parent_events) := if equal then (u, []) else audit_semi_value_counted EV
        corrected u in
      (Map.set EV v parent corrected,
       [AuditLtInner (AuditSemiGet v provisional found); AuditLtCase 12; AuditLtEncode u a] ++
         map AuditLtInner value_events ++ [AuditLtEncode value b; AuditLtEq a b equal] ++
         map AuditLtInner parent_events ++ [AuditLtInner (AuditSemiSet v parent corrected)])
  end.

Fixpoint audit_lt_correct_fold {V E} (EV : encoding V) (semis provisional : Map.t V V)
    (vertices : list V) (corrected : Map.t V V) : Map.t V V * list (audit_lt_call V E) :=
  match vertices with
  | [] => (corrected, [AuditLtCase 13])
  | v :: rest => let '(middle, here) := audit_lt_correct_counted EV semis provisional corrected v in
      let '(result, later) := audit_lt_correct_fold EV semis provisional rest middle in
      (result, AuditLtCase 14 :: here ++ later)
  end.

(** An LT computation run relates its inputs, result and event trace. *)

Definition audit_lt_compute_run {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (semis : Map.t V V) (result : Map.t V V) (events : list (audit_lt_call V E)) : Prop :=
  let '(buckets, bucket_events) := audit_lt_buckets_counted EV semis (preorder r) Map.empty in
  exists settled reverse_events,
    audit_lt_reverse_fold_run EV g r semis buckets (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty) settled reverse_events /\
    let '(output, correction_events) := audit_lt_correct_fold EV semis (LtState.parents settled)
      (preorder r) Map.empty in
    result = output /\ events = bucket_events ++ [AuditLtOutput (length (preorder r))] ++
      reverse_events ++ correction_events.

Definition audit_lt_event_work {V E} (EV : encoding V) (event : audit_lt_call V E) : nat :=
  64 +
  match event with
  | AuditLtInner item => audit_semi_call_work EV item
  | AuditLtBucketGet v _ _
  | AuditLtTreeGet v _ _ =>
      audit_encoding_weight (audit_key_bits_weight (encode EV v)) + audit_get_weight (encode EV v)
  | AuditLtBucketSet v _ _ => audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v)
  | AuditLtLink v _ _ => 3 * (audit_encoding_weight (audit_key_bits_weight (encode EV v)) +
    audit_set_weight (encode EV v))
  | AuditLtEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditLtEq a b _ => audit_binary_weight (Z.pos a) (Z.pos b)
  | AuditLtOutput size => S size
  | _ => 0
  end.

Definition audit_lt_model_work {V E} (EV : encoding V) (events : list (audit_lt_call V E)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event total => audit_lt_event_work EV event + total) 0 events.

Definition audit_lt_event_bound {V E} (r : dfs_result V E) : nat :=
  let n := S (length (preorder r)) in 200 * n * n * S (audit_semi_compute_rank_bound r).

Definition audit_lt_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge
    r)) ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
      r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => audit_key_bits_weight (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => audit_key_bits_weight (snd row)) (Map.elements (pre_num
      r)))).

Definition audit_lt_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let count := audit_lt_event_bound r in let width := audit_lt_input_width EV g r semis in
  512 * S count * S count + count * (512 + 16 * width).

(** LT computation admits a run with the original result and bounded events and work. *)
Definition audit_lt_compute_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis,
    exists result events, audit_lt_compute_run EV g r semis result events /\ result = lt_compute
      EV g r semis /\
      length events <= audit_lt_event_bound r /\ audit_lt_model_work EV events <=
        audit_lt_input_budget EV g r semis.

(** LT computation runs have unique results and event traces. *)
Definition audit_lt_compute_unique_statement : Prop :=
  forall V E (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis a b ea eb,
    audit_lt_compute_run EV g r semis a ea -> audit_lt_compute_run EV g r semis b eb -> a = b /\
      ea = eb.

Inductive audit_lt_nested_event (V E B : Type) : Type :=
  | LtNestedCase : nat -> audit_lt_nested_event V E B
  | LtNestedSemi : audit_semi_nested_event V B -> audit_lt_nested_event V E B
  | LtNestedProducer : audit_semi_producer_nested_event V E B -> audit_lt_nested_event V E B
  | LtNestedBucket : audit_map_event V (list V) B -> audit_lt_nested_event V E B
  | LtNestedTree : audit_map_event V E B -> audit_lt_nested_event V E B
  | LtNestedSource : E -> V -> list B -> audit_lt_nested_event V E B
  | LtNestedEncode : V -> positive -> list B -> audit_lt_nested_event V E B
  | LtNestedEqual : positive -> positive -> bool -> list audit_positive_eqb_event ->
  audit_lt_nested_event V E B
  | LtNestedOutput : nat -> audit_lt_nested_event V E B.
Arguments LtNestedCase {V E B} _.
Arguments LtNestedSemi {V E B} _.
Arguments LtNestedProducer {V E B} _.
Arguments LtNestedBucket {V E B} _.
Arguments LtNestedTree {V E B} _.
Arguments LtNestedSource {V E B} _ _ _.
Arguments LtNestedEncode {V E B} _ _ _.
Arguments LtNestedEqual {V E B} _ _ _ _.
Arguments LtNestedOutput {V E B} _.

Fixpoint audit_lt_nested_buckets {V E B} (enc : V -> positive * list B) (semis : Map.t V V)
    (order : list V) (buckets : Map.t V (list V)) : Map.t V (list V) * list (audit_lt_nested_event
      V E B) :=
  match order with
  | [] => (buckets, [LtNestedCase 0])
  | v :: rest => let '(found, get_events) := audit_map_get enc v semis in
      match found with
      | None => let '(result, later) := audit_lt_nested_buckets enc semis rest buckets in
          (result, [LtNestedCase 1] ++ map (fun item => LtNestedSemi (SemiNestedVertexMap item))
            get_events ++
            [LtNestedCase 2] ++ later)
      | Some s => let '(old, bucket_events) := audit_map_get enc s buckets in
          let row :=
            match old with
            | Some xs => xs
            | None => []
            end in
          let '(next, set_events) := audit_map_set enc s (v :: row) buckets in
          let '(result, later) := audit_lt_nested_buckets enc semis rest next in
          (result, [LtNestedCase 1] ++ map (fun item => LtNestedSemi (SemiNestedVertexMap item))
            get_events ++
            [LtNestedCase 3] ++ map LtNestedBucket bucket_events ++ map LtNestedBucket set_events
              ++ later)
      end
  end.

Inductive audit_lt_nested_member_run {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (s : V) :
    LtState.t V -> V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
  | LtNestedMember st v links root part inner u score score_events rank rank_events choose
  compare_events
    parents set_events :
    audit_semi_nested_compress_run enc r semis (LtState.links st) v (links, (root, part)) inner ->
    u =
      match part with
      | Some best => best
      | None => v
      end ->
    audit_semi_nested_score enc r semis u = (score, score_events) ->
    audit_semi_nested_rank enc r s = (rank, rank_events) ->
    audit_positive_ltb score rank = (choose, compare_events) ->
    audit_map_set enc v (if choose then u else s) (LtState.parents st) = (parents, set_events) ->
    audit_lt_nested_member_run enc r semis s st v (LtState.Make links parents)
      (map LtNestedSemi inner ++ [LtNestedCase 4] ++ map LtNestedSemi score_events ++
       map LtNestedSemi rank_events ++ [LtNestedSemi (SemiNestedCompare score rank choose
         compare_events)] ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) set_events).

Inductive audit_lt_nested_members_run {V E B} (enc : V -> positive * list B)
    (r : dfs_result V E) (semis : Map.t V V) (s : V) :
    list V -> LtState.t V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
  | LtNestedMembersNil st : audit_lt_nested_members_run enc r semis s [] st st [LtNestedCase 5]
  | LtNestedMembersCons v rest initial middle result here later :
    audit_lt_nested_member_run enc r semis s initial v middle here ->
    audit_lt_nested_members_run enc r semis s rest middle result later ->
    audit_lt_nested_members_run enc r semis s (v :: rest) initial result (LtNestedCase 6 :: here
      ++ later).

Inductive audit_lt_nested_reverse_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) (buckets : Map.t V (list
      V)) :
    LtState.t V -> V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
  | LtNestedReverseRoot st s bucket bucket_events members settled events tree_events :
    audit_map_get enc s buckets = (bucket, bucket_events) ->
    members =
      match bucket with
      | Some xs => xs
      | None => []
      end ->
    audit_lt_nested_members_run enc r semis s members st settled events ->
    audit_map_get enc s (tree_edge r) = (None, tree_events) ->
    audit_lt_nested_reverse_run enc source r semis buckets st s settled
      (map LtNestedBucket bucket_events ++ events ++ map LtNestedTree tree_events ++ [LtNestedCase
        7])
  | LtNestedReverseNode st s bucket bucket_events members settled events edge tree_events parent
  source_body links link_events :
    audit_map_get enc s buckets = (bucket, bucket_events) ->
    members =
      match bucket with
      | Some xs => xs
      | None => []
      end ->
    audit_lt_nested_members_run enc r semis s members st settled events ->
    audit_map_get enc s (tree_edge r) = (Some edge, tree_events) -> source edge = (parent,
      source_body) ->
    audit_semi_producer_link enc (LtState.links settled) s parent = (links, link_events) ->
    audit_lt_nested_reverse_run enc source r semis buckets st s (LtState.Make links
      (LtState.parents settled))
      (map LtNestedBucket bucket_events ++ events ++ map LtNestedTree tree_events ++
        [LtNestedCase 8; LtNestedSource edge parent source_body] ++ map LtNestedProducer
          link_events).

Inductive audit_lt_nested_reverse_fold_run {V E B} (enc : V -> positive * list B)
    (source : E -> V * list B) (r : dfs_result V E) (semis : Map.t V V) (buckets : Map.t V (list
      V)) :
    list V -> LtState.t V -> LtState.t V -> list (audit_lt_nested_event V E B) -> Prop :=
  | LtNestedReverseNil st : audit_lt_nested_reverse_fold_run enc source r semis buckets [] st st
  [LtNestedCase 9]
  | LtNestedReverseCons v rest initial middle result here later :
    audit_lt_nested_reverse_run enc source r semis buckets initial v middle here ->
    audit_lt_nested_reverse_fold_run enc source r semis buckets rest middle result later ->
    audit_lt_nested_reverse_fold_run enc source r semis buckets (v :: rest) initial result
      (LtNestedCase 10 :: here ++ later).

Definition audit_lt_nested_correct {V E B} (enc : V -> positive * list B)
    (semis provisional corrected : Map.t V V) (v : V) : Map.t V V * list (audit_lt_nested_event V
      E B) :=
  let '(found, first) := audit_map_get enc v provisional in
  match found with
  | None => (corrected, map (fun item => LtNestedSemi (SemiNestedVertexMap item)) first ++
    [LtNestedCase 11])
  | Some u => let '(a, a_body) := enc u in
      let '(value, value_events) := audit_map_get enc v semis in
      let value :=
        match value with
        | Some x => x
        | None => v
        end in
      let '(b, b_body) := enc value in let '(equal, equal_events) := audit_positive_eqb a b in
      let '(parent, parent_events) := if equal then (u, []) else
        let '(found_parent, events) := audit_map_get enc u corrected in
        (
          match found_parent with
          | Some x => x
          | None => u
          end, events) in
      let '(result, set_events) := audit_map_set enc v parent corrected in
      (result, map (fun item => LtNestedSemi (SemiNestedVertexMap item)) first ++ [LtNestedCase
        12; LtNestedEncode u a a_body] ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) value_events ++
       [LtNestedEncode value b b_body; LtNestedEqual a b equal equal_events] ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) parent_events ++
       map (fun item => LtNestedSemi (SemiNestedVertexMap item)) set_events)
  end.

Fixpoint audit_lt_nested_correct_fold {V E B} (enc : V -> positive * list B)
    (semis provisional : Map.t V V) (vertices : list V) (corrected : Map.t V V)
    : Map.t V V * list (audit_lt_nested_event V E B) :=
  match vertices with
  | [] => (corrected, [LtNestedCase 13])
  | v :: rest => let '(middle, here) := audit_lt_nested_correct enc semis provisional corrected v in
      let '(result, later) := audit_lt_nested_correct_fold enc semis provisional rest middle in
      (result, LtNestedCase 14 :: here ++ later)
  end.

(** A nested LT run relates callback operations, its result and event trace. *)
Definition audit_lt_nested_run {V E B} (enc : V -> positive * list B) (source : E -> V * list B)
    (r : dfs_result V E) (semis : Map.t V V) (result : Map.t V V) (events : list
      (audit_lt_nested_event V E B)) : Prop :=
  let '(buckets, bucket_events) := audit_lt_nested_buckets enc semis (preorder r) Map.empty in
  exists settled reverse_events,
    audit_lt_nested_reverse_fold_run enc source r semis buckets (rev (preorder r))
      (LtState.Make semi_links_empty Map.empty) settled reverse_events /\
    let '(output, correction_events) := audit_lt_nested_correct_fold enc semis (LtState.parents
      settled) (preorder r) Map.empty in
    result = output /\ events = bucket_events ++ [LtNestedOutput (length (preorder r))] ++
      reverse_events ++ correction_events.

(** Nested LT computation admits a run yielding the ordinary result. *)
Definition audit_lt_nested_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis
    (enc : V -> positive * list B) (source : E -> V * list B),
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    exists result events, audit_lt_nested_run enc source r semis result events /\ result =
      lt_compute EV g r semis.

(** Nested LT computation runs have unique results and event traces. *)
Definition audit_lt_nested_unique_statement : Prop :=
  forall V E B (enc : V -> positive * list B) (source : E -> V * list B) r semis a ea b eb,
    audit_lt_nested_run enc source r semis a ea -> audit_lt_nested_run enc source r semis b eb ->
      a = b /\ ea = eb.

Definition audit_lt_nested_event_work {V E B} (weight : B -> nat) (event : audit_lt_nested_event V
  E B) : nat :=
  let body := fun events => fold_right (fun item n => weight item + n) 0 events in
  64 +
  match event with
  | LtNestedSemi item => audit_semi_nested_event_work weight item
  | LtNestedProducer item => audit_semi_producer_nested_event_work weight item
  | LtNestedBucket item => audit_map_source_work body [item]
  | LtNestedTree item => audit_map_source_work body [item]
  | LtNestedSource _ _ events
  | LtNestedEncode _ _ events => body events
  | LtNestedEqual _ _ _ events => audit_positive_eqb_source_work events
  | LtNestedOutput size => S size
  | LtNestedCase _ => 0
  end.

Definition audit_lt_nested_body_event_work {V E B} (weight : B -> nat)
    (event : audit_lt_nested_event V E B) : nat :=
  match event with
  | LtNestedSemi item => audit_semi_nested_body_event_work weight item
  | LtNestedProducer item => audit_semi_producer_nested_body_event_work weight item
  | LtNestedSource _ _ body
  | LtNestedEncode _ _ body
  | LtNestedBucket (AuditMapGet _ _ _ _ body _)
  | LtNestedBucket (AuditMapSet _ _ _ _ _ body _)
  | LtNestedBucket (AuditMapRemove _ _ _ _ body _)
  | LtNestedTree (AuditMapGet _ _ _ _ body _)
  | LtNestedTree (AuditMapSet _ _ _ _ _ body _)
  | LtNestedTree (AuditMapRemove _ _ _ _ body _) =>
      fold_right (fun item n => weight item + n) 0 body
  | LtNestedCase _
  | LtNestedEqual _ _ _ _
  | LtNestedOutput _ => 0
  end.

Definition audit_lt_nested_work {V E B} (weight : B -> nat) (events : list (audit_lt_nested_event
  V E B)) : nat :=
  fold_right (fun item n => audit_lt_nested_event_work weight item + n) 0 events.

Definition audit_lt_nested_body_work {V E B} (weight : B -> nat) (events : list
  (audit_lt_nested_event V E B)) : nat :=
  fold_right (fun item n => audit_lt_nested_body_event_work weight item + n) 0 events.

Definition audit_lt_nested_input_width {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let rows := Map.elements semis in
  let vertices := preorder r ++ map fst rows ++ map snd rows ++ map fst (Map.elements (tree_edge
    r)) ++
    map (Graph.source g) (map snd (Map.elements (tree_edge r))) ++ map fst (Map.elements (pre_num
      r)) in
  Nat.max (fold_right Nat.max 0 (map (fun v => Pos.size_nat (encode EV v)) vertices))
    (fold_right Nat.max 0 (map (fun row => Pos.size_nat (snd row)) (Map.elements (pre_num r)))).

Definition audit_lt_nested_input_event_bound {V E} (r : dfs_result V E) : nat :=
  let n := S (length (preorder r)) in 200 * n * n * S (audit_semi_producer_input_rank r).

Definition audit_lt_nested_input_budget {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : nat :=
  let count := audit_lt_nested_input_event_bound r in
  512 * S count * S count + count * (512 + 64 * audit_lt_nested_input_width EV g r semis).

(** Nested LT computation runs obey their event and total-work bounds. *)
Definition audit_lt_nested_bound_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) semis
    (enc : V -> positive * list B) (source : E -> V * list B) (weight : B -> nat) result events,
    (forall v, fst (enc v) = encode EV v) -> (forall e, fst (source e) = Graph.source g e) ->
    audit_lt_nested_run enc source r semis result events ->
    length events <= audit_lt_nested_input_event_bound r /\
    audit_lt_nested_work weight events <= audit_lt_nested_input_budget EV g r semis +
      audit_lt_nested_body_work weight events.
(** A virtual LT run composes semidominator, LT and parent-erasure runs. *)
Definition audit_virtual_lt_run {V E B} (EV : encoding V) (g : Graph.t V E)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B)
    (result : Map.t V V)
    (semi_events : list (audit_semi_producer_nested_event (V + unit) (E + V)
      (audit_virtual_full_call V E B)))
    (lt_events : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B)))
    (erase_events : list (audit_erase_nested_event V B)) : Prop :=
  let '(vp, (search, _)) := audit_virtual_full_search_with_prepared EV g cb in
  exists semi_state virtual_parents,
    audit_semi_producer_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      vp search semi_state semi_events /\
    audit_lt_nested_run (audit_virtual_full_encode cb) (audit_virtual_full_source source)
      search (SemiState.result semi_state) virtual_parents lt_events /\
    audit_erase_virtual_nested (audit_virtual_base_encode cb) virtual_parents = (result,
      erase_events).

(** Virtual LT computation admits a run yielding the original immediate dominators. *)
Definition audit_virtual_lt_erasure_statement : Prop :=
  forall V E B (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (cb : audit_virtual_base_callbacks V E B) (source : E -> V * list B),
    audit_virtual_base_callbacks_erase EV g cb ->
    (forall edge, fst (source edge) = Graph.source g edge) ->
    exists result semi_events lt_events erase_events,
      audit_virtual_lt_run EV g cb source result semi_events lt_events erase_events /\ result =
        simple_lt_idom p.

Definition audit_virtual_lt_stage_work {V E B} (weight : B -> nat)
    (events : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B))) :
      nat :=
  audit_lt_nested_work
    (fun event => audit_virtual_full_internal_event_work event +
      audit_virtual_full_body_event_work weight event)
    events.

Definition audit_virtual_lt_external_work {V E B} (weight : B -> nat)
    (events : list (audit_lt_nested_event (V + unit) (E + V) (audit_virtual_full_call V E B))) :
      nat :=
  audit_lt_nested_body_work (audit_virtual_full_body_event_work weight) events.

Definition audit_virtual_lt_input_support {V E} (g : Graph.t V E) : list V :=
  let edges := flat_map (Graph.out g) (Graph.nodes g) in
  Graph.nodes g ++ Graph.entries g ++ map (Graph.source g) edges ++ map (Graph.target g) edges.

Definition audit_virtual_lt_input_width {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  fold_right Nat.max 0 (map (fun vertex => Pos.size_nat (encode EV vertex))
    (audit_virtual_lt_input_support g)).

Definition audit_virtual_lt_input_scale {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  4 + length (Graph.nodes g) + length (Graph.entries g) +
    length (flat_map (Graph.out g) (Graph.nodes g)) + audit_virtual_lt_input_width EV g.

Definition audit_virtual_lt_input_budget {V E} (EV : encoding V) (g : Graph.t V E) : nat :=
  (1024 * 1024)%nat * Nat.pow (audit_virtual_lt_input_scale EV g) 40.
