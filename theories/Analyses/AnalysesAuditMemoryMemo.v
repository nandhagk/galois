(** * Source-shaped memoized memory walk

    These rules retain actual probes, cut branches, child runs, unions and persistent writes.
    For example, a completed hit returns its saved roots without expanding successors.
    Builds on: G4 memory semantics and shared collection observers. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_memo_event (N E CV CK NE : Type) : Type :=
  | AuditMemoActive (v : memory_version N E) (result : bool)
      (calls : list (audit_set_event (memory_version N E) CV))
  | AuditMemoLookup (v : memory_version N E) (result : option (memo_entry N E))
      (calls : list (audit_map_event (positive * memory_version N E) (memo_entry N E) CK))
  | AuditMemoExpand (v : memory_version N E) (successors : list (memory_version N E))
      (calls : list NE)
  | AuditMemoAddActive (v : memory_version N E)
      (calls : list (audit_set_event (memory_version N E) CV))
  | AuditMemoStore (v : memory_version N E) (roots : list (memory_version N E))
      (calls : list (audit_map_event (positive * memory_version N E) (memo_entry N E) CK))
  | AuditMemoUnion (left right output : list (memory_version N E))
      (build : list (audit_set_event (memory_version N E) CV))
      (enumerate : list (audit_set_elements_event (memory_version N E))).

Arguments AuditMemoActive {N E CV CK NE} _ _ _.
Arguments AuditMemoLookup {N E CV CK NE} _ _ _.
Arguments AuditMemoExpand {N E CV CK NE} _ _ _.
Arguments AuditMemoAddActive {N E CV CK NE} _ _.
Arguments AuditMemoStore {N E CV CK NE} _ _ _.
Arguments AuditMemoUnion {N E CV CK NE} _ _ _ _ _.

(** The union executes the actual set construction and enumeration on the same intermediate set. *)
Definition audit_memo_union {N E CV} (enc : memory_version N E -> positive * list CV)
    (left right : list (memory_version N E))
    : list (memory_version N E) *
      (list (audit_set_event (memory_version N E) CV) *
       list (audit_set_elements_event (memory_version N E))) :=
  let '(set, build) := audit_finset_of_list enc (left ++ right) in
  let '(out, enumerate) := audit_finset_elements set in
  (out, (build, enumerate)).

(** Count every actual outgoing occurrence, including duplicate successors. *)
Fixpoint audit_memo_successor_occurrences {N E CV CK NE}
    (events : list (audit_memo_event N E CV CK NE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoExpand _ successors _ :: rest =>
      length successors + audit_memo_successor_occurrences rest
  | _ :: rest => audit_memo_successor_occurrences rest
  end.

(** Nested costs use the very captured maps, sets, encoder traces and successor traces. *)
Fixpoint audit_memo_primitive_work {N E CV CK NE} (version_work : list CV -> nat)
    (key_work : list CK -> nat) (next_work : list NE -> nat)
    (events : list (audit_memo_event N E CV CK NE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoActive _ _ calls :: rest => audit_finset_source_work version_work calls +
      audit_memo_primitive_work version_work key_work next_work rest
  | AuditMemoLookup _ _ calls :: rest => audit_map_source_work key_work calls +
      audit_memo_primitive_work version_work key_work next_work rest
  | AuditMemoExpand _ _ calls :: rest => next_work calls +
      audit_memo_primitive_work version_work key_work next_work rest
  | AuditMemoAddActive _ calls :: rest => audit_finset_source_work version_work calls +
      audit_memo_primitive_work version_work key_work next_work rest
  | AuditMemoStore _ _ calls :: rest => audit_map_source_work key_work calls +
      audit_memo_primitive_work version_work key_work next_work rest
  | AuditMemoUnion lroots _ _ build enumeration :: rest =>
      length lroots + audit_finset_source_work version_work build +
      audit_set_elements_work enumeration + audit_memo_primitive_work version_work key_work
        next_work rest
  end.

(** The model charges a fixed positive control cost per branch and the captured body costs. *)
Definition audit_memo_source_work {N E CV CK NE} (version_work : list CV -> nat)
    (key_work : list CK -> nat) (next_work : list NE -> nat)
    (events : list (audit_memo_event N E CV CK NE)) : nat :=
  2 * length events + audit_memo_primitive_work version_work key_work next_work events.

Section MemoRules.
  Context {N E CV CK NE : Type}.
  Let V := memory_version N E.
  Let M := Map.t (positive * V) (memo_entry N E).
  Variable version_enc : V -> positive * list CV.
  Variable key_enc : (positive * V) -> positive * list CK.
  Variable scope : positive.
  Variable next : V -> list V * list NE.

  (** Each clause fixes branch priority, actual map/set calls and their returned traces. *)
  Inductive audit_memo_tree : FinSet.t V -> M -> V -> BinNums.N -> memory_clobber_result N E ->
      M -> BinNums.N -> list (audit_memo_event N E CV CK NE) -> Prop :=
    | AuditMemoTreeActive : forall active memo v fuel ae,
        audit_finset_mem version_enc v active = (true, ae) ->
        audit_memo_tree active memo v fuel (MemoryClobberResult [v] false) memo fuel
          [AuditMemoActive v true ae]
    | AuditMemoTreeDone : forall active memo v fuel ae le roots,
        audit_finset_mem version_enc v active = (false, ae) ->
        audit_map_get key_enc (scope, v) memo = (Some (MemoDone roots), le) ->
        audit_memo_tree active memo v fuel (MemoryClobberResult roots true) memo fuel
          [AuditMemoActive v false ae; AuditMemoLookup v (Some (MemoDone roots)) le]
    | AuditMemoTreeBusy : forall active memo v fuel ae le,
        audit_finset_mem version_enc v active = (false, ae) ->
        audit_map_get key_enc (scope, v) memo = (Some MemoBusy, le) ->
        audit_memo_tree active memo v fuel (MemoryClobberResult [v] false) memo fuel
          [AuditMemoActive v false ae; AuditMemoLookup v (Some MemoBusy) le]
    | AuditMemoTreeFuel : forall active memo v ae le,
        audit_finset_mem version_enc v active = (false, ae) ->
        audit_map_get key_enc (scope, v) memo = (None, le) ->
        audit_memo_tree active memo v 0%N (MemoryClobberResult [v] false) memo 0%N
          [AuditMemoActive v false ae; AuditMemoLookup v None le]
    | AuditMemoTreeTerminal : forall active memo v fuel ae le ne final se,
        audit_finset_mem version_enc v active = (false, ae) ->
        audit_map_get key_enc (scope, v) memo = (None, le) -> next v = ([], ne) ->
        audit_map_set key_enc (scope, v) (MemoDone [v]) memo = (final, se) ->
        audit_memo_tree active memo v (N.succ fuel) (MemoryClobberResult [v] true) final fuel
          [AuditMemoActive v false ae; AuditMemoLookup v None le; AuditMemoExpand v [] ne;
           AuditMemoStore v [v] se]
    | AuditMemoTreeBranchComplete :
        forall active memo v fuel ae le ne first rest active' add_events result memo' remaining
          children_events final se,
        audit_finset_mem version_enc v active = (false, ae) ->
        audit_map_get key_enc (scope, v) memo = (None, le) -> next v = (first :: rest, ne) ->
        audit_finset_add version_enc v active = (active', add_events) ->
        audit_memo_children active' memo (first :: rest) fuel result memo' remaining
          children_events ->
        clobber_complete result = true ->
        audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) memo' = (final, se) ->
        audit_memo_tree active memo v (N.succ fuel) result final remaining
          ([AuditMemoActive v false ae; AuditMemoLookup v None le;
            AuditMemoExpand v (first :: rest) ne; AuditMemoAddActive v add_events] ++
            children_events ++ [AuditMemoStore v (clobber_roots result) se])
    | AuditMemoTreeBranchIncomplete :
        forall active memo v fuel ae le ne first rest active' add_events result final remaining
          children_events,
        audit_finset_mem version_enc v active = (false, ae) ->
        audit_map_get key_enc (scope, v) memo = (None, le) -> next v = (first :: rest, ne) ->
        audit_finset_add version_enc v active = (active', add_events) ->
        audit_memo_children active' memo (first :: rest) fuel result final remaining
          children_events ->
        clobber_complete result = false ->
        audit_memo_tree active memo v (N.succ fuel) result final remaining
          ([AuditMemoActive v false ae; AuditMemoLookup v None le;
            AuditMemoExpand v (first :: rest) ne; AuditMemoAddActive v add_events] ++
              children_events)
  (** Children thread cache and fuel in order and union their roots with the recorded events. *)
  with audit_memo_children : FinSet.t V -> M -> list V -> BinNums.N -> memory_clobber_result N E ->
      M -> BinNums.N -> list (audit_memo_event N E CV CK NE) -> Prop :=
    | AuditMemoChildrenNil : forall active memo fuel,
        audit_memo_children active memo [] fuel (MemoryClobberResult [] true) memo fuel []
    | AuditMemoChildrenCons : forall active memo v vs fuel one memo' fuel' first rest memo'' fuel''
        tail roots build enumeration,
        audit_memo_tree active memo v fuel one memo' fuel' first ->
        audit_memo_children active memo' vs fuel' rest memo'' fuel'' tail ->
        audit_memo_union version_enc (clobber_roots one) (clobber_roots rest) =
          (roots, (build, enumeration)) ->
        audit_memo_children active memo (v :: vs) fuel
          (MemoryClobberResult roots (andb (clobber_complete one) (clobber_complete rest)))
          memo'' fuel'' (first ++ tail ++
            [AuditMemoUnion (clobber_roots one) (clobber_roots rest) roots build enumeration]).

  (** Every input memo, active set, version and fuel has a finite tree derivation. *)
  Definition audit_memo_tree_total_at : Prop :=
    forall active memo v fuel, exists result final remaining events,
      audit_memo_tree active memo v fuel result final remaining events.

  (** Two memo trees with the same initial state, version and fuel have equal results, final
    caches, remaining credit and events. *)
  Definition audit_memo_tree_deterministic_at : Prop :=
    forall active memo v fuel result1 final1 remaining1 events1 result2 final2 remaining2 events2,
      audit_memo_tree active memo v fuel result1 final1 remaining1 events1 ->
      audit_memo_tree active memo v fuel result2 final2 remaining2 events2 ->
      result1 = result2 /\ final1 = final2 /\ remaining1 = remaining2 /\ events1 = events2.

  (** For a memo-tree derivation, source work is bounded by fuel, successor occurrences and
    the captured primitive work. *)
  Definition audit_memo_tree_source_bound_at : Prop :=
    forall active memo v fuel result final remaining events version_work key_work next_work,
      audit_memo_tree active memo v fuel result final remaining events ->
      audit_memo_source_work version_work key_work next_work events <=
        8 + 8 * BinNat.N.to_nat fuel + 6 * audit_memo_successor_occurrences events +
        audit_memo_primitive_work version_work key_work next_work events.
End MemoRules.

(** Every initial memo, active set, version and fuel has a finite tree derivation. *)
Definition audit_memo_tree_total_statement : Prop :=
  forall N E CV CK NE version_enc key_enc scope next,
    @audit_memo_tree_total_at N E CV CK NE version_enc key_enc scope next.

(** A memo tree fixes its result, final cache, remaining fuel and events. *)
Definition audit_memo_tree_deterministic_statement : Prop :=
  forall N E CV CK NE version_enc key_enc scope next,
    @audit_memo_tree_deterministic_at N E CV CK NE version_enc key_enc scope next.

(** For a memo-tree derivation, source work is bounded by fuel, successor occurrences and
    captured primitive work. *)
Definition audit_memo_tree_source_bound_statement : Prop :=
  forall N E CV CK NE version_enc key_enc scope next,
    @audit_memo_tree_source_bound_at N E CV CK NE version_enc key_enc scope next.

(** * Public query connection *)

(** A memo query takes a state, scope, version and fuel and returns clobbers and a state. *)
Definition audit_memo_query_type : Type :=
  forall N E T (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E),
    memo_state EN g effects mg -> memory_scope T -> memory_version N E -> positive ->
    memory_clobber_result N E * memo_state EN g effects mg.

(** With matching encoders and successor callback, the query result and final entries have a
    memo-tree witness while prepared indexes remain unchanged. *)
Definition audit_memo_query_execution_contract (query : audit_memo_query_type) : Prop :=
  forall N E T CV CK NE (EN : encoding N) (EE : encoding E) (ET : encoding T)
      (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
      (state : memo_state EN g effects mg) q start fuel
      (version_enc : memory_version N E -> positive * list CV)
      (key_enc : (positive * memory_version N E) -> positive * list CK)
      (next : memory_version N E -> list (memory_version N E) * list NE),
    (forall v, fst (version_enc v) = encode (memory_version_encoding EN EE) v) ->
    (forall k, fst (key_enc k) = encode (memo_key EN EE) k) ->
    (forall v, fst (next v) =
      memory_walk_raw_next EE ET (@memo_effect_index N E T EN g effects mg state)
        (pred_edges (@memo_adjacency N E T EN g effects mg state)) mg q v) ->
    let '(result, final) := query N E T EN EE ET g effects mg state q start fuel in
    exists remaining events,
      audit_memo_tree version_enc key_enc (scope_code ET q) next FinSet.empty
        (@memo_entries N E T EN g effects mg state) start (BinNums.Npos fuel) result
        (@memo_entries N E T EN g effects mg final) remaining events /\
      @memo_adjacency N E T EN g effects mg final = @memo_adjacency N E T EN g effects mg state /\
      @memo_effect_index N E T EN g effects mg final =
        @memo_effect_index N E T EN g effects mg state.
