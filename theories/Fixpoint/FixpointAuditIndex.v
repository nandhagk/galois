(** * Indexed preparation with same-call callback bodies

    Each target, side, dependency and encoder model executes at its actual source site.
    The same intermediate sets, enumerations and maps feed the final index.
    For example, index preparation records a target callback together with its result.
    Builds on: FixpointIndex and the frozen collection source models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditElements.
Import List.ListNotations.

Record fx_index_external_model (X C B : Type) : Type := FxIndexExternalModel {
  fxi_encode : X -> positive * list B;
  fxi_target : C -> X * list B;
  fxi_sides : C -> list X * list B;
  fxi_deps : C -> list X * list B
}.

Arguments fxi_encode {X C B} _ _.

Arguments fxi_target {X C B} _ _.

Arguments fxi_sides {X C B} _ _.

Arguments fxi_deps {X C B} _ _.

(** The modeled encoder, target, side and dependency callbacks return the original system values. *)
Definition fx_index_external_erases {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (cb : fx_index_external_model X C B) : Prop :=
  (forall x, fst (fxi_encode cb x) = encode EX x) /\
  (forall c, fst (fxi_target cb c) = System.target S c) /\
  (forall c, fst (fxi_sides cb c) = side_targets SS c) /\
  (forall c, fst (fxi_deps cb c) = deps SS c).

Inductive fx_index_nested_event (X C B : Type) : Type :=
  | FxiTarget (c : C) (out : X) (body : list B)
  | FxiSides (c : C) (out : list X) (body : list B)
  | FxiDeps (c : C) (out : list X) (body : list B)
  | FxiDistinctBuild (input : list X) (set : FinSet.t X) (body : list (audit_set_event X B))
  | FxiDistinctElements (set : FinSet.t X) (output : list X) (body : list (audit_set_elements_event
    X))
  | FxiRead (x : X) (code : positive) (input : Map.t X (list C)) (raw : option (list C))
      (encode_body : list B) (trie_body : audit_trace (audit_trie_call (X * list C)))
  | FxiWrite (x : X) (code : positive) (value : list C) (before after : Map.t X (list C))
      (encode_body : list B) (trie_body : audit_trace (audit_trie_call (X * list C)))
  | FxiCase (site : nat).

Arguments FxiTarget {X C B} _ _ _.

Arguments FxiSides {X C B} _ _ _.

Arguments FxiDeps {X C B} _ _ _.

Arguments FxiDistinctBuild {X C B} _ _ _.

Arguments FxiDistinctElements {X C B} _ _ _.

Arguments FxiRead {X C B} _ _ _ _ _ _.

Arguments FxiWrite {X C B} _ _ _ _ _ _ _.

Arguments FxiCase {X C B} _.

Definition fxi_distinct_counted {X C B} (cb : fx_index_external_model X C B) (input : list X) :
    list X * list (fx_index_nested_event X C B) :=
  let '(set, build) := audit_finset_of_list (fxi_encode cb) input in
  let '(output, elements) := audit_finset_elements set in
  (output, [FxiDistinctBuild input set build; FxiDistinctElements set output elements]).

Fixpoint fxi_push_many {X C B} (cb : fx_index_external_model X C B) (c : C)
    (xs : list X) (m : Map.t X (list C)) : Map.t X (list C) * list (fx_index_nested_event X C B) :=
  match xs with
  | [] => (m, [FxiCase 0])
  | x :: rest =>
      let '(before, tail) := fxi_push_many cb c rest m in
      let '(read_code, read_body) := fxi_encode cb x in
      let '(raw, get_body) := audit_map_code_get read_code before in
      let prior :=
        match raw with
        | Some values => values
        | None => []
        end in
      let value := c :: prior in
      let '(write_code, write_body) := fxi_encode cb x in
      let '(after, set_body) := audit_trie_set write_code (x, value) before in
      (after, FxiCase 0 :: tail ++ [FxiRead x read_code before raw read_body get_body;
        FxiCase 1; FxiWrite x write_code value before after write_body set_body])
  end.

Fixpoint fxi_fold {X C B} (cb : fx_index_external_model X C B) (cs : list C) :
    sys_index X C * list (fx_index_nested_event X C B) :=
  match cs with
  | [] => (SysIndex Map.empty Map.empty, [FxiCase 2])
  | c :: rest =>
      let '(ix, tail) := fxi_fold cb rest in
      let '(target, target_body) := fxi_target cb c in
      let '(sides, sides_body) := fxi_sides cb c in
      let '(outputs, output_events) := fxi_distinct_counted cb (target :: sides) in
      let '(contributors_map, contributor_events) := fxi_push_many cb c outputs (contributors ix) in
      let '(deps, deps_body) := fxi_deps cb c in
      let '(reads, read_events) := fxi_distinct_counted cb deps in
      let '(readers_map, reader_events) := fxi_push_many cb c reads (readers ix) in
      (SysIndex contributors_map readers_map, FxiCase 2 :: tail ++
        [FxiTarget c target target_body; FxiSides c sides sides_body] ++ output_events ++
        contributor_events ++ FxiDeps c deps deps_body :: read_events ++ reader_events)
  end.

Definition fx_index_nested_counted {X C A B} (S : System.t X C A)
    (cb : fx_index_external_model X C B) := fxi_fold cb (System.constraints S).

(** If callbacks erase correctly, counted index construction returns the original prepared index. *)
Definition fx_index_nested_erasure_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B), fx_index_external_erases EX S SS cb ->
    fst (fx_index_nested_counted S cb) = index_system EX S SS.

(** Budgets concern each external callback body separately; no whole-index bound is assumed. *)

Record fx_index_external_budget (X C B : Type) : Type := FxIndexExternalBudget {
  fxi_body_weight : B -> nat;
  fxi_encode_bound : X -> nat;
  fxi_target_bound : C -> nat;
  fxi_sides_bound : C -> nat;
  fxi_deps_bound : C -> nat
}.

Arguments fxi_body_weight {X C B} _ _.

Arguments fxi_encode_bound {X C B} _ _.

Arguments fxi_target_bound {X C B} _ _.

Arguments fxi_sides_bound {X C B} _ _.

Arguments fxi_deps_bound {X C B} _ _.

Definition fxi_body_work {X C B} (budget : fx_index_external_budget X C B) (body : list B) : nat :=
  fold_right (fun event n => fxi_body_weight budget event + n) 0 body.

(** Each index callback body fits its input bound and each body event has positive weight. *)
Definition fx_index_external_bounded {X C B} (cb : fx_index_external_model X C B)
    (budget : fx_index_external_budget X C B) : Prop :=
  (forall b, 1 <= fxi_body_weight budget b) /\
  (forall x, fxi_body_work budget (snd (fxi_encode cb x)) <= fxi_encode_bound budget x) /\
  (forall c, fxi_body_work budget (snd (fxi_target cb c)) <= fxi_target_bound budget c) /\
  (forall c, fxi_body_work budget (snd (fxi_sides cb c)) <= fxi_sides_bound budget c) /\
  (forall c, fxi_body_work budget (snd (fxi_deps cb c)) <= fxi_deps_bound budget c).

Definition fxi_event_work {X C B} (budget : fx_index_external_budget X C B)
    (event : fx_index_nested_event X C B) : nat :=
  match event with
  | FxiTarget _ _ body
  | FxiSides _ _ body
  | FxiDeps _ _ body => 3 + fxi_body_work budget body
  | FxiDistinctBuild _ _ body => 3 + audit_finset_source_work (fxi_body_work budget) body
  | FxiDistinctElements _ _ body => 3 + audit_set_elements_work body
  | FxiRead _ _ _ _ enc trie => 8 + fxi_body_work budget enc + audit_trie_get_trace_source_work trie
  | FxiWrite _ _ _ _ _ enc trie => 8 + fxi_body_work budget enc +
    audit_trie_update_trace_source_work trie
  | FxiCase _ => 3
  end.

Definition fx_index_adapter_work {X C B} (budget : fx_index_external_budget X C B)
    (events : list (fx_index_nested_event X C B)) : nat :=
  fold_right (fun event n => fxi_event_work budget event + n) 0 events.

Fixpoint fxi_set_input_budget {X C B} (EX : encoding X) (budget : fx_index_external_budget X C B)
    (input : list X) : nat :=
  match input with
  | [] => 1
  | x :: rest => 3 + fxi_encode_bound budget x + 16 * Pos.size_nat (encode EX x) +
      fxi_set_input_budget EX budget rest
  end.

Definition fxi_distinct_input_budget {X C B} (EX : encoding X)
    (budget : fx_index_external_budget X C B) (input : list X) : nat :=
  let set := FinSet.of_list EX input in
  12 + fxi_set_input_budget EX budget input + 19 * audit_trie_nodes set + audit_trie_output_bits
    set.

Fixpoint fxi_push_input_budget {X C B} (EX : encoding X) (budget : fx_index_external_budget X C B)
    (keys : list X) : nat :=
  match keys with
  | [] => 3
  | x :: rest => 22 + 2 * fxi_encode_bound budget x + 21 * Pos.size_nat (encode EX x) +
      fxi_push_input_budget EX budget rest
  end.

Fixpoint fxi_constraints_input_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (budget : fx_index_external_budget X C B) (cs : list C) : nat :=
  match cs with
  | [] => 3
  | c :: rest =>
      let outputs := System.target S c :: side_targets SS c in
      let reads := deps SS c in
      12 + fxi_target_bound budget c + fxi_sides_bound budget c + fxi_deps_bound budget c +
      fxi_distinct_input_budget EX budget outputs + fxi_push_input_budget EX budget
        (distinct_unknowns EX outputs) +
      fxi_distinct_input_budget EX budget reads + fxi_push_input_budget EX budget (distinct_unknowns
        EX reads) +
      fxi_constraints_input_budget EX S SS budget rest
  end.

Definition fx_index_nested_input_budget {X C A B} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (budget : fx_index_external_budget X C B) : nat :=
  fxi_constraints_input_budget EX S SS budget (System.constraints S).

(** With index callback erasure and bounds, counted index construction returns the original index
    within its input budget. *)
Definition fx_index_nested_input_bound_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (budget : fx_index_external_budget X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb budget ->
    let '(result, events) := fx_index_nested_counted S cb in
    result = index_system EX S SS /\
    fx_index_adapter_work budget events <= fx_index_nested_input_budget EX S SS budget.

(** Only individual external callback source relations are supplied by a concrete client.
    Internal set, enumeration and trie bodies are the shared fixed collection models. *)

Record fx_index_external_source (X C B : Type) : Type := FxIndexExternalSource {
  fxi_encode_source : X -> positive -> list B -> Prop;
  fxi_target_source : C -> X -> list B -> Prop;
  fxi_sides_source : C -> list X -> list B -> Prop;
  fxi_deps_source : C -> list X -> list B -> Prop
}.

Arguments fxi_encode_source {X C B} _ _ _ _.

Arguments fxi_target_source {X C B} _ _ _ _.

Arguments fxi_sides_source {X C B} _ _ _ _.

Arguments fxi_deps_source {X C B} _ _ _ _.

(** Set addition, membership and removal bodies satisfy the encoder source relation for each key
    and code; fold events impose no condition. *)
Definition fxi_set_external_adequacy {X C B} (source : fx_index_external_source X C B)
    (events : list (audit_set_event X B)) : Prop :=
  Forall (fun e =>
    match e with
    | AuditSetAdd x code _ _ body _
    | AuditSetMem x code _ _ body _
    | AuditSetRemove x code _ _ body _ => fxi_encode_source source x code body
    | AuditSetFold _ _ => True
    end) events.

(** Target, side, dependency, set-build and map events satisfy their respective source relations;
    other index events impose no condition. *)
Definition fx_index_external_trace_adequacy {X C B} (source : fx_index_external_source X C B)
    (events : list (fx_index_nested_event X C B)) : Prop :=
  Forall (fun e =>
    match e with
    | FxiTarget c out body => fxi_target_source source c out body
    | FxiSides c out body => fxi_sides_source source c out body
    | FxiDeps c out body => fxi_deps_source source c out body
    | FxiDistinctBuild _ _ body => fxi_set_external_adequacy source body
    | FxiRead x code _ _ body _
    | FxiWrite x code _ _ _ body _ => fxi_encode_source source x code
      body
    | _ => True
    end) events.

(** Given index callback erasure and bounds and adequate receipts for the counted trace, index
    construction returns the original index within its input budget. *)
Definition fx_index_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (cb : fx_index_external_model X C B) (budget : fx_index_external_budget X C B)
    (source : fx_index_external_source X C B),
    fx_index_external_erases EX S SS cb -> fx_index_external_bounded cb budget ->
    let '(result, events) := fx_index_nested_counted S cb in
    fx_index_external_trace_adequacy source events ->
    result = index_system EX S SS /\
    fx_index_adapter_work budget events <= fx_index_nested_input_budget EX S SS budget.
