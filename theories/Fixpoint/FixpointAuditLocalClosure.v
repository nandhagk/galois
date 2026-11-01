(** * Counted local dependency-closure traversal

    This proposed model retains each tested set, contributor lookup and dependency callback.
    For example, a duplicate root is tested again but expanded only on its first visit.
    Builds on: FixpointLocal and counted collection models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointLocal.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist.
Import List.ListNotations.

Inductive fx_local_event (X C : Type) : Type :=
  | FxLocalUnknownMem (x : X) (input : FinSet.t X) (answer : bool)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxLocalUnknownAdd (x : X) (input output : FinSet.t X)
      (body : list (audit_set_event X (fx_encoder_entry X)))
  | FxLocalConstraintMem (c : C) (input : FinSet.t C) (answer : bool)
      (body : list (audit_set_event C (fx_encoder_entry C)))
  | FxLocalConstraintAdd (c : C) (input output : FinSet.t C)
      (body : list (audit_set_event C (fx_encoder_entry C)))
  | FxLocalContributors (x : X) (code : positive) (input : Map.t X (list C))
      (raw : option (list C)) (body : audit_trace (audit_trie_call (X * list C)))
  | FxLocalDeps (c : C) (result : list X)
  | FxLocalFoldUnknown (remaining : list X)
  | FxLocalFoldConstraint (remaining : list C)
  | FxLocalCase (site : nat).

Arguments FxLocalUnknownMem {X C} _ _ _ _.

Arguments FxLocalUnknownAdd {X C} _ _ _ _.

Arguments FxLocalConstraintMem {X C} _ _ _ _.

Arguments FxLocalConstraintAdd {X C} _ _ _ _.

Arguments FxLocalContributors {X C} _ _ _ _ _.

Arguments FxLocalDeps {X C} _ _.

Arguments FxLocalFoldUnknown {X C} _.

Arguments FxLocalFoldConstraint {X C} _.

Arguments FxLocalCase {X C} _.

Fixpoint fx_local_inl {X C} (xs : list X) (rest : list (X + C)) :
    list (X + C) * list (fx_local_event X C) :=
  match xs with
  | [] => (rest, [FxLocalFoldUnknown []])
  | x :: tail => let '(output, events) := fx_local_inl tail rest in
      (inl x :: output, FxLocalFoldUnknown (x :: tail) :: events ++ [FxLocalCase 6])
  end.

Fixpoint fx_local_inr {X C} (cs : list C) (rest : list (X + C)) :
    list (X + C) * list (fx_local_event X C) :=
  match cs with
  | [] => (rest, [FxLocalFoldConstraint []])
  | c :: tail => let '(output, events) := fx_local_inr tail rest in
      (inr c :: output, FxLocalFoldConstraint (c :: tail) :: events ++ [FxLocalCase 6])
  end.

Section Closure.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Definition fx_local_step (state : LocalClosure.state X C) :
    LocalClosure.outcome X C * list (fx_local_event X C) :=
  match LocalClosure.pending state with
  | [] => (LocalClosure.Done (LocalClosure.unknowns state) (LocalClosure.constraints state),
           [FxLocalCase 0])
  | inl x :: rest =>
      let seen := LocalClosure.unknowns state in
      let '(present, mem_events) := audit_finset_mem (fx_index_encoder EX) x seen in
      let prefix := [FxLocalCase 0; FxLocalUnknownMem x seen present mem_events;
                     FxLocalCase 1] in
      if present then
        (LocalClosure.Pending (LocalClosure.State seen (LocalClosure.constraints state) rest),
         prefix)
      else
        let '(next, add_events) := audit_finset_add (fx_index_encoder EX) x seen in
        let code := encode EX x in
        let '(raw, trie_events) := audit_map_code_get code (contributors ix) in
        let cs :=
          match raw with
          | Some found => found
          | None => []
          end in
        let '(todo, folds) := fx_local_inr cs rest in
        (LocalClosure.Pending (LocalClosure.State next (LocalClosure.constraints state) todo),
         prefix ++ [FxLocalUnknownAdd x seen next add_events;
                    FxLocalContributors x code (contributors ix) raw trie_events;
                    FxLocalCase 2] ++ folds)
  | inr c :: rest =>
      let seen := LocalClosure.constraints state in
      let '(present, mem_events) := audit_finset_mem (fx_index_encoder EC) c seen in
      let prefix := [FxLocalCase 0; FxLocalConstraintMem c seen present mem_events;
                     FxLocalCase 3] in
      if present then
        (LocalClosure.Pending (LocalClosure.State (LocalClosure.unknowns state) seen rest),
         prefix)
      else
        let '(next, add_events) := audit_finset_add (fx_index_encoder EC) c seen in
        let ds := deps SS c in
        let '(todo, folds) := fx_local_inl ds rest in
        (LocalClosure.Pending (LocalClosure.State (LocalClosure.unknowns state) next todo),
         prefix ++ [FxLocalConstraintAdd c seen next add_events; FxLocalDeps c ds] ++ folds)
  end.

Fixpoint fx_local_walk (fuel : positive) (state : LocalClosure.state X C) :
    LocalClosure.outcome X C * list (fx_local_event X C) :=
  match fuel with
  | xH => let '(out, events) := fx_local_step state in (out, FxLocalCase 4 :: events)
  | xO p =>
      let '(first, events) := fx_local_walk p state in
      match first with
      | LocalClosure.Done region selected =>
          (LocalClosure.Done region selected, FxLocalCase 4 :: events ++ [FxLocalCase 5])
      | LocalClosure.Pending next =>
          let '(out, later) := fx_local_walk p next in
          (out, FxLocalCase 4 :: events ++ FxLocalCase 5 :: later)
      end
  | xI p =>
      let '(first, events) := fx_local_walk p state in
      match first with
      | LocalClosure.Done region selected =>
          (LocalClosure.Done region selected, FxLocalCase 4 :: events ++ [FxLocalCase 5; FxLocalCase
            5])
      | LocalClosure.Pending next =>
          let '(second, later) := fx_local_walk p next in
          match second with
          | LocalClosure.Done region selected =>
              (LocalClosure.Done region selected, FxLocalCase 4 :: events ++
               FxLocalCase 5 :: later ++ [FxLocalCase 5])
          | LocalClosure.Pending last =>
              let '(out, final) := fx_local_step last in
              (out, FxLocalCase 4 :: events ++ FxLocalCase 5 :: later ++ FxLocalCase 5 :: final)
          end
      end
  end.

(** Discarding a counted closure step's event list yields the original closure step. *)
Definition fx_local_step_erasure_statement : Prop :=
  forall state, fst (fx_local_step state) = LocalClosure.step EX EC S SS ix state.

(** Discarding a counted closure walk's event list yields the original fuel-bounded walk. *)
Definition fx_local_walk_erasure_statement : Prop :=
  forall fuel state, fst (fx_local_walk fuel state) =
    LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel state.

End Closure.

(** Selected primitive source frames use the shared trie and set recurrences. Encoder
    callback entries are counted once; recursive callback-body adequacy is separate. *)

Definition fx_local_event_work {X C} (event : fx_local_event X C) : nat :=
  match event with
  | FxLocalUnknownMem _ _ _ body
  | FxLocalUnknownAdd _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) body
  | FxLocalConstraintMem _ _ _ body
  | FxLocalConstraintAdd _ _ _ body =>
      1 + audit_finset_source_work (@length (fx_encoder_entry C)) body
  | FxLocalContributors _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | _ => 1
  end.

Definition fx_local_event_budget {X C} (EX : encoding X) (EC : encoding C)
    (event : fx_local_event X C) : nat :=
  match event with
  | FxLocalUnknownMem x _ _ _
  | FxLocalUnknownAdd x _ _ _ =>
      12 + 17 * Pos.size_nat (encode EX x)
  | FxLocalConstraintMem c _ _ _
  | FxLocalConstraintAdd c _ _ _ =>
      12 + 17 * Pos.size_nat (encode EC c)
  | FxLocalContributors _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | _ => 1
  end.

Definition fx_local_work {X C} (events : list (fx_local_event X C)) : nat :=
  fold_right (fun event n => fx_local_event_work event + n) 0 events.

Definition fx_local_budget {X C} (EX : encoding X) (EC : encoding C)
    (events : list (fx_local_event X C)) : nat :=
  fold_right (fun event n => fx_local_event_budget EX EC event + n) 0 events.

(** The counted closure walk returns the original result and its recorded work fits the trace
    budget. *)
Definition fx_local_walk_selected_cost_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) fuel state,
    let '(out, events) := fx_local_walk EX EC S SS ix fuel state in
    out = LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel state /\
    fx_local_work events <= fx_local_budget EX EC events.

Definition fx_local_step_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (state : LocalClosure.state X C) : nat :=
  match LocalClosure.pending state with
  | [] => 1
  | inl x :: _ =>
      2 + (12 + 5 * Pos.size_nat (encode EX x)) +
      if FinSet.mem EX x (LocalClosure.unknowns state) then 0 else
        (12 + 17 * Pos.size_nat (encode EX x)) +
        (2 + 6 * Pos.size_nat (encode EX x)) + 1 +
        1 + 2 * length (contributors_of EX ix x)
  | inr c :: _ =>
      2 + (12 + 5 * Pos.size_nat (encode EC c)) +
      if FinSet.mem EC c (LocalClosure.constraints state) then 0 else
        (12 + 17 * Pos.size_nat (encode EC c)) + 1 + 1 + 2 * length (deps SS c)
  end.

Fixpoint fx_local_walk_input_budget {X C A} (EX : encoding X) (EC : encoding C)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (fuel : positive) (state : LocalClosure.state X C) : nat :=
  let step := LocalClosure.step EX EC S SS ix in
  match fuel with
  | xH => 1 + fx_local_step_input_budget EX EC S SS ix state
  | xO smaller =>
      2 + fx_local_walk_input_budget EX EC S SS ix smaller state +
      match LocalClosure.walk step smaller state with
      | LocalClosure.Done _ _ => 0
      | LocalClosure.Pending next => fx_local_walk_input_budget EX EC S SS ix smaller next
      end
  | xI smaller =>
      let first := LocalClosure.walk step smaller state in
      let second :=
        match first with
        | LocalClosure.Done a b => LocalClosure.Done a b
        | LocalClosure.Pending next => LocalClosure.walk step smaller next
        end in
      3 + fx_local_walk_input_budget EX EC S SS ix smaller state +
      (
        match first with
        | LocalClosure.Done _ _ => 0
        | LocalClosure.Pending next =>
          fx_local_walk_input_budget EX EC S SS ix smaller next
        end) +
      match second with
      | LocalClosure.Done _ _ => 0
      | LocalClosure.Pending next =>
        fx_local_step_input_budget EX EC S SS ix next
      end
  end.

(** The counted closure walk returns the original result and its work fits an input-derived
    budget. *)
Definition fx_local_walk_input_bound_statement : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) ix fuel state,
    let '(out, events) := fx_local_walk EX EC S SS ix fuel state in
    out = LocalClosure.walk (LocalClosure.step EX EC S SS ix) fuel state /\
    fx_local_work events <= fx_local_walk_input_budget EX EC S SS ix fuel state.
