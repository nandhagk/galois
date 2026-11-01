(** * Full nested atom-fold library model

    This preserves all three encoder calls and each actual trie subrun of delta_add_atoms.
    For example, two identical atoms remain two separate fold iterations.
    Builds on: RulesDelta and shared models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditFinSet CollectionsAuditEncoding CollectionsAuditElements.
From Galois.Rules Require Import RulesAuditRelations.
Import List.ListNotations.

Inductive rules_atom_full_event (P : Type) : Type :=
  | RafRelationGet (predicate : P) (code : positive) (before : database P)
      (raw : option (FinSet.t tuple)) (body : audit_trace (audit_trie_call (P * FinSet.t tuple)))
  | RafTupleAdd (row : tuple) (before after : FinSet.t tuple)
      (body : list (audit_set_event tuple (audit_list_event positive (audit_basic_encoding_event
  positive))))
  | RafRelationSet (predicate : P) (value : FinSet.t tuple) (code : positive)
      (before after : database P) (body : audit_trace (audit_trie_call (P * FinSet.t tuple)))
  | RafElements (input : FinSet.t (ground_atom P)) (output : list (ground_atom P))
      (body : list (audit_set_elements_event (ground_atom P)))
  | RafCase (site : nat).
Arguments RafRelationGet {P} _ _ _ _ _.
Arguments RafTupleAdd {P} _ _ _ _.
Arguments RafRelationSet {P} _ _ _ _ _ _.
Arguments RafElements {P} _ _ _.
Arguments RafCase {P} _.

Fixpoint rules_atom_fold_counted {P} (prog : program P) (atoms : list (ground_atom P))
    (initial : database P) : database P * list (rules_atom_full_event P) :=
  match atoms with
  | [] => (initial, [RafCase 0])
  | (p, row) :: rest =>
      let '(before, tail) := rules_atom_fold_counted prog rest initial in
      let lookup_code := encode (penc prog) p in
      let '(raw, get_body) := audit_map_code_get lookup_code before in
      let relation := match raw with
      | Some r => r
      | None => FinSet.empty
      end in
      let '(next, add_body) := audit_finset_add (audit_list_encode audit_positive_encode) row
  relation in
      let write_code := encode (penc prog) p in
      let '(after, set_body) := audit_trie_set write_code (p, next) before in
      (after, RafCase 0 :: tail ++ [RafRelationGet p lookup_code before raw get_body; RafCase 1;
        RafTupleAdd row relation next add_body; RafRelationSet p next write_code before after
  set_body])
  end.

Definition rules_delta_index_counted {P} (prog : program P) (input : FinSet.t (ground_atom P)) :
    database P * list (rules_atom_full_event P) :=
  let '(atoms, element_body) := audit_finset_elements input in
  let '(out, events) := rules_atom_fold_counted prog atoms Map.empty in
  (out, RafElements input atoms element_body :: events).

(** Erasing the counted atom fold gives the original delta insertion. *)
Definition rules_atom_fold_erasure_statement : Prop :=
  (forall P (prog : program P) atoms initial,
    fst (rules_atom_fold_counted prog atoms initial) = delta_add_atoms prog atoms initial) /\
  (forall P (prog : program P) input,
    fst (rules_delta_index_counted prog input) = delta_index prog input).

Definition rules_atom_full_event_work {P} (event : rules_atom_full_event P) : nat :=
  match event with
  | RafRelationGet _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_get_trace_source_work body
  | RafTupleAdd _ _ _ body =>
      audit_finset_source_work (audit_list_events_work audit_basic_encoding_work) body
  | RafRelationSet _ _ code _ _ body =>
      1 + audit_encoding_weight (Pos.size_nat code) + audit_trie_update_trace_source_work body
  | RafElements _ _ body => audit_set_elements_work body
  | RafCase _ => 1
  end.

Definition rules_atom_full_event_budget {P} (event : rules_atom_full_event P) : nat :=
  match event with
  | RafRelationGet _ code _ _ _ => 2 + 6 * Pos.size_nat code
  | RafTupleAdd row _ _ _ =>
      10 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
        16 * Pos.size_nat (encode tuple_encoding row)
  | RafRelationSet _ _ code _ _ _ => 2 + 17 * Pos.size_nat code
  | RafElements input _ _ => 6 + 19 * audit_trie_nodes input + audit_trie_output_bits input
  | RafCase _ => 1
  end.

Definition rules_atom_full_work {P} (events : list (rules_atom_full_event P)) : nat :=
  fold_right (fun event n => rules_atom_full_event_work event + n) 0 events.

Definition rules_atom_full_budget {P} (events : list (rules_atom_full_event P)) : nat :=
  fold_right (fun event n => rules_atom_full_event_budget event + n) 0 events.

(** The selected event costs bound the counted atom fold work. *)
Definition rules_atom_fold_selected_cost_statement : Prop :=
  forall P (prog : program P) atoms initial,
    let '(result, events) := rules_atom_fold_counted prog atoms initial in
    result = delta_add_atoms prog atoms initial /\
    rules_atom_full_work events <= rules_atom_full_budget events.

(** This selected bound depends only on the original atom list and encoded operands. It
    excludes execution of the mathematical observer and external predicate encoder bodies. *)
Fixpoint rules_atom_fold_input_budget {P} (prog : program P) (atoms : list (ground_atom P)) : nat :=
  match atoms with
  | [] => 1
  | (p, row) :: rest =>
      1 + rules_atom_fold_input_budget prog rest +
      (2 + 6 * Pos.size_nat (encode (penc prog) p)) + 1 +
      (10 + 10 * length row + 20 * audit_encoded_bits audit_positive_encode row +
       16 * Pos.size_nat (encode tuple_encoding row)) +
      (2 + 17 * Pos.size_nat (encode (penc prog) p))
  end.

(** The input budget bounds the counted atom fold work. *)
Definition rules_atom_fold_input_bound_statement : Prop :=
  forall P (prog : program P) atoms initial,
    let '(result, events) := rules_atom_fold_counted prog atoms initial in
    result = delta_add_atoms prog atoms initial /\
    rules_atom_full_work events <= rules_atom_fold_input_budget prog atoms.

Definition rules_delta_index_input_budget {P} (prog : program P) (input : FinSet.t (ground_atom
  P)) : nat :=
  6 + 19 * audit_trie_nodes input + audit_trie_output_bits input +
    rules_atom_fold_input_budget prog (FinSet.elements input).

(** The input budget bounds the counted delta index work. *)
Definition rules_delta_index_input_bound_statement : Prop :=
  forall P (prog : program P) input,
    let '(result, events) := rules_delta_index_counted prog input in
    result = delta_index prog input /\
    rules_atom_full_work events <= rules_delta_index_input_budget prog input.

(** Source-shaped fold derivation. Each cons contains the same recursively produced
    database, actual get, actual tuple-encoder/add subrun and actual database write. *)
Inductive rules_atom_fold_run {P} (prog : program P) :
    list (ground_atom P) -> database P -> database P -> list (rules_atom_full_event P) -> Prop :=
  | RulesAtomFoldNil : forall initial,
      rules_atom_fold_run prog [] initial initial [RafCase 0]
  | RulesAtomFoldCons : forall p row rest initial before tail raw get_body relation next add_body
      after set_body,
      rules_atom_fold_run prog rest initial before tail ->
      audit_map_code_get (encode (penc prog) p) before = (raw, get_body) ->
      relation = (match raw with
      | Some value => value
      | None => FinSet.empty
      end) ->
      audit_finset_add (audit_list_encode audit_positive_encode) row relation = (next, add_body) ->
      audit_trie_set (encode (penc prog) p) (p, next) before = (after, set_body) ->
      rules_atom_fold_run prog ((p, row) :: rest) initial after
        (RafCase 0 :: tail ++ [RafRelationGet p (encode (penc prog) p) before raw get_body;
          RafCase 1; RafTupleAdd row relation next add_body;
          RafRelationSet p next (encode (penc prog) p) before after set_body]).

(** Every atom fold has a corresponding recorded run. *)
Definition rules_atom_fold_run_total_statement : Prop :=
  forall P (prog : program P) atoms initial,
    let '(result, events) := rules_atom_fold_counted prog atoms initial in
    rules_atom_fold_run prog atoms initial result events.

(** An atom fold input determines its recorded run uniquely. *)
Definition rules_atom_fold_run_unique_statement : Prop :=
  forall P (prog : program P) atoms initial result events,
    rules_atom_fold_run prog atoms initial result events ->
    rules_atom_fold_counted prog atoms initial = (result, events).

(** A recorded atom fold run erases to the original fold. *)
Definition rules_atom_fold_run_erasure_statement : Prop :=
  forall P (prog : program P) atoms initial result events,
    rules_atom_fold_run prog atoms initial result events ->
    result = delta_add_atoms prog atoms initial /\
    rules_atom_full_work events <= rules_atom_fold_input_budget prog atoms.
