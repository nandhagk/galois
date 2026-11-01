(** * Shared Rules materialization adapters

    The adapters retain actual predicate encoder calls and imported atom-fold subruns.
    For example, inserting a ground atom emits separate read and write encoder receipts.
    Builds on: RulesAuditMaterializePrelude, RulesAuditRelations and RulesAuditAtomFold. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta
  RulesAuditMaterializePrelude RulesAuditRelations RulesAuditAtomFold RulesAuditNestedProbe.
Import List.ListNotations.

Definition mat_ground_encoder {P} (prog : program P) :=
  audit_pair_encode (rules_encoder (penc prog)) (audit_list_encode audit_positive_encode).

Definition mat_ground_encoding_work {P}
    (events : list (audit_pair_event P tuple (rules_encode_entry P)
      (audit_list_event positive (audit_basic_encoding_event positive)))) :=
  audit_pair_events_work (@length (rules_encode_entry P))
    (audit_list_events_work audit_basic_encoding_work) events.

Definition mat_ground_calls {P} (prog : program P)
    (events : list (audit_set_event (ground_atom P) (audit_pair_event P tuple
      (rules_encode_entry P) (audit_list_event positive (audit_basic_encoding_event positive))))) :
    list mat_frame :=
  flat_map (fun event => match event with
    | AuditSetAdd _ _ _ _ encoded _ => flat_map (fun pair => match pair with
        | AuditPairFirst p code _ => [MatEncode P (penc prog) p code]
        | _ => []
        end) encoded
    | _ => []
    end) events.

Definition mat_ground_set {P} (prog : program P) (xs : list (ground_atom P)) :=
  let '(out, events) := audit_finset_of_list (mat_ground_encoder prog) xs in
  (out, MatImported _ 13 (out, events)
    (audit_finset_source_work (@mat_ground_encoding_work P) events)
    (1 + length xs + audit_trie_nodes out) :: mat_ground_calls prog events).

Definition mat_atom_calls {P} (prog : program P) (events : list (rules_atom_full_event P)) :
    list mat_frame :=
  flat_map (fun event => match event with
    | RafRelationGet p code _ _ _
    | RafRelationSet p _ code _ _ _ =>
        [MatEncode P (penc prog) p code]
    | _ => []
    end) events.

Definition mat_atom_fold {P} (prog : program P) atoms db :=
  let '(out, events) := rules_atom_fold_counted prog atoms db in
  (out, MatImported _ 17 (out, events) (rules_atom_full_work events) (mat_db_size out) ::
    mat_atom_calls prog events).

Definition mat_index {P} (prog : program P) set :=
  let '(out, events) := rules_delta_index_counted prog set in
  (out, MatImported _ 18 (out, events) (rules_atom_full_work events) (mat_db_size out) ::
    mat_atom_calls prog events).

Definition mat_instantiate (b : binding) (ts : list term) :=
  mat_lift 27 mat_tuple_size rules_nested_probe_work (rules_probe_instantiate b ts).

Definition mat_tagged_encoder {P} (prog : program P) (q : P * bool) :=
  let '(out, events) := audit_pair_encode (rules_encoder (penc prog)) audit_bool_encode q in
  (out, MatImported _ 28 (out, events)
    (audit_pair_events_work (@length (rules_encode_entry P)) audit_basic_encoding_work events)
    (Pos.size_nat out) ::
    flat_map (fun event => match event with
      | AuditPairFirst p code _ => [MatEncode P (penc prog) p code]
      | _ => []
      end) events).
