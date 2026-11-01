(** * Counted materialization row snapshot

    The source maps every stored relation once before exposing its lookup closure.
    Nested relation traversals are retained inside their actual map callbacks.
    For example, each stored relation is enumerated once for a snapshot.
    Builds on: RulesDelta and the shared map and set-enumeration models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditElements CollectionsAuditMapTraverse.
Import List.ListNotations.

Definition rules_delta_rows_snapshot_counted {P} (db : database P) :
    Map.t P (list tuple) *
      list (audit_map_transform_event P (FinSet.t tuple) (list tuple) (audit_set_elements_event
  tuple)) :=
  audit_map_transform audit_finset_elements db.

Definition rules_delta_rows_lookup_counted {P} (prog : program P) (snapshot : Map.t P (list tuple))
    (p : P) : list tuple * (positive * option (list tuple) * audit_trace (audit_trie_call (P *
  list tuple))) :=
  let code := encode (penc prog) p in
  let '(raw, body) := audit_map_code_get code snapshot in
  (match raw with
  | Some rows => rows
  | None => []
  end, (code, raw, body)).

(** Erasing the counted lookup gives the original delta row lookup. *)
Definition rules_delta_rows_erasure_statement : Prop :=
  forall P (prog : program P) db p,
    let '(snapshot, _) := rules_delta_rows_snapshot_counted db in
    fst (rules_delta_rows_lookup_counted prog snapshot p) = delta_rows prog db p.

Definition rules_delta_rows_snapshot_work {P}
    (events : list (audit_map_transform_event P (FinSet.t tuple) (list tuple)
      (audit_set_elements_event tuple))) : nat :=
  audit_map_transform_source_work audit_set_elements_work events.

Definition rules_delta_rows_snapshot_budget {P} (db : database P)
    (events : list (audit_map_transform_event P (FinSet.t tuple) (list tuple)
      (audit_set_elements_event tuple))) : nat :=
  20 * audit_trie_nodes db + audit_map_transform_child_work audit_set_elements_work events.

(** The selected events account for snapshot work. *)
Definition rules_delta_rows_snapshot_cost_statement : Prop :=
  forall P (db : database P),
    let '(snapshot, events) := rules_delta_rows_snapshot_counted db in
    snapshot = Map.map FinSet.elements db /\
    rules_delta_rows_snapshot_work events <= rules_delta_rows_snapshot_budget db events.

(** Input-only budget accounts for every relation stored in the original database. *)
Definition rules_delta_rows_input_budget {P} (db : database P) : nat :=
  20 * audit_trie_nodes db +
  fold_right (fun pair n =>
    let relation := snd pair in
    6 + 19 * audit_trie_nodes relation + audit_trie_output_bits relation + n)
    0 (Map.elements db).

(** The snapshot input budget bounds its recorded work. *)
Definition rules_delta_rows_input_bound_statement : Prop :=
  forall P (db : database P),
    let '(snapshot, events) := rules_delta_rows_snapshot_counted db in
    snapshot = Map.map FinSet.elements db /\
    rules_delta_rows_snapshot_work events <= rules_delta_rows_input_budget db.
