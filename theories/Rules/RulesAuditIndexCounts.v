(** * Row-index call counts

    A fold derivation preserves the actual events of each individual source row.
    For example, a wrong-arity row has one add call and no map get or set.
    Builds on: RulesAuditIndex. *)

From Stdlib Require Import List Arith.
From Galois.Collections Require Import CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesAuditMaterializePrelude
  RulesAuditIndex.
Import List.ListNotations.

Definition mat_block_count (site : nat) (events : list mat_frame) : nat :=
  length (filter (fun event => match event with
    | MatBlock actual => Nat.eqb actual site
    | _ => false
    end) events).

Definition mat_import_count (site : nat) (events : list mat_frame) : nat :=
  length (filter (fun event => match event with
    | MatImported _ actual _ _ _ => Nat.eqb actual site
    | _ => false
    end) events).

Definition mat_index_success (bound : FinSet.t nat) (terms : list term) (row : tuple) : bool :=
  match tuple_key bound terms row with
  | Some _ => true
  | None => false
  end.

(** Chunks align with input rows; emitted events retain the actual tail-first fold order. *)
Inductive mat_index_fold_run (bound : FinSet.t nat) (terms : list term) :
    list tuple -> tuple_index -> list mat_frame -> list (list mat_frame) -> Prop :=
  | MatIndexFoldNil :
      mat_index_fold_run bound terms [] Map.empty [MatBlock 5; MatBlock 0] []
  | MatIndexFoldCons : forall row rows before out later here chunks,
      mat_index_fold_run bound terms rows before later chunks ->
      mat_index_add_full bound terms row before = (out, here) ->
      mat_index_fold_run bound terms (row :: rows) out (MatBlock 5 :: later ++ here)
        (here :: chunks).

(** Each row performs one key computation; successful keys perform one get, one set and two
  encodings. *)
Definition mat_index_row_counts_statement : Prop :=
  forall bound terms row before,
    let '(_, events) := mat_index_add_full bound terms row before in
    mat_import_count 10 events = (if mat_index_success bound terms row then 1 else 0) /\
    mat_import_count 11 events = (if mat_index_success bound terms row then 1 else 0) /\
    mat_import_count 100 events = (if mat_index_success bound terms row then 2 else 0).

(** The whole fold has m+1 entries and m actual row calls, including duplicates and failures. *)
Definition mat_index_fold_counts_statement : Prop :=
  forall bound terms rows,
    let '(out, events) := mat_build_index_full bound terms rows in
    exists chunks, mat_index_fold_run bound terms rows out events chunks /\
      length chunks = length rows /\ mat_block_count 5 events = S (length rows) /\
      mat_import_count 10 events = length (filter (mat_index_success bound terms) rows) /\
      mat_import_count 11 events = length (filter (mat_index_success bound terms) rows) /\
      mat_import_count 100 events = 2 * length (filter (mat_index_success bound terms) rows).

(** A row derivation retains exactly its one key computation and its selected map branch. *)
Inductive mat_index_add_run (bound : FinSet.t nat) (terms : list term) (row : tuple)
    (before : tuple_index) : tuple_index -> list mat_frame -> Prop :=
  | MatIndexAddNoKey : forall key_events,
      mat_tuple_key bound terms row = (None, key_events) ->
      mat_index_add_run bound terms row before before (key_events ++ [MatBlock 0])
  | MatIndexAddKey : forall key key_events raw get_events old out set_events,
      mat_tuple_key bound terms row = (Some key, key_events) ->
      mat_get_encoded mat_tuple_encoder key before = (raw, get_events) ->
      old = (match raw with
      | Some rows => rows
      | None => []
      end) ->
      mat_set_encoded mat_tuple_encoder key (row :: old) before = (out, set_events) ->
      mat_index_add_run bound terms row before out
        (key_events ++ get_events ++ [MatBlock 0] ++ set_events).

(** Every actual row subrun has the corresponding single-key derivation. *)
Definition mat_index_add_run_total_statement : Prop :=
  forall bound terms row before,
    let '(out, events) := mat_index_add_full bound terms row before in
    mat_index_add_run bound terms row before out events.
