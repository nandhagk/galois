(** * Counted dense universe preparation

    This observer retains each distinctness probe, index insertion and numeric conversion.
    For example, a repeated key is probed twice but numbered only once.
    Builds on: CollectionsDenseSet and shared collection cost models. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet
  CollectionsAuditEncoding
  CollectionsAuditMap
  CollectionsAuditFinSet.
Import List.ListNotations.

(** * Original numeric conversion cases *)

Inductive audit_dense_numeric_event : Type :=
  | AuditDenseBinarySuccessor (input output : N) (events : list audit_n_encoding_event)
  | AuditDenseLengthConversion (input : nat) (output : N) (events : list audit_nat_encoding_event).

(** [N.succ] and [N.succ_pos] share the same positive carry computation. *)
Definition audit_dense_N_succ (input : N) : N * list audit_dense_numeric_event :=
  let '(p, events) := audit_N_encode input in
  (Npos p, [AuditDenseBinarySuccessor input (Npos p) events]).

(** [N.of_nat] inspects zero or invokes [Pos.of_succ_nat] on the predecessor. *)
Definition audit_dense_N_of_nat (input : nat) : N * list audit_dense_numeric_event :=
  match input with
  | 0 => (N0, [AuditDenseLengthConversion input N0 []])
  | S rest =>
      let '(p, events) := audit_nat_encode rest in
      (Npos p, [AuditDenseLengthConversion input (Npos p) events])
  end.

(** Discarding the dense N succ events recovers the corresponding original operation under its
  premises. *)
Definition audit_dense_N_succ_erases_statement : Prop :=
  forall input, fst (audit_dense_N_succ input) = N.succ input.

(** Discarding the dense N of nat events recovers the corresponding original operation under
  its premises. *)
Definition audit_dense_N_of_nat_erases_statement : Prop :=
  forall input, fst (audit_dense_N_of_nat input) = N.of_nat input.

(** * First-occurrence selection and position indexing *)

Inductive audit_dense_prepare_event (K CE : Type) : Type :=
  | AuditDenseUniqueCase (remaining : list K) (seen : FinSet.t K)
  | AuditDenseUniqueProbe (key : K) (found : bool) (calls : list (audit_set_event K CE))
  | AuditDenseUniqueAdd (key : K) (calls : list (audit_set_event K CE))
  | AuditDenseUniqueKeep (key : K)
  | AuditDenseNumberCase (remaining : list K) (index : N)
  | AuditDenseNumberNext (input output : N) (events : list audit_dense_numeric_event)
  | AuditDenseNumberStore (key : K) (index : N) (calls : list (audit_map_event K N CE))
  | AuditDenseLength (input : nat) (output : N) (events : list audit_dense_numeric_event).

Arguments AuditDenseUniqueCase {K CE} _ _.
Arguments AuditDenseUniqueProbe {K CE} _ _ _.
Arguments AuditDenseUniqueAdd {K CE} _ _.
Arguments AuditDenseUniqueKeep {K CE} _.
Arguments AuditDenseNumberCase {K CE} _ _.
Arguments AuditDenseNumberNext {K CE} _ _ _.
Arguments AuditDenseNumberStore {K CE} _ _ _.
Arguments AuditDenseLength {K CE} _ _ _.

(** Duplicates retain the original seen set and do not issue an insertion. *)
Fixpoint audit_dense_unique {K CE} (enc : K -> positive * list CE) (seen : FinSet.t K)
    (keys : list K) : list K * list (audit_dense_prepare_event K CE) :=
  match keys with
  | [] => ([], [AuditDenseUniqueCase keys seen])
  | key :: rest =>
      let '(found, probes) := audit_finset_mem enc key seen in
      if found then
        let '(unique, events) := audit_dense_unique enc seen rest in
        (unique, [AuditDenseUniqueCase keys seen; AuditDenseUniqueProbe key found probes] ++ events)
      else
        let '(next, adds) := audit_finset_add enc key seen in
        let '(unique, events) := audit_dense_unique enc next rest in
        (key :: unique, [AuditDenseUniqueCase keys seen; AuditDenseUniqueProbe key found probes;
                         AuditDenseUniqueAdd key adds; AuditDenseUniqueKeep key] ++ events)
  end.

(** Numbering calls [N.succ] before the recursive tail and writes the map on return. *)
Fixpoint audit_dense_number {K CE} (enc : K -> positive * list CE) (keys : list K) (index : N)
    : Map.t K N * list (audit_dense_prepare_event K CE) :=
  match keys with
  | [] => (Map.empty, [AuditDenseNumberCase keys index])
  | key :: rest =>
      let '(next, ne) := audit_dense_N_succ index in
      let '(tail, te) := audit_dense_number enc rest next in
      let '(out, se) := audit_map_set enc key index tail in
      (out, [AuditDenseNumberCase keys index; AuditDenseNumberNext index next ne] ++ te ++
        [AuditDenseNumberStore key index se])
  end.

Definition audit_dense_prepare {K CE} (enc : K -> positive * list CE) (keys : list K)
    : dense_universe K * list (audit_dense_prepare_event K CE) :=
  let '(unique, ue) := audit_dense_unique enc FinSet.empty keys in
  let '(index, ie) := audit_dense_number enc unique 0%N in
  let '(length, le) := audit_dense_N_of_nat (List.length unique) in
  (DenseUniverse K unique index length, ue ++ ie ++ [AuditDenseLength (List.length unique)
    length le]).

(** * Future exact source-result obligations *)

Definition audit_dense_unique_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) seen keys,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (audit_dense_unique enc seen keys) = dense_unique original seen keys.

(** Discarding the dense number events recovers the corresponding original operation under its
  premises. *)
Definition audit_dense_number_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) keys index,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (audit_dense_number enc keys index) = dense_number original keys index.

(** Discarding the dense prepare events recovers the corresponding original operation under its
  premises. *)
Definition audit_dense_prepare_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) keys,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (audit_dense_prepare enc keys) = dense_prepare original keys.

(** * Fixed source charges and original-input preparation budget *)

Fixpoint audit_dense_prepare_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_dense_prepare_event K CE)) : nat :=
  match events with
  | [] => 0
  | AuditDenseUniqueCase _ _ :: rest => 1 + audit_dense_prepare_work enc_work rest
  | AuditDenseUniqueProbe _ _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_dense_prepare_work enc_work rest
  | AuditDenseUniqueAdd _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_dense_prepare_work enc_work rest
  | AuditDenseUniqueKeep _ :: rest => 1 + audit_dense_prepare_work enc_work rest
  | AuditDenseNumberCase _ _ :: rest => 1 + audit_dense_prepare_work enc_work rest
  | AuditDenseNumberNext _ _ calls :: rest =>
      2 + (match calls with
           | [AuditDenseBinarySuccessor _ _ sub] => audit_N_encoding_work sub
           | _ => 0
           end) + audit_dense_prepare_work enc_work rest
  | AuditDenseNumberStore _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_dense_prepare_work enc_work rest
  | AuditDenseLength input _ calls :: rest =>
      2 + input + (match calls with
                   | [AuditDenseLengthConversion _ _ sub] => audit_nat_events_work sub
                   | _ => 0
                   end) + audit_dense_prepare_work enc_work rest
  end.

Fixpoint audit_dense_unique_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 10 + 2 * enc_work (snd (enc key)) + 21 * Pos.size_nat (fst (enc key)) +
      audit_dense_unique_budget enc enc_work rest
  end.

Fixpoint audit_dense_number_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) (index : N) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      let '(next, ne) := audit_dense_N_succ index in
      5 + (match ne with
           | [AuditDenseBinarySuccessor _ _ sub] => audit_N_encoding_work sub
           | _ => 0
           end) + enc_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
        audit_dense_number_budget enc enc_work rest next
  end.

Definition audit_dense_prepare_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) : nat :=
  let unique := fst (audit_dense_unique enc FinSet.empty keys) in
  let converted := audit_dense_N_of_nat (List.length unique) in
  audit_dense_unique_budget enc enc_work keys + audit_dense_number_budget enc enc_work unique 0%N +
    2 + List.length unique +
    (match snd converted with
     | [AuditDenseLengthConversion _ _ sub] => audit_nat_events_work sub
     | _ => 0
     end).

(** The dense prepare work is bounded by [audit_dense_prepare_budget]. *)
Definition audit_dense_prepare_source_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work keys,
    audit_dense_prepare_work enc_work (snd (audit_dense_prepare enc keys)) <=
      audit_dense_prepare_budget enc enc_work keys.
