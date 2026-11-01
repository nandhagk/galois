(** * Relation snapshot observations

    These computed fixtures inspect empty, duplicate and distinct relation snapshots.
    For example, repeating a predicate causes one environment call.
    Builds on: RulesAuditRelations and RulesAuditRelationsAdequacy. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve RulesAuditRelations
  RulesAuditRelationsAdequacy RulesAuditAtomFold RulesAuditDeltaRows RulesAuditUniverse.
From Galois.Tests.Rules Require Import RulesRUL2a.
Import List.ListNotations.

Definition data_environment (p : nat) : FinSet.t tuple :=
  if Nat.eqb p 1 then FinSet.of_list tuple_encoding [[2%positive]; [3%positive]]
  else FinSet.empty.

(** No atoms make no environment calls and produce an empty snapshot. *)
Example data_empty_snapshot :
    fst (rules_join_relations_counted nat_encoding [] data_environment) = Map.empty /\
    length (filter (rules_relation_is_env nat)
      (snd (rules_join_relations_counted nat_encoding [] data_environment))) = 0.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Duplicate atom insertions retain two reads while storing one tuple. *)
Example data_duplicate_atom_fold :
    let prog := join_test_program [] in
    let '(db, events) := rules_atom_fold_counted prog
      [(1, [2%positive]); (1, [2%positive])] Map.empty in
    FinSet.elements (rel_of prog db 1) = [[2%positive]] /\
    length (filter (fun event =>
      match event with
      | RafRelationGet _ _ _ _ _ => true
      | _ => false
      end) events) = 2 /\
    flat_map (fun event =>
      match event with
      | RafRelationGet _ _ _ raw _ =>
          [match raw with
           | None => true
           | Some _ => false
           end]
      | _ => []
      end) events = [true; false] /\
    fst (rules_delta_rows_lookup_counted prog (fst (rules_delta_rows_snapshot_counted db)) 3) = [].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Universe checks reject absent constants, wrong arity, and absent predicates. *)
Example data_universe_boundaries :
    let prog := join_test_program [] in
    let facts := [(1, [2%positive; 3%positive])] in
    let check p row :=
      fst (@rules_universe_check_counted nat
        (fst (rules_universe_prepare_counted prog facts p)) row) in
    check 1 [2%positive; 3%positive] = true /\
    check 1 [2%positive; 4%positive] = false /\
    check 1 [2%positive] = false /\
    check 2 [2%positive; 3%positive] = false.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Duplicate atoms enumerate once; a second predicate retains its empty relation. *)
Example data_duplicate_and_missing_snapshot :
    let a := Atom 1 [TVar 0] in
    let b := Atom 2 [TVar 0] in
    let '(snapshot, events) := rules_join_relations_counted nat_encoding [a; a; b]
      data_environment in
    length (filter (rules_relation_is_env nat) events) = 2 /\
    Map.get nat_encoding 1 snapshot = Some [[2%positive]; [3%positive]] /\
    Map.get nat_encoding 2 snapshot = Some [] /\
    Map.get nat_encoding 3 snapshot = None.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.
