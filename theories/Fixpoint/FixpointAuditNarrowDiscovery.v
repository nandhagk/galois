(** * Narrowing output discovery

    The model retains the actual target and side calls and the distinct-set build.
    For example, duplicate outputs are inserted separately before enumeration.
    Builds on: FixpointNarrow and the shared set audit. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditCost
  CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointSystem FixpointAuditWorklist.
Import List.ListNotations.

Inductive fx_dependency_event (X C : Type) : Type :=
  | FxDepTarget (c : C) (out : X)
  | FxDepSides (c : C) (out : list X)
  | FxDepDistinct (input : list X) (set : FinSet.t X) (out : list X)
      (build : list (audit_set_event X (fx_encoder_entry X)))
      (enumerate : list (audit_set_elements_event X))
  | FxDepAppend (size : nat)
  | FxDepCase (site : nat).

Arguments FxDepTarget {X C} _ _.

Arguments FxDepSides {X C} _ _.

Arguments FxDepDistinct {X C} _ _ _ _ _.

Arguments FxDepAppend {X C} _.

Arguments FxDepCase {X C} _.

Definition fx_dependency_distinct {X C} (EX : encoding X) (input : list X) :
    list X * list (fx_dependency_event X C) :=
  let '(set, build) := audit_finset_of_list (fx_index_encoder EX) input in
  let '(out, enumerate) := audit_finset_elements set in
  (out, [FxDepDistinct input set out build enumerate]).

Fixpoint fx_dependency_outputs_input {X C A} (S : System.t X C A) (SS : System.static S)
    (cs : list C) : list X * list (fx_dependency_event X C) :=
  match cs with
  | [] => ([], [FxDepCase 1])
  | c :: rest =>
      let x := System.target S c in
      let sides := side_targets SS c in
      let row := x :: sides in
      let '(tail, events) := fx_dependency_outputs_input S SS rest in
      (row ++ tail, FxDepCase 1 :: FxDepTarget c x :: FxDepSides c sides :: events ++
        [FxDepAppend (length row)])
  end.

Definition fx_index_input_bits {X} (EX : encoding X) (xs : list X) : nat :=
  fold_right (fun x n => Pos.size_nat (encode EX x) + n) 0 xs.

Definition fx_dependency_event_work {X C} (event : fx_dependency_event X C) : nat :=
  match event with
  | FxDepDistinct _ _ _ build enumerate =>
      1 + audit_finset_source_work (@length (fx_encoder_entry X)) build +
        audit_set_elements_work enumerate
  | FxDepAppend n => 1 + n
  | _ => 1
  end.

Definition fx_dependency_event_budget {X C} (EX : encoding X)
    (event : fx_dependency_event X C) : nat :=
  match event with
  | FxDepDistinct input set _ _ _ =>
      20 + 12 * length input + 17 * fx_index_input_bits EX input +
        19 * audit_trie_nodes set + audit_trie_output_bits set
  | FxDepAppend n => 1 + n
  | _ => 1
  end.

Definition fx_dependency_work {X C} (_ : encoding X) (events : list (fx_dependency_event X C)) :
  nat :=
  fold_right (fun e n => fx_dependency_event_work e + n) 0 events.

Definition fx_dependency_budget {X C} (EX : encoding X)
    (events : list (fx_dependency_event X C)) : nat :=
  fold_right (fun e n => fx_dependency_event_budget EX e + n) 0 events.
