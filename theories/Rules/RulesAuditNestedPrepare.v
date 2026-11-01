(** * Nested index preparation

    This model records the primitive subruns of nested index preparation.
    For example, each positive atom builds an index from its relation rows.
    Builds on: RulesAuditIndex and RulesAuditJoinSyntax. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditJoinSyntax.
From Galois.Collections Require Import CollectionsAuditElements.
Import List.ListNotations.

Fixpoint rules_prepare_nested_full {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (atoms : list (atom P))
    (bound : FinSet.t nat) : mat_run (list nested_search) :=
  mat_mark 201 (
    match atoms with
    | [] => mat_return []
    | a :: rest =>
        raw <- mat_get E (pred a) relations;;
        let rows := match raw with
        | Some found => found
        | None => []
        end in
        index <- mat_build_index_full bound (args a) rows;;
        let search := NestedSearch bound (args a) index in
        next_bound <- mat_bound_add bound a;;
        tail <- rules_prepare_nested_full E relations rest next_bound;;
        mat_return (search :: tail)
    end).

(** Erasing nested preparation gives the original prepared indexes. *)
Definition rules_prepare_nested_full_erases_statement : Prop :=
  forall P (E : encoding P) relations atoms bound,
    fst (rules_prepare_nested_full E relations atoms bound) =
      prepare_nested atoms bound (join_relation_rows E relations).

(** A candidate input-only allowance for this preparation phase. The model charges each
    predicate encoder as one external call; its real body needs a separate adapter. *)
Definition rules_nested_prepare_input_size {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (atoms : list (atom P))
    (bound : FinSet.t nat) : nat :=
  1 + audit_trie_nodes relations + audit_trie_nodes bound +
  fold_right (fun entry n => mat_index_rows_input (snd entry) + n) 0 (Map.elements relations) +
  fold_right (fun a n => 1 + Pos.size_nat (encode E (pred a)) +
    mat_index_terms_input (args a) + n) 0 atoms.

Definition rules_nested_prepare_input_budget {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (atoms : list (atom P))
    (bound : FinSet.t nat) : nat :=
  (1000 * 1000 * 1000) * Nat.pow (rules_nested_prepare_input_size E relations atoms bound) 16.

(** The input budget bounds nested preparation work. *)
Definition rules_prepare_nested_full_input_bound_statement : Prop :=
  forall P (E : encoding P) relations atoms bound,
    mat_work (snd (rules_prepare_nested_full E relations atoms bound)) <=
      rules_nested_prepare_input_budget E relations atoms bound.
