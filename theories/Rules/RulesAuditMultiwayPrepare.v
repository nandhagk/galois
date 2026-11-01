(** * Multiway index preparation

    This model records the primitive subruns of multiway index preparation.
    For example, each variable retains the rows used to build its index.
    Builds on: RulesAuditIndex and RulesAuditJoinSyntax. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditJoinSyntax.
Import List.ListNotations.

Fixpoint rules_variable_map_full {P} (E : encoding P) (relations : Map.t P (list tuple))
    (bound : FinSet.t nat) (v : nat) (atoms : list (atom P)) : mat_run (list variable_search) :=
  mat_mark 221 (match atoms with
  | [] => mat_return []
  | a :: rest =>
      raw <- mat_get E (pred a) relations;;
      let rows := match raw with
      | Some found => found
      | None => []
      end in
      index <- mat_build_variable_full bound (args a) v rows;;
      tail <- rules_variable_map_full E relations bound v rest;;
      mat_return (VariableSearch (args a) index :: tail)
  end).

Definition rules_prepare_variable_full {P} (E : encoding P) (relations : Map.t P (list tuple))
    (bound : FinSet.t nat) (v : nat) (atoms : list (atom P)) : mat_run (list variable_search) :=
  selected <- mat_atoms_with v atoms;;
  rules_variable_map_full E relations bound v selected.

Fixpoint rules_prepare_multiway_full {P} (E : encoding P) (relations : Map.t P (list tuple))
    (vars : list nat) (bound : FinSet.t nat) (atoms : list (atom P)) : mat_run (list
  multiway_search) :=
  mat_mark 222 (match vars with
  | [] => mat_return []
  | v :: rest =>
      domains <- rules_prepare_variable_full E relations bound v atoms;;
      next <- mat_nat_add v bound;;
      tail <- rules_prepare_multiway_full E relations rest next atoms;;
      mat_return (MultiwaySearch v bound domains :: tail)
  end).

(** Erasing multiway preparation gives the original prepared indexes. *)
Definition rules_prepare_multiway_full_erases_statement : Prop :=
  forall P (E : encoding P) relations vars bound atoms,
    fst (rules_prepare_multiway_full E relations vars bound atoms) =
      prepare_multiway vars bound atoms (join_relation_rows E relations).
