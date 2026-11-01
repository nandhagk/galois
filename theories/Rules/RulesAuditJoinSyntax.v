(** * Join syntax and variable preparation

    These source mirrors retain list, set and union work before index preparation.
    For example, repeated variables cause repeated insertion before set enumeration.
    Builds on: RulesAuditMaterializePrelude and RulesCompile. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditEncoding
  CollectionsAuditFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude.
Import List.ListNotations.

Definition mat_term_vars (t : term) : mat_run (list nat) :=
  mat_mark 41 (match t with
    | TVar v => mat_return [v]
    | TConst _ => mat_return []
    end).

Definition mat_atom_vars {P} (a : atom P) : mat_run (list nat) :=
  mat_flatmap mat_term_vars (args a).

Definition mat_bound_add {P} (bound : FinSet.t nat) (a : atom P) : mat_run (FinSet.t nat) :=
  variables <- mat_atom_vars a;;
  vars <- mat_of_list audit_nat_encode audit_nat_events_work variables;;
  mat_union bound vars.

Definition mat_positive_literal {P} (item : literal P) : mat_run (list (atom P)) :=
  mat_mark 42 (match item with
    | LPos a => mat_return [a]
    | LNeg _ => mat_return []
    end).

Definition mat_positive_atoms {P} (items : list (literal P)) : mat_run (list (atom P)) :=
  mat_flatmap mat_positive_literal items.

Definition mat_join_variables {P} (atoms : list (atom P)) : mat_run (list nat) :=
  variables <- mat_flatmap mat_atom_vars atoms;;
  vars <- mat_of_list audit_nat_encode audit_nat_events_work variables;;
  mat_elements vars.

Definition mat_has_variable {P} (v : nat) (a : atom P) : mat_run bool :=
  variables <- mat_atom_vars a;;
  vars <- mat_of_list audit_nat_encode audit_nat_events_work variables;;
  mat_lift 43 (fun _ => 1 + v + mat_set_size vars)
    (audit_finset_source_work audit_nat_events_work) (audit_finset_mem audit_nat_encode v vars).

Definition mat_atoms_with {P} (v : nat) (atoms : list (atom P)) : mat_run (list (atom P)) :=
  mat_filter (mat_has_variable v) atoms.

(** Each syntax helper returns the value of the corresponding original source operation. *)
Definition mat_join_syntax_erasure_statement : Prop :=
  (forall P (a : atom P), fst (mat_atom_vars a) = atom_vars a) /\
  (forall P bound (a : atom P), fst (mat_bound_add bound a) = bound_add bound a) /\
  (forall P (items : list (literal P)), fst (mat_positive_atoms items) = positive_atoms items) /\
  (forall P (atoms : list (atom P)), fst (mat_join_variables atoms) = join_variables atoms) /\
  (forall P v (atoms : list (atom P)), fst (mat_atoms_with v atoms) = atoms_with_variable v atoms).
