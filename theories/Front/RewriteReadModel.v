(** * The model of the relations beside equations

    The soundness of the rows and the lattice values of a specification with equations rests on
    one model, [unit_model] of [RewriteReadSig.v]. It has one class, its relations hold of the
    rows of [lat_derived] and its lattice tables hold the merges of [lat_merged]. This file
    proves that it satisfies the clauses that derive rows or assign values ([value_part]), when
    every relation and every lattice table takes only values, and that those clauses form a
    well-sorted specification.

    For example, the model of the relation [known] of constant propagation holds [known 1 5]
    exactly when [known 1 5] is a derived row.

    Builds on: the signature of rewrites that read rows, the meaning of lattice reads, the
    specifications and their lowering. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadModel (V : VALUE) (PS : LOWER_PLAN) <: REWRITE_READ_VALUE_PLAN V.
  (* STUB: [check_program_spec] reads [check_program] as [program_ok], a [Forall] over the
     rules. The rules of [value_part s] are the rules of the clauses that [filter] keeps, over
     the same declarations, so each is well sorted. [kinds_ok] is a [forallb] over the clauses,
     which [filter] keeps true. *)
  Lemma value_part_ok : forall (s : spec V.t),
    spec_ok s = true -> spec_ok (value_part s) = true.
  Proof.
  Admitted. (* STUB *)

  (* STUB: the sorts of a well-sorted specification whose relations and lattice tables take
     only values put no constructor pattern in a clause that derives a row or assigns a value.
     For such a pattern, the meaning under an environment of the model is [inr v] exactly when
     the value under the environment of its [inr] values is [v]. The input rows are rows by
     [lat_derived_input]. A clause whose premises are true binds each variable of its head to an
     [inr] value, by [PS.head_vars_bound], and gives a row by [lat_derived_clause] or an
     assigned value by [lat_assigned_clause] and [lat_merged_one], with [lat_body_intro].
     [lat_merged_merge] closes the lattice values under the merges. *)
  Lemma unit_model_satisfies : forall (s : spec V.t) (I : positive -> list V.t -> Prop),
    spec_ok s = true -> value_tables s = true ->
    satisfies V.prim V.merge (unit_model V.prim V.merge s I) (value_part s) I.
  Proof.
  Admitted. (* STUB *)
End RewriteReadModel.
