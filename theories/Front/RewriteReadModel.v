(** * The model of the relations beside equations

    The soundness of the rows and the lattice values of a specification with equations rests on
    one model, [unit_model] of [RewriteReadSig.v]. It has one class, its relations hold of the
    rows of [lat_derived] and its lattice tables hold the merges of [lat_merged]. This file
    proves that it satisfies a well-sorted specification when every relation and every lattice
    table takes only values. A clause that derives a row or assigns a value holds by the meaning
    of the relations, and an equation holds because both of its sides mean the one class.

    For example, the model of the relation [known] of constant propagation holds [known 1 5]
    exactly when [known 1 5] is a derived row.

    Builds on: the signature of rewrites that read rows, the meaning of lattice reads, the
    specifications and their lowering. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadModel (V : VALUE) (PS : LOWER_PLAN)
    (HP : REWRITE_READ_HEADS_PLAN) <: REWRITE_READ_VALUE_PLAN V.
  (* STUB: the sorts of a well-sorted specification whose relations and lattice tables take
     only values put no constructor pattern in a clause that derives a row or assigns a value.
     For such a pattern, the meaning under an environment of the model is [inr v] exactly when
     the value under the environment of its [inr] values is [v]. The input rows are rows by
     [lat_derived_input]. A clause that derives a row or assigns a value, and whose premises are
     true, binds each variable of its head to an [inr] value, by [PS.head_vars_bound], and gives
     a row by [lat_derived_clause] or an assigned value by [lat_assigned_clause] and
     [lat_merged_one], with [lat_body_intro]. For an equation, [HP.equation_sides_class] makes
     both sides variables or constructor patterns. The clause uses a variable of a side as a
     class, so an environment that fits the sorts of the clause gives it the one class, and a
     constructor pattern means the one class, so the two sides are equal. [lat_merged_merge]
     closes the lattice values under the merges. *)
  Lemma unit_model_satisfies : forall (s : spec V.t) (I : positive -> list V.t -> Prop),
    spec_ok s = true -> value_tables s = true ->
    satisfies V.prim V.merge (unit_model V.prim V.merge s I) s I.
  Proof.
  Admitted. (* STUB *)
End RewriteReadModel.
