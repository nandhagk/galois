(** * Soundness of the relations beside equations

    Every outcome of a saturation keeps the model [unit_model] of [RewriteReadSig.v]. The model
    validates the rules of the relations by the lowering of [value_part] and the rules of the
    equations by [REWRITE_READ_EQUATION_PLAN], it satisfies the seed, whose rows are the input
    rows, and adding terms keeps it, because its one class is the meaning of every term. A
    stored row of values then holds in the model, so it is a row of [lat_derived], and a stored
    value of a lattice table is a merge of [lat_merged]. The theorems take the plans of
    [RewriteReadModel.v], [RewriteReadEquations.v] and [RewriteTerms.v] as parameters.

    For example, a saturation of constant propagation with rewrites stores [known 1 5] only
    when [known 1 5] is a derived row.

    Builds on: the signature of rewrites that read rows and its plans, the runner facts, the
    lowering laws, the plan of added terms and the run contracts. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig RewriteSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadSound (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    (PT : REWRITE_TERMS_PLAN V I J D R X) (VP : REWRITE_READ_VALUE_PLAN V)
    (EP : REWRITE_READ_EQUATION_PLAN V) <: REWRITE_READ_SOUND V I J D R X.
  (* STUB: write [M] for [unit_model V.prim V.merge s (rows_in rows)]. [LW.lower_valid] on
     [value_part s], with [VP.value_part_ok] and [VP.unit_model_satisfies], validates the rule
     of each clause that derives a row or assigns a value, over the declarations of [s].
     [EP.equation_rule_valid] validates the other rules, so [M] validates the rules of
     [spec_program s], and [lat_merged_merge] closes its lattice values. [F.seed_rows] gives
     the seed the input rows, which hold in [M] by [lat_derived_input], and [R.loaded] of
     [F.seed_ready] gives the kinds of its tables. [X.saturate_unfold], [PT.add_terms_sat] and
     [R.run_sat] carry [sat] to the outcome, where the row holds in [M]. *)
  Lemma saturate_rows_sound : forall (s : spec V.t) rows es lim st db cs r vs,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    row (D.view db) r (map Val vs) None ->
    lat_derived V.prim V.merge s (rows_in rows) r vs.
  Proof.
  Admitted. (* STUB *)

  (* STUB: as [saturate_rows_sound], where the stored value holds in the lattice of [M]. *)
  Lemma saturate_values_sound : forall (s : spec V.t) rows es lim st db cs f ks v,
    spec_ok s = true -> value_tables s = true -> rows_ok s rows = true ->
    forallb (term_ok s) es = true ->
    X.saturate (spec_program s) rows es lim = (st, db, cs) ->
    row (D.view db) f (map Val ks) (Some (Val v)) ->
    lat_merged V.prim V.merge s (rows_in rows) f ks v.
  Proof.
  Admitted. (* STUB *)
End RewriteReadSound.
