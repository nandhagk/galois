(** * Timed runner

    The timed runner, with the bounds of solving, saturating and deciding equality. It
    includes the bounds of seeding from [RunnerSeedTime.v], of lookups and comparisons of
    cells from [RunnerQueryTime.v] and of adding terms from [RunnerTermsTime.v]. A saturation
    pays for its seed, its terms and the rounds of its run at bounds of the outcome, which
    bound the databases before the run too, because a run never lowers the identifier count
    or the unit. The potential that the puts and the constructors leave pays for the deferred
    rebuilds that the run charges.
    For example, [equal Math.program [] lim t u] costs the saturation with [t] and [u] and two
    finds in its outcome.

    Builds on: the runner signature, the first three parts of the timed runner, and the time
    contracts of the database and the run. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig RunnerTermsTime.

Import List.ListNotations.
Import ComplexityNotations.

Module RunnerT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) <: RUNNER_T V I J D R.
  Include RunnerTermsT V I J D R.
  Definition c_saturate : N := 1. (* STUB *)

  (* STUB: [T_solve_split] with [T_seed_amort] at [B] and [U], [R.T_run_le] on the seed, whose
     potential pays for the credit of the run, and [R.T_plan_le]. [R.run_ids] and [R.run_unit]
     give the bounds of the seed. The seed facts come from [RunnerFacts] applied to a named
     [Module X0 := Runner V I J D R], whose operations convert to those of this module. *)
  Lemma solve_complexity :
    T_solve (spec_program s) rows lim ∈ 𝑂(saturate_cost B U (spec_program s) rows [] lim)
      for (B, U, s, rows, lim) |
        spec_ok s = true /\ rows_ok s rows = true /\
        (D.ids (snd (solve (spec_program s) rows lim)) <= B)%N /\
        D.unit (snd (solve (spec_program s) rows lim)) <= U.
  Proof.
  Admitted. (* STUB *)

  Lemma T_saturate_split : forall p rows es lim,
    (T_saturate p rows es lim <=
      T_seed p rows + T_add_terms es (seed p rows) + R.T_plan p +
      R.T_run p (R.plan p) lim (snd (add_terms es (seed p rows))) + c_saturate)%N.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [T_saturate_split] with [T_seed_amort], [T_add_terms_amort] and [R.T_run_le], whose
     potentials cancel. [R.run_ids] and [R.run_unit] bound the database before the run by the
     outcome, and [add_terms_unit] bounds the unit of the seed. The runner facts and
     [add_terms_ready] of the rewrite plan, applied to [X0] as for [solve_complexity], give the
     conditions of each contract. *)
  Lemma saturate_complexity :
    T_saturate (spec_program s) rows es lim ∈ 𝑂(saturate_cost B U (spec_program s) rows es lim)
      for (B, U, s, rows, es, lim) |
        spec_ok s = true /\ rows_ok s rows = true /\ forallb (term_ok s) es = true /\
        (D.ids (snd (fst (saturate (spec_program s) rows es lim))) <= B)%N /\
        D.unit (snd (fst (saturate (spec_program s) rows es lim))) <= U.
  Proof.
  Admitted. (* STUB *)

  Lemma T_equal_split : forall p rows lim t u st db c d,
    saturate p rows [t; u] lim = (st, db, [c; d]) ->
    (T_equal p rows lim t u <= T_saturate p rows [t; u] lim + T_same_cell c d db + c_saturate)%N.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [T_equal_split] with [saturate_complexity] and [T_same_cell_le] on the outcome, which
     [R.run_wf] keeps well formed. The cells are allocated before the run by
     [add_terms_allocated], and [R.run_ids] keeps them allocated. *)
  Lemma equal_complexity :
    T_equal (spec_program s) rows lim t u ∈
      𝑂(saturate_cost B U (spec_program s) rows [t; u] lim +
        N.of_nat (cell_bits V.encode (D.canon db c)))
      for (B, U, s, rows, lim, t, u, st, db, c, d) |
        spec_ok s = true /\ rows_ok s rows = true /\ term_ok s t = true /\ term_ok s u = true /\
        saturate (spec_program s) rows [t; u] lim = (st, db, [c; d]) /\
        (D.ids db <= B)%N /\ D.unit db <= U.
  Proof.
  Admitted. (* STUB *)
End RunnerT.
