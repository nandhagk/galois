(** * Time of seeding and of queries

    The first part of the timed runner. It derives the time function of each operation of the
    runner and bounds seeding, solving, lookups and comparisons of cells. A seed starts from a
    load without potential, and each put pays for its share of the deferred rebuild at the unit
    bound. [RunnerTermsTime.v] adds the bounds of adding terms, and [RunnerTime.v] the bounds of
    saturation and equality.
    For example, [T_holds_le] bounds the points-to query of Andersen's analysis by one lookup of
    a key of two values.

    Builds on: the runner signature, the runner and the time contracts of the database and the
    run. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig Runner.

Import List.ListNotations.
Import ComplexityNotations.

Module RunnerSeedT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D).
  Include Runner V I J D R.
  TimeFun put_row.
  TimeFun seed.
  TimeFun solve.
  TimeFun holds.
  TimeFun add_term.
  TimeFun add_terms.
  TimeFun saturate.
  TimeFun same_cell.
  TimeFun equal.
  Definition c_runner : N := 1. (* STUB *)
  Definition seed_cost (B : N) (U : nat) (p : program V.t) (rows : list (positive * list V.t))
      : N :=
    (N.of_nat ((R.size_program p + 1) * (R.size_program p + 1) * (R.size_program p + 1)) +
     R.load_cost p (R.plan p) +
     N.of_nat (U * (N.to_nat (N.log2 B) + 1) * (length (Syntax.slots V.t (R.plan p)) + 1) *
       (rows_work rows + 1)))%N.
  Definition saturate_cost (B : N) (U : nat) (p : program V.t)
      (rows : list (positive * list V.t)) (es : list (@expr V.t)) (lim : limits) : N :=
    (seed_cost B U p rows +
     N.of_nat (U * (N.to_nat (N.log2 B) + 1) *
       ((length (Syntax.slots V.t (R.plan p)) + 1) * (terms_work es + 1) +
        (R.wbits p + 1) * R.run_work p (R.plan p) lim (snd (add_terms es (seed p rows))))) +
     N.of_nat (N.size_nat (max_iter lim) + 1))%N.

  (* STUB: induction on the rows from the load, whose potential is zero by [R.load_spec] and
     [D.potential_init]. Each put meets [D.T_put_amort] with the slots of the plan and the
     arity that [rows_ok] checks, and [D.unit_mono_put] keeps every unit below [U]. *)
  Lemma T_seed_amort : forall B U (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    (D.ids (seed (spec_program s) rows) <= B)%N -> D.unit (seed (spec_program s) rows) <= U ->
    (T_seed (spec_program s) rows + N.of_nat U * D.potential B (seed (spec_program s) rows) <=
      R.T_plan (spec_program s) + R.T_load (spec_program s) (R.plan (spec_program s)) +
      c_runner * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (rows_work rows + 1))%N.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [T_seed_amort]. [c_runner] must be at least [2 * D.c_db] plus the overheads of the
     derived time functions. *)
  Lemma T_seed_le : forall B U (s : spec V.t) rows,
    spec_ok s = true -> rows_ok s rows = true ->
    (D.ids (seed (spec_program s) rows) <= B)%N -> D.unit (seed (spec_program s) rows) <= U ->
    (T_seed (spec_program s) rows <=
      R.T_plan (spec_program s) + R.T_load (spec_program s) (R.plan (spec_program s)) +
      c_runner * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (rows_work rows + 1))%N.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [T_seed_le] at the bounds of the seed, with [R.T_plan_le], [R.T_load_le] and
     [D.T_init_le]. *)
  Lemma seed_complexity :
    T_seed (spec_program s) rows ∈
      𝑂(seed_cost (D.ids (seed (spec_program s) rows)) (D.unit (seed (spec_program s) rows))
        (spec_program s) rows)
      for (s, rows) | spec_ok s = true /\ rows_ok s rows = true.
  Proof.
  Admitted. (* STUB *)

  Lemma T_solve_split : forall p rows lim,
    (T_solve p rows lim <=
      T_seed p rows + R.T_plan p + R.T_run p (R.plan p) lim (seed p rows) + c_runner)%N.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [D.T_lookup_le] on the key [map Val vs], whose unit is at least one. *)
  Lemma T_holds_le : forall r vs db, D.wf db ->
    (T_holds r vs db <= c_runner * N.of_nat ((length vs + 1) * D.unit db +
      fold_right (fun v n => (cell_bits V.encode (Val v) + n)%nat) 0%nat vs + 1))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma holds_complexity :
    T_holds r vs db ∈
      𝑂(N.of_nat ((length vs + 1) * D.unit db +
        fold_right (fun v n => (cell_bits V.encode (Val v) + n)%nat) 0%nat vs))
      for (r, vs, db) | D.wf db.
  Proof.
  Admitted. (* STUB *)

  (* STUB: [D.T_find_le] for both identifiers, [D.find_spec] and [Std.Pos.T_eqb_le] for the
     representatives, and [V.T_eqb_le] for values. *)
  Lemma T_same_cell_le : forall a b db, D.wf db ->
    (forall i, In (Id i) [a; b] -> D.allocated db i) ->
    (T_same_cell a b db <=
      c_runner * N.of_nat (2 * D.unit db + cell_bits V.encode (D.canon db a) + 1))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma same_cell_complexity :
    T_same_cell a b db ∈ 𝑂(N.of_nat (D.unit db + cell_bits V.encode (D.canon db a)))
      for (a, b, db) | D.wf db /\ (forall i, In (Id i) [a; b] -> D.allocated db i).
  Proof.
  Admitted. (* STUB *)
End RunnerSeedT.
