(** * Timed inclusion-based pointer analysis

    The timed module of the Andersen driver. It applies the law module to the timed runner, its
    facts and the relational theorems, derives the time function of each operation, and states
    the costs of seeding, querying and solving with the plan of the signature.
    For example, a points-to query costs one lookup in the final database.

    Main results
    - [seed_complexity] Seeding is linear in the constraints and initial pointers at the database
      unit.
    - [compile_complexity] Compilation emits a fixed program, so its cost is a constant, O(1).
    - [points_complexity] A points-to query is linear in the database unit and the bits of its
      two cells.
    - [solve_complexity] A solve costs its seed, the cube of the fixed program for planning, and
      the run.

    Builds on: AndersenSig, the Andersen driver, the timed runner and its facts, the lowering
    laws and the relational theorems. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Lower RunnerSig Runner RunnerFacts RunnerTime Relational.
From Galois.Clients Require Import AndersenSig Andersen.
Import List.ListNotations.
Import ComplexityNotations.

(** * Time *)

Module AndersenT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D)
    <: ANDERSEN_ALL V I J D R.
  (** The runner with its time functions, its facts, and the relational theorems. *)
  Module XT := RunnerT V I J D R.
  Module FT := RunnerFacts V I J D R XT.
  Module TT := Relational V I J D R XT FT LowerLaws.
  Include Andersen V I J D R XT FT TT.
  TimeFun compile.
  TimeFun seed.
  TimeFun solve.
  TimeFun points.
  Definition k_rules : N := 1. (* STUB *)
  Definition k_seed : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Definition c_andersen : N := 1. (* STUB *)

  (* STUB: [XT.T_seed_le] for [MayPoints.spec] and the facts of [q], whose rows have two values
     each, with the planning and loading costs of the fixed program as constants. *)
  Lemma T_seed_le : forall q,
    (T_seed q <= c_andersen *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_compile_le : forall q, (T_compile q <= c_andersen)%N.
  Proof. Admitted. (* STUB *)

  (* STUB: [XT.T_holds_le] at [MayPoints.may_points_code] and the two values [x] and [a]. *)
  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_andersen * (N.of_nat (3 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (* STUB: [XT.T_solve_split] for the fixed program. *)
  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_andersen)%N.
  Proof. Admitted. (* STUB *)

  (** Seeding is linear in the constraints and initial pointers at the database unit. *)
  Lemma seed_complexity :
    T_seed q ∈ 𝑂(N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1))) for q.
  Proof. Admitted. (* STUB *)

  (** Compilation emits a fixed program, so its cost is a constant. *)
  Lemma compile_complexity : T_compile q ∈ 𝑂(0) for q.
  Proof. Admitted. (* STUB *)

  (** A points-to query is linear in the database unit and the bits of its two cells. *)
  Lemma points_complexity :
    T_points db (x : positive) (a : positive) ∈
      𝑂(N.of_nat (3 * D.unit db + cell_bits V.encode (Val x) + cell_bits V.encode (Val a) + 1))
      for (db, x, a) | D.wf db.
  Proof. Admitted. (* STUB *)

  (** A solve costs its seed, the cube of the fixed program for planning, and the run. *)
  Lemma solve_complexity :
    T_solve q lim ∈ 𝑂((N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)) +
      N.of_nat ((R.size_program (compile q) + 1) * (R.size_program (compile q) + 1) *
        (R.size_program (compile q) + 1)) +
      R.run_cost B U (compile q) (R.plan (compile q)) lim (seed q))%N)
      for (B, U, q, lim) |
        (D.ids (snd (solve q lim)) <= B)%N /\ D.unit (snd (solve q lim)) <= U.
  Proof. Admitted. (* STUB *)

  Lemma source_closed : forall q, pointer_closed q (may_points q).
  Proof.
    exact pointer_source_closed.
  Qed.

  Lemma source_least : forall q r, pointer_closed q r ->
    forall x a, may_points q x a -> r x a.
  Proof.
    exact pointer_source_least.
  Qed.

  Lemma step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  Proof.
    exact pointer_step_covered.
  Qed.

  (* STUB: [XT.T_solve_split], with the costs of the wrapper as constants. *)
  Lemma T_solve_split : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)
End AndersenT.
