(** * Unification-based pointer analysis

    Four instruction equations generate a congruence over cells and dereferences.
    For example, loading from y equates the result's pointee with y's second dereference.

    Main results
    - [points_spec] Queries test whether the pointee term equals the addressed cell in the final
      congruence.
    - [seed_complexity] Seeding is linear in the constraints and initial pointers at the database
      unit.
    - [compile_complexity] Compilation emits a fixed program, so its cost is a constant, O(1).
    - [points_complexity] A points-to query is linear in the database unit and the bits of its
      two cells.
    - [solve_complexity] A solve costs its seed, the cube of the fixed program for planning, and
      the run.

    Builds on: the uniform-cell source semantics and the engine's identifier congruence. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec Derive.
From Galois.Clients Require Import AndersenSig.
Import List.ListNotations.
Import ComplexityNotations.

Inductive pointer_term :=
  | Cell (address : positive)
  | Deref (pointer : pointer_term).

(** Source equations and unary congruence define the unification approximation. *)
Inductive pointer_congruence (q : pointer_input) : pointer_term -> pointer_term -> Prop :=
  | Cong_refl : forall t, pointer_congruence q t t
  | Cong_sym : forall t u, pointer_congruence q t u -> pointer_congruence q u t
  | Cong_trans : forall t u v, pointer_congruence q t u -> pointer_congruence q u v ->
      pointer_congruence q t v
  | Cong_deref : forall t u, pointer_congruence q t u ->
      pointer_congruence q (Deref t) (Deref u)
  | Cong_initial : forall x a, In (x, a) (initial_pointers q) ->
      pointer_congruence q (Deref (Cell x)) (Cell a)
  | Cong_addr : forall x a, In (Addr x a) (constraints q) ->
      pointer_congruence q (Deref (Cell x)) (Cell a)
  | Cong_copy : forall x y, In (Copy x y) (constraints q) ->
      pointer_congruence q (Deref (Cell x)) (Deref (Cell y))
  | Cong_load : forall x y, In (Load x y) (constraints q) ->
      pointer_congruence q (Deref (Cell x)) (Deref (Deref (Cell y)))
  | Cong_store : forall x y, In (Store x y) (constraints q) ->
      pointer_congruence q (Deref (Deref (Cell x))) (Deref (Cell y)).

(** The engine program is derived from [pointer_congruence], and every table code is generated. *)
Egglog Unification from pointer_congruence.

Definition steensgaard_program : program positive := Unification.program.

Module Type STEENSGAARD_OPS (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D).
  Parameter compile : pointer_input -> program V.t.
  Parameter seed : pointer_input -> D.t.
  Parameter solve : pointer_input -> limits -> stop * D.t.
  Parameter points : D.t -> positive -> positive -> bool.
End STEENSGAARD_OPS.

Module Type STEENSGAARD_LAWS (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D)
    (Import A : STEENSGAARD_OPS V I J D R).
  (** Compilation emits exactly the four instruction equations as identifier unions. *)
  Parameter compile_rules : forall q, compile q = steensgaard_program.
  (** Seeds contain exactly the input rows of the source constraints and initial pointers. *)
  Parameter seed_rows : forall q f k o, row (D.view (seed q)) f k o <->
    o = None /\ exists vs, k = map Val vs /\ In (f, vs) (Unification.facts q).
  (** Seeds carry the compiled declarations, the layout of the compiled plan and
      well-sorted rows. *)
  Parameter seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  (** Seeding produces a canonical well-formed database. *)
  Parameter seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  (** The solver runs the engine with the planned program on the seed. *)
  Parameter solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  (** Queries test whether the pointee term equals the addressed cell in the final congruence. *)
  Parameter points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j,
      represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x))) /\
      represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a)) /\
      same (D.view db) i j)
      (points db x a).
  (** Every returned database is canonical and well formed. *)
  Parameter solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  (** Saturated query answers contain the source congruence approximation. *)
  Parameter solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
End STEENSGAARD_LAWS.

Module Type STEENSGAARD (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) :=
  STEENSGAARD_OPS V I J D R <+ STEENSGAARD_LAWS V I J D R.

Module Type STEENSGAARD_TIME (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D)
    (Import A : STEENSGAARD V I J D R).
  Parameter T_compile T_seed : pointer_input -> N.
  Parameter T_solve : pointer_input -> limits -> N.
  Parameter T_points : D.t -> positive -> positive -> N.
  Parameter c_steensgaard : N.
  (** Seeding initializes the database and inserts one row per constraint and initial pointer. *)
  Parameter T_seed_le : forall q,
    (T_seed q <= c_steensgaard *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  (** Compilation emits a fixed program. *)
  Parameter T_compile_le : forall q, (T_compile q <= c_steensgaard)%N.
  (** A points-to query is one relation lookup. *)
  Parameter T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_steensgaard * (N.of_nat (8 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.

  (** The driver retains the costs of rule compilation, seeding, planning and the engine. *)
  Parameter T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
  (** Seeding is linear in the constraints and initial pointers at the database unit. *)
  Parameter seed_complexity :
    T_seed q ∈ 𝑂(N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1))) for q.
  (** Compilation emits a fixed program, so its cost is a constant. *)
  Parameter compile_complexity : T_compile q ∈ 𝑂(0) for q.
  (** A points-to query is linear in the database unit and the bits of its two cells. *)
  Parameter points_complexity :
    T_points db (x : positive) (a : positive) ∈
      𝑂(N.of_nat (8 * D.unit db + cell_bits V.encode (Val x) + cell_bits V.encode (Val a) + 1))
      for (db, x, a) | D.wf db.
  (** A solve costs its seed, the cube of the fixed program for planning, and the run. *)
  Parameter solve_complexity :
    T_solve q lim ∈ 𝑂((N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)) +
      N.of_nat ((R.size_program (compile q) + 1) * (R.size_program (compile q) + 1) *
        (R.size_program (compile q) + 1)) +
      R.run_cost B U (compile q) (R.plan (compile q)) lim (seed q))%N)
      for (B, U, q, lim) |
        (D.ids (snd (solve q lim)) <= B)%N /\ D.unit (snd (solve q lim)) <= U.
End STEENSGAARD_TIME.

Module Type STEENSGAARD_T (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) :=
  STEENSGAARD V I J D R <+ STEENSGAARD_TIME V I J D R.

Module Type STEENSGAARD_PLAN (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D)
    (Import A : STEENSGAARD_T V I J D R).
  Parameter k_rules k_seed k_wrap : N.
  (** Dereference equality covers every source-closed pointer rule. *)
  Parameter source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  (** Every inclusion-derived pointer belongs to the unification approximation. *)
  Parameter inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  (** Saturation makes each source equation's two ground terms equal in the database. *)
  Parameter saturated_equations : forall q lim db, solve q lim = (Saturated, db) ->
    forall t u, pointer_congruence q t u ->
    forall i j, represents (D.view db) (Id i) (Unification.encode_pointer_term t) ->
      represents (D.view db) (Id j) (Unification.encode_pointer_term u) -> same (D.view db) i j.
  (** Congruence consequences queried as pointers have represented endpoint terms. *)
  Parameter endpoints_represented : forall q lim db x a,
    solve q lim = (Saturated, db) -> pointer_congruence q (Deref (Cell x)) (Cell a) ->
    (exists i, represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x)))) /\
    (exists j, represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a))).
  (** Concrete instruction updates retain coverage by the source congruence. *)
  Parameter step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  (** Wrapper composition includes every actual engine and database primitive. *)
  Parameter T_solve_split : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
End STEENSGAARD_PLAN.

Module Type STEENSGAARD_ALL (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) :=
  STEENSGAARD_T V I J D R <+ STEENSGAARD_PLAN V I J D R.

Module Type STEENSGAARD_SOUND (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (L : POINTER_LINK).
  (** Every reachable concrete pointer is included in every saturated unification result. *)
  Parameter concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
End STEENSGAARD_SOUND.

Module Type STEENSGAARD_EXACT (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R).
  (** Two terms related by the generated program's congruence are related by the source
      congruence, so the engine's congruence adds no equation. *)
  Parameter pointer_congruence_back : forall prim q t u,
    congruent prim Unification.spec (Unification.inputs q)
      (Unification.encode_pointer_term t) (Unification.encode_pointer_term u) ->
    pointer_congruence q t u.

  (** Saturated query answers are exactly the source congruence approximation. *)
  Parameter solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
End STEENSGAARD_EXACT.
