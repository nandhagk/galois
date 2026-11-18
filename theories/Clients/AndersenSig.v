(** * Inclusion-based pointer analysis

    Four first-order constraints generate the least may-points-to relation over uniform cells.
    For example, a load follows the pointer in its operand cell and then the pointer in that cell.

    Main results
    - [points_spec] Points-to queries reflect canonical relation membership.
    - [solve_exact] A saturated result is exactly the least inclusion solution.
    - [seed_complexity] Seeding is linear in the constraints and initial pointers at the database
      unit.
    - [compile_complexity] Compilation emits a fixed program, so its cost is a constant, O(1).
    - [points_complexity] A points-to query is linear in the database unit and the bits of its
      two cells.
    - [solve_complexity] A solve costs its seed, the cube of the fixed program for planning, and
      the run.

    Builds on: binary tries and the relational engine's derivation and saturation contracts. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec Derive.
Import List.ListNotations.
Import ComplexityNotations.

Inductive pointer_constraint :=
  | Addr (x address : positive)
  | Copy (x y : positive)
  | Load (x y : positive)
  | Store (x y : positive).

Record pointer_input := PointerInput {
  constraints : list pointer_constraint;
  initial_pointers : list (positive * positive)
}.

(** Variables occupy distinguished cells in the same address space as heap cells. *)
Definition pointer_exec (instruction : pointer_constraint) (memory : ptrie positive) :
    option (ptrie positive) :=
  match instruction with
  | Addr x address => Some (PTrieCode.set x address memory)
  | Copy x y =>
      match trie_get y memory with
      | Some address => Some (PTrieCode.set x address memory)
      | None => None
      end
  | Load x y =>
      match trie_get y memory with
      | None => None
      | Some location =>
          match trie_get location memory with
          | Some address => Some (PTrieCode.set x address memory)
          | None => None
          end
      end
  | Store x y =>
      match trie_get x memory, trie_get y memory with
      | Some location, Some address => Some (PTrieCode.set location address memory)
      | _, _ => None
      end
  end.
TimeFun pointer_exec.

(** These rules describe the least inclusion solution independently of the engine. *)
Inductive may_points (q : pointer_input) : positive -> positive -> Prop :=
  | May_initial : forall x a, In (x, a) (initial_pointers q) -> may_points q x a
  | May_addr : forall x a, In (Addr x a) (constraints q) -> may_points q x a
  | May_copy : forall x y a, In (Copy x y) (constraints q) ->
      may_points q y a -> may_points q x a
  | May_load : forall x y location a, In (Load x y) (constraints q) ->
      may_points q y location -> may_points q location a -> may_points q x a
  | May_store : forall x y location a, In (Store x y) (constraints q) ->
      may_points q x location -> may_points q y a -> may_points q location a.

Definition pointer_closed (q : pointer_input) (r : positive -> positive -> Prop) :=
  (forall x a, In (x, a) (initial_pointers q) -> r x a) /\
  (forall x a, In (Addr x a) (constraints q) -> r x a) /\
  (forall x y a, In (Copy x y) (constraints q) -> r y a -> r x a) /\
  (forall x y location a, In (Load x y) (constraints q) ->
    r y location -> r location a -> r x a) /\
  (forall x y location a, In (Store x y) (constraints q) ->
    r x location -> r y a -> r location a).

Definition memory_covered (r : positive -> positive -> Prop) (memory : ptrie positive) :=
  forall x a, trie_get x memory = Some a -> r x a.

Inductive pointer_reachable {S} (initial : S -> Prop) (step : S -> S -> Prop) : S -> Prop :=
  | Pointer_initial : forall s, initial s -> pointer_reachable initial step s
  | Pointer_next : forall s t, pointer_reachable initial step s -> step s t ->
      pointer_reachable initial step t.

(** A source provider exposes its actual snapshots and the instruction taken by each step. *)
Module Type POINTER_LINK.
  (* spec: state memory initial step *)
  Parameter state : Type.
  Parameter memory : state -> ptrie positive.
  Parameter initial : pointer_input -> state -> Prop.
  Parameter step : pointer_input -> state -> state -> Prop.
  (** Every pointer in an initial snapshot is included among the input seeds. *)
  Parameter initial_coverage : forall q s x a, initial q s ->
    trie_get x (memory s) = Some a -> In (x, a) (initial_pointers q).
  (** Every actual transition performs one listed instruction's concrete update. *)
  Parameter step_update : forall q s t, step q s t ->
    exists instruction, In instruction (constraints q) /\
      pointer_exec instruction (memory s) = Some (memory t).
End POINTER_LINK.

(** The engine program is derived from [may_points], and every table code is generated. *)
Egglog MayPoints from may_points.

Definition andersen_program : program positive := MayPoints.program.

Module Type ANDERSEN_OPS (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D).
  Parameter compile : pointer_input -> program V.t.
  Parameter seed : pointer_input -> D.t.
  Parameter solve : pointer_input -> limits -> stop * D.t.
  Parameter points : D.t -> positive -> positive -> bool.
End ANDERSEN_OPS.

Module Type ANDERSEN_LAWS (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D)
    (Import A : ANDERSEN_OPS V I J D R).
  (** Compilation emits exactly the four inclusion rules. *)
  Parameter compile_rules : forall q, compile q = andersen_program.
  (** Seeds contain exactly the input rows of the source constraints and initial pointers. *)
  Parameter seed_rows : forall q f k o, row (D.view (seed q)) f k o <->
    o = None /\ exists vs, k = map Val vs /\ In (f, vs) (MayPoints.facts q).
  (** Seeds carry the compiled declarations, the layout of the compiled plan and
      well-sorted rows. *)
  Parameter seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  (** Seed construction produces a well-formed canonical relational database. *)
  Parameter seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  (** The solver runs the engine with the planned program on the seed. *)
  Parameter solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  (** Points-to queries reflect canonical relation membership. *)
  Parameter points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) MayPoints.may_points_code [Val x; Val a] None) (points db x a).
  (** Every returned database is well formed and canonical. *)
  Parameter solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).

  (** A run with enough iteration fuel saturates. *)
  Parameter solve_saturates : forall q lim,
    N.to_nat (max_iter lim) >= 2 * R.herbrand (compile q) (seed q) + 3 ->
    fst (solve q lim) = Saturated.

  (** A saturated result is exactly the least inclusion solution. *)
  Parameter solve_exact : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> may_points q x a.
End ANDERSEN_LAWS.

Module Type ANDERSEN (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) :=
  ANDERSEN_OPS V I J D R <+ ANDERSEN_LAWS V I J D R.

Module Type ANDERSEN_TIME (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D)
    (Import A : ANDERSEN V I J D R).
  Parameter T_compile T_seed : pointer_input -> N.
  Parameter T_solve : pointer_input -> limits -> N.
  Parameter T_points : D.t -> positive -> positive -> N.
  Parameter c_andersen : N.
  (** Seeding initializes the database and inserts one row per constraint and initial pointer. *)
  Parameter T_seed_le : forall q,
    (T_seed q <= c_andersen *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  (** Compilation emits a fixed program. *)
  Parameter T_compile_le : forall q, (T_compile q <= c_andersen)%N.
  (** A points-to query is one relation lookup. *)
  Parameter T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_andersen * (N.of_nat (3 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.

  (** The driver pays for compilation, seeding, planning and the engine run. *)
  Parameter T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_andersen)%N.
  (** Seeding is linear in the constraints and initial pointers at the database unit. *)
  Parameter seed_complexity :
    T_seed q ∈ 𝑂(N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1))) for q.
  (** Compilation emits a fixed program, so its cost is a constant. *)
  Parameter compile_complexity : T_compile q ∈ 𝑂(0) for q.
  (** A points-to query is linear in the database unit and the bits of its two cells. *)
  Parameter points_complexity :
    T_points db (x : positive) (a : positive) ∈
      𝑂(N.of_nat (3 * D.unit db + cell_bits V.encode (Val x) + cell_bits V.encode (Val a) + 1))
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
End ANDERSEN_TIME.

Module Type ANDERSEN_T (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) :=
  ANDERSEN V I J D R <+ ANDERSEN_TIME V I J D R.

Module Type ANDERSEN_PLAN (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D)
    (Import A : ANDERSEN_T V I J D R).
  Parameter k_rules k_seed k_wrap : N.
  (** The least source relation contains all seeds and is closed under the four instructions. *)
  Parameter source_closed : forall q, pointer_closed q (may_points q).
  (** Every relation closed under the four source rules contains the least source relation. *)
  Parameter source_least : forall q r, pointer_closed q r ->
    forall x a, may_points q x a -> r x a.
  (** Concrete updates preserve coverage by every source-closed relation. *)
  Parameter step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  (** Wrapper composition retains each actual primitive cost. *)
  Parameter T_solve_split : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
End ANDERSEN_PLAN.

Module Type ANDERSEN_ALL (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) :=
  ANDERSEN_T V I J D R <+ ANDERSEN_PLAN V I J D R.

Module Type ANDERSEN_SOUND (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : ANDERSEN V I J D R) (L : POINTER_LINK).
  (** Every reachable concrete pointer appears in every saturated analysis result. *)
  Parameter concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
End ANDERSEN_SOUND.
