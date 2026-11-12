(** * Inclusion-based pointer analysis

    Four first-order constraints generate the least may-points-to relation over uniform cells.
    For example, a load follows the pointer in its operand cell and then the pointer in that cell.
    Builds on: binary tries and the relational engine's derivation and saturation contracts. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model ValueSig IndexSig JoinSig DatabaseSig RunSig.
Import List.ListNotations.

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

Definition pointer_relation (q : pointer_input) (f x y : positive) : Prop :=
  (f = 1%positive /\ In (Addr x y) (constraints q)) \/
  (f = 2%positive /\ In (Copy x y) (constraints q)) \/
  (f = 3%positive /\ In (Load x y) (constraints q)) \/
  (f = 4%positive /\ In (Store x y) (constraints q)) \/
  (f = 5%positive /\ may_points q x y).

Definition andersen_model (q : pointer_input) : model (V := positive) :=
  Model unit (fun f args => exists x y, args = [inr x; inr y] /\ pointer_relation q f x y)
    (fun _ _ => tt) (fun _ _ _ => False).

Definition andersen_program : program positive := Program positive
  [Decl 1 2 ORel; Decl 2 2 ORel; Decl 3 2 ORel; Decl 4 2 ORel; Decl 5 2 ORel]
  [Rule positive [Fun positive 1 [Var 1; Var 2] None]
      [Put 5 [Var 1; Var 2] None];
   Rule positive [Fun positive 2 [Var 1; Var 2] None;
      Fun positive 5 [Var 2; Var 3] None] [Put 5 [Var 1; Var 3] None];
   Rule positive [Fun positive 3 [Var 1; Var 2] None;
      Fun positive 5 [Var 2; Var 3] None; Fun positive 5 [Var 3; Var 4] None]
      [Put 5 [Var 1; Var 4] None];
   Rule positive [Fun positive 4 [Var 1; Var 2] None;
      Fun positive 5 [Var 1; Var 3] None; Fun positive 5 [Var 2; Var 4] None]
      [Put 5 [Var 3; Var 4] None]].

Definition pointer_seed_row (q : pointer_input) f (k : list (cell positive))
    (o : option (cell positive)) :=
  o = None /\ exists x y, k = [Val x; Val y] /\
    ((f = 1%positive /\ In (Addr x y) (constraints q)) \/
     (f = 2%positive /\ In (Copy x y) (constraints q)) \/
     (f = 3%positive /\ In (Load x y) (constraints q)) \/
     (f = 4%positive /\ In (Store x y) (constraints q)) \/
     (f = 5%positive /\ In (x, y) (initial_pointers q))).

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
  (** The generated rules are valid in the independent least inclusion model. *)
  Parameter rules_valid : forall q, valid V.prim V.merge (andersen_model q) (compile q).
  (** Seeds contain exactly the source constraints and initial pointer facts. *)
  Parameter seed_rows : forall q f k o, row (D.view (seed q)) f k o <-> pointer_seed_row q f k o.
  (** Seed relation kinds agree with the compiled declaration list. *)
  Parameter seed_kinds : forall q f, kind (D.view (seed q)) f = program_kind (compile q) f.
  (** Seed slots use the checked program's compiled layout. *)
  Parameter seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  (** Seed construction produces a well-formed canonical relational database. *)
  Parameter seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  (** A plan is checked before the run starts. *)
  Parameter solve_checked : forall q lim, let cp := R.plan (compile q) in
    solve q lim = if R.check_plan (compile q) cp then R.run (compile q) cp lim (seed q)
      else (IterLimit, seed q).
  (** Points-to queries reflect canonical relation membership. *)
  Parameter points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) 5 [Val x; Val a] None) (points db x a).
  (** Every returned database is well formed and canonical. *)
  Parameter solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).

  (** A run with enough iteration fuel saturates. *)
  Parameter solve_saturates : forall q lim,
    N.to_nat (max_iter lim) >= 2 * R.herbrand (compile q) (seed q) + 2 ->
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

  (** The driver pays for compilation, seeding, planning, checking and the selected engine run. *)
  Parameter T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p + R.T_check_plan p cp +
      R.T_run p cp lim (seed q) + c_andersen)%N.
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
  Parameter F1_source_closed : forall q, pointer_closed q (may_points q).
  (** Every relation closed under the four source rules contains the least source relation. *)
  Parameter F2_source_least : forall q r, pointer_closed q r ->
    forall x a, may_points q x a -> r x a.
  (** Each generated rule is valid by its matching source closure rule. *)
  Parameter F3_rule_valid : forall q r rho, In r (rules V.t (compile q)) ->
    Forall (model_atom V.prim (andersen_model q) (program_kind (compile q)) rho)
      (query V.t r) ->
    model_actions V.prim (andersen_model q) (program_kind (compile q)) rho (actions V.t r).
  (** Initial database rows satisfy the least inclusion model. *)
  Parameter F4_seed_sat : forall q,
    sat V.merge (andersen_model q) (fun _ => tt) (D.view (seed q)).
  (** Engine derivations of points-to rows yield source inclusion derivations. *)
  Parameter F5_derives_source : forall q x a,
    derives V.prim (compile q) (D.view (seed q)) 5 [Val x; Val a] -> may_points q x a.
  (** Source inclusion derivations occur in every closed extension of the seed view. *)
  Parameter F6_closed_source : forall q w, closed V.prim V.merge (compile q) w ->
    (forall f k o, row (D.view (seed q)) f k o -> row w f k o) ->
    forall x a, may_points q x a -> row w 5 [Val x; Val a] None.
  (** Concrete updates preserve coverage by every source-closed relation. *)
  Parameter F7_step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  (** Wrapper composition retains each actual primitive cost. *)
  Parameter T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p + R.T_check_plan p cp +
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
