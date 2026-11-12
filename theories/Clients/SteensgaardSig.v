(** * Unification-based pointer analysis

    Four instruction equations generate a congruence over cells and dereferences.
    For example, loading from y equates the result's pointee with y's second dereference.
    Builds on: the uniform-cell source semantics and the engine's identifier congruence. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Clients Require Import AndersenSig.
Import List.ListNotations.

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

Fixpoint pointer_denote {A} (cell : positive -> A) (deref : A -> A) (t : pointer_term) : A :=
  match t with
  | Cell x => cell x
  | Deref u => deref (pointer_denote cell deref u)
  end.
TimeFun pointer_denote.

Fixpoint pointer_expression (t : pointer_term) : expr (V := positive) :=
  match t with
  | Cell x => EApp 6 [ELit x]
  | Deref u => EApp 7 [pointer_expression u]
  end.
TimeFun pointer_expression.

(** This provider interprets exactly the source congruence in a unary algebra. *)
Module Type POINTER_QUOTIENT.
  (* spec: carrier cell deref *)
  Parameter carrier : pointer_input -> Type.
  Parameter cell : forall q, positive -> carrier q.
  Parameter deref : forall q, carrier q -> carrier q.
  (** Algebra equality reflects the independently generated source congruence. *)
  Parameter source_exact : forall q t u,
    pointer_denote (cell q) (deref q) t = pointer_denote (cell q) (deref q) u <->
      pointer_congruence q t u.
End POINTER_QUOTIENT.

Definition steensgaard_program : program positive := Program positive
  [Decl 1 2 ORel; Decl 2 2 ORel; Decl 3 2 ORel; Decl 4 2 ORel; Decl 6 1 OId; Decl 7 1 OId]
  [Rule positive [Fun positive 1 [Var 1; Var 2] None]
    [Make 3 6 [Var 1]; Make 4 6 [Var 2]; Make 5 7 [Var 3]; Union (Var 5) (Var 4)];
   Rule positive [Fun positive 2 [Var 1; Var 2] None]
    [Make 3 6 [Var 1]; Make 4 6 [Var 2]; Make 5 7 [Var 3]; Make 6 7 [Var 4];
      Union (Var 5) (Var 6)];
   Rule positive [Fun positive 3 [Var 1; Var 2] None]
    [Make 3 6 [Var 1]; Make 4 6 [Var 2]; Make 5 7 [Var 3]; Make 6 7 [Var 4];
      Make 7 7 [Var 6]; Union (Var 5) (Var 7)];
   Rule positive [Fun positive 4 [Var 1; Var 2] None]
    [Make 3 6 [Var 1]; Make 4 6 [Var 2]; Make 5 7 [Var 3]; Make 6 7 [Var 4];
      Make 7 7 [Var 5]; Union (Var 7) (Var 6)]].

Definition steensgaard_seed_row (q : pointer_input) f (k : list (cell positive))
    (o : option (cell positive)) :=
  o = None /\ exists x y, k = [Val x; Val y] /\
    ((f = 1%positive /\ (In (Addr x y) (constraints q) \/ In (x, y) (initial_pointers q))) \/
     (f = 2%positive /\ In (Copy x y) (constraints q)) \/
     (f = 3%positive /\ In (Load x y) (constraints q)) \/
     (f = 4%positive /\ In (Store x y) (constraints q))).

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
  (** Seeding includes source constraints and treats initial pointers as address equations. *)
  Parameter seed_rows : forall q f k o,
    row (D.view (seed q)) f k o <-> steensgaard_seed_row q f k o.
  (** Seed relation and constructor kinds agree with the compiled declarations. *)
  Parameter seed_kinds : forall q f, kind (D.view (seed q)) f = program_kind (compile q) f.
  (** Seed slots use the checked program's compiled layout. *)
  Parameter seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  (** Seeding produces a canonical well-formed database. *)
  Parameter seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  (** A plan is checked before the engine is called. *)
  Parameter solve_checked : forall q lim, let cp := R.plan (compile q) in
    solve q lim = if R.check_plan (compile q) cp then R.run (compile q) cp lim (seed q)
      else (IterLimit, seed q).
  (** Queries test whether the pointee term equals the addressed cell in the final congruence. *)
  Parameter points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j)
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
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p + R.T_check_plan p cp +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
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
  Parameter F1_source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  (** Every inclusion-derived pointer belongs to the unification approximation. *)
  Parameter F2_inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  (** Saturation makes each source equation's two ground terms equal in the database. *)
  Parameter F3_saturated_equations : forall q lim db, solve q lim = (Saturated, db) ->
    forall t u, pointer_congruence q t u ->
    forall i j, represents (D.view db) (Id i) (pointer_expression t) ->
      represents (D.view db) (Id j) (pointer_expression u) -> same (D.view db) i j.
  (** Congruence consequences queried as pointers have represented endpoint terms. *)
  Parameter F4_endpoints_represented : forall q lim db x a,
    solve q lim = (Saturated, db) -> pointer_congruence q (Deref (Cell x)) (Cell a) ->
    (exists i, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x)))) /\
    (exists j, represents (D.view db) (Id j) (pointer_expression (Cell a))).
  (** Concrete instruction updates retain coverage by the source congruence. *)
  Parameter F6_step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  (** Wrapper composition includes every actual engine and database primitive. *)
  Parameter T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p + R.T_check_plan p cp +
      R.T_run p cp lim (seed q) + k_wrap)%N.
End STEENSGAARD_PLAN.

Module Type STEENSGAARD_ALL (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D) :=
  STEENSGAARD_T V I J D R <+ STEENSGAARD_PLAN V I J D R.

Module Type STEENSGAARD_SOUND (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (L : POINTER_LINK) (Q : POINTER_QUOTIENT).
  Definition source_relation q f x y :=
    (f = 1%positive /\ (In (Addr x y) (constraints q) \/ In (x, y) (initial_pointers q))) \/
    (f = 2%positive /\ In (Copy x y) (constraints q)) \/
    (f = 3%positive /\ In (Load x y) (constraints q)) \/
    (f = 4%positive /\ In (Store x y) (constraints q)).
  Definition concrete_model q : model (V := V.t) :=
    Model (Q.carrier q)
      (fun f args => exists x y, args = [inr x; inr y] /\ source_relation q f x y)
      (fun f args =>
        match f, args with
        | 6%positive, [inr x] => Q.cell q x
        | 7%positive, [inl address] => Q.deref q address
        | _, _ => Q.cell q 1%positive
        end)
      (fun _ _ _ => False).
  (** Address constraints equate the pointer's dereference with the addressed cell. *)
  Parameter addr_equation : forall q x a,
    In (Addr x a) (constraints q) \/ In (x, a) (initial_pointers q) ->
    Q.deref q (Q.cell q x) = Q.cell q a.
  (** Copy constraints equate their two dereference terms. *)
  Parameter copy_equation : forall q x y, In (Copy x y) (constraints q) ->
    Q.deref q (Q.cell q x) = Q.deref q (Q.cell q y).
  (** Load constraints equate a result's dereference with the operand's second dereference. *)
  Parameter load_equation : forall q x y, In (Load x y) (constraints q) ->
    Q.deref q (Q.cell q x) = Q.deref q (Q.deref q (Q.cell q y)).
  (** Store constraints equate the destination's second dereference with the stored pointer. *)
  Parameter store_equation : forall q x y, In (Store x y) (constraints q) ->
    Q.deref q (Q.deref q (Q.cell q x)) = Q.deref q (Q.cell q y).
  (** Source equations establish validity of all generated union rules. *)
  Parameter rules_valid : forall q, valid V.prim V.merge (concrete_model q) (A.compile q).

  (** Saturated query answers are exactly the source congruence approximation. *)
  Parameter solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).

  (** Every reachable concrete pointer is included in every saturated unification result. *)
  Parameter concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
  (* SIG-QUESTION: the exact source-congruence quotient needs a provider. *)
End STEENSGAARD_SOUND.
