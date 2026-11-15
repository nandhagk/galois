(** * Placeholder Steensgaard driver

    This driver provides the pointer analysis interface.
    For example, its placeholder query returns false.
    Builds on: SteensgaardSig. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Clients Require Import AndersenSig Andersen SteensgaardSig.
Import List.ListNotations.

(** The unary congruence covers every source pointer instruction. *)
Lemma pointer_congruence_closed : forall q,
  pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
Proof.
  intro q; unfold pointer_closed; repeat split.
  - intros x a Hinitial; apply Cong_initial; exact Hinitial.
  - intros x a Haddr; apply Cong_addr; exact Haddr.
  - intros x y a Hcopy Hpoints; eapply Cong_trans; [apply Cong_copy; exact Hcopy | exact Hpoints].
  - intros x y location a Hload Hlocation Hpoints.
    eapply Cong_trans; [apply Cong_load; exact Hload |].
    eapply Cong_trans; [apply Cong_deref; exact Hlocation | exact Hpoints].
  - intros x y location a Hstore Hlocation Hpoints.
    eapply Cong_trans; [apply Cong_sym; apply Cong_deref; exact Hlocation |].
    eapply Cong_trans; [apply Cong_store; exact Hstore | exact Hpoints].
Qed.

(** Every inclusion derivation is also a congruence derivation. *)
Lemma pointer_inclusion_unifies : forall q x a, may_points q x a ->
  pointer_congruence q (Deref (Cell x)) (Cell a).
Proof.
  intros q x a Hpoints.
  eapply (pointer_source_least q
    (fun y b => pointer_congruence q (Deref (Cell y)) (Cell b))).
  - apply pointer_congruence_closed.
  - exact Hpoints.
Qed.

Module SteensgaardCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: STEENSGAARD_OPS V I J D R.
  (* STUB-CODE *)
  Definition compile (_ : pointer_input) : program V.t := steensgaard_program.
  (* STUB-CODE *)
  Definition seed (_ : pointer_input) : D.t := D.init [] [].
  (* STUB-CODE *)
  Definition solve (q : pointer_input) (_ : limits) : stop * D.t := (IterLimit, seed q).
  (* STUB-CODE *)
  Definition points (_ : D.t) (_ _ : positive) : bool := false.
End SteensgaardCode.

Module Steensgaard (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: STEENSGAARD V I J D R.
  Include SteensgaardCode V I J D R.
  Lemma compile_rules : forall q, compile q = steensgaard_program.
  Proof.
    reflexivity.
  Qed.

  Lemma seed_rows : forall q f k o,
    row (D.view (seed q)) f k o <-> steensgaard_seed_row q f k o.
  Proof. Admitted. (* STUB *)

  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  Proof. Admitted. (* STUB *)

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof. Admitted. (* STUB *)

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j)
      (points db x a).
  Proof. Admitted. (* STUB *)

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof. Admitted. (* STUB *)

  Lemma solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
  Proof. Admitted. (* STUB *)

End Steensgaard.

Module SteensgaardT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D) <: STEENSGAARD_ALL V I J D R.
  Include Steensgaard V I J D R.
  TimeFun compile.
  TimeFun seed.
  TimeFun solve.
  TimeFun points.
  Definition c_steensgaard : N := 1. (* STUB *)
  Definition k_rules : N := 1. (* STUB *)
  Definition k_seed : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Lemma T_seed_le : forall q,
    (T_seed q <= c_steensgaard *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_compile_le : forall q, (T_compile q <= c_steensgaard)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_steensgaard * (N.of_nat (8 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  Proof.
    exact pointer_congruence_closed.
  Qed.

  Lemma F2_inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof.
    exact pointer_inclusion_unifies.
  Qed.

  Lemma F3_saturated_equations : forall q lim db, solve q lim = (Saturated, db) ->
    forall t u, pointer_congruence q t u ->
    forall i j, represents (D.view db) (Id i) (pointer_expression t) ->
      represents (D.view db) (Id j) (pointer_expression u) -> same (D.view db) i j.
  Proof. Admitted. (* STUB *)

  Lemma F4_endpoints_represented : forall q lim db x a,
    solve q lim = (Saturated, db) -> pointer_congruence q (Deref (Cell x)) (Cell a) ->
    (exists i, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x)))) /\
    (exists j, represents (D.view db) (Id j) (pointer_expression (Cell a))).
  Proof. Admitted. (* STUB *)

  Lemma F6_step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  Proof.
    intros q instruction before after Hin Hcovered Hexec.
    eapply pointer_step_covered.
    - apply pointer_congruence_closed.
    - exact Hin.
    - exact Hcovered.
    - exact Hexec.
  Qed.

  Lemma T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)

End SteensgaardT.

Module SteensgaardSound (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (L : POINTER_LINK) <: STEENSGAARD_SOUND V I J D R A L.
  (** The source congruence contains every seed and is closed under its pointer rules. *)
  Lemma F1_source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  Proof.
    exact pointer_congruence_closed.
  Qed.

  (** Every inclusion-derived pointer belongs to the source congruence. *)
  Lemma F2_inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof.
    exact pointer_inclusion_unifies.
  Qed.

  (** Each concrete instruction preserves coverage by the source congruence. *)
  Lemma F6_step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  Proof.
    intros q instruction before after Hin Hcovered Hexec.
    eapply pointer_step_covered.
    - apply F1_source_closed.
    - exact Hin.
    - exact Hcovered.
    - exact Hexec.
  Qed.

  (** Every reachable concrete pointer is included in every saturated unification result. *)
  Lemma concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
  Proof.
    intros q lim db s Hsolve Hreach.
    assert (Hcovered : memory_covered
      (fun y b => pointer_congruence q (Deref (Cell y)) (Cell b)) (L.memory s)).
    { induction Hreach as [s Hinitial | s t Hreach IH Hstep].
      - intros y b Hy; apply Cong_initial; eapply L.initial_coverage; eassumption.
      - destruct (L.step_update q s t Hstep) as [instruction [Hin Hexec]].
        eapply F6_step_covered; [exact Hin | exact IH | exact Hexec]. }
    intros x a Hget; apply (A.solve_covers q lim db Hsolve x a).
    apply Hcovered; exact Hget.
  Qed.
End SteensgaardSound.

Module SteensgaardExact (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (Q : POINTER_QUOTIENT)
    <: STEENSGAARD_EXACT V I J D R A Q.
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
  Lemma addr_equation : forall q x a,
    In (Addr x a) (constraints q) \/ In (x, a) (initial_pointers q) ->
    Q.deref q (Q.cell q x) = Q.cell q a.
  Proof.
    intros q x a Hsource.
    apply (proj2 (Q.source_exact q (Deref (Cell x)) (Cell a))).
    destruct Hsource as [Haddr | Hinitial].
    - apply Cong_addr; exact Haddr.
    - apply Cong_initial; exact Hinitial.
  Qed.
  (** Copy constraints equate their two dereference terms. *)
  Lemma copy_equation : forall q x y, In (Copy x y) (constraints q) ->
    Q.deref q (Q.cell q x) = Q.deref q (Q.cell q y).
  Proof.
    intros q x y Hcopy.
    apply (proj2 (Q.source_exact q (Deref (Cell x)) (Deref (Cell y)))).
    apply Cong_copy; exact Hcopy.
  Qed.
  (** Load constraints equate a result's dereference with the operand's second dereference. *)
  Lemma load_equation : forall q x y, In (Load x y) (constraints q) ->
    Q.deref q (Q.cell q x) = Q.deref q (Q.deref q (Q.cell q y)).
  Proof.
    intros q x y Hload.
    apply (proj2 (Q.source_exact q (Deref (Cell x)) (Deref (Deref (Cell y))))).
    apply Cong_load; exact Hload.
  Qed.
  (** Store constraints equate the destination's second dereference with the stored pointer. *)
  Lemma store_equation : forall q x y, In (Store x y) (constraints q) ->
    Q.deref q (Q.deref q (Q.cell q x)) = Q.deref q (Q.cell q y).
  Proof.
    intros q x y Hstore.
    apply (proj2 (Q.source_exact q (Deref (Deref (Cell x))) (Deref (Cell y)))).
    apply Cong_store; exact Hstore.
  Qed.
  (** Source equations establish validity of all generated union rules. *)
  Lemma rules_valid : forall q, valid V.prim V.merge (concrete_model q) (A.compile q).
  Proof. Admitted. (* STUB *)

  (** Saturated query answers are exactly the source congruence approximation. *)
  Lemma solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)
End SteensgaardExact.
