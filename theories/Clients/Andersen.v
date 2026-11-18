(** * Inclusion-based pointer analysis driver

    This driver compiles source constraints and queries their least inclusion solution.
    The source-semantics lemmas shared with the Steensgaard client stay here.
    For example, an address constraint seeds a row used by the first inclusion rule.

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

    Builds on: AndersenSig and the relational database and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Runner.
From Galois.Clients Require Import AndersenSig.
Import List.ListNotations.
Import ComplexityNotations.

(** The inductive inclusion relation contains the seeds and obeys all source constraints. *)
Lemma pointer_source_closed : forall q, pointer_closed q (may_points q).
Proof.
  intro q; unfold pointer_closed; repeat split.
  - intros x a Hinitial; apply May_initial; exact Hinitial.
  - intros x a Haddr; apply May_addr; exact Haddr.
  - intros x y a Hcopy Hpoints; eapply May_copy; eassumption.
  - intros x y location a Hload Hlocation Hpoints; eapply May_load; eassumption.
  - intros x y location a Hstore Hlocation Hpoints; eapply May_store; eassumption.
Qed.

(** Induction over source derivations gives their least closed relation. *)
Lemma pointer_source_least : forall q r, pointer_closed q r ->
  forall x a, may_points q x a -> r x a.
Proof.
  intros q r [Hinitial [Haddr [Hcopy [Hload Hstore]]]] x a Hpoints.
  induction Hpoints; eauto.
Qed.

(** Updating a single pointer preserves coverage when its new target is covered. *)
Lemma pointer_set_covered : forall r memory x a, memory_covered r memory -> r x a ->
  memory_covered r (PTrieCode.set x a memory).
Proof.
  intros r memory x a Hcovered Hnew y b Hget.
  destruct (Pos.eq_dec y x) as [Heq | Hneq].
  - subst y; rewrite PTrie.get_set_same in Hget; inversion Hget; subst b; exact Hnew.
  - rewrite PTrie.get_set_other in Hget by exact Hneq; apply Hcovered; exact Hget.
Qed.

(** Each concrete instruction preserves any source-closed covering relation. *)
Lemma pointer_step_covered : forall q r instruction before after,
  pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
  pointer_exec instruction before = Some after -> memory_covered r after.
Proof.
  intros q r instruction before after [Hinitial [Haddr [Hcopy [Hload Hstore]]]]
    Hin Hcovered Hexec.
  destruct instruction as [x a | x y | x y | x y]; cbn [pointer_exec] in Hexec.
  - inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    apply Haddr; exact Hin.
  - destruct (trie_get y before) as [a |] eqn:Hy; [|discriminate].
    inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    eapply Hcopy; [exact Hin | apply Hcovered; exact Hy].
  - destruct (trie_get y before) as [location |] eqn:Hy; [|discriminate].
    destruct (trie_get location before) as [a |] eqn:Hlocation; [|discriminate].
    inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    eapply Hload; [exact Hin | apply Hcovered; exact Hy | apply Hcovered; exact Hlocation].
  - destruct (trie_get x before) as [location |] eqn:Hx; [|discriminate].
    destruct (trie_get y before) as [a |] eqn:Hy; [|discriminate].
    inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    eapply Hstore; [exact Hin | apply Hcovered; exact Hx | apply Hcovered; exact Hy].
Qed.

(** * Code *)

Module AndersenCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: ANDERSEN_OPS V I J D R.
  Module X := RunnerCode V I J D R.
  Definition compile (_ : pointer_input) : program V.t := andersen_program.
  Definition seed (q : pointer_input) : D.t :=
    X.seed (compile q) (MayPoints.facts q).
  Definition solve (q : pointer_input) (lim : limits) : stop * D.t :=
    X.solve (compile q) (MayPoints.facts q) lim.
  Definition points (db : D.t) (x a : positive) : bool :=
    X.holds MayPoints.may_points_code [x; a] db.
End AndersenCode.

(** * Laws *)

Module Andersen (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: ANDERSEN V I J D R.
  Include AndersenCode V I J D R.

  (** The derived program passes the source sort checker. *)
  Lemma program_sorted : forall q, program_ok (compile q).
  Proof.
    intro q; apply (proj1 (check_program_spec V.t (compile q))); vm_compute; reflexivity.
  Qed.

  Lemma compile_rules : forall q, compile q = andersen_program.
  Proof.
    reflexivity.
  Qed.

  (* STUB: RELATIONAL_PLAN.seed_rows for [MayPoints.spec], with [rows_ok] by vm_compute. *)
  Lemma seed_rows : forall q f k o, row (D.view (seed q)) f k o <->
    o = None /\ exists vs, k = map Val vs /\ In (f, vs) (MayPoints.facts q).
  Proof. Admitted. (* STUB *)

  (* STUB: RELATIONAL_PLAN.seed_ready for [MayPoints.spec], with [spec_ok] by vm_compute. *)
  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  (* STUB: RELATIONAL_PLAN.seed_ready for [MayPoints.spec], with [spec_ok] by vm_compute. *)
  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  Proof. Admitted. (* STUB *)

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof.
    reflexivity.
  Qed.

  (* STUB: RELATIONAL.holds_spec at [MayPoints.may_points_code], and the sorts of the program
     give an output-free row. *)
  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) MayPoints.may_points_code [Val x; Val a] None)
      (points db x a).
  Proof. Admitted. (* STUB *)

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    destruct (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hwf [Hcanonical Hloaded]]; auto.
  Qed.

  Lemma solve_saturates : forall q lim,
    N.to_nat (max_iter lim) >= 2 * R.herbrand (compile q) (seed q) + 3 ->
    fst (solve q lim) = Saturated.
  Proof.
    intros q lim Hfuel; rewrite solve_run; apply R.run_terminates.
    - apply R.plan_checked; apply program_sorted.
    - exact (proj1 (seed_wf q)).
    - apply seed_loaded.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - exact (proj2 (proj2 (seed_wf q))).
    - exact Hfuel.
  Qed.

  (* STUB: RELATIONAL.solve_sound and solve_complete with [MayPoints.may_points_spec], and
     [points_spec]. *)
  Lemma solve_exact : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> may_points q x a.
  Proof. Admitted. (* STUB *)
End Andersen.

(** * Time *)

Module AndersenT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D)
    <: ANDERSEN_ALL V I J D R.
  Include Andersen V I J D R.
  TimeFun compile.
  (* STUB-CODE: the runner has no time functions yet. *)
  Definition T_seed (q : pointer_input) : N := 1.
  (* STUB-CODE: the runner has no time functions yet. *)
  Definition T_solve (q : pointer_input) (lim : limits) : N := 1.
  (* STUB-CODE: the runner has no time functions yet. *)
  Definition T_points (db : D.t) (x a : positive) : N := 1.
  Definition k_rules : N := 1. (* STUB *)
  Definition k_seed : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Definition c_andersen : N := 1. (* STUB *)

  Lemma T_seed_le : forall q,
    (T_seed q <= c_andersen *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_compile_le : forall q, (T_compile q <= c_andersen)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_andersen * (N.of_nat (3 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof. Admitted. (* STUB *)

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

  Lemma T_solve_split : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)
End AndersenT.

Module AndersenSound (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : ANDERSEN V I J D R) (L : POINTER_LINK) <: ANDERSEN_SOUND V I J D R A L.
  (** The least source relation contains all seeds and is closed under its four instructions. *)
  Lemma source_closed : forall q, pointer_closed q (may_points q).
  Proof.
    exact pointer_source_closed.
  Qed.

  (** Each concrete instruction preserves coverage by a source-closed relation. *)
  Lemma step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  Proof.
    exact pointer_step_covered.
  Qed.

  (** Every reachable concrete pointer appears in every saturated analysis result. *)
  Lemma concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
  Proof.
    intros q lim db s Hsolve Hreach.
    assert (Hcovered : memory_covered (may_points q) (L.memory s)).
    { induction Hreach as [s Hinitial | s t Hreach IH Hstep].
      - intros y b Hy; apply May_initial; eapply L.initial_coverage; eassumption.
      - destruct (L.step_update q s t Hstep) as [instruction [Hin Hexec]].
        eapply step_covered; [apply source_closed | exact Hin | exact IH | exact Hexec]. }
    intros x a Hget; apply (proj2 (A.solve_exact q lim db Hsolve x a)).
    apply Hcovered; exact Hget.
  Qed.
End AndersenSound.
