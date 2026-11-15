(** * Placeholder Andersen driver

    This driver provides the pointer analysis interface.
    For example, its placeholder query returns false.
    Builds on: AndersenSig. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Clients Require Import AndersenSig.
Import List.ListNotations.

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

(** A relation atom reads the two values named by its source constraint. *)
Lemma andersen_model_pair : forall prim q rho f u v,
  program_kind andersen_program f = Some ORel ->
  model_atom prim (andersen_model q) (program_kind andersen_program) rho
    (Fun positive f [Var u; Var v] None) ->
  exists x y, rho u = Some (inr x) /\ rho v = Some (inr y) /\ pointer_relation q f x y.
Proof.
  intros prim q rho f u v Hkind [k [Hterms Hrelation]].
  rewrite Hkind in Hrelation; cbn [andersen_model rel] in Hrelation.
  destruct Hrelation as [x [y [Hk Hrelation]]]; subst k.
  inversion Hterms as [|term terms value values Hu Htail]; subst.
  inversion Htail as [|term terms value values Hv Hnil]; subst.
  exists x, y; exact (conj Hu (conj Hv Hrelation)).
Qed.

(** A justified source pointer satisfies the generated points-to action. *)
Lemma andersen_model_put : forall prim q rho u v x a,
  rho u = Some (inr x) -> rho v = Some (inr a) -> may_points q x a ->
  model_actions prim (andersen_model q) (program_kind andersen_program) rho
    [Put 5 [Var u; Var v] None].
Proof.
  intros prim q rho u v x a Hx Ha Hpoints.
  exists [inr x; inr a]; split.
  - constructor; [exact Hx | constructor; [exact Ha | constructor]].
  - split; [|exact I].
    exists x, a; split; [reflexivity |].
    unfold pointer_relation; right; right; right; right; auto.
Qed.

(** Each fixed inclusion rule implements the matching source closure constructor. *)
Lemma andersen_rule_valid : forall prim q r rho,
  In r (rules positive andersen_program) ->
  Forall (model_atom prim (andersen_model q) (program_kind andersen_program) rho)
    (query positive r) ->
  model_actions prim (andersen_model q) (program_kind andersen_program) rho
    (actions positive r).
Proof.
  intros prim q r rho Hin Hquery.
  destruct Hin as [Hr | [Hr | [Hr | [Hr | Hnone]]]]; [subst r | subst r | subst r | subst r |].
  - destruct (andersen_model_pair prim q rho 1 1 2 eq_refl (Forall_inv Hquery))
      as [x [a [Hx [Ha Hsource]]]].
    apply (andersen_model_put prim q rho 1 2 x a Hx Ha).
    apply May_addr; unfold pointer_relation in Hsource; intuition discriminate.
  - pose proof (Forall_inv Hquery) as Hcopy.
    pose proof (Forall_inv (Forall_inv_tail Hquery)) as Hpoints.
    destruct (andersen_model_pair prim q rho 2 1 2 eq_refl Hcopy)
      as [x [y [Hx [Hy Hsource]]]].
    destruct (andersen_model_pair prim q rho 5 2 3 eq_refl Hpoints)
      as [y' [a [Hy' [Ha Htarget]]]].
    assert (Heq : y' = y) by congruence; subst y'.
    apply (andersen_model_put prim q rho 1 3 x a Hx Ha).
    eapply May_copy with (y := y).
    + unfold pointer_relation in Hsource; intuition discriminate.
    + unfold pointer_relation in Htarget; intuition discriminate.
  - pose proof (Forall_inv Hquery) as Hload.
    pose proof (Forall_inv (Forall_inv_tail Hquery)) as Hlocatom.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hquery))) as Hpoints.
    destruct (andersen_model_pair prim q rho 3 1 2 eq_refl Hload)
      as [x [y [Hx [Hy Hsource]]]].
    destruct (andersen_model_pair prim q rho 5 2 3 eq_refl Hlocatom)
      as [y' [location [Hy' [Hlocation Hfirst]]]].
    destruct (andersen_model_pair prim q rho 5 3 4 eq_refl Hpoints)
      as [location' [a [Hlocation' [Ha Hsecond]]]].
    assert (Hy_eq : y' = y) by congruence; subst y'.
    assert (Hl_eq : location' = location) by congruence; subst location'.
    apply (andersen_model_put prim q rho 1 4 x a Hx Ha).
    eapply May_load with (y := y) (location := location).
    + unfold pointer_relation in Hsource; intuition discriminate.
    + unfold pointer_relation in Hfirst; intuition discriminate.
    + unfold pointer_relation in Hsecond; intuition discriminate.
  - pose proof (Forall_inv Hquery) as Hstore.
    pose proof (Forall_inv (Forall_inv_tail Hquery)) as Hlocatom.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hquery))) as Hpoints.
    destruct (andersen_model_pair prim q rho 4 1 2 eq_refl Hstore)
      as [x [y [Hx [Hy Hsource]]]].
    destruct (andersen_model_pair prim q rho 5 1 3 eq_refl Hlocatom)
      as [x' [location [Hx' [Hlocation Hfirst]]]].
    destruct (andersen_model_pair prim q rho 5 2 4 eq_refl Hpoints)
      as [y' [a [Hy' [Ha Hsecond]]]].
    assert (Hx_eq : x' = x) by congruence; subst x'.
    assert (Hy_eq : y' = y) by congruence; subst y'.
    apply (andersen_model_put prim q rho 3 4 location a Hlocation Ha).
    eapply May_store with (x := x) (y := y).
    + unfold pointer_relation in Hsource; intuition discriminate.
    + unfold pointer_relation in Hfirst; intuition discriminate.
    + unfold pointer_relation in Hsecond; intuition discriminate.
  - contradiction.
Qed.

Module AndersenCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: ANDERSEN_OPS V I J D R.
  (* STUB-CODE *)
  Definition compile (_ : pointer_input) : program V.t := andersen_program.
  (* STUB-CODE *)
  Definition seed (_ : pointer_input) : D.t := D.init [] [].
  (* STUB-CODE *)
  Definition solve (q : pointer_input) (_ : limits) : stop * D.t := (IterLimit, seed q).
  (* STUB-CODE *)
  Definition points (_ : D.t) (_ _ : positive) : bool := false.
End AndersenCode.

Module Andersen (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: ANDERSEN V I J D R.
  Include AndersenCode V I J D R.
  Lemma compile_rules : forall q, compile q = andersen_program.
  Proof.
    reflexivity.
  Qed.

  Lemma rules_valid : forall q, valid V.prim V.merge (andersen_model q) (compile q).
  Proof.
    intro q; split.
    - exact (andersen_rule_valid V.prim q).
    - intros f m k a b Hkind Hlat Hlat'; exact Hlat.
  Qed.

  Lemma seed_rows : forall q f k o, row (D.view (seed q)) f k o <-> pointer_seed_row q f k o.
  Proof. Admitted. (* STUB *)

  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  Proof. Admitted. (* STUB *)

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof. Admitted. (* STUB *)

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) 5 [Val x; Val a] None) (points db x a).
  Proof. Admitted. (* STUB *)

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof. Admitted. (* STUB *)

  Lemma solve_saturates : forall q lim,
    N.to_nat (max_iter lim) >= 2 * R.herbrand (compile q) (seed q) + 2 ->
    fst (solve q lim) = Saturated.
  Proof. Admitted. (* STUB *)

  Lemma solve_exact : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> may_points q x a.
  Proof. Admitted. (* STUB *)

End Andersen.

Module AndersenT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D) <: ANDERSEN_ALL V I J D R.
  Include Andersen V I J D R.
  TimeFun compile.
  TimeFun seed.
  TimeFun solve.
  TimeFun points.
  Definition c_andersen : N := 1. (* STUB *)
  Definition k_rules : N := 1. (* STUB *)
  Definition k_seed : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
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

  Lemma F1_source_closed : forall q, pointer_closed q (may_points q).
  Proof.
    exact pointer_source_closed.
  Qed.

  Lemma F2_source_least : forall q r, pointer_closed q r ->
    forall x a, may_points q x a -> r x a.
  Proof.
    exact pointer_source_least.
  Qed.

  Lemma F3_rule_valid : forall q r rho, In r (rules V.t (compile q)) ->
    Forall (model_atom V.prim (andersen_model q) (program_kind (compile q)) rho)
      (query V.t r) ->
    model_actions V.prim (andersen_model q) (program_kind (compile q)) rho (actions V.t r).
  Proof.
    exact (andersen_rule_valid V.prim).
  Qed.

  Lemma F4_seed_sat : forall q,
    sat V.merge (andersen_model q) (fun _ => tt) (D.view (seed q)).
  Proof. Admitted. (* STUB *)

  Lemma F5_derives_source : forall q x a,
    derives V.prim (compile q) (D.view (seed q)) 5 [Val x; Val a] -> may_points q x a.
  Proof. Admitted. (* STUB *)

  Lemma F6_closed_source : forall q w, closed V.prim V.merge (compile q) w ->
    (forall f k o, row (D.view (seed q)) f k o -> row w f k o) ->
    forall x a, may_points q x a -> row w 5 [Val x; Val a] None.
  Proof. Admitted. (* STUB *)

  Lemma F7_step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  Proof.
    exact pointer_step_covered.
  Qed.

  Lemma T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)

End AndersenT.

Module AndersenSound (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : ANDERSEN V I J D R) (L : POINTER_LINK) <: ANDERSEN_SOUND V I J D R A L.
  (** The least source relation contains all seeds and is closed under its four instructions. *)
  Lemma F1_source_closed : forall q, pointer_closed q (may_points q).
  Proof.
    exact pointer_source_closed.
  Qed.

  (** Each concrete instruction preserves coverage by a source-closed relation. *)
  Lemma F7_step_covered : forall q r instruction before after,
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
        eapply F7_step_covered; [apply F1_source_closed | exact Hin | exact IH | exact Hexec]. }
    intros x a Hget; apply (proj2 (A.solve_exact q lim db Hsolve x a)).
    apply Hcovered; exact Hget.
  Qed.
End AndersenSound.
