(** * Timed unification-based pointer analysis

    The timed module of the Steensgaard driver. It applies the law module to the timed runner,
    its facts and the ground theorems, derives the time function of each operation, and states
    the costs of seeding, querying and solving with the plan of the signature.
    For example, a points-to query costs three lookups in the final database.

    Main results
    - [seed_complexity] Seeding is linear in the constraints and initial pointers at the database
      unit.
    - [compile_complexity] Compilation emits a fixed program, so its cost is a constant, O(1).
    - [points_complexity] A points-to query is linear in the database unit and the bits of its
      two cells.
    - [solve_complexity] A solve costs its seed, the cube of the fixed program for planning, and
      the run.

    Builds on: SteensgaardSig, the Steensgaard driver, the timed runner and its facts, the
    lowering laws, the exact model and the ground theorems. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec Lower RunnerSig Runner RunnerFacts CongruenceRef Ground.
From Galois.Clients Require Import AndersenSig Andersen SteensgaardSig Steensgaard
  SteensgaardExact.
Import List.ListNotations.
Import ComplexityNotations.

Module SteensgaardT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D)
    <: STEENSGAARD_ALL V I J D R.
  (** The runner with its time functions, its facts, and the ground theorems. *)
  Module XT := RunnerT V I J D R.
  Module FT := RunnerFacts V I J D R XT.
  Module CR := CongruenceRef V.
  Module GT := Ground V I J D R XT FT LowerLaws CR.
  Include Steensgaard V I J D R XT FT GT.
  TimeFun compile.
  TimeFun lookup_id.
  TimeFun points.
  TimeFun seed.
  TimeFun solve.
  Definition k_rules : N := (R.c_run * 512 * 512 * 512 + 1)%N.
  Definition k_seed : N := (128 * (D.c_db + 1) * (k_rules + 32) * (k_rules + 32))%N.
  Definition k_wrap : N := 32%N.
  Definition c_steensgaard : N := (k_seed + D.c_db + k_wrap + 32)%N.

  (** Inspecting a lookup result adds only a constant number of constructor tests. *)
  Lemma lookup_id_time : forall f key db,
    (T_lookup_id f key db <= D.T_lookup f key db + 4)%N.
  Proof.
    intros f key db; time_unfold T_lookup_id; time_simpl; time_cases; lia.
  Qed.

  (** A stored constructor output fits in the database spending unit. *)
  Lemma lookup_id_unit : forall db f key i, D.wf db -> lookup_id f key db = Some i ->
    cell_bits V.encode (Id i) <= D.unit db.
  Proof.
    intros db f key i Hwf Hlookup.
    apply (proj1 (lookup_id_spec f key db i Hwf)) in Hlookup.
    pose proof (D.wmark_cells db f (map (D.canon db) key) (Some (Id i)) (Id i)
      Hwf Hlookup ltac:(apply in_or_app; right; left; reflexivity)) as Hbits.
    unfold D.unit; nia.
  Qed.

  (* STUB: [XT.T_seed_le] for [Unification.spec] and the facts of [q], whose rows have two
     values each, with the planning and loading costs of the fixed program as constants. *)
  Lemma T_seed_le : forall q,
    (T_seed q <= c_steensgaard *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_compile_le : forall q, (T_compile q <= c_steensgaard)%N.
  Proof.
    intro q; time_unfold T_compile; time_simpl; unfold c_steensgaard, k_wrap; lia.
  Qed.

  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_steensgaard * (N.of_nat (8 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof.
    intros db x a Hwf.
    pose proof (D.T_lookup_le Unification.Cell_code [Val x] db Hwf) as Hlookup_x.
    pose proof (D.T_lookup_le Unification.Cell_code [Val a] db Hwf) as Hlookup_a.
    pose proof (lookup_id_time Unification.Cell_code [Val x] db) as Htime_x.
    pose proof (lookup_id_time Unification.Cell_code [Val a] db) as Htime_a.
    cbn [length fold_right] in Hlookup_x, Hlookup_a.
    time_unfold T_points; time_simpl.
    destruct (lookup_id Unification.Cell_code [Val x] db) as [pointer |] eqn:Hx;
      destruct (lookup_id Unification.Cell_code [Val a] db) as [address |] eqn:Ha; time_simpl.
    - pose proof (D.T_lookup_le Unification.Deref_code [Id pointer] db Hwf) as Hlookup_p.
      pose proof (lookup_id_time Unification.Deref_code [Id pointer] db) as Htime_p.
      pose proof (lookup_id_unit db Unification.Cell_code [Val x] pointer Hwf Hx) as Hbits_p.
      cbn [length fold_right] in Hlookup_p.
      destruct (lookup_id Unification.Deref_code [Id pointer] db) as [target |] eqn:Ht; time_simpl.
      + pose proof (lookup_id_unit db Unification.Deref_code [Id pointer] target Hwf Ht) as Hbits_t.
        pose proof (Std.Pos.T_eqb_le target address) as Heq.
        cbn [cell_bits Pos.size_nat] in Hbits_t.
        apply time_of_nat_le in Hbits_p; apply time_of_nat_le in Hbits_t.
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *.
        unfold c_steensgaard, k_wrap; nia.
      + apply time_of_nat_le in Hbits_p.
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *.
        unfold c_steensgaard, k_wrap; nia.
    - rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *.
      unfold c_steensgaard, k_wrap; nia.
    - rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *.
      unfold c_steensgaard, k_wrap; nia.
    - rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *.
      unfold c_steensgaard, k_wrap; nia.
  Qed.

  (* STUB: [XT.T_solve_split] for the fixed program. *)
  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
  Proof. Admitted. (* STUB *)


  (** Seeding is linear in the input count at the final database's unit and identifier width. *)
  Lemma seed_complexity :
    T_seed q ∈ 𝑂(N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1))) for q.
  Proof.
    apply (bigO_intro _ _ _ c_steensgaard).
    intros q _; pose proof (T_seed_le q) as Hseed.
    rewrite !Nat2N.inj_mul; nia.
  Qed.

  (** The fixed pointer program has a constant compilation cost. *)
  Lemma compile_complexity : T_compile q ∈ 𝑂(0) for q.
  Proof.
    apply (bigO_intro _ _ _ c_steensgaard).
    intros q _; rewrite N.mul_0_r, N.add_0_l; apply T_compile_le.
  Qed.

  (** A points-to query costs its two encoded cells and the database lookup unit. *)
  Lemma points_complexity :
    T_points db (x : positive) (a : positive) ∈
      𝑂(N.of_nat (8 * D.unit db + cell_bits V.encode (Val x) + cell_bits V.encode (Val a) + 1))
      for (db, x, a) | D.wf db.
  Proof.
    apply (bigO_intro _ _ _ c_steensgaard).
    intros [[db x] a] Hwf; cbn [fst snd] in Hwf |- *.
    pose proof (T_points_le db x a Hwf) as Hpoints.
    rewrite !Nat2N.inj_add in Hpoints |- *; change V.t with positive in *; nia.
  Qed.

  (** Solving composes the seed and fixed-program plan with the engine's trace cost. *)
  Lemma solve_complexity :
    T_solve q lim ∈ 𝑂((N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)) +
      N.of_nat ((R.size_program (compile q) + 1) * (R.size_program (compile q) + 1) *
        (R.size_program (compile q) + 1)) +
      R.run_cost B U (compile q) (R.plan (compile q)) lim (seed q))%N)
      for (B, U, q, lim) |
        (D.ids (snd (solve q lim)) <= B)%N /\ D.unit (snd (solve q lim)) <= U.
  Proof.
    destruct seed_complexity as [cseed Hseed].
    destruct R.plan_complexity as [cplan Hplan].
    destruct R.run_complexity as [crun Hrun].
    apply (bigO_intro _ _ _ (2 * c_steensgaard + cseed + cplan + crun)%N).
    intros [[[B U] q] lim] [Hids Hunit].
    specialize (Hseed q I).
    specialize (Hplan (compile q) I).
    specialize (Hrun (B, U, compile q, R.plan (compile q), lim, seed q)).
    cbn beta iota zeta in Hrun.
    assert (Hready : R.plans_ok (compile q) (R.plan (compile q)) /\
      D.wf (seed q) /\ R.loaded (compile q) (R.plan (compile q)) (seed q) /\
      (D.ids (snd (R.run (compile q) (R.plan (compile q)) lim (seed q))) <= B)%N /\
      D.unit (snd (R.run (compile q) (R.plan (compile q)) lim (seed q))) <= U).
    { split; [apply R.plan_checked; apply program_sorted |].
      split; [exact (proj1 (seed_wf q)) |].
      split; [apply seed_loaded |].
      rewrite <- solve_run; split; assumption. }
    specialize (Hrun Hready).
    pose proof (T_solve_le q lim) as Hsolve.
    pose proof (T_compile_le q) as Hcompile.
    cbn beta iota zeta in Hseed, Hplan, Hsolve |- *.
    clear Hready Hids Hunit.
    nia.
  Qed.

  Lemma source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  Proof.
    exact pointer_congruence_closed.
  Qed.

  Lemma inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof.
    exact pointer_inclusion_unifies.
  Qed.

  (* STUB: [GT.solve_complete] with [Unification.pointer_congruence_congruent] at [V.prim]. *)
  Lemma saturated_equations : forall q lim db, solve q lim = (Saturated, db) ->
    forall t u, pointer_congruence q t u ->
    forall i j, represents (D.view db) (Id i) (Unification.encode_pointer_term t) ->
      represents (D.view db) (Id j) (Unification.encode_pointer_term u) -> same (D.view db) i j.
  Proof. Admitted. (* STUB *)

  Lemma endpoints_represented : forall q lim db x a,
    solve q lim = (Saturated, db) -> pointer_congruence q (Deref (Cell x)) (Cell a) ->
    (exists i, represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x)))) /\
    (exists j, represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a))).
  Proof.
    intros q lim db x a Hsolve Hcong.
    pose proof (solve_wf q lim) as Hvalid; rewrite Hsolve in Hvalid; cbn [snd] in Hvalid.
    pose proof (solve_covers q lim db Hsolve x a Hcong) as Hpoints.
    destruct (points_spec db x a (proj1 Hvalid) (proj2 Hvalid)) as [Hrep | Hnone]; [|discriminate].
    destruct Hrep as [i [j [Hi [Hj Hsame]]]]; split; [exists i | exists j]; assumption.
  Qed.

  Lemma step_covered : forall q instruction before after,
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

  (* STUB: [XT.T_solve_split], with the costs of the wrapper as constants. *)
  Lemma T_solve_split : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)
End SteensgaardT.
