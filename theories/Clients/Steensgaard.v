(** * Unification-based pointer analysis driver

    This driver seeds the derived unification program with the source equations and queries the
    constructor congruence that its saturation computes.
    For example, an address constraint equates a pointer's dereference with an addressed cell.

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

    Builds on: SteensgaardSig, Andersen, the runner and the database and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec RunnerSig Runner.
From Galois.Clients Require Import AndersenSig Andersen SteensgaardSig.
Import List.ListNotations.
Import ComplexityNotations.

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
    (R : RUN_OPS V I J D) (X : RUNNER_OPS V I J D R) <: STEENSGAARD_OPS V I J D R.
  Definition compile (_ : pointer_input) : program V.t := steensgaard_program.
  Definition seed (q : pointer_input) : D.t := X.seed (compile q) (Unification.facts q).
  Definition solve (q : pointer_input) (lim : limits) : stop * D.t :=
    X.solve (compile q) (Unification.facts q) lim.
  Definition lookup_id (f : positive) (key : list (cell V.t)) (db : D.t) : option positive :=
    match fst (D.lookup f key db) with
    | Some (Some (Id i)) => Some i
    | _ => None
    end.
  Definition points (db : D.t) (x a : positive) : bool :=
    match lookup_id Unification.Cell_code [Val x] db,
          lookup_id Unification.Cell_code [Val a] db with
    | Some pointer, Some address =>
      match lookup_id Unification.Deref_code [Id pointer] db with
      | Some target => Pos.eqb target address
      | None => false
      end
    | _, _ => false
    end.
End SteensgaardCode.

Module Steensgaard (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (X : RUNNER V I J D R) <: STEENSGAARD V I J D R.
  Include SteensgaardCode V I J D R X.

  (** The derived unification program passes the source sort checker. *)
  Lemma program_sorted : forall q, program_ok (compile q).
  Proof.
    intro q; apply (proj1 (check_program_spec V.t (compile q))); vm_compute; reflexivity.
  Qed.

  Lemma compile_rules : forall q, compile q = steensgaard_program.
  Proof.
    reflexivity.
  Qed.

  (* STUB: RELATIONAL_PLAN.seed_rows for [Unification.spec], with [rows_ok] by vm_compute. *)
  Lemma seed_rows : forall q f k o, row (D.view (seed q)) f k o <->
    o = None /\ exists vs, k = map Val vs /\ In (f, vs) (Unification.facts q).
  Proof. Admitted. (* STUB *)

  (* STUB: RELATIONAL_PLAN.seed_ready for [Unification.spec], with [spec_ok] by vm_compute. *)
  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  (* STUB: RELATIONAL_PLAN.seed_ready for [Unification.spec], with [spec_ok] by vm_compute. *)
  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  Proof. Admitted. (* STUB *)

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof.
    intros q lim.
    unfold solve, seed.
    apply X.solve_unfold.
  Qed.

  (** Identifier lookup is exactly membership at the canonicalized query key. *)
  Lemma lookup_id_spec : forall f key db i, D.wf db ->
    lookup_id f key db = Some i <->
      row (D.view db) f (map (D.canon db) key) (Some (Id i)).
  Proof.
    intros f key db i Hwf.
    change ((match fst (D.lookup f key db) with
      Some (Some (Id j)) => Some j | _ => None end) = Some i <->
      row (D.view db) f (map (D.canon db) key) (Some (Id i))).
    rewrite (proj1 (D.lookup_spec f key db Hwf)).
    destruct (D.old db f (map (D.canon db) key)) as [[c |] |] eqn:Hlookup.
    - destruct c as [j | v]; split; intro H.
      + inversion H; subst j; apply (proj1 (D.old_row db f _ _ Hwf)); exact Hlookup.
      + apply (proj2 (D.old_row db f _ _ Hwf)) in H; congruence.
      + discriminate.
      + apply (proj2 (D.old_row db f _ _ Hwf)) in H; congruence.
    - split; intro H; [discriminate |].
      apply (proj2 (D.old_row db f _ _ Hwf)) in H; congruence.
    - split; intro H; [discriminate |].
      apply (proj2 (D.old_row db f _ _ Hwf)) in H; congruence.
  Qed.

  (** An identifier stored as a canonical output is its own representative. *)
  Lemma canonical_output : forall db f key i, D.canonical db ->
    row (D.view db) f key (Some (Id i)) -> D.repr db i = i.
  Proof.
    intros db f key i Hcanonical Hrow.
    apply (Hcanonical f key (Some (Id i)) Hrow i).
    apply in_or_app; right; left; reflexivity.
  Qed.

  (** A represented cell name is a constructor row up to identifier equality. *)
  Lemma represents_cell : forall db x i,
    represents (D.view db) (Id i) (Unification.encode_pointer_term (Cell x)) <->
      exists j, row (D.view db) Unification.Cell_code [Val x] (Some (Id j)) /\ same (D.view db) i j.
  Proof.
    intros db x i; split.
    - intro Hrep; inversion Hrep as [|f key i' j args Hrow Hsame Hargs]; subst.
      inversion Hargs as [|c expression key' args' Hcell Htail]; subst.
      inversion Htail; subst; inversion Hcell; subst; exists j; auto.
    - intros [j [Hrow Hsame]].
      eapply rep_app; [exact Hrow | exact Hsame |].
      constructor; [constructor | constructor].
  Qed.

  (** A represented dereference follows the canonical cell row and its dereference row. *)
  Lemma represents_deref : forall db x i, D.wf db -> D.canonical db ->
    (represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x))) <->
      exists cell_id target, row (D.view db) Unification.Cell_code [Val x] (Some (Id cell_id)) /\
        row (D.view db) Unification.Deref_code [Id cell_id] (Some (Id target)) /\
        same (D.view db) i target).
  Proof.
    intros db x i Hwf Hcanonical; split.
    - intro Hrep; inversion Hrep as [|f key i' target args Hrow Hsame Hargs]; subst.
      inversion Hargs as [|c expression key' args' Hcell Htail]; subst.
      inversion Htail; subst.
      destruct c as [cell_id | value]; [|inversion Hcell].
      apply represents_cell in Hcell; destruct Hcell as [stored [Hstored Hequal]].
      assert (Hcell_canonical : D.repr db cell_id = cell_id).
      { apply (Hcanonical Unification.Deref_code [Id cell_id] (Some (Id target)) Hrow cell_id).
        left; reflexivity. }
      pose proof (canonical_output db Unification.Cell_code [Val x] stored Hcanonical Hstored)
        as Hstored_canonical.
      apply (proj1 (D.same_repr db cell_id stored Hwf)) in Hequal.
      assert (Heq : cell_id = stored) by congruence; subst stored.
      exists cell_id, target; auto.
    - intros [cell_id [target [Hcell [Htarget Hsame]]]].
      eapply rep_app; [exact Htarget | exact Hsame |].
      constructor; [|constructor].
      apply represents_cell; exists cell_id; split; [exact Hcell |].
      apply (proj2 (D.same_repr db cell_id cell_id Hwf)); reflexivity.
  Qed.

  (** A positive executable query supplies represented and equal endpoint identifiers. *)
  Lemma points_sound : forall db x a, D.wf db -> D.canonical db -> points db x a = true ->
    exists i j,
      represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x))) /\
      represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a)) /\
      same (D.view db) i j.
  Proof.
    intros db x a Hwf Hcanonical.
    change ((match lookup_id Unification.Cell_code [Val x] db,
      lookup_id Unification.Cell_code [Val a] db with
      | Some pointer, Some address =>
        match lookup_id Unification.Deref_code [Id pointer] db with
        | Some target => Pos.eqb target address
        | None => false
        end
      | _, _ => false end) = true ->
      exists i j,
        represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x))) /\
        represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a)) /\
        same (D.view db) i j).
    destruct (lookup_id Unification.Cell_code [Val x] db) as [pointer |] eqn:Hx; [|discriminate].
    destruct (lookup_id Unification.Cell_code [Val a] db) as [address |] eqn:Ha; [|discriminate].
    destruct (lookup_id Unification.Deref_code [Id pointer] db)
      as [target |] eqn:Ht; [|discriminate].
    intro Heq; apply Pos.eqb_eq in Heq; subst target.
    apply (proj1 (lookup_id_spec Unification.Cell_code [Val x] db pointer Hwf)) in Hx.
    apply (proj1 (lookup_id_spec Unification.Cell_code [Val a] db address Hwf)) in Ha.
    change (row (D.view db) Unification.Cell_code [Val x] (Some (Id pointer))) in Hx.
    change (row (D.view db) Unification.Cell_code [Val a] (Some (Id address))) in Ha.
    apply (proj1 (lookup_id_spec Unification.Deref_code [Id pointer] db address Hwf)) in Ht.
    change (row (D.view db) Unification.Deref_code [Id (D.repr db pointer)] (Some (Id address)))
      in Ht.
    rewrite (canonical_output db Unification.Cell_code [Val x] pointer Hcanonical Hx) in Ht.
    assert (Hsame : same (D.view db) address address).
    { apply (proj2 (D.same_repr db address address Hwf)); reflexivity. }
    exists address, address; split.
    - apply (proj2 (represents_deref db x address Hwf Hcanonical)); exists pointer, address; auto.
    - split; [apply represents_cell; exists address; auto | exact Hsame].
  Qed.

  (** Represented equal endpoints make the three canonical lookups agree. *)
  Lemma points_complete : forall db x a, D.wf db -> D.canonical db ->
    (exists i j,
      represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x))) /\
      represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a)) /\
      same (D.view db) i j) ->
    points db x a = true.
  Proof.
    intros db x a Hwf Hcanonical [i [j [Hi [Hj Hij]]]].
    apply (proj1 (represents_deref db x i Hwf Hcanonical)) in Hi.
    destruct Hi as [pointer [target [Hx [Ht Hit]]]].
    apply represents_cell in Hj; destruct Hj as [address [Ha Hja]].
    apply (proj1 (D.same_repr db i j Hwf)) in Hij.
    apply (proj1 (D.same_repr db i target Hwf)) in Hit.
    apply (proj1 (D.same_repr db j address Hwf)) in Hja.
    pose proof (canonical_output db Unification.Deref_code [Id pointer] target Hcanonical Ht)
      as Htarget.
    pose proof (canonical_output db Unification.Cell_code [Val a] address Hcanonical Ha)
      as Haddress.
    assert (Heq : target = address) by congruence; subst target.
    assert (Hlookup_x : lookup_id Unification.Cell_code [Val x] db = Some pointer).
    { apply (proj2 (lookup_id_spec Unification.Cell_code [Val x] db pointer Hwf)); exact Hx. }
    assert (Hlookup_a : lookup_id Unification.Cell_code [Val a] db = Some address).
    { apply (proj2 (lookup_id_spec Unification.Cell_code [Val a] db address Hwf)); exact Ha. }
    assert (Hlookup_t : lookup_id Unification.Deref_code [Id pointer] db = Some address).
    { apply (proj2 (lookup_id_spec Unification.Deref_code [Id pointer] db address Hwf)).
      change (row (D.view db) Unification.Deref_code [Id (D.repr db pointer)] (Some (Id address))).
      rewrite (canonical_output db Unification.Cell_code [Val x] pointer Hcanonical Hx); exact Ht. }
    change ((match lookup_id Unification.Cell_code [Val x] db,
      lookup_id Unification.Cell_code [Val a] db with
      | Some pointer, Some address =>
        match lookup_id Unification.Deref_code [Id pointer] db with
        | Some target => Pos.eqb target address
        | None => false
        end
      | _, _ => false end) = true).
    rewrite Hlookup_x, Hlookup_a, Hlookup_t; apply Pos.eqb_refl.
  Qed.

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j,
      represents (D.view db) (Id i) (Unification.encode_pointer_term (Deref (Cell x))) /\
      represents (D.view db) (Id j) (Unification.encode_pointer_term (Cell a)) /\
      same (D.view db) i j)
      (points db x a).
  Proof.
    intros db x a Hwf Hcanonical; destruct (points db x a) eqn:Hpoints.
    - constructor; apply points_sound; assumption.
    - constructor; intro Hrep; apply (points_complete db x a Hwf Hcanonical) in Hrep; congruence.
  Qed.

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    destruct (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hwf [Hcanonical Hloaded]]; auto.
  Qed.

  (* STUB: GROUND.solve_complete with [pointer_congruence_congruent], and [points_spec]. *)
  Lemma solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
  Proof. Admitted. (* STUB *)
End Steensgaard.

(** * Time *)

Module SteensgaardT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D)
    <: STEENSGAARD_ALL V I J D R.
  (** The runner with its time functions. *)
  Module XT := RunnerT V I J D R.
  Include Steensgaard V I J D R XT.
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

  (* STUB: seeding is the runner's fold of puts, so this follows from the runner's cost
     bound. *)
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

  (* STUB: the solve is the runner's solve, so this follows from the runner's cost bound. *)
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

  (* STUB: GROUND.solve_complete with [pointer_congruence_congruent]. *)
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

  (* STUB: the runner's solve cost, with the planned slots' constants. *)
  Lemma T_solve_split : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof. Admitted. (* STUB *)
End SteensgaardT.

Module SteensgaardSound (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) (L : POINTER_LINK) <: STEENSGAARD_SOUND V I J D R A L.
  (** The source congruence contains every seed and is closed under its pointer rules. *)
  Lemma source_closed : forall q,
    pointer_closed q (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)).
  Proof.
    exact pointer_congruence_closed.
  Qed.

  (** Every inclusion-derived pointer belongs to the source congruence. *)
  Lemma inclusion_unifies : forall q x a, may_points q x a ->
    pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof.
    exact pointer_inclusion_unifies.
  Qed.

  (** Each concrete instruction preserves coverage by the source congruence. *)
  Lemma step_covered : forall q instruction before after,
    In instruction (constraints q) ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) before ->
    pointer_exec instruction before = Some after ->
    memory_covered (fun x a => pointer_congruence q (Deref (Cell x)) (Cell a)) after.
  Proof.
    intros q instruction before after Hin Hcovered Hexec.
    eapply pointer_step_covered.
    - apply source_closed.
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
        eapply step_covered; [exact Hin | exact IH | exact Hexec]. }
    intros x a Hget; apply (A.solve_covers q lim db Hsolve x a).
    apply Hcovered; exact Hget.
  Qed.
End SteensgaardSound.

Module SteensgaardExact (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : STEENSGAARD V I J D R) <: STEENSGAARD_EXACT V I J D R A.
  (* STUB: induction on [congruent] with the invariant that a term congruent to an encoding
     is an encoding and the decoded terms are related by [pointer_congruence]. Literals are
     congruent only to themselves, and every clause side is a constructor term built from
     input values. *)
  Lemma pointer_congruence_back : forall prim q t u,
    congruent prim Unification.spec (Unification.inputs q)
      (Unification.encode_pointer_term t) (Unification.encode_pointer_term u) ->
    pointer_congruence q t u.
  Proof. Admitted. (* STUB *)

  (* STUB: GROUND.solve_sound, solve_complete and solve_builds, with
     [pointer_congruence_congruent], [pointer_congruence_back] and [points_spec], and
     [spec_ok], [ground] and [rows_ok] by vm_compute. *)
  Lemma solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)
End SteensgaardExact.
