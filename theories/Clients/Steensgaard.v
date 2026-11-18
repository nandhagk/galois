(** * Unification-based pointer analysis driver

    This driver seeds the derived unification program with the source equations and queries the
    constructor congruence that its saturation computes. The file holds the code, the base of
    the law module with the proofs about lookups, and the soundness of every concrete run. The
    law module [Steensgaard] adds the exactness laws in [SteensgaardExact.v], and the timed
    module [SteensgaardT] is in [SteensgaardTime.v].
    For example, an address constraint equates a pointer's dereference with an addressed cell.

    Main results
    - [points_spec] Queries test whether the pointee term equals the addressed cell in the final
      congruence.
    - [solve_covers] Saturated query answers contain the source congruence approximation.
    - [concrete_sound] Every reachable concrete pointer is included in every saturated result.

    Builds on: SteensgaardSig, Andersen, the runner facts, the ground theorems and the database
    and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig CongruenceRefSig GroundSig.
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

Module SteensgaardBase (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (G : GROUND V I J D R X).
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

  (* STUB: the rows of [Unification.facts q] are rows of the five input tables with two values
     each, so a case on each constraint shows that they pass the row check. *)
  (** Every input row of a pointer input passes the row check. *)
  Lemma facts_rows_ok : forall q, rows_ok Unification.spec (Unification.facts q) = true.
  Proof. Admitted. (* STUB *)

  (* STUB: [F.seed_rows] for [Unification.spec], with [spec_ok] by vm_compute and
     [facts_rows_ok]. *)
  Lemma seed_rows : forall q f k o, row (D.view (seed q)) f k o <->
    o = None /\ exists vs, k = map Val vs /\ In (f, vs) (Unification.facts q).
  Proof. Admitted. (* STUB *)

  (* STUB: [F.seed_ready] for [Unification.spec], with [spec_ok] by vm_compute and
     [facts_rows_ok]. *)
  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  (* STUB: [F.seed_ready] for [Unification.spec], with [spec_ok] by vm_compute and
     [facts_rows_ok]. *)
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

  (* STUB: an induction on [pointer_congruence] shows that two related terms are equal, or are
     represented in one class of a saturated outcome, or are dereferences of related terms.
     The cases of the clauses use [G.solve_builds] and [G.solve_complete] with
     [Unification.pointer_congruence_congruent], and transitivity uses the canonical rows of
     the outcome. [Deref (Cell x)] and [Cell a] are neither equal nor two dereferences, so they
     are represented in one class, and [points_spec] answers [true]. *)
  Lemma solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
  Proof. Admitted. (* STUB *)
End SteensgaardBase.

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
