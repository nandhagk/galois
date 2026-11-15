(** * Unification-based pointer analysis driver

    This driver compiles pointer equations and queries their constructor congruence.
    For example, an address constraint equates a pointer's dereference with an addressed cell.
    Builds on: SteensgaardSig, Andersen and the database and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
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
  Definition compile (_ : pointer_input) : program V.t := steensgaard_program.
  Definition seed_put (db : D.t) (entry : positive * (positive * positive)) : D.t :=
    D.put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None db.
  Definition seed (q : pointer_input) : D.t :=
    fold_left seed_put (pointer_seed_entries 1 q)
      (D.init (decls V.t (compile q)) (pointer_plan_slots (R.plan (compile q)))).
  Definition solve (q : pointer_input) (lim : limits) : stop * D.t :=
    let p := compile q in R.run p (R.plan p) lim (seed q).
  Definition lookup_id (f : positive) (key : list (cell V.t)) (db : D.t) : option positive :=
    match fst (D.lookup f key db) with
    | Some (Some (Id i)) => Some i
    | _ => None
    end.
  Definition points (db : D.t) (x a : positive) : bool :=
    match lookup_id 6 [Val x] db, lookup_id 6 [Val a] db with
    | Some pointer, Some address =>
      match lookup_id 7 [Id pointer] db with
      | Some target => Pos.eqb target address
      | None => false
      end
    | _, _ => false
    end.
End SteensgaardCode.

Module Steensgaard (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: STEENSGAARD V I J D R.
  Include SteensgaardCode V I J D R.
  Module Seeds := PointerSeedFacts V I J D R.

  (** The fixed unification program passes the source sort checker. *)
  Lemma program_sorted : forall q, program_ok (compile q).
  Proof.
    intro q; apply (proj1 (check_program_spec V.t (compile q))); vm_compute; reflexivity.
  Qed.

  (** Every source and initial-pointer seed targets a declared binary relation. *)
  Lemma seed_entries_ok : forall q, Forall (Seeds.entry_ok (compile q)) (pointer_seed_entries 1 q).
  Proof.
    intros [instructions initial]; cbn [pointer_seed_entries]; apply Forall_app; split.
    - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin.
      destruct Hin as [instruction [Heq Hin]]; subst entry; destruct instruction; split; reflexivity.
    - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin.
      destruct Hin as [[x y] [Heq Hin]]; subst entry; split; reflexivity.
  Qed.

  (** Seeding records the program layout and only identifier-free value rows. *)
  Lemma seed_invariant : forall q, Seeds.invariant (compile q) (seed q).
  Proof.
    intro q; change (Seeds.invariant (compile q)
      (fold_left Seeds.put_entry (pointer_seed_entries 1 q)
        (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))))).
    apply Seeds.fold_invariant.
    - apply R.plan_checked; apply program_sorted.
    - apply Seeds.init_invariant.
    - apply seed_entries_ok.
  Qed.

  Lemma compile_rules : forall q, compile q = steensgaard_program.
  Proof.
    reflexivity.
  Qed.

  Lemma seed_rows : forall q f k o,
    row (D.view (seed q)) f k o <-> steensgaard_seed_row q f k o.
  Proof.
    intros q f k o.
    change (row (D.view (fold_left Seeds.put_entry (pointer_seed_entries 1 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))))) f k o <->
      steensgaard_seed_row q f k o).
    rewrite (Seeds.fold_rows (compile q) (pointer_seed_entries 1 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q))))
      (R.plan_checked (compile q) (program_sorted q)) (Seeds.init_invariant (compile q))
      (seed_entries_ok q) f k o).
    split.
    - intros [Hinitial | [[g [x y]] [Hin [Hf [Hk Ho]]]]].
      + apply (proj1 (proj1 (D.init_view (decls V.t (compile q))
          (Syntax.slots V.t (R.plan (compile q))) f k o 1 1))) in Hinitial; contradiction.
      + cbn [fst snd] in Hf, Hk; subst f k o.
        split; [reflexivity | exists x, y; split; [reflexivity |]].
        apply pointer_seed_entries_spec in Hin; tauto.
    - intros [Ho [x [y [Hk Hsource]]]]; subst k o; right.
      exists (f, (x, y)); split.
      + apply pointer_seed_entries_spec; tauto.
      + repeat split; reflexivity.
  Qed.

  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof.
    intro q; exact (proj1 (proj2 (seed_invariant q))).
  Qed.

  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q).
  Proof.
    intro q; destruct (seed_invariant q) as [Hwf [Hloaded Hnoids]].
    split; [exact Hwf | apply Seeds.no_ids_canonical; exact Hnoids].
  Qed.

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof.
    reflexivity.
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
    represents (D.view db) (Id i) (pointer_expression (Cell x)) <->
      exists j, row (D.view db) 6 [Val x] (Some (Id j)) /\ same (D.view db) i j.
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
    (represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) <->
      exists cell_id target, row (D.view db) 6 [Val x] (Some (Id cell_id)) /\
        row (D.view db) 7 [Id cell_id] (Some (Id target)) /\ same (D.view db) i target).
  Proof.
    intros db x i Hwf Hcanonical; split.
    - intro Hrep; inversion Hrep as [|f key i' target args Hrow Hsame Hargs]; subst.
      inversion Hargs as [|c expression key' args' Hcell Htail]; subst.
      inversion Htail; subst.
      destruct c as [cell_id | value]; [|inversion Hcell].
      apply represents_cell in Hcell; destruct Hcell as [stored [Hstored Hequal]].
      assert (Hcell_canonical : D.repr db cell_id = cell_id).
      { apply (Hcanonical 7%positive [Id cell_id] (Some (Id target)) Hrow cell_id).
        left; reflexivity. }
      pose proof (canonical_output db 6 [Val x] stored Hcanonical Hstored) as Hstored_canonical.
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
    exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j.
  Proof.
    intros db x a Hwf Hcanonical.
    change ((match lookup_id 6 [Val x] db, lookup_id 6 [Val a] db with
      | Some pointer, Some address =>
        match lookup_id 7 [Id pointer] db with Some target => Pos.eqb target address | None => false end
      | _, _ => false end) = true ->
      exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
        represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j).
    destruct (lookup_id 6 [Val x] db) as [pointer |] eqn:Hx; [|discriminate].
    destruct (lookup_id 6 [Val a] db) as [address |] eqn:Ha; [|discriminate].
    destruct (lookup_id 7 [Id pointer] db) as [target |] eqn:Ht; [|discriminate].
    intro Heq; apply Pos.eqb_eq in Heq; subst target.
    apply (proj1 (lookup_id_spec 6 [Val x] db pointer Hwf)) in Hx.
    apply (proj1 (lookup_id_spec 6 [Val a] db address Hwf)) in Ha.
    change (row (D.view db) 6 [Val x] (Some (Id pointer))) in Hx.
    change (row (D.view db) 6 [Val a] (Some (Id address))) in Ha.
    apply (proj1 (lookup_id_spec 7 [Id pointer] db address Hwf)) in Ht.
    change (row (D.view db) 7 [Id (D.repr db pointer)] (Some (Id address))) in Ht.
    rewrite (canonical_output db 6 [Val x] pointer Hcanonical Hx) in Ht.
    assert (Hsame : same (D.view db) address address).
    { apply (proj2 (D.same_repr db address address Hwf)); reflexivity. }
    exists address, address; split.
    - apply (proj2 (represents_deref db x address Hwf Hcanonical)); exists pointer, address; auto.
    - split; [apply represents_cell; exists address; auto | exact Hsame].
  Qed.

  (** Represented equal endpoints make the three canonical lookups agree. *)
  Lemma points_complete : forall db x a, D.wf db -> D.canonical db ->
    (exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j) ->
    points db x a = true.
  Proof.
    intros db x a Hwf Hcanonical [i [j [Hi [Hj Hij]]]].
    apply (proj1 (represents_deref db x i Hwf Hcanonical)) in Hi.
    destruct Hi as [pointer [target [Hx [Ht Hit]]]].
    apply represents_cell in Hj; destruct Hj as [address [Ha Hja]].
    apply (proj1 (D.same_repr db i j Hwf)) in Hij.
    apply (proj1 (D.same_repr db i target Hwf)) in Hit.
    apply (proj1 (D.same_repr db j address Hwf)) in Hja.
    pose proof (canonical_output db 7 [Id pointer] target Hcanonical Ht) as Htarget.
    pose proof (canonical_output db 6 [Val a] address Hcanonical Ha) as Haddress.
    assert (Heq : target = address) by congruence; subst target.
    assert (Hlookup_x : lookup_id 6 [Val x] db = Some pointer).
    { apply (proj2 (lookup_id_spec 6 [Val x] db pointer Hwf)); exact Hx. }
    assert (Hlookup_a : lookup_id 6 [Val a] db = Some address).
    { apply (proj2 (lookup_id_spec 6 [Val a] db address Hwf)); exact Ha. }
    assert (Hlookup_t : lookup_id 7 [Id pointer] db = Some address).
    { apply (proj2 (lookup_id_spec 7 [Id pointer] db address Hwf)).
      change (row (D.view db) 7 [Id (D.repr db pointer)] (Some (Id address))).
      rewrite (canonical_output db 6 [Val x] pointer Hcanonical Hx); exact Ht. }
    change ((match lookup_id 6 [Val x] db, lookup_id 6 [Val a] db with
      | Some pointer, Some address =>
        match lookup_id 7 [Id pointer] db with Some target => Pos.eqb target address | None => false end
      | _, _ => false end) = true).
    rewrite Hlookup_x, Hlookup_a, Hlookup_t; apply Pos.eqb_refl.
  Qed.

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (exists i j, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
      represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j)
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

  Lemma solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
  Proof. Admitted. (* STUB *)

End Steensgaard.

Module SteensgaardT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D) <: STEENSGAARD_ALL V I J D R.
  Include Steensgaard V I J D R.
  TimeFun compile.
  TimeFun seed_put.
  TimeFun seed.
  TimeFun solve.
  TimeFun lookup_id.
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

  (** A source relation atom binds precisely its two value arguments. *)
  Lemma model_pair : forall q rho f u v,
    program_kind steensgaard_program f = Some ORel ->
    model_atom V.prim (concrete_model q) (program_kind steensgaard_program) rho
      (Fun positive f [Var u; Var v] None) ->
    exists x y, rho u = Some (inr x) /\ rho v = Some (inr y) /\ source_relation q f x y.
  Proof.
    intros q rho f u v Hkind [k [Hterms Hrelation]].
    rewrite Hkind in Hrelation; cbn [concrete_model rel] in Hrelation.
    destruct Hrelation as [x [y [Hk Hrelation]]]; subst k.
    inversion Hterms as [|term terms value values Hu Htail]; subst.
    inversion Htail as [|term terms value values Hv Hnil]; subst.
    exists x, y; exact (conj Hu (conj Hv Hrelation)).
  Qed.

  (* Establish one generated Make action and its singleton argument interpretation. *)
  Local Ltac make_pointer args :=
    exists args; split;
    [ constructor;
      [ cbn [model_term model_update concrete_model con];
        first [assumption | reflexivity | congruence] | constructor ]
    | split; [reflexivity |] ].

  (** Source equations establish validity of all generated union rules. *)
  Lemma rules_valid : forall q, valid V.prim V.merge (concrete_model q) (A.compile q).
  Proof.
    intro q; rewrite A.compile_rules; split.
    - intros r rho Hin Hquery.
      destruct Hin as [Hr | [Hr | [Hr | [Hr | Hnone]]]];
        [subst r | subst r | subst r | subst r |].
      + destruct (model_pair q rho 1 1 2 eq_refl (Forall_inv Hquery))
          as [x [y [Hx [Hy Hsource]]]].
        make_pointer ([inr x] : list (Q.carrier q + V.t)).
        make_pointer ([inr y] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q x)] : list (Q.carrier q + V.t)).
        exists (inl (Q.deref q (Q.cell q x))), (inl (Q.cell q y)).
        repeat split; try reflexivity.
        apply addr_equation; unfold source_relation in Hsource; intuition discriminate.
      + destruct (model_pair q rho 2 1 2 eq_refl (Forall_inv Hquery))
          as [x [y [Hx [Hy Hsource]]]].
        make_pointer ([inr x] : list (Q.carrier q + V.t)).
        make_pointer ([inr y] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q x)] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q y)] : list (Q.carrier q + V.t)).
        exists (inl (Q.deref q (Q.cell q x))), (inl (Q.deref q (Q.cell q y))).
        repeat split; try reflexivity.
        apply copy_equation; unfold source_relation in Hsource; intuition discriminate.
      + destruct (model_pair q rho 3 1 2 eq_refl (Forall_inv Hquery))
          as [x [y [Hx [Hy Hsource]]]].
        make_pointer ([inr x] : list (Q.carrier q + V.t)).
        make_pointer ([inr y] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q x)] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q y)] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.deref q (Q.cell q y))] : list (Q.carrier q + V.t)).
        exists (inl (Q.deref q (Q.cell q x))),
          (inl (Q.deref q (Q.deref q (Q.cell q y)))).
        repeat split; try reflexivity.
        apply load_equation; unfold source_relation in Hsource; intuition discriminate.
      + destruct (model_pair q rho 4 1 2 eq_refl (Forall_inv Hquery))
          as [x [y [Hx [Hy Hsource]]]].
        make_pointer ([inr x] : list (Q.carrier q + V.t)).
        make_pointer ([inr y] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q x)] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.cell q y)] : list (Q.carrier q + V.t)).
        make_pointer ([inl (Q.deref q (Q.cell q x))] : list (Q.carrier q + V.t)).
        exists (inl (Q.deref q (Q.deref q (Q.cell q x)))),
          (inl (Q.deref q (Q.cell q y))).
        repeat split; try reflexivity.
        apply store_equation; unfold source_relation in Hsource; intuition discriminate.
      + contradiction.
    - intros f m k a b Hkind Hlat Hlat'; exact Hlat.
  Qed.

  (** Saturated query answers are exactly the source congruence approximation. *)
  Lemma solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof. Admitted. (* STUB *)
End SteensgaardExact.
