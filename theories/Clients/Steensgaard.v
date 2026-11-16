(** * Unification-based pointer analysis driver

    This driver compiles pointer equations and queries their constructor congruence.
    For example, an address constraint equates a pointer's dereference with an addressed cell.
    Builds on: SteensgaardSig, Andersen and the database and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import
  Syntax Model ModelFacts Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Clients Require Import AndersenSig Andersen SteensgaardSig.
Import List.ListNotations.

(** A total unary algebra retains terms whose constructors are absent from the database. *)
Inductive pointer_normal :=
  | PointerKnown (identifier : positive)
  | PointerCell (address : positive)
  | PointerDeref (pointer : pointer_normal).

(** A singleton constructor action stores the value of its one argument. *)
Lemma pointer_make_row : forall prim merge (w : view (V := positive)) rho variable f arg c rest,
  term_value rho arg c -> present prim merge w rho (Make variable f [arg] :: rest) ->
  exists i, row w f [c] (Some (Id i)) /\ present prim merge w (update rho variable (Id i)) rest.
Proof.
  intros prim merge w rho variable f arg c rest Harg [key [i [Hterms [Hrow Hrest]]]].
  assert (Hkey : key = [c]).
  { eapply pointer_terms_unique; [exact Hterms | constructor; [exact Harg | constructor]]. }
  subst key; exists i; auto.
Qed.

(** A present identifier union states equality of the two bound identifiers. *)
Lemma pointer_union_same : forall prim merge (w : view (V := positive)) rho u v i j rest,
  rho u = Some (Id i) -> rho v = Some (Id j) ->
  present prim merge w rho (Union (Var u) (Var v) :: rest) -> same w i j.
Proof.
  intros prim merge w rho u v i j rest Hu Hv [c [d [Hc [Hd [Hsame Hrest]]]]].
  cbn [term_value] in Hc, Hd.
  assert (Hci : c = Id i) by congruence; assert (Hdj : d = Id j) by congruence.
  subst c d; exact Hsame.
Qed.

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
      destruct Hin as [instruction [Heq Hin]]; subst entry;
        destruct instruction; split; reflexivity.
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
        match lookup_id 7 [Id pointer] db with
        | Some target => Pos.eqb target address
        | None => false
        end
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
        match lookup_id 7 [Id pointer] db with
        | Some target => Pos.eqb target address
        | None => false
        end
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

  Definition normal_cell (db : D.t) (x : positive) : pointer_normal :=
    match lookup_id 6 [Val x] db with Some i => PointerKnown i | None => PointerCell x end.
  Definition normal_deref (db : D.t) (value : pointer_normal) : pointer_normal :=
    match value with
    | PointerKnown i =>
      match lookup_id 7 [Id i] db with
      | Some j => PointerKnown j
      | None => PointerDeref value
      end
    | _ => PointerDeref value
    end.
  Fixpoint normal_term (db : D.t) (t : pointer_term) : pointer_normal :=
    match t with
    | Cell x => normal_cell db x
    | Deref t => normal_deref db (normal_term db t)
    end.

  (** A known normal form is an identifier stored as a canonical output. *)
  Lemma normal_known_canonical : forall db t i, D.wf db -> D.canonical db ->
    normal_term db t = PointerKnown i -> D.repr db i = i.
  Proof.
    intros db [x | t] i Hwf Hcanonical Hnormal.
    - change ((match lookup_id 6 [Val x] db with
        Some j => PointerKnown j | None => PointerCell x end) = PointerKnown i) in Hnormal.
      destruct (lookup_id 6 [Val x] db) as [j |] eqn:Hlookup; [|discriminate].
      inversion Hnormal; subst j; apply (proj1 (lookup_id_spec 6 [Val x] db i Hwf)) in Hlookup.
      eapply canonical_output; eassumption.
    - change (normal_deref db (normal_term db t) = PointerKnown i) in Hnormal.
      destruct (normal_term db t) as [arg | address | value]; try discriminate.
      change ((match lookup_id 7 [Id arg] db with
        Some j => PointerKnown j | None => PointerDeref (PointerKnown arg) end) = PointerKnown i)
        in Hnormal.
      destruct (lookup_id 7 [Id arg] db) as [j |] eqn:Hlookup; [|discriminate].
      inversion Hnormal; subst j; apply (proj1 (lookup_id_spec 7 [Id arg] db i Hwf)) in Hlookup.
      eapply canonical_output; eassumption.
  Qed.

  (** A stored cell constructor fixes that cell's normal form. *)
  Lemma normal_cell_row : forall db x i, D.wf db ->
    row (D.view db) 6 [Val x] (Some (Id i)) -> normal_term db (Cell x) = PointerKnown i.
  Proof.
    intros db x i Hwf Hrow.
    assert (Hlookup : lookup_id 6 [Val x] db = Some i).
    { apply (proj2 (lookup_id_spec 6 [Val x] db i Hwf)); exact Hrow. }
    change ((match lookup_id 6 [Val x] db with
      Some j => PointerKnown j | None => PointerCell x end) = PointerKnown i).
    rewrite Hlookup; reflexivity.
  Qed.

  (** A stored dereference constructor reduces a known argument's normal form. *)
  Lemma normal_deref_row : forall db t i j, D.wf db -> D.canonical db ->
    normal_term db t = PointerKnown i -> row (D.view db) 7 [Id i] (Some (Id j)) ->
    normal_term db (Deref t) = PointerKnown j.
  Proof.
    intros db t i j Hwf Hcanonical Hnormal Hrow.
    assert (Hlookup : lookup_id 7 [Id i] db = Some j).
    { apply (proj2 (lookup_id_spec 7 [Id i] db j Hwf)).
      change (row (D.view db) 7 [Id (D.repr db i)] (Some (Id j))).
      rewrite (normal_known_canonical db t i Hwf Hcanonical Hnormal); exact Hrow. }
    change (normal_deref db (normal_term db t) = PointerKnown j).
    rewrite Hnormal.
    change ((match lookup_id 7 [Id i] db with
      | Some target => PointerKnown target
      | None => PointerDeref (PointerKnown i)
      end) = PointerKnown j).
    rewrite Hlookup; reflexivity.
  Qed.

  (** Represented pointer terms normalize to the representative of their identifier. *)
  Lemma normal_represents : forall db t i, D.wf db -> D.canonical db ->
    represents (D.view db) (Id i) (pointer_expression t) ->
    normal_term db t = PointerKnown (D.repr db i).
  Proof.
    intros db t; induction t as [x | t IH]; intros i Hwf Hcanonical Hrep.
    - apply represents_cell in Hrep; destruct Hrep as [j [Hrow Hsame]].
      rewrite (normal_cell_row db x j Hwf Hrow).
      apply (proj1 (D.same_repr db i j Hwf)) in Hsame.
      rewrite Hsame, (canonical_output db 6 [Val x] j Hcanonical Hrow); reflexivity.
    - inversion Hrep as [|f key i' target args Hrow Hsame Hargs]; subst.
      inversion Hargs as [|c expression key' args' Harg Htail]; subst.
      inversion Htail; subst.
      destruct c as [arg | value]; [|destruct t; inversion Harg].
      pose proof (IH arg Hwf Hcanonical Harg) as Hnormal.
      assert (Harg_canonical : D.repr db arg = arg).
      { apply (Hcanonical 7%positive [Id arg] (Some (Id target)) Hrow arg).
        left; reflexivity. }
      rewrite Harg_canonical in Hnormal.
      rewrite (normal_deref_row db t arg target Hwf Hcanonical Hnormal Hrow).
      apply (proj1 (D.same_repr db i target Hwf)) in Hsame.
      rewrite Hsame, (canonical_output db 7 [Id arg] target Hcanonical Hrow); reflexivity.
  Qed.

  (** Equal pointee and cell normal forms force all three query lookups to succeed. *)
  Lemma normal_points : forall db x a,
    normal_term db (Deref (Cell x)) = normal_term db (Cell a) -> points db x a = true.
  Proof.
    intros db x a Hnormal.
    change (normal_deref db (normal_cell db x) = normal_cell db a) in Hnormal.
    unfold normal_cell, normal_deref in Hnormal.
    change ((match lookup_id 6 [Val x] db, lookup_id 6 [Val a] db with
      | Some pointer, Some address =>
        match lookup_id 7 [Id pointer] db with
        | Some target => Pos.eqb target address
        | None => false
        end
      | _, _ => false end) = true).
    destruct (lookup_id 6 [Val x] db) as [pointer |] eqn:Hx;
      destruct (lookup_id 6 [Val a] db) as [address |] eqn:Ha; try discriminate.
    - destruct (lookup_id 7 [Id pointer] db) as [target |] eqn:Ht; [|discriminate].
      inversion Hnormal; subst target; apply Pos.eqb_refl.
    - destruct (lookup_id 7 [Id pointer] db); discriminate.
  Qed.

  (** Equality of two canonical stored outputs is ordinary identifier equality. *)
  Lemma same_outputs : forall db f key i g key' j, D.wf db -> D.canonical db ->
    row (D.view db) f key (Some (Id i)) -> row (D.view db) g key' (Some (Id j)) ->
    same (D.view db) i j -> i = j.
  Proof.
    intros db f key i g key' j Hwf Hcanonical Hi Hj Hsame.
    apply (proj1 (D.same_repr db i j Hwf)) in Hsame.
    rewrite (canonical_output db f key i Hcanonical Hi),
      (canonical_output db g key' j Hcanonical Hj) in Hsame; exact Hsame.
  Qed.

  (** A closed view performs a source rule on its two source value arguments. *)
  Lemma source_present : forall db r x y f,
    query positive r = [Fun positive f [Var 1; Var 2] None] ->
    closed V.prim V.merge steensgaard_program (D.view db) ->
    In r (rules positive steensgaard_program) -> row (D.view db) f [Val x; Val y] None ->
    present V.prim V.merge (D.view db) (binding_env [1%positive; 2%positive] [Val x; Val y])
      (actions positive r).
  Proof.
    intros db r x y f Hquery Hclosed Hin Hrow.
    apply (Hclosed r (binding_env [1%positive; 2%positive] [Val x; Val y]));
      [exact Hin | change (matches V.prim (D.view db) (query positive r)
        (binding_env [1%positive; 2%positive] [Val x; Val y])); rewrite Hquery].
    constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hrow] | constructor].
  Qed.

  (** The saturated address rule establishes equality in the total normalization algebra. *)
  Lemma normal_addr : forall db x a, D.wf db -> D.canonical db ->
    closed V.prim V.merge steensgaard_program (D.view db) ->
    row (D.view db) 1 [Val x; Val a] None ->
    normal_term db (Deref (Cell x)) = normal_term db (Cell a).
  Proof.
    intros db x a Hwf Hcanonical Hclosed Hsource.
    pose proof (source_present db
      (nth 0 (rules positive steensgaard_program) (Rule positive [] [])) x a 1 eq_refl
      Hclosed (or_introl eq_refl) Hsource) as Hpresent.
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 3 6 (Var 1) (Val x) _
      eq_refl Hpresent) as [cx [Hcx Hnext]].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 4 6 (Var 2) (Val a) _
      eq_refl Hnext) as [ca [Hca Hnext']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 5 7 (Var 3) (Id cx) _
      eq_refl Hnext') as [dx [Hdx Hunion]].
    pose proof (pointer_union_same V.prim V.merge (D.view db) _ 5 4 dx ca []
      eq_refl eq_refl Hunion) as Hsame.
    pose proof (normal_cell_row db x cx Hwf Hcx) as Hx.
    rewrite (normal_deref_row db (Cell x) cx dx Hwf Hcanonical Hx Hdx),
      (normal_cell_row db a ca Hwf Hca).
    f_equal; exact (same_outputs db 7 [Id cx] dx 6 [Val a] ca Hwf Hcanonical Hdx Hca Hsame).
  Qed.

  (** The saturated copy rule equates the two normalized dereferences. *)
  Lemma normal_copy : forall db x y, D.wf db -> D.canonical db ->
    closed V.prim V.merge steensgaard_program (D.view db) ->
    row (D.view db) 2 [Val x; Val y] None ->
    normal_term db (Deref (Cell x)) = normal_term db (Deref (Cell y)).
  Proof.
    intros db x y Hwf Hcanonical Hclosed Hsource.
    pose proof (source_present db
      (nth 1 (rules positive steensgaard_program) (Rule positive [] [])) x y 2 eq_refl
      Hclosed (or_intror (or_introl eq_refl)) Hsource) as Hpresent.
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 3 6 (Var 1) (Val x) _
      eq_refl Hpresent) as [cx [Hcx Hnext]].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 4 6 (Var 2) (Val y) _
      eq_refl Hnext) as [cy [Hcy Hnext']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 5 7 (Var 3) (Id cx) _
      eq_refl Hnext') as [dx [Hdx Hnext'']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 6 7 (Var 4) (Id cy) _
      eq_refl Hnext'') as [dy [Hdy Hunion]].
    pose proof (pointer_union_same V.prim V.merge (D.view db) _ 5 6 dx dy []
      eq_refl eq_refl Hunion) as Hsame.
    pose proof (normal_cell_row db x cx Hwf Hcx) as Hx.
    pose proof (normal_cell_row db y cy Hwf Hcy) as Hy.
    rewrite (normal_deref_row db (Cell x) cx dx Hwf Hcanonical Hx Hdx),
      (normal_deref_row db (Cell y) cy dy Hwf Hcanonical Hy Hdy).
    f_equal; exact (same_outputs db 7 [Id cx] dx 7 [Id cy] dy Hwf Hcanonical Hdx Hdy Hsame).
  Qed.

  (** The saturated load rule equates a pointee with a second dereference. *)
  Lemma normal_load : forall db x y, D.wf db -> D.canonical db ->
    closed V.prim V.merge steensgaard_program (D.view db) ->
    row (D.view db) 3 [Val x; Val y] None ->
    normal_term db (Deref (Cell x)) = normal_term db (Deref (Deref (Cell y))).
  Proof.
    intros db x y Hwf Hcanonical Hclosed Hsource.
    pose proof (source_present db
      (nth 2 (rules positive steensgaard_program) (Rule positive [] [])) x y 3 eq_refl
      Hclosed (or_intror (or_intror (or_introl eq_refl))) Hsource) as Hpresent.
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 3 6 (Var 1) (Val x) _
      eq_refl Hpresent) as [cx [Hcx Hnext]].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 4 6 (Var 2) (Val y) _
      eq_refl Hnext) as [cy [Hcy Hnext']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 5 7 (Var 3) (Id cx) _
      eq_refl Hnext') as [dx [Hdx Hnext'']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 6 7 (Var 4) (Id cy) _
      eq_refl Hnext'') as [dy [Hdy Hnext''']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 7 7 (Var 6) (Id dy) _
      eq_refl Hnext''') as [ddy [Hddy Hunion]].
    pose proof (pointer_union_same V.prim V.merge (D.view db) _ 5 7 dx ddy []
      eq_refl eq_refl Hunion) as Hsame.
    pose proof (normal_cell_row db x cx Hwf Hcx) as Hx.
    pose proof (normal_cell_row db y cy Hwf Hcy) as Hy.
    pose proof (normal_deref_row db (Cell y) cy dy Hwf Hcanonical Hy Hdy) as Hnormal_y.
    rewrite (normal_deref_row db (Cell x) cx dx Hwf Hcanonical Hx Hdx),
      (normal_deref_row db (Deref (Cell y)) dy ddy Hwf Hcanonical Hnormal_y Hddy).
    f_equal; exact (same_outputs db 7 [Id cx] dx 7 [Id dy] ddy Hwf Hcanonical Hdx Hddy Hsame).
  Qed.

  (** The saturated store rule equates a second dereference with the stored pointee. *)
  Lemma normal_store : forall db x y, D.wf db -> D.canonical db ->
    closed V.prim V.merge steensgaard_program (D.view db) ->
    row (D.view db) 4 [Val x; Val y] None ->
    normal_term db (Deref (Deref (Cell x))) = normal_term db (Deref (Cell y)).
  Proof.
    intros db x y Hwf Hcanonical Hclosed Hsource.
    pose proof (source_present db
      (nth 3 (rules positive steensgaard_program) (Rule positive [] [])) x y 4 eq_refl
      Hclosed (or_intror (or_intror (or_intror (or_introl eq_refl)))) Hsource) as Hpresent.
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 3 6 (Var 1) (Val x) _
      eq_refl Hpresent) as [cx [Hcx Hnext]].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 4 6 (Var 2) (Val y) _
      eq_refl Hnext) as [cy [Hcy Hnext']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 5 7 (Var 3) (Id cx) _
      eq_refl Hnext') as [dx [Hdx Hnext'']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 6 7 (Var 4) (Id cy) _
      eq_refl Hnext'') as [dy [Hdy Hnext''']].
    destruct (pointer_make_row V.prim V.merge (D.view db) _ 7 7 (Var 5) (Id dx) _
      eq_refl Hnext''') as [ddx [Hddx Hunion]].
    pose proof (pointer_union_same V.prim V.merge (D.view db) _ 7 6 ddx dy []
      eq_refl eq_refl Hunion) as Hsame.
    pose proof (normal_cell_row db x cx Hwf Hcx) as Hx.
    pose proof (normal_cell_row db y cy Hwf Hcy) as Hy.
    pose proof (normal_deref_row db (Cell x) cx dx Hwf Hcanonical Hx Hdx) as Hnormal_x.
    rewrite (normal_deref_row db (Deref (Cell x)) dx ddx Hwf Hcanonical Hnormal_x Hddx),
      (normal_deref_row db (Cell y) cy dy Hwf Hcanonical Hy Hdy).
    f_equal; exact (same_outputs db 7 [Id dx] ddx 7 [Id cy] dy Hwf Hcanonical Hddx Hdy Hsame).
  Qed.

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    destruct (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hwf [Hcanonical Hloaded]]; auto.
  Qed.

  (** The returned rows retain the source declarations and their output sorts. *)
  Lemma solve_loaded : forall q lim,
    R.loaded (compile q) (R.plan (compile q)) (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    exact (proj2 (proj2 (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q)))).
  Qed.

  (** Source relation rows persist with their absent outputs through the run. *)
  Lemma solve_seed_rows : forall q lim f key output, steensgaard_seed_row q f key output ->
    row (D.view (snd (solve q lim))) f key output.
  Proof.
    intros q lim f key output Hseed.
    pose proof (proj2 (seed_rows q f key output) Hseed) as Hrow.
    destruct Hseed as [Ho [x [y [Hkey Hsource]]]]; subst key output.
    assert (Hrelation : program_kind (compile q) f = Some ORel).
    { destruct Hsource as [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [Hf Hin]]]];
        subst f; reflexivity. }
    destruct (R.run_grows (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hsame Hrows].
    rewrite <- solve_run in Hrows.
    destruct (Hrows f [Val x; Val y] None Hrow) as [output [Hnew Hle]].
    change (row (D.view (snd (solve q lim))) f [Val x; Val y] output) in Hnew.
    destruct (solve_loaded q lim) as [Hkinds [Hslots Hsorted]].
    destruct (Hsorted f [Val x; Val y] output Hnew) as [out [Hsort [Hkind Houtput]]].
    rewrite Hkinds, Hrelation in Hkind; inversion Hkind; subst out.
    destruct output as [[i | v] |]; [discriminate | discriminate | exact Hnew].
  Qed.

  (** Source congruence is equality in the total normalization algebra of a closed view. *)
  Lemma normal_source : forall q db, D.wf db -> D.canonical db ->
    closed V.prim V.merge steensgaard_program (D.view db) ->
    (forall f key output, steensgaard_seed_row q f key output -> row (D.view db) f key output) ->
    forall t u, pointer_congruence q t u -> normal_term db t = normal_term db u.
  Proof.
    intros q db Hwf Hcanonical Hclosed Hseed t u Hcong; induction Hcong.
    - reflexivity.
    - symmetry; exact IHHcong.
    - transitivity (normal_term db u); assumption.
    - cbn [normal_term]; rewrite IHHcong; reflexivity.
    - apply normal_addr; try assumption; apply Hseed.
      split; [reflexivity | exists x, a; split;
        [reflexivity | left; split; [reflexivity | right; assumption]]].
    - apply normal_addr; try assumption; apply Hseed.
      split; [reflexivity | exists x, a; split;
        [reflexivity | left; split; [reflexivity | left; assumption]]].
    - apply normal_copy; try assumption; apply Hseed.
      split; [reflexivity | exists x, y; split;
        [reflexivity | right; left; split; [reflexivity | assumption]]].
    - apply normal_load; try assumption; apply Hseed.
      split; [reflexivity | exists x, y; split;
        [reflexivity | right; right; left; split; [reflexivity | assumption]]].
    - apply normal_store; try assumption; apply Hseed.
      split; [reflexivity | exists x, y; split;
        [reflexivity | right; right; right; split; [reflexivity | assumption]]].
  Qed.

  (** Every source equation holds in the total algebra of a saturated result. *)
  Lemma solve_normal : forall q lim db, solve q lim = (Saturated, db) ->
    forall t u, pointer_congruence q t u -> normal_term db t = normal_term db u.
  Proof.
    intros q lim db Hsolve t u Hcong.
    pose proof (solve_wf q lim) as Hvalid; rewrite Hsolve in Hvalid; cbn [snd] in Hvalid.
    eapply (normal_source q db); [exact (proj1 Hvalid) | exact (proj2 Hvalid) | | | exact Hcong].
    - apply (R.run_closed (compile q) (R.plan (compile q)) lim (seed q) db).
      + apply R.plan_checked; apply program_sorted.
      + exact (proj1 (seed_wf q)).
      + apply seed_loaded.
      + rewrite <- solve_run; exact Hsolve.
    - intros f key output Hseed; pose proof (solve_seed_rows q lim f key output Hseed) as Hrow.
      rewrite Hsolve in Hrow; exact Hrow.
  Qed.

  Lemma solve_covers : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, pointer_congruence q (Deref (Cell x)) (Cell a) -> points db x a = true.
  Proof.
    intros q lim db Hsolve x a Hcong; apply normal_points.
    exact (solve_normal q lim db Hsolve (Deref (Cell x)) (Cell a) Hcong).
  Qed.

End Steensgaard.

Module SteensgaardT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D)
    <: STEENSGAARD_ALL V I J D R.
  Include Steensgaard V I J D R.
  Module SeedTime := PointerSeedTime V I J D R.
  TimeFun compile.
  TimeFun seed_put.
  TimeFun seed.
  TimeFun solve.
  TimeFun lookup_id.
  TimeFun points.
  Definition k_rules : N := (R.c_run * 512 * 512 * 512 + 1)%N.
  Definition k_seed : N := (128 * (D.c_db + 1) * (k_rules + 32) * (k_rules + 32))%N.
  Definition k_wrap : N := 32%N.
  Definition c_steensgaard : N := (k_seed + D.c_db + k_wrap + 32)%N.

  (** Planning the fixed program and storing its slots have a fixed cost budget. *)
  Lemma seed_plan_time : forall q,
    (R.T_plan (compile q) <= k_rules)%N /\
    (N.of_nat (pointer_layout_size (Syntax.slots V.t (R.plan (compile q)))) <= k_rules)%N.
  Proof.
    intro q.
    pose proof (R.T_plan_le (compile q)) as Hplan.
    pose proof (R.plan_slots_le (compile q)) as Hslots.
    change (N.of_nat (pointer_layout_size (Syntax.slots V.t (R.plan (compile q)))) <=
      R.c_run * N.of_nat (R.size_program (compile q) + 1) *
        N.of_nat (R.size_program (compile q) + 1) *
        N.of_nat (R.size_program (compile q) + 1))%N in Hslots.
    assert (Hsize : (N.of_nat (R.size_program (compile q) + 1) <= 512)%N).
    { change (N.of_nat (program_bits steensgaard_program + 1) <= 512)%N; vm_compute; discriminate. }
    assert (Hcube : (R.c_run * N.of_nat (R.size_program (compile q) + 1) *
      N.of_nat (R.size_program (compile q) + 1) * N.of_nat (R.size_program (compile q) + 1) <=
      R.c_run * 512 * 512 * 512)%N).
    { apply N.mul_le_mono; [apply N.mul_le_mono; [apply N.mul_le_mono_l |] |]; exact Hsize. }
    split.
    - eapply N.le_trans; [exact Hplan |].
      eapply N.le_trans; [exact Hcube | unfold k_rules; apply N.le_add_r].
    - eapply N.le_trans; [exact Hslots |].
      eapply N.le_trans; [exact Hcube | unfold k_rules; apply N.le_add_r].
  Qed.

  (** The fixed program's binary declarations and slots bound initialization work. *)
  Lemma seed_init_time : forall q,
    (D.T_init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q))) <=
      64 * (D.c_db + 1) * (k_rules + 8) * (k_rules + 8))%N.
  Proof.
    intro q; apply SeedTime.init_time.
    - apply R.plan_checked; apply program_sorted.
    - vm_compute; repeat constructor.
    - vm_compute; lia.
    - vm_compute; lia.
    - exact (proj2 (seed_plan_time q)).
  Qed.

  (** The generated seed callback charges the database call and constant tuple plumbing. *)
  Lemma seed_put_time : forall db entry,
    (T_seed_put db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N.
  Proof.
    intros db entry; time_unfold T_seed_put; time_simpl; lia.
  Qed.

  (** Folding all seed entries is linear at the final database's spending unit. *)
  Lemma seed_fold_time : forall q,
    let p := compile q in
    let initial := D.init (decls V.t p) (Syntax.slots V.t (R.plan p)) in
    (Std.List.T_fold_left seed_put T_seed_put (pointer_seed_entries 1 q) initial <=
      N.of_nat (D.unit (seed q)) * (16 * D.c_db * (k_rules + 1) + 33) *
        N.of_nat (length (constraints q) + length (initial_pointers q)) + 1)%N.
  Proof.
    intro q; cbn zeta.
    assert (Hslots : (N.of_nat (length (Syntax.slots V.t (R.plan (compile q))) + 1) <=
      k_rules + 1)%N).
    { pose proof (proj2 (seed_plan_time q)) as Hsize.
      pose proof (proj1 (pointer_layout_size_bounds (Syntax.slots V.t (R.plan (compile q)))))
        as Hlength; lia. }
    pose proof (SeedTime.fold_time (compile q) (pointer_seed_entries 1 q) T_seed_put (k_rules + 1)
      (R.plan_checked (compile q) (program_sorted q)) Hslots seed_put_time (seed_entries_ok q))
      as Hfold.
    rewrite pointer_seed_entries_length in Hfold; exact Hfold.
  Qed.

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
  Lemma T_seed_le : forall q,
    (T_seed q <= c_steensgaard *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof.
    intro q.
    pose proof (pointer_seed_entries_time 1 q) as Hentries.
    pose proof (seed_fold_time q) as Hfold; cbn zeta in Hfold.
    pose proof (seed_init_time q) as Hinit.
    pose proof (proj1 (seed_plan_time q)) as Hplan.
    assert (Hcharge : (16 * D.c_db * (k_rules + 1) + 33 <= k_seed)%N).
    { exact (proj1 (pointer_seed_budget D.c_db k_rules)). }
    assert (Hfixed : (D.T_init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q))) +
      R.T_plan (compile q) + 16 <= k_seed)%N).
    { eapply N.le_trans;
        [apply N.add_le_mono_r; apply N.add_le_mono; [exact Hinit | exact Hplan] |].
      exact (proj2 (pointer_seed_budget D.c_db k_rules)). }
    clear Hinit Hplan.
    pose proof (N.mul_le_mono_l _ _ (N.of_nat (D.unit (seed q))) Hcharge) as Hscaled.
    pose proof (N.mul_le_mono_r _ _
      (N.of_nat (length (constraints q) + length (initial_pointers q))) Hscaled) as Hscaled_entries.
    assert (Hfold_bound : (Std.List.T_fold_left seed_put T_seed_put (pointer_seed_entries 1 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))) <=
      N.of_nat (D.unit (seed q)) * k_seed *
        N.of_nat (length (constraints q) + length (initial_pointers q)) + 1)%N) by lia.
    clear Hfold Hcharge Hscaled Hscaled_entries.
    assert (Hunit : (1 <= N.of_nat (D.unit (seed q)))%N).
    { clear - q; pose proof (SeedTime.unit_positive (seed q)); lia. }
    rewrite (proj1 (proj2 (proj2 (seed_invariant q)))); cbn [N.log2 N.to_nat].
    rewrite N.mul_1_r.
    time_unfold T_seed; time_simpl.
    change (pointer_plan_slots (R.plan (compile q))) with
      (Syntax.slots V.t (R.plan (compile q))).
    rewrite (Nat2N.inj_add (length (constraints q) + length (initial_pointers q)) 1)
      in Hentries |- *.
    pose proof (pointer_seed_composition _ _ _ _ D.c_db k_seed _ _
      Hunit Hentries Hfixed Hfold_bound) as Htotal.
    unfold c_steensgaard, k_wrap.
    change (fun db entry => T_seed_put db entry) with T_seed_put.
    replace (k_seed + D.c_db + 32 + 32)%N with (k_seed + D.c_db + 64)%N by lia.
    lia.
  Qed.

  Lemma T_compile_le : forall q, (T_compile q <= c_steensgaard)%N.
  Proof.
    intro q; time_unfold T_compile; time_simpl; unfold c_steensgaard, k_wrap; lia.
  Qed.

  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_steensgaard * (N.of_nat (8 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof.
    intros db x a Hwf.
    pose proof (D.T_lookup_le 6 [Val x] db Hwf) as Hlookup_x.
    pose proof (D.T_lookup_le 6 [Val a] db Hwf) as Hlookup_a.
    pose proof (lookup_id_time 6 [Val x] db) as Htime_x.
    pose proof (lookup_id_time 6 [Val a] db) as Htime_a.
    cbn [length fold_right] in Hlookup_x, Hlookup_a.
    time_unfold T_points; time_simpl.
    destruct (lookup_id 6 [Val x] db) as [pointer |] eqn:Hx;
      destruct (lookup_id 6 [Val a] db) as [address |] eqn:Ha; time_simpl.
    - pose proof (D.T_lookup_le 7 [Id pointer] db Hwf) as Hlookup_p.
      pose proof (lookup_id_time 7 [Id pointer] db) as Htime_p.
      pose proof (lookup_id_unit db 6 [Val x] pointer Hwf Hx) as Hbits_p.
      cbn [length fold_right] in Hlookup_p.
      destruct (lookup_id 7 [Id pointer] db) as [target |] eqn:Ht; time_simpl.
      + pose proof (lookup_id_unit db 7 [Id pointer] target Hwf Ht) as Hbits_t.
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

  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_steensgaard)%N.
  Proof.
    intros q lim; time_unfold T_solve; time_simpl; unfold c_steensgaard, k_wrap; lia.
  Qed.

  Lemma seed_bigO : bigO (fun _ => True)
    (fun q => N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
      D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)))
    T_seed.
  Proof. Admitted. (* STUB *)

  Lemma compile_bigO : bigO (fun _ => True) (fun _ => 0%N) T_compile.
  Proof. Admitted. (* STUB *)

  Lemma points_bigO : bigO (fun z : D.t * positive * positive => D.wf (fst (fst z)))
    (fun z => let '(db, x, a) := z in
      N.of_nat (8 * D.unit db + cell_bits V.encode (Val x) + cell_bits V.encode (Val a) + 1))
    (fun z => let '(db, x, a) := z in T_points db x a).
  Proof. Admitted. (* STUB *)

  Lemma solve_bigO : bigO
    (fun x : N * nat * pointer_input * limits =>
      let '(B, U, q, lim) := x in
      (D.ids (snd (solve q lim)) <= B)%N /\ D.unit (snd (solve q lim)) <= U)
    (fun x => let '(B, U, q, lim) := x in
      (N.of_nat ((length (constraints q) + length (initial_pointers q) + 1) *
        D.unit (seed q) * (N.to_nat (N.log2 (D.ids (seed q))) + 1)) +
      N.of_nat ((R.size_program (compile q) + 1) * (R.size_program (compile q) + 1) *
        (R.size_program (compile q) + 1)) +
      R.run_cost B U (compile q) (R.plan (compile q)) lim (seed q))%N)
    (fun x => let '(_, _, q, lim) := x in T_solve q lim).
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
  Proof.
    intros q lim db Hsolve t u Hcong i j Hi Hj.
    pose proof (solve_wf q lim) as Hvalid; rewrite Hsolve in Hvalid; cbn [snd] in Hvalid.
    destruct Hvalid as [Hwf Hcanonical].
    pose proof (solve_normal q lim db Hsolve t u Hcong) as Hnormal.
    rewrite (normal_represents db t i Hwf Hcanonical Hi),
      (normal_represents db u j Hwf Hcanonical Hj) in Hnormal.
    apply (proj2 (D.same_repr db i j Hwf)); congruence.
  Qed.

  Lemma F4_endpoints_represented : forall q lim db x a,
    solve q lim = (Saturated, db) -> pointer_congruence q (Deref (Cell x)) (Cell a) ->
    (exists i, represents (D.view db) (Id i) (pointer_expression (Deref (Cell x)))) /\
    (exists j, represents (D.view db) (Id j) (pointer_expression (Cell a))).
  Proof.
    intros q lim db x a Hsolve Hcong.
    pose proof (solve_wf q lim) as Hvalid; rewrite Hsolve in Hvalid; cbn [snd] in Hvalid.
    pose proof (solve_covers q lim db Hsolve x a Hcong) as Hpoints.
    destruct (points_spec db x a (proj1 Hvalid) (proj2 Hvalid)) as [Hrep | Hnone]; [|discriminate].
    destruct Hrep as [i [j [Hi [Hj Hsame]]]]; split; [exists i | exists j]; assumption.
  Qed.

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
  Proof.
    intros q lim; time_unfold T_solve; time_simpl; unfold k_wrap; lia.
  Qed.

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

  (** The compiled source equations are accepted by the sort checker. *)
  Lemma program_sorted : forall q, program_ok (A.compile q).
  Proof.
    intro q; rewrite A.compile_rules.
    apply (proj1 (check_program_spec V.t steensgaard_program)); vm_compute; reflexivity.
  Qed.

  (** Identifier-free source rows satisfy the quotient interpretation. *)
  Lemma seed_sat : forall q,
    sat V.merge (concrete_model q) (fun _ => Q.cell q 1%positive) (D.view (A.seed q)).
  Proof.
    intro q; split.
    - intros f key output Hrow; apply A.seed_rows in Hrow.
      destruct Hrow as [Ho [x [y [Hkey Hsource]]]]; subst output key.
      unfold holds; rewrite (proj1 (A.seed_loaded q) f), A.compile_rules.
      destruct Hsource as [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [Hf Hin]]]]; subst f;
        cbn [program_kind steensgaard_program decls lookup_kind map den concrete_model rel];
        exists x, y; split; try reflexivity; unfold source_relation; tauto.
    - split; [intros i j Hsame; reflexivity |].
      intros f m key a b Hkind Hlat Hlat'; exact Hlat.
  Qed.

  (** Translating a pointer term preserves its meaning in the quotient algebra. *)
  Lemma expression_denote : forall q t,
    denote (concrete_model q) (pointer_expression t) =
      inl (pointer_denote (Q.cell q) (Q.deref q) t).
  Proof.
    intros q t; induction t as [x | t IH].
    - reflexivity.
    - cbn [pointer_expression denote map]; rewrite IH; reflexivity.
  Qed.

  (** Saturated query answers are exactly the source congruence approximation. *)
  Lemma solve_exact : forall q lim db, A.solve q lim = (Saturated, db) ->
    forall x a, A.points db x a = true <-> pointer_congruence q (Deref (Cell x)) (Cell a).
  Proof.
    intros q lim db Hsolve x a; split.
    - intro Hpoints; pose proof (A.solve_wf q lim) as Hvalid.
      rewrite Hsolve in Hvalid; cbn [snd] in Hvalid; destruct Hvalid as [Hwf Hcanonical].
      assert (Hrepresented : exists i j,
        represents (D.view db) (Id i) (pointer_expression (Deref (Cell x))) /\
        represents (D.view db) (Id j) (pointer_expression (Cell a)) /\ same (D.view db) i j).
      { destruct (A.points_spec db x a Hwf Hcanonical); [assumption | discriminate]. }
      destruct Hrepresented as [i [j [Hi [Hj Hij]]]].
      destruct (R.run_sat (A.compile q) (R.plan (A.compile q)) lim (A.seed q)
        (concrete_model q) (fun _ => Q.cell q 1%positive)
        (R.plan_checked (A.compile q) (program_sorted q)) (proj1 (A.seed_wf q)) (A.seed_loaded q)
        (valid_sorted_of_valid V.t V.prim V.merge (concrete_model q) (A.compile q) (rules_valid q))
        (seed_sat q)) as [nu [Hextends Hsat]].
      rewrite <- A.solve_run, Hsolve in Hsat; cbn [snd] in Hsat.
      assert (Hi_den : den nu (Id i) =
        denote (concrete_model q) (pointer_expression (Deref (Cell x)))).
      { eapply represents_den; [exact Hsat | exact Hi]. }
      assert (Hj_den : den nu (Id j) =
        denote (concrete_model q) (pointer_expression (Cell a))).
      { eapply represents_den; [exact Hsat | exact Hj]. }
      rewrite expression_denote in Hi_den, Hj_den; cbn [den] in Hi_den, Hj_den.
      injection Hi_den as Hi_eq; injection Hj_den as Hj_eq.
      apply (proj1 (Q.source_exact q (Deref (Cell x)) (Cell a))).
      change (Q.deref q (Q.cell q x) = Q.cell q a).
      rewrite <- Hi_eq, <- Hj_eq; exact (proj1 (proj2 Hsat) i j Hij).
    - apply (A.solve_covers q lim db Hsolve x a).
  Qed.
End SteensgaardExact.
