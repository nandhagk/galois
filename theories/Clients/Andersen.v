(** * Inclusion-based pointer analysis driver

    This driver compiles source constraints and queries their least inclusion solution.
    For example, an address constraint seeds a row used by the first inclusion rule.
    Builds on: AndersenSig and the relational database and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
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

(** Each source instruction is stored in its own binary relation. *)
Definition pointer_constraint_entry (instruction : pointer_constraint) :
    positive * (positive * positive) :=
  match instruction with
  | Addr x y => (1%positive, (x, y))
  | Copy x y => (2%positive, (x, y))
  | Load x y => (3%positive, (x, y))
  | Store x y => (4%positive, (x, y))
  end.
TimeFun pointer_constraint_entry.

(** Initial pointers use the relation chosen by the analysis client. *)
Definition pointer_seed_entries (initial_relation : positive) (q : pointer_input) :
    list (positive * (positive * positive)) :=
  match q with
  | PointerInput instructions initial =>
    map pointer_constraint_entry instructions ++
      map (fun pointer => (initial_relation, pointer)) initial
  end.
TimeFun pointer_seed_entries.

(** Reading a plan's slot layout is one record elimination. *)
Definition pointer_plan_slots {V} (plan : compiled V) : list (positive * list nat) :=
  match plan with Compiled _ layout _ _ => layout end.
TimeFun pointer_plan_slots.

(** Entry membership is exactly a source constraint or a listed initial pointer. *)
Lemma pointer_seed_entries_spec : forall initial_relation q f x y,
  In (f, (x, y)) (pointer_seed_entries initial_relation q) <->
    (f = 1%positive /\ In (Addr x y) (constraints q)) \/
    (f = 2%positive /\ In (Copy x y) (constraints q)) \/
    (f = 3%positive /\ In (Load x y) (constraints q)) \/
    (f = 4%positive /\ In (Store x y) (constraints q)) \/
    (f = initial_relation /\ In (x, y) (initial_pointers q)).
Proof.
  intros initial_relation [instructions initial] f x y.
  cbn [pointer_seed_entries constraints initial_pointers]; rewrite in_app_iff; split.
  - intros [Hinstruction | Hinitial].
    + apply in_map_iff in Hinstruction; destruct Hinstruction as [instruction [Heq Hin]].
      destruct instruction; cbn [pointer_constraint_entry] in Heq; inversion Heq; subst;
        tauto.
    + apply in_map_iff in Hinitial; destruct Hinitial as [[a b] [Heq Hin]].
      inversion Heq; subst; tauto.
  - intros [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [Hf Hin]]]]]; subst f.
    + left; apply in_map_iff; exists (Addr x y); auto.
    + left; apply in_map_iff; exists (Copy x y); auto.
    + left; apply in_map_iff; exists (Load x y); auto.
    + left; apply in_map_iff; exists (Store x y); auto.
    + right; apply in_map_iff; exists (x, y); auto.
Qed.

(** A successful declaration search agrees with both declaration lookup functions. *)
Lemma pointer_declaration_lookup : forall ds f d,
  find (fun entry => Pos.eqb (name entry) f) ds = Some d ->
  lookup_kind ds f = Some (out d) /\ lookup_sorts ds f = Some (arg_sorts d).
Proof.
  induction ds as [|entry rest IH]; intros f d Hfind; [discriminate |].
  cbn [find lookup_kind lookup_sorts] in *.
  destruct (Pos.eqb (name entry) f) eqn:Hname.
  - inversion Hfind; subst d; split; reflexivity.
  - apply IH; exact Hfind.
Qed.

(** Seeding preserves a relational database and records exactly the inserted value pairs. *)
Module PointerSeedFacts (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D).
  Definition put_entry (db : D.t) (entry : positive * (positive * positive)) : D.t :=
    D.put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None db.
  Definition entry_ok (p : program V.t) (entry : positive * (positive * positive)) :=
    program_kind p (fst entry) = Some ORel /\
    program_sorts p (fst entry) = Some [SVal; SVal].
  Definition entry_row (entry : positive * (positive * positive)) f k
      (o : option (cell V.t)) :=
    f = fst entry /\ k = [Val (fst (snd entry)); Val (snd (snd entry))] /\ o = None.
  Definition invariant (p : program V.t) (db : D.t) :=
    D.wf db /\ R.loaded p (R.plan p) db /\ R.no_ids db.

  (** Every slot of a checked binary relation accepts its two value arguments. *)
  Lemma entry_kind_ok : forall p db entry, R.plans_ok p (R.plan p) ->
    R.loaded p (R.plan p) db -> entry_ok p entry ->
    D.kind_ok db (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None.
  Proof.
    intros p db [f [x y]] Hplan [Hkinds [Hslots Hsorted]] [Hkind Hsort].
    cbn [fst snd] in *; split.
    - intros i Hin; cbn [option_list app] in Hin.
      destruct Hin as [Heq | [Heq | Hnone]]; discriminate || contradiction.
    - split.
      + intros perm Hin; rewrite Hslots in Hin.
        destruct (R.check_plan_slots p (R.plan p) f perm Hplan Hin)
          as [d [Hfind [Hdistinct Hbounds]]].
        destruct (pointer_declaration_lookup (decls V.t p) f d Hfind) as [Hout Hargs].
        assert (Hout_eq : out d = ORel) by (unfold program_kind in Hkind; congruence).
        assert (Hargs_eq : arg_sorts d = [SVal; SVal]) by
          (unfold program_sorts in Hsort; congruence).
        rewrite Hout_eq, Hargs_eq in Hbounds; cbn in Hbounds.
        split; [exact Hdistinct | exact Hbounds].
      + rewrite Hkinds, Hkind; exact I.
  Qed.

  (** Inserting a relation row adds that row and preserves every old relation row. *)
  Lemma entry_rows : forall p db entry, R.plans_ok p (R.plan p) ->
    invariant p db -> entry_ok p entry -> forall f k o,
    row (D.view (put_entry db entry)) f k o <-> row (D.view db) f k o \/ entry_row entry f k o.
  Proof.
    intros p db [g [x y]] Hplan [Hwf [Hloaded [Hids Hrows]]] Hentry f k o.
    pose proof (entry_kind_ok p db (g, (x, y)) Hplan Hloaded Hentry) as Hkind.
    assert (Hcombine : D.combine db g (D.old db g [Val x; Val y]) None = None).
    { destruct (D.old db g [Val x; Val y]) as [[c |] |] eqn:Hlookup; [|reflexivity|reflexivity].
      pose proof (proj1 (D.old_row db g [Val x; Val y] (Some c) Hwf) Hlookup) as Hrow.
      destruct (Hrows g [Val x; Val y] (Some c) Hrow) as [Hnone _]; discriminate. }
    unfold put_entry, entry_row; cbn [fst snd].
    rewrite (D.put_rows g [Val x; Val y] None db Hwf Hkind).
    change (((row (D.view db) f k o /\ (f, k) <> (g, [Val x; Val y])) \/
      (f = g /\ k = [Val x; Val y] /\
        D.combine db g (D.old db g [Val x; Val y]) None = o)) <->
      row (D.view db) f k o \/ (f = g /\ k = [Val x; Val y] /\ o = None)).
    rewrite Hcombine; split.
    - intros [[Hrow Hneq] | [Hf [Hk Ho]]]; [left; exact Hrow | right; auto].
    - intros [Hrow | [Hf [Hk Ho]]].
      + destruct (Pos.eq_dec f g) as [Hf | Hf].
        * subst f.
          assert (Hkeys : {k = [Val x; Val y]} + {k <> [Val x; Val y]}).
          { decide equality; decide equality; apply Pos.eq_dec. }
          destruct Hkeys as [Hk | Hk].
          -- right; subst k; repeat split; try reflexivity.
             symmetry; exact (proj1 (Hrows g [Val x; Val y] o Hrow)).
          -- left; split; [exact Hrow | congruence].
        * left; split; [exact Hrow | congruence].
      + right; auto.
  Qed.

  (** Adding a well-sorted relation row preserves the complete seeding invariant. *)
  Lemma entry_invariant : forall p db entry, R.plans_ok p (R.plan p) ->
    invariant p db -> entry_ok p entry -> invariant p (put_entry db entry).
  Proof.
    intros p db entry Hplan Hinv Hentry.
    destruct Hinv as [Hwf [Hloaded Hnoids]].
    destruct Hloaded as [Hkinds [Hslots Hsorted]].
    destruct Hnoids as [Hids Hrows].
    pose proof (entry_kind_ok p db entry Hplan (conj Hkinds (conj Hslots Hsorted)) Hentry)
      as Hkind.
    destruct (D.layout_put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))]
      None db Hwf) as [Hkind_next [Hslots_next [Hids_next Hpending]]].
    assert (Hrow_spec : forall f k o, row (D.view (put_entry db entry)) f k o <->
      row (D.view db) f k o \/ entry_row entry f k o).
    { apply entry_rows with (p := p).
      - exact Hplan.
      - exact (conj Hwf (conj (conj Hkinds (conj Hslots Hsorted)) (conj Hids Hrows))).
      - exact Hentry. }
    unfold invariant, put_entry; split; [apply D.wf_put; assumption | split].
    - split; [intro f; rewrite Hkind_next; apply Hkinds | split].
      + rewrite Hslots_next; exact Hslots.
      + intros f k o Hrow; apply Hrow_spec in Hrow.
        destruct Hrow as [Hrow | [Hf [Hk Ho]]].
        * unfold row_sorted; rewrite Hkind_next; apply Hsorted; exact Hrow.
        * subst f k o; exists ORel; split; [exact (proj2 Hentry) | split; [|reflexivity]].
          rewrite Hkind_next, Hkinds; exact (proj1 Hentry).
    - split; [rewrite Hids_next; exact Hids |].
      intros f k o Hrow; apply Hrow_spec in Hrow.
      destruct Hrow as [Hrow | [Hf [Hk Ho]]].
      + exact (Hrows f k o Hrow).
      + subst k o; split; [reflexivity |].
        constructor; [eexists; reflexivity | constructor; [eexists; reflexivity | constructor]].
  Qed.

  (** Folding over compatible entries preserves the seeding invariant. *)
  Lemma fold_invariant : forall p entries db, R.plans_ok p (R.plan p) ->
    invariant p db -> Forall (entry_ok p) entries ->
    invariant p (fold_left put_entry entries db).
  Proof.
    intros p entries; induction entries as [|entry rest IH]; intros db Hplan Hinv Hentries.
    - exact Hinv.
    - inversion Hentries as [|e es Hentry Hrest]; subst.
      apply IH; [exact Hplan | eapply entry_invariant; eassumption | exact Hrest].
  Qed.

  (** Folding inserts exactly the listed entries in addition to the initial rows. *)
  Lemma fold_rows : forall p entries db, R.plans_ok p (R.plan p) ->
    invariant p db -> Forall (entry_ok p) entries -> forall f k o,
    row (D.view (fold_left put_entry entries db)) f k o <->
      row (D.view db) f k o \/ exists entry, In entry entries /\ entry_row entry f k o.
  Proof.
    intros p entries; induction entries as [|entry rest IH]; intros db Hplan Hinv Hentries f k o.
    - cbn [fold_left]; split; [auto | intros [Hrow | [e [Hnone _]]]; [exact Hrow | contradiction]].
    - inversion Hentries as [|e es Hentry Hrest]; subst; cbn [fold_left].
      rewrite (IH (put_entry db entry) Hplan
        (entry_invariant p db entry Hplan Hinv Hentry) Hrest f k o).
      rewrite (entry_rows p db entry Hplan Hinv Hentry f k o).
      split.
      + intros [[Hrow | Hnew] | [e [Hin He]]].
        * left; exact Hrow.
        * right; exists entry; split; [left; reflexivity | exact Hnew].
        * right; exists e; split; [right; exact Hin | exact He].
      + intros [Hrow | [e [[Heq | Hin] He]]].
        * left; left; exact Hrow.
        * subst e; left; right; exact He.
        * right; exists e; auto.
  Qed.

  (** Database initialization establishes the empty relational invariant. *)
  Lemma init_invariant : forall p,
    invariant p (D.init (decls V.t p) (Syntax.slots V.t (R.plan p))).
  Proof.
    intro p; split; [apply D.wf_init | split].
    - split.
      + intro f; exact (proj1 (proj2 (proj2
          (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) f [] None 1 1)))).
      + split.
        * exact (proj1 (proj2 (proj2 (proj2
            (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) 1 [] None 1 1))))).
        * intros f k o Hrow.
          apply (proj1 (proj1
            (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) f k o 1 1))) in Hrow.
          contradiction.
    - split.
      + exact (proj1 (proj2 (proj2 (proj2 (proj2
          (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) 1 [] None 1 1)))))).
      + intros f k o Hrow.
        apply (proj1 (proj1
          (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) f k o 1 1))) in Hrow.
        contradiction.
  Qed.

  (** An identifier-free relational database is canonical. *)
  Lemma no_ids_canonical : forall db, R.no_ids db -> D.canonical db.
  Proof.
    intros db [Hids Hrows] f k o Hrow i Hin.
    destruct (Hrows f k o Hrow) as [Ho Hvalues]; subst o.
    cbn [option_list] in Hin; rewrite app_nil_r in Hin.
    apply (proj1 (Forall_forall _ _) Hvalues) in Hin.
    destruct Hin as [v Heq]; discriminate.
  Qed.
End PointerSeedFacts.

Module AndersenCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: ANDERSEN_OPS V I J D R.
  Definition compile (_ : pointer_input) : program V.t := andersen_program.
  Definition seed_put (db : D.t) (entry : positive * (positive * positive)) : D.t :=
    D.put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None db.
  Definition seed (q : pointer_input) : D.t :=
    fold_left seed_put (pointer_seed_entries 5 q)
      (D.init (decls V.t (compile q)) (pointer_plan_slots (R.plan (compile q)))).
  Definition solve (q : pointer_input) (lim : limits) : stop * D.t :=
    let p := compile q in R.run p (R.plan p) lim (seed q).
  Definition points (db : D.t) (x a : positive) : bool :=
    match fst (D.lookup 5 [Val x; Val a] db) with
    | Some None => true
    | _ => false
    end.
End AndersenCode.

Module Andersen (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: ANDERSEN V I J D R.
  Include AndersenCode V I J D R.
  Module Seeds := PointerSeedFacts V I J D R.

  (** The fixed inclusion program passes the source sort checker. *)
  Lemma program_sorted : forall q, program_ok (compile q).
  Proof.
    intro q; apply (proj1 (check_program_spec V.t (compile q))); vm_compute; reflexivity.
  Qed.

  (** Every seed entry targets a declared binary relation. *)
  Lemma seed_entries_ok : forall q, Forall (Seeds.entry_ok (compile q)) (pointer_seed_entries 5 q).
  Proof.
    intros [instructions initial]; cbn [pointer_seed_entries]; apply Forall_app; split.
    - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin.
      destruct Hin as [instruction [Heq Hin]]; subst entry; destruct instruction; split; reflexivity.
    - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin.
      destruct Hin as [[x y] [Heq Hin]]; subst entry; split; reflexivity.
  Qed.

  (** Seeding establishes well-formedness, the plan layout and identifier-free rows. *)
  Lemma seed_invariant : forall q, Seeds.invariant (compile q) (seed q).
  Proof.
    intro q; change (Seeds.invariant (compile q)
      (fold_left Seeds.put_entry (pointer_seed_entries 5 q)
        (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))))).
    apply Seeds.fold_invariant.
    - apply R.plan_checked; apply program_sorted.
    - apply Seeds.init_invariant.
    - apply seed_entries_ok.
  Qed.

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
  Proof.
    intros q f k o.
    change (row (D.view (fold_left Seeds.put_entry (pointer_seed_entries 5 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))))) f k o <->
      pointer_seed_row q f k o).
    rewrite (Seeds.fold_rows (compile q) (pointer_seed_entries 5 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q))))
      (R.plan_checked (compile q) (program_sorted q)) (Seeds.init_invariant (compile q))
      (seed_entries_ok q) f k o).
    split.
    - intros [Hinitial | [[g [x y]] [Hin [Hf [Hk Ho]]]]].
      + apply (proj1 (proj1 (D.init_view (decls V.t (compile q))
          (Syntax.slots V.t (R.plan (compile q))) f k o 1 1))) in Hinitial; contradiction.
      + cbn [fst snd] in Hf, Hk; subst f k o.
        split; [reflexivity | exists x, y; split; [reflexivity |]].
        apply pointer_seed_entries_spec in Hin; exact Hin.
    - intros [Ho [x [y [Hk Hsource]]]]; subst k o; right.
      exists (f, (x, y)); split.
      + apply pointer_seed_entries_spec; exact Hsource.
      + repeat split; reflexivity.
  Qed.

  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof.
    intro q; exact (proj1 (proj2 (seed_invariant q))).
  Qed.

  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  Proof.
    intro q; destruct (seed_invariant q) as [Hwf [Hloaded Hnoids]].
    split; [exact Hwf | split; [apply Seeds.no_ids_canonical; exact Hnoids | exact Hnoids]].
  Qed.

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof.
    reflexivity.
  Qed.

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) 5 [Val x; Val a] None) (points db x a).
  Proof.
    intros db x a Hwf Hcanonical.
    change (reflect (row (D.view db) 5 [Val x; Val a] None)
      (match fst (D.lookup 5 [Val x; Val a] db) with Some None => true | _ => false end)).
    rewrite (proj1 (D.lookup_spec 5 [Val x; Val a] db Hwf)).
    change (reflect (row (D.view db) 5 [Val x; Val a] None)
      (match D.old db 5 [Val x; Val a] with Some None => true | _ => false end)).
    destruct (D.old db 5 [Val x; Val a]) as [[c |] |] eqn:Hlookup.
    - constructor; intro Hrow.
      apply (proj2 (D.old_row db 5 [Val x; Val a] None Hwf)) in Hrow; congruence.
    - constructor; apply (proj1 (D.old_row db 5 [Val x; Val a] None Hwf)); exact Hlookup.
    - constructor; intro Hrow.
      apply (proj2 (D.old_row db 5 [Val x; Val a] None Hwf)) in Hrow; congruence.
  Qed.

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    destruct (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hwf [Hcanonical Hloaded]]; auto.
  Qed.

  Lemma solve_saturates : forall q lim,
    N.to_nat (max_iter lim) >= 2 * R.herbrand (compile q) (seed q) + 2 ->
    fst (solve q lim) = Saturated.
  Proof.
    intros q lim Hfuel; rewrite solve_run; apply R.run_terminates.
    - apply R.plan_checked; apply program_sorted.
    - exact (proj1 (seed_wf q)).
    - apply seed_loaded.
    - reflexivity.
    - reflexivity.
    - exact (proj2 (proj2 (seed_wf q))).
    - exact Hfuel.
  Qed.

  Lemma solve_exact : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> may_points q x a.
  Proof. Admitted. (* STUB *)

End Andersen.

Module AndersenT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D) <: ANDERSEN_ALL V I J D R.
  Include Andersen V I J D R.
  TimeFun compile.
  TimeFun seed_put.
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
