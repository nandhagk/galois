(** * Inclusion-based pointer analysis driver

    This driver compiles source constraints and queries their least inclusion solution.
    The seed helpers shared with the Steensgaard client stay here.
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

From Stdlib Require Import List PArith NArith Bool Lia Arith.
From Argent Require Import Time Tactics Std Complexity.
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


(** Evaluating the same list of terms twice yields the same list of cells. *)
Lemma pointer_terms_unique : forall (rho : env (V := positive)) ts first second,
  terms_value rho ts first -> terms_value rho ts second -> first = second.
Proof.
  intros rho ts first second Hfirst; revert second.
  induction Hfirst as [|t c ts cs Hvalue Htail IH]; intros second Hsecond.
  - inversion Hsecond; reflexivity.
  - inversion Hsecond as [|t' c' ts' cs' Hvalue' Htail']; subst.
    f_equal.
    + destruct t; cbn [term_value] in Hvalue, Hvalue'; congruence.
    + apply IH; exact Htail'.
Qed.

(** A list of value cells determines its underlying values uniquely. *)
Lemma pointer_values_unique : forall (cells : list (cell positive)) first second,
  values cells first -> values cells second -> first = second.
Proof.
  intros cells first second Hfirst; revert second.
  induction Hfirst as [|c v cells vals Hvalue Htail IH]; intros second Hsecond.
  - inversion Hsecond; reflexivity.
  - inversion Hsecond as [|c' v' cells' vals' Hvalue' Htail']; subst.
    f_equal; [congruence | apply IH; exact Htail'].
Qed.

(** A derivable action output occurs in every output-free view where the actions are present. *)
(** A binary relation row satisfies the corresponding variable-only query atom. *)
Lemma pointer_atom_row : forall prim w rho f u v x y,
  rho u = Some (Val x) -> rho v = Some (Val y) -> row w f [Val x; Val y] None ->
  atom_holds prim w rho (Fun positive f [Var u; Var v] None).
Proof.
  intros prim w rho f u v x y Hx Hy Hrow; exists [Val x; Val y], None; split.
  - constructor; [exact Hx | constructor; [exact Hy | constructor]].
  - split; [exact I | exact Hrow].
Qed.

(** A present relational action gives its precise row when that relation has no outputs. *)

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

(** Each source item contributes exactly one seed entry. *)
Lemma pointer_seed_entries_length : forall initial_relation q,
  length (pointer_seed_entries initial_relation q) =
    length (constraints q) + length (initial_pointers q).
Proof.
  intros initial_relation [instructions initial].
  cbn [pointer_seed_entries constraints initial_pointers].
  rewrite length_app, !length_map; reflexivity.
Qed.

(** Encoding and concatenating the source seed entries takes linear list work. *)
Lemma pointer_seed_entries_time : forall initial_relation q,
  (T_pointer_seed_entries initial_relation q <=
    16 * N.of_nat (length (constraints q) + length (initial_pointers q) + 1))%N.
Proof.
  intros initial_relation [instructions initial].
  assert (Hconstraint : forall c, (T_pointer_constraint_entry c <= 1)%N).
  { intro c; destruct c; reflexivity. }
  pose proof (ListDef.T_map_le pointer_constraint_entry T_pointer_constraint_entry 1 instructions
    Hconstraint) as Hmap.
  pose proof (ListDef.T_map_le (fun pointer : positive * positive => (initial_relation, pointer))
    (fun _ => 1%N) 1 initial ltac:(intros; reflexivity)) as Hinitial.
  pose proof (Datatypes.T_app_le (map pointer_constraint_entry instructions)
    (map (fun pointer => (initial_relation, pointer)) initial)) as Happ.
  rewrite length_map in Happ.
  time_unfold T_pointer_seed_entries; time_simpl.
  cbn [constraints initial_pointers]; rewrite !Nat2N.inj_add.
  unfold T_pointer_constraint_entry in Hmap; nia.
Qed.

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

(** A fixed plan is charged for each function name and each selected position. *)
Definition pointer_layout_size (sl : list (positive * list nat)) : nat :=
  fold_right (fun s n => Pos.size_nat (fst s) + length (snd s) + 1 + n) 0 sl.

(** The plan-size sum bounds its slot count, tuple lengths and function-name sizes. *)
Lemma pointer_layout_size_bounds : forall sl,
  length sl <= pointer_layout_size sl /\
  fold_right (fun s n => length (snd s) + n) 0 sl <= pointer_layout_size sl /\
  fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl <= pointer_layout_size sl.
Proof.
  intro sl; induction sl as [|[f perm] rest [Hcount [Hlength Hnames]]].
  - repeat split; reflexivity.
  - unfold pointer_layout_size in *; cbn [length fold_right fst snd] in *.
    split; [|split]; lia.
Qed.

(** A permutation of at most two positions has a fixed preparation budget. *)
Lemma pointer_permutation_work : forall perm, NoDup perm -> Forall (fun i => i < 2) perm ->
  (length perm + 1) * (fold_right Nat.add 0 (map S perm) + length perm + 1) <= 21.
Proof.
  intros perm Hdistinct Hbounds.
  assert (Hlength : length perm <= 2).
  { change (length perm <= length [0; 1]); apply NoDup_incl_length; [exact Hdistinct |].
    intros i Hin; apply (proj1 (Forall_forall _ _) Hbounds) in Hin.
    cbn; lia. }
  assert (Hsum : fold_right Nat.add 0 (map S perm) <= 2 * length perm).
  { clear Hlength Hdistinct.
    induction Hbounds as [|i rest Hi Hrest IH]; cbn [map fold_right length]; lia. }
  nia.
Qed.

(** Preparing binary slots costs at most a fixed multiple of their encoded size. *)
Lemma pointer_layout_work : forall sl,
  Forall (fun s => NoDup (snd s) /\ Forall (fun i => i < 2) (snd s)) sl ->
  layout_work sl <= 21 * pointer_layout_size sl.
Proof.
  intros sl Hslots; induction Hslots as [|[f perm] rest [Hdistinct Hbounds] Hrest IH].
  - reflexivity.
  - pose proof (pointer_permutation_work perm Hdistinct Hbounds) as Hperm.
    unfold layout_work, pointer_layout_size in *; cbn [map fold_right fst snd] in *; nia.
Qed.

Module PointerSeedTime (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D).
  Module Facts := PointerSeedFacts V I J D R.

  (** Checked plans for binary tuples have only permutations of the two positions. *)
  Lemma binary_plan_slots : forall p, R.plans_ok p (R.plan p) ->
    Forall (fun d => length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end <= 2)
      (decls V.t p) ->
    Forall (fun s => NoDup (snd s) /\ Forall (fun i => i < 2) (snd s))
      (Syntax.slots V.t (R.plan p)).
  Proof.
    intros p Hplan Hdecls; apply Forall_forall; intros [f perm] Hin.
    destruct (R.check_plan_slots p (R.plan p) f perm Hplan Hin)
      as [d [Hfind [Hdistinct Hbounds]]].
    split; [exact Hdistinct |].
    apply find_some in Hfind; destruct Hfind as [Hdecl Hname].
    apply (proj1 (Forall_forall _ _) Hdecls) in Hdecl.
    apply Forall_forall; intros i Hin_position.
    apply (proj1 (Forall_forall _ _) Hbounds) in Hin_position; lia.
  Qed.

  (** Initializing a binary fixed program is quadratic in the bounded plan size. *)
  Lemma init_time : forall p K, R.plans_ok p (R.plan p) ->
    Forall (fun d => length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end <= 2)
      (decls V.t p) ->
    length (decls V.t p) <= 8 ->
    fold_right (fun d n => Pos.size_nat (name d) + n) 0 (decls V.t p) <= 32 ->
    (N.of_nat (pointer_layout_size (Syntax.slots V.t (R.plan p))) <= K)%N ->
    (D.T_init (decls V.t p) (Syntax.slots V.t (R.plan p)) <=
      64 * (D.c_db + 1) * (K + 8) * (K + 8))%N.
  Proof.
    intros p K Hplan Hdecls Hcount Hnames Hsize.
    pose proof (D.T_init_le (decls V.t p) (Syntax.slots V.t (R.plan p))) as Hinit.
    pose proof (pointer_layout_size_bounds (Syntax.slots V.t (R.plan p)))
      as [Hslots [Hlengths Hslot_names]].
    pose proof (pointer_layout_work (Syntax.slots V.t (R.plan p))
      (binary_plan_slots p Hplan Hdecls)) as Hwork.
    apply time_of_nat_le in Hcount; apply time_of_nat_le in Hnames.
    apply time_of_nat_le in Hslots; apply time_of_nat_le in Hlengths.
    apply time_of_nat_le in Hslot_names; apply time_of_nat_le in Hwork.
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *; nia.
  Qed.
(** Scaling a nonnegative amortized credit to a larger positive unit is sound. *)
  Lemma credit_scale : forall (ticks charge before after : N) (u U : nat),
    (1 <= u)%nat -> (u <= U)%nat ->
    (ticks + N.of_nat u * after <= N.of_nat u * (charge + before))%N ->
    (ticks + N.of_nat U * after <= N.of_nat U * (charge + before))%N.
  Proof.
    intros ticks charge before after u U Hpositive Hunit Hcredit.
    assert (Hu : (0 < N.of_nat u)%N) by lia.
    assert (HuU : (N.of_nat u <= N.of_nat U)%N) by lia.
    assert (Hbalance : (after <= charge + before)%N) by nia.
    nia.
  Qed.

  (** Every database spending unit is positive by its manifest definition. *)
  Lemma unit_positive : forall db, (1 <= D.unit db)%nat.
  Proof.
    intro db. unfold D.unit. nia.
  Qed.

  (** A loaded database has at most as many matching slots as the complete plan. *)
  Lemma entry_slots : forall p db f, R.loaded p (R.plan p) db ->
    (D.slots_of db f <= length (Syntax.slots V.t (R.plan p)))%nat.
  Proof.
    intros p db f [_ [Hslots _]]. unfold D.slots_of. rewrite Hslots.
    apply filter_length_le.
  Qed.

  (** The unit of every intermediate seed is bounded by the completed fold's unit. *)
  Lemma fold_unit_mono : forall p entries db,
    R.plans_ok p (R.plan p) -> Facts.invariant p db ->
    Forall (Facts.entry_ok p) entries ->
    (D.unit db <= D.unit (fold_left Facts.put_entry entries db))%nat.
  Proof.
    intros p entries. induction entries as [|entry rest IH]; intros db Hplan Hinv Hentries.
    - reflexivity.
    - inversion Hentries as [|entry' rest' Hentry Hrest]; subst.
      cbn [fold_left]. eapply Nat.le_trans.
      + unfold Facts.put_entry. apply D.unit_mono_put. exact (proj1 Hinv).
      + apply IH; [exact Hplan| |exact Hrest].
        exact (Facts.entry_invariant p db entry Hplan Hinv Hentry).
  Qed.

  (** A binary value-row insertion pays its clock and credit at any final upper unit. *)
  Lemma entry_credit : forall p (T_entry : D.t -> positive * (positive * positive) -> N)
      (K : N) (U : nat) db entry,
    R.plans_ok p (R.plan p) -> Facts.invariant p db -> Facts.entry_ok p entry ->
    (N.of_nat (length (Syntax.slots V.t (R.plan p)) + 1) <= K)%N ->
    (D.unit (Facts.put_entry db entry) <= U)%nat ->
    (T_entry db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N ->
    (T_entry db entry + N.of_nat U * D.potential 0 (Facts.put_entry db entry) <=
      N.of_nat U * ((16 * D.c_db * K + 32) + D.potential 0 db))%N.
  Proof.
    intros p T_entry K U db [f [x y]] Hplan Hinv Hentry HK HU Hclock.
    pose proof (Facts.entry_invariant p db (f, (x, y)) Hplan Hinv Hentry) as Hnext.
    pose proof (Facts.entry_kind_ok p db (f, (x, y)) Hplan
      (proj1 (proj2 Hinv)) Hentry) as Hkind.
    assert (Hids : (D.ids (D.put f [Val x; Val y] None db) <= 0)%N).
    { change (D.ids (Facts.put_entry db (f, (x, y))) <= 0)%N.
      rewrite (proj1 (proj2 (proj2 Hnext))). reflexivity. }
    pose proof (D.T_put_amort 0 f [Val x; Val y] None db (proj1 Hinv)
      (proj1 (proj2 Hkind)) Hids) as Hraw.
    change (D.T_put f [Val x; Val y] None db +
      N.of_nat (D.unit (Facts.put_entry db (f, (x, y)))) *
        D.potential 0 (Facts.put_entry db (f, (x, y))) <=
      N.of_nat (D.unit (Facts.put_entry db (f, (x, y)))) *
        (D.c_db * 16 * N.of_nat (D.slots_of db f + 1) * 1 + D.potential 0 db))%N in Hraw.
    rewrite N.mul_1_r in Hraw.
    pose proof (credit_scale _ _ _ _ _ U
      (unit_positive (Facts.put_entry db (f, (x, y)))) HU Hraw) as Hscaled.
    pose proof (entry_slots p db f (proj1 (proj2 Hinv))) as Hslots.
    assert (HslotN : (N.of_nat (D.slots_of db f + 1) <= K)%N) by lia.
    assert (Hcharge : (D.c_db * 16 * N.of_nat (D.slots_of db f + 1) <=
      16 * D.c_db * K)%N) by nia.
    pose proof (N.mul_le_mono_l _ _ (N.of_nat U) Hcharge) as Hcharged.
    assert (HUpositive : (1 <= N.of_nat U)%N).
    { pose proof (unit_positive (Facts.put_entry db (f, (x, y)))). lia. }
    cbn [fst snd] in Hclock.
    repeat rewrite N.mul_add_distr_l in Hscaled |- *. lia.
  Qed.

  (** A seed fold telescopes potential at one fixed upper bound on its final unit. *)
  Lemma fold_credit : forall p entries
      (T_entry : D.t -> positive * (positive * positive) -> N) (K : N) (U : nat),
    R.plans_ok p (R.plan p) ->
    (N.of_nat (length (Syntax.slots V.t (R.plan p)) + 1) <= K)%N ->
    (forall db entry, (T_entry db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N) ->
    forall db, Facts.invariant p db -> Forall (Facts.entry_ok p) entries ->
    (D.unit (fold_left Facts.put_entry entries db) <= U)%nat ->
    (Std.List.T_fold_left Facts.put_entry T_entry entries db +
      N.of_nat U * D.potential 0 (fold_left Facts.put_entry entries db) <=
      N.of_nat U * ((16 * D.c_db * K + 33) * N.of_nat (length entries) +
        D.potential 0 db) + 1)%N.
  Proof.
    intros p entries T_entry K U Hplan HK Hclock.
    induction entries as [|entry rest IH]; intros db Hinv Hentries Hfinal.
    - time_unfold @Std.List.T_fold_left. cbn [fold_left length]. nia.
    - inversion Hentries as [|entry' rest' Hentry Hrest]; subst.
      pose proof (Facts.entry_invariant p db entry Hplan Hinv Hentry) as Hnext.
      assert (Hnext_unit : (D.unit (Facts.put_entry db entry) <= U)%nat).
      { eapply Nat.le_trans; [apply (fold_unit_mono p rest _ Hplan Hnext Hrest)|].
        exact Hfinal. }
      pose proof (entry_credit p T_entry K U db entry Hplan Hinv Hentry HK Hnext_unit
        (Hclock db entry)) as Hstep.
      specialize (IH (Facts.put_entry db entry) Hnext Hrest Hfinal).
      assert (HUpositive : (1 <= N.of_nat U)%N).
      { pose proof (unit_positive (Facts.put_entry db entry)). lia. }
      time_unfold @Std.List.T_fold_left. cbn [fold_left length].
      rewrite Nat2N.inj_succ.
      set (tail_charge := ((16 * D.c_db * K + 33) * N.of_nat (length rest))%N) in *.
      replace ((16 * D.c_db * K + 33) * N.succ (N.of_nat (length rest)))%N with
        (tail_charge + (16 * D.c_db * K + 33))%N by (unfold tail_charge; nia).
      repeat rewrite N.mul_add_distr_l in Hstep, IH |- *. lia.
  Qed.

  (** Initialization has zero credit, giving a plain bound for the complete seed fold. *)
  Lemma fold_time : forall p entries
      (T_entry : D.t -> positive * (positive * positive) -> N) (K : N),
    R.plans_ok p (R.plan p) ->
    (N.of_nat (length (Syntax.slots V.t (R.plan p)) + 1) <= K)%N ->
    (forall db entry, (T_entry db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N) ->
    Forall (Facts.entry_ok p) entries ->
    let initial := D.init (decls V.t p) (Syntax.slots V.t (R.plan p)) in
    (Std.List.T_fold_left Facts.put_entry T_entry entries initial <=
      N.of_nat (D.unit (fold_left Facts.put_entry entries initial)) *
        (16 * D.c_db * K + 33) * N.of_nat (length entries) + 1)%N.
  Proof.
    intros p entries T_entry K Hplan HK Hclock Hentries initial.
    pose proof (fold_credit p entries T_entry K
      (D.unit (fold_left Facts.put_entry entries initial)) Hplan HK Hclock initial
      (Facts.init_invariant p) Hentries (Nat.le_refl _)) as Hfold.
    unfold initial in Hfold. rewrite D.potential_init in Hfold.
    fold initial in Hfold. nia.
  Qed.

End PointerSeedTime.

(** The fixed seed budget pays both each entry and initial plan preparation. *)
Lemma pointer_seed_budget : forall c K : N,
  (16 * c * (K + 1) + 33 <= 128 * (c + 1) * (K + 32) * (K + 32))%N /\
  (64 * (c + 1) * (K + 8) * (K + 8) + K + 16 <=
    128 * (c + 1) * (K + 32) * (K + 32))%N.
Proof.
  intros c K; split; nia.
Qed.

(** Linear seed preparation and telescoped insertion work fit the final unit budget. *)
Lemma pointer_seed_composition : forall preparation initialization planning insertion c K U n : N,
  (1 <= U)%N -> (preparation <= 16 * (n + 1))%N ->
  (initialization + planning + 16 <= K)%N -> (insertion <= U * K * n + 1)%N ->
  (preparation + initialization + planning + insertion + 8 <=
    (K + c + 64) * (n + 1) * U)%N.
Proof.
  intros preparation initialization planning insertion c K U n Hunit Hpreparation Hfixed Hfold.
  assert (HK : (K <= U * K)%N) by nia.
  assert (Hn : (n + 1 <= (n + 1) * U)%N) by nia.
  nia.
Qed.


(** * Code *)

Module AndersenCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: ANDERSEN_OPS V I J D R.
  Module X := RunnerCode V I J D R.
  Definition compile (_ : pointer_input) : program V.t := andersen_program.
  Definition seed (q : pointer_input) : D.t :=
    X.seed (compile q) (AndersenSig.Andersen.facts q).
  Definition solve (q : pointer_input) (lim : limits) : stop * D.t :=
    X.solve (compile q) (AndersenSig.Andersen.facts q) lim.
  Definition points (db : D.t) (x a : positive) : bool :=
    X.holds AndersenSig.Andersen.may_points_code [x; a] db.
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

  (* STUB: RELATIONAL_PLAN.seed_rows for [Andersen.spec], with [rows_ok] by vm_compute. *)
  Lemma seed_rows : forall q f k o, row (D.view (seed q)) f k o <->
    o = None /\ exists vs, k = map Val vs /\ In (f, vs) (AndersenSig.Andersen.facts q).
  Proof. Admitted. (* STUB *)

  (* STUB: RELATIONAL_PLAN.seed_ready for [Andersen.spec], with [spec_ok] by vm_compute. *)
  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof. Admitted. (* STUB *)

  (* STUB: RELATIONAL_PLAN.seed_ready for [Andersen.spec], with [spec_ok] by vm_compute. *)
  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  Proof. Admitted. (* STUB *)

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof.
    reflexivity.
  Qed.

  (* STUB: RELATIONAL.holds_spec at [Andersen.may_points_code], and the sorts of the program
     give an output-free row. *)
  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) AndersenSig.Andersen.may_points_code [Val x; Val a] None)
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

  (* STUB: RELATIONAL.solve_sound and solve_complete with [Andersen.may_points_spec], and
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
