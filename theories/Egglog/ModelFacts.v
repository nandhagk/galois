(** * Meaning of stored engine facts

    These lemmas connect the frozen view semantics to interpretations in a model.
    For example, equal identifiers in a satisfying view have the same denotation.
    Builds on: Syntax, Model and Stdlib lists. *)

From Stdlib Require Import List PArith NArith Lia Relations.Relation_Operators.
From Galois.Base Require Import UnionFindSig Trie.
From Galois.Egglog Require Import Syntax Model DatabaseSig.

Import List.ListNotations.

Module UnionFindFacts (U : UNION_FIND).
  (** Redirecting one class identifies precisely its old class and the winning class. *)
  Lemma redirect_eq_cases : forall (r : positive -> positive) winner loser a b,
    (if Pos.eqb (r a) loser then winner else r a) =
      (if Pos.eqb (r b) loser then winner else r b) <->
    r a = r b \/ (r a = loser /\ r b = winner) \/
      (r a = winner /\ r b = loser).
  Proof.
    intros r winner loser a b.
    destruct (Pos.eqb (r a) loser) eqn:Ha; destruct (Pos.eqb (r b) loser) eqn:Hb.
    - apply Pos.eqb_eq in Ha, Hb. intuition congruence.
    - apply Pos.eqb_eq in Ha. apply Pos.eqb_neq in Hb. intuition congruence.
    - apply Pos.eqb_neq in Ha. apply Pos.eqb_eq in Hb. intuition congruence.
    - apply Pos.eqb_neq in Ha, Hb. intuition congruence.
  Qed.

  (** Union relates old classmates and the two orientations of the requested class pair. *)
  Lemma union_eq_cases : forall i j u a b, U.wf u ->
    U.repr (snd (U.union i j u)) a = U.repr (snd (U.union i j u)) b <->
    U.repr u a = U.repr u b \/
      (U.repr u a = U.repr u i /\ U.repr u b = U.repr u j) \/
      (U.repr u a = U.repr u j /\ U.repr u b = U.repr u i).
  Proof.
    intros i j u a b Hwf.
    destruct (U.union i j u) as [roots u'] eqn:Hunion.
    destruct roots as [[winner loser] |]; cbn [snd].
    - destruct (U.union_some i j u winner loser u' Hwf Hunion)
        as [_ [Hroots Hrepr]].
      rewrite (Hrepr a), (Hrepr b), redirect_eq_cases.
      destruct Hroots as [[-> ->] | [-> ->]]; tauto.
    - destruct (U.union_none i j u u' Hwf Hunion) as [Hij Hrepr].
      rewrite (Hrepr a), (Hrepr b). intuition congruence.
  Qed.

  (** Union preserves every equality already represented by its input forest. *)
  Lemma union_old : forall i j u a b, U.wf u -> U.repr u a = U.repr u b ->
    U.repr (snd (U.union i j u)) a = U.repr (snd (U.union i j u)) b.
  Proof.
    intros i j u a b Hwf Heq.
    apply (proj2 (union_eq_cases i j u a b Hwf)). now left.
  Qed.

  (** Union always identifies its requested endpoints. *)
  Lemma union_requested : forall i j u, U.wf u ->
    U.repr (snd (U.union i j u)) i = U.repr (snd (U.union i j u)) j.
  Proof.
    intros i j u Hwf. apply (proj2 (union_eq_cases i j u i j Hwf)).
    right. left. split; reflexivity.
  Qed.

  (** Forest union adds exactly the equality closure of the requested pair. *)
  Lemma union_same_closure : forall i j u a b, U.wf u ->
    (U.repr (snd (U.union i j u)) a = U.repr (snd (U.union i j u)) b <->
      clos_refl_sym_trans positive
        (fun x y => U.repr u x = U.repr u y \/ (x, y) = (i, j)) a b).
  Proof.
    intros i j u a b Hwf. split.
    - intro Heq. apply (proj1 (union_eq_cases i j u a b Hwf)) in Heq.
      destruct Heq as [Heq | [[Ha Hb] | [Ha Hb]]].
      + apply rst_step. now left.
      + eapply rst_trans with (y := i).
        * apply rst_step. now left.
        * eapply rst_trans with (y := j).
          -- apply rst_step. right. reflexivity.
          -- apply rst_step. left. symmetry. exact Hb.
      + eapply rst_trans with (y := j).
        * apply rst_step. now left.
        * eapply rst_trans with (y := i).
          -- apply rst_sym. apply rst_step. right. reflexivity.
          -- apply rst_step. left. symmetry. exact Hb.
    - intro Hclosure.
      induction Hclosure as
        [x y Hstep | x | x y Hstep IH | x y z Hleft IHleft Hright IHright].
      + destruct Hstep as [Heq | Hpair].
        * exact (union_old i j u x y Hwf Heq).
        * inversion Hpair; subst. exact (union_requested i j u Hwf).
      + reflexivity.
      + symmetry. exact IH.
      + exact (eq_trans IHleft IHright).
  Qed.
End UnionFindFacts.

Section ModelFacts.
Context {V : Type} (prim : positive -> list V -> option V)
  (merge : positive -> V -> V -> V).
Context (M : model (V := V)) (nu : positive -> carrier M).

(** A change of identifier names preserves cells when it preserves their meanings. *)
Lemma den_rename : forall (rename : positive -> positive),
  (forall i, nu (rename i) = nu i) -> forall c,
  den nu (match c with Id i => Id (rename i) | Val v => Val v end) = den nu c.
Proof.
  intros rename Hrename [i | v]; cbn [den].
  - now rewrite Hrename.
  - reflexivity.
Qed.

(** A satisfying view gives the same meaning to related identifiers. *)
Lemma sat_same : forall w i j,
  sat merge M nu w -> same w i j -> nu i = nu j.
Proof.
  intros w i j [_ [Hsame _]]. exact (Hsame i j).
Qed.

(** A stored constructor output denotes the model's constructor result. *)
Lemma sat_constructor : forall w f k i,
  sat merge M nu w -> row w f k (Some (Id i)) ->
  con M f (map (den nu) k) = nu i.
Proof.
  intros w f k i [Hrows _] Hrow.
  specialize (Hrows f k (Some (Id i)) Hrow).
  unfold holds in Hrows.
  destruct (kind w f) as [[| |m] |]; try contradiction.
  exact Hrows.
Qed.

(** Terms keep their value when an environment is interpreted in a model. *)
Lemma term_value_model : forall s t c,
  term_value s t c ->
  model_term M (fun x => option_map (den nu) (s x)) t (den nu c).
Proof.
  intros s [x | v] c Hvalue; cbn [term_value model_term] in *.
  - rewrite Hvalue. reflexivity.
  - subst c. reflexivity.
Qed.

(** Interpreting a tuple preserves the values of its source terms. *)
Lemma terms_value_model : forall s ts cs,
  terms_value s ts cs ->
  Forall2 (model_term M (fun x => option_map (den nu) (s x))) ts (map (den nu) cs).
Proof.
  intros s ts cs Hvalues.
  induction Hvalues as [| t c ts cs Hvalue Hvalues IH]; cbn [map].
  - constructor.
  - constructor.
    + now apply term_value_model.
    + exact IH.
Qed.

(** Primitive arguments remain values under identifier interpretation. *)
Lemma values_model : forall cs vs,
  values cs vs -> model_values M (map (den nu) cs) vs.
Proof.
  intros cs vs Hvalues.
  induction Hvalues as [| c v cs vs Hvalue Hvalues IH]; cbn [map].
  - constructor.
  - constructor.
    + subst c. reflexivity.
    + exact IH.
Qed.

(** A matching atom in a satisfying view also holds in the model. *)
Lemma atom_holds_model : forall w s a,
  sat merge M nu w -> atom_holds prim w s a ->
  model_atom prim M (kind w) (fun x => option_map (den nu) (s x)) a.
Proof.
  intros w s [f args res | p args res] Hsat Hatom.
  - destruct Hatom as [k [o [Hargs [Hres Hrow]]]].
    destruct Hsat as [Hrows _].
    specialize (Hrows f k o Hrow).
    exists (map (den nu) k). split.
    + now apply terms_value_model.
    + unfold holds in Hrows.
      destruct (kind w f) as [[| |m] |] eqn:Hkind;
        destruct o as [[i | v] |]; try contradiction;
        destruct res as [t |]; cbn in Hres; try contradiction.
      * exact Hrows.
      * rewrite Hrows. exact (term_value_model s t (Id i) Hres).
      * exists v. split; [exact (term_value_model s t (Val v) Hres) | exact Hrows].
  - destruct Hatom as [k [vs [v [Hargs [Hvalues [Hprim Hres]]]]]].
    exists (map (den nu) k), vs, v. split.
    + now apply terms_value_model.
    + split; [now apply values_model |].
      split; [exact Hprim | exact (term_value_model s res (Val v) Hres)].
Qed.

(** Every atom of a matching query transfers to the satisfying model. *)
Lemma matches_model : forall w q s,
  sat merge M nu w -> matches prim w q s ->
  Forall (model_atom prim M (kind w) (fun x => option_map (den nu) (s x))) q.
Proof.
  intros w q s Hsat Hmatches.
  induction Hmatches as [| a q Hatom Hmatches IH].
  - constructor.
  - constructor.
    + now apply atom_holds_model.
    + exact IH.
Qed.

(** A represented expression has exactly the meaning of its representing cell. *)
Lemma represents_den : forall w c e,
  sat merge M nu w -> represents w c e -> den nu c = denote M e.
Proof.
  intros w c e Hsat Hrep.
  induction Hrep as [v | f k i j args Hrow Hsame Hargs IHargs].
  - reflexivity.
  - assert (Hden : map (den nu) k = map (denote M) args).
    { clear Hrow Hsame.
      induction IHargs as [| c0 e0 ks es Hr Hhead Htail Hall IH]; cbn [map].
      - reflexivity.
      - now rewrite Hhead, IH. }
    cbn [den denote].
    rewrite (sat_same w i j Hsat Hsame), <- (sat_constructor w f k j Hsat Hrow), Hden.
    reflexivity.
Qed.

(** Constructor congruence equates identifiers in every satisfying model. *)
Lemma fd_congruence_den : forall w i j,
  sat merge M nu w -> fd_congruence w i j -> nu i = nu j.
Proof.
  intros w i j Hsat Hcong.
  induction Hcong as
    [i j Hsame | f k1 k2 i j Hrow1 Hrow2 Hcells IHcells |
     i j Hcong IH | i j k Hleft IHleft Hright IHright].
  - exact (sat_same w i j Hsat Hsame).
  - assert (Hden : map (den nu) k1 = map (den nu) k2).
    { clear Hrow1 Hrow2.
      induction IHcells as [| c d ks ds Hr Hhead Htail Hall IH]; cbn [map].
      - reflexivity.
      - assert (Hcell_den : den nu c = den nu d).
        { destruct Hhead as [i0 j0 Hr0 Heq | v]; cbn [den]; congruence. }
        now rewrite Hcell_den, IH. }
    rewrite <- (sat_constructor w f k1 i Hsat Hrow1),
      <- (sat_constructor w f k2 j Hsat Hrow2), Hden.
    reflexivity.
  - symmetry. exact IH.
  - exact (eq_trans IHleft IHright).
Qed.

(** A row's truth depends only on its kind and interpreted arguments and output. *)
Lemma holds_transport : forall (nu' : positive -> carrier M) w w' f k k' o o',
  kind w' f = kind w f -> map (den nu') k' = map (den nu) k ->
  option_map (den nu') o' = option_map (den nu) o ->
  holds M nu w f k o -> holds M nu' w' f k' o'.
Proof.
  intros nu' w w' f k k' o o' Hkind Hargs Hout Hholds.
  unfold holds in *. rewrite Hkind, Hargs.
  destruct (kind w f) as [[| |m] |];
    destruct o as [[i | v] |]; destruct o' as [[j | v'] |];
    cbn [option_map den] in *; try contradiction; try discriminate; congruence.
Qed.

(** Renaming an output preserves its truth when every identifier keeps its meaning. *)
Lemma holds_output_rename : forall (rename : positive -> positive),
  (forall i, nu (rename i) = nu i) -> forall w f k o,
  holds M nu w f k o ->
  holds M nu w f k
    (option_map (fun c => match c with Id i => Id (rename i) | Val v => Val v end) o).
Proof.
  intros rename Hrename w f k o Hholds.
  eapply (holds_transport nu w w f k k o).
  - reflexivity.
  - reflexivity.
  - destruct o as [c |]; cbn [option_map]; [| reflexivity].
    f_equal. exact (den_rename rename Hrename c).
  - exact Hholds.
Qed.

(** Keeping an old output or merging two lattice values preserves the row's meaning. *)
Lemma holds_combine : forall w f k previous o,
  lat_closed merge M w ->
  (forall old, previous = Some old -> holds M nu w f k old) ->
  holds M nu w f k o ->
  holds M nu w f k
    (match previous, kind w f, o with
     | Some (Some (Val a)), Some (OLat m), Some (Val b) => Some (Val (merge m a b))
     | Some old, _, _ => old
     | None, _, _ => o
     end).
Proof.
  intros w f k [old |] o Hlat Hprevious Hnew; [| exact Hnew].
  pose proof (Hprevious old eq_refl) as Hold.
  destruct old as [[i | a] |]; destruct (kind w f) as [[| |m] |] eqn:Hkind;
    destruct o as [[j | b] |]; try exact Hold.
  unfold holds in Hold, Hnew |- *. rewrite Hkind in Hold, Hnew |- *.
  exact (Hlat f m (map (den nu) k) a b Hkind Hold Hnew).
Qed.

(** Removing rows and equalities preserves satisfaction when function kinds are unchanged. *)
Lemma sat_restrict : forall w w',
  kind w' = kind w ->
  (forall f k o, row w' f k o -> row w f k o) ->
  (forall i j, same w' i j -> same w i j) ->
  sat merge M nu w -> sat merge M nu w'.
Proof.
  intros w w' Hkind Hrows Hsame [Hrow_sat [Hsame_sat Hlat]].
  split.
  - intros f k o Hrow. unfold holds. rewrite Hkind.
    exact (Hrow_sat f k o (Hrows f k o Hrow)).
  - split.
    + intros i j Hrelation. exact (Hsame_sat i j (Hsame i j Hrelation)).
    + unfold lat_closed in *. rewrite Hkind. exact Hlat.
Qed.

(** Equality closure preserves an interpretation when every generating pair agrees. *)
Lemma equality_closure_den : forall R,
  (forall i j, R i j -> nu i = nu j) -> forall i j,
  clos_refl_sym_trans positive R i j -> nu i = nu j.
Proof.
  intros R Hstep i j Hclosure.
  induction Hclosure as [i j Hpair | i | i j Hpair IH | i j k Hleft IHleft Hright IHright].
  - exact (Hstep i j Hpair).
  - reflexivity.
  - symmetry. exact IH.
  - exact (eq_trans IHleft IHright).
Qed.

(** Adding a justified equality keeps every row and every satisfying interpretation. *)
Lemma sat_union_view : forall w w' i j,
  kind w' = kind w -> row w' = row w ->
  (forall a b, same w' a b ->
    clos_refl_sym_trans positive (fun x y => same w x y \/ (x = i /\ y = j)) a b) ->
  sat merge M nu w -> nu i = nu j -> sat merge M nu w'.
Proof.
  intros w w' i j Hkind Hrows Hsame [Hrow_sat [Hsame_sat Hlat]] Heq.
  split.
  - intros f k o Hrow. unfold holds. rewrite Hkind.
    apply Hrow_sat. now rewrite <- Hrows.
  - split.
    + intros a b Hab. apply (equality_closure_den
        (fun x y => same w x y \/ (x = i /\ y = j))).
      * intros x y [Hxy | [-> ->]].
        -- exact (Hsame_sat x y Hxy).
        -- exact Heq.
      * exact (Hsame a b Hab).
    + unfold lat_closed in *. rewrite Hkind. exact Hlat.
Qed.

End ModelFacts.

(** * Giving a fresh constructor output its meaning *)

Section FreshConstructor.
Context {V : Type} (merge : positive -> V -> V -> V).
Context (M : model (V := V)) (nu : positive -> carrier M).

(** Changing one absent identifier leaves the denotation of a tuple unchanged. *)
Local Lemma fresh_map_den : forall i (nu' : positive -> carrier M) cs,
  (forall j, j <> i -> nu' j = nu j) -> ~ In (Id i) cs ->
  map (den nu') cs = map (den nu) cs.
Proof.
  intros i nu' cs Hkeep Habsent.
  apply map_ext_in. intros [j | v] Hin; cbn [den].
  - f_equal. apply Hkeep. intro Heq. subst j. exact (Habsent Hin).
  - reflexivity.
Qed.

(** A row without the changed identifier keeps its truth and output meaning. *)
Local Lemma fresh_holds_preserved : forall i (nu' : positive -> carrier M) w w' f k o,
  (forall j, j <> i -> nu' j = nu j) ->
  kind w' = kind w -> ~ In (Id i) (k ++ option_list o) ->
  holds M nu w f k o -> holds M nu' w' f k o.
Proof.
  intros i nu' w w' f k o Hkeep Hkind Habsent Hholds.
  assert (Hargs : ~ In (Id i) k).
  { intro Hin. apply Habsent. apply in_or_app. now left. }
  pose proof (fresh_map_den i nu' k Hkeep Hargs) as Hden.
  unfold holds in *. rewrite Hkind, Hden.
  destruct (kind w f) as [[| |m] |]; destruct o as [[j | v] |];
    try exact Hholds.
  assert (Hneq : j <> i).
  { intro Heq. subst j. apply Habsent. apply in_or_app. right. now left. }
  now rewrite (Hkeep j Hneq).
Qed.

(** A fresh singleton output can be assigned the constructor value while preserving a model. *)
Lemma sat_fresh_constructor_view : forall w w' f k i,
  sat merge M nu w -> kind w' = kind w ->
  (forall g args o, row w g args o -> ~ In (Id i) (args ++ option_list o)) ->
  (forall a b, same w a b -> (a = i <-> b = i)) ->
  (forall a b, same w' a b <-> same w a b \/ (a = i /\ b = i)) ->
  (forall g args o, row w' g args o <->
    row w g args o \/ (g = f /\ args = k /\ o = Some (Id i))) ->
  kind w f = Some OId -> ~ In (Id i) k ->
  exists nu', (forall j, j <> i -> nu' j = nu j) /\
    nu' i = con M f (map (den nu) k) /\ sat merge M nu' w'.
Proof.
  intros w w' f k i [Hrows [Hsame Hlat]] Hkind Hrow_absent Hsingleton Hsame_new
    Hrows_new Hconstructor Hargs.
  set (nu' := fun j =>
    if Pos.eqb j i then con M f (map (den nu) k) else nu j).
  assert (Hkeep : forall j, j <> i -> nu' j = nu j).
  { intros j Hneq. unfold nu'. destruct (Pos.eqb_spec j i); congruence. }
  assert (Hfresh : nu' i = con M f (map (den nu) k)).
  { unfold nu'. now rewrite Pos.eqb_refl. }
  exists nu'. split; [exact Hkeep |]. split; [exact Hfresh |]. split.
  - intros g args o Hrow. apply Hrows_new in Hrow as [Hrow | [-> [-> ->]]].
    + eapply fresh_holds_preserved; [exact Hkeep | exact Hkind | |].
      * exact (Hrow_absent g args o Hrow).
      * exact (Hrows g args o Hrow).
    + unfold holds. rewrite Hkind, Hconstructor.
      rewrite (fresh_map_den i nu' k Hkeep Hargs). symmetry. exact Hfresh.
  - split.
    + intros a b Hrelated. apply Hsame_new in Hrelated as [Hrelated | [-> ->]].
      * destruct (Pos.eqb_spec a i) as [Ha | Ha].
        -- assert (Hb : b = i) by (apply (proj1 (Hsingleton a b Hrelated)); exact Ha).
           now subst a b.
        -- assert (Hb : b <> i).
           { intro Heq. apply Ha. apply (proj2 (Hsingleton a b Hrelated)). exact Heq. }
           rewrite (Hkeep a Ha), (Hkeep b Hb). exact (Hsame a b Hrelated).
      * reflexivity.
    + intros g m args a b Hmerge Hleft Hright.
      apply (Hlat g m args a b); [| exact Hleft | exact Hright].
      now rewrite <- Hkind.
Qed.

End FreshConstructor.

(** * Preserving a model while inserting or combining one row *)

Section PutView.
Context {V : Type} (merge : positive -> V -> V -> V).
Context (M : model (V := V)) (nu : positive -> carrier M).

(** True constructor outputs for the same arguments have equal meanings. *)
Local Lemma put_constructor_outputs_agree : forall w f k a b,
  holds M nu w f k (Some (Id a)) -> holds M nu w f k (Some (Id b)) -> nu a = nu b.
Proof.
  intros w f k a b Hleft Hright. unfold holds in Hleft, Hright.
  destruct (kind w f) as [[| |m] |]; try contradiction; congruence.
Qed.

(** A true row and its justified identifier conflicts preserve a satisfying interpretation. *)
Lemma sat_put_view : forall w w' f k o ck co previous,
  let updated :=
    match previous, kind w f, co with
    | Some (Some (Val a)), Some (OLat m), Some (Val b) => Some (Val (merge m a b))
    | Some old, _, _ => old
    | None, _, _ => co
    end in
  sat merge M nu w -> kind w' = kind w ->
  (forall old, previous = Some old -> row w f ck old) ->
  map (den nu) ck = map (den nu) k ->
  option_map (den nu) co = option_map (den nu) o -> holds M nu w f k o ->
  (forall g args output, row w' g args output ->
    row w g args output \/ (g = f /\ args = ck /\ output = updated)) ->
  (forall a b, same w' a b -> clos_refl_sym_trans positive
    (fun x y => same w x y \/ (previous = Some (Some (Id x)) /\ co = Some (Id y))) a b) ->
  sat merge M nu w'.
Proof.
  intros w w' f k o ck co previous updated [Hrows [Hsame Hlat]] Hkind Hlookup
    Hargs Hout Hholds Hrows_new Hsame_new.
  assert (Hcanonical : holds M nu w f ck co).
  { exact (@holds_transport V M nu nu w w f k ck o co eq_refl Hargs Hout Hholds). }
  assert (Hprevious : forall old, previous = Some old -> holds M nu w f ck old).
  { intros old Hlookup_old. exact (Hrows f ck old (Hlookup old Hlookup_old)). }
  assert (Hupdated : holds M nu w f ck updated).
  { exact (@holds_combine V merge M nu w f ck previous co Hlat Hprevious Hcanonical). }
  assert (Hgenerators : forall a b,
    same w a b \/ (previous = Some (Some (Id a)) /\ co = Some (Id b)) -> nu a = nu b).
  { intros a b [Hrelated | [Hprevious_id Hnew_id]].
    - exact (Hsame a b Hrelated).
    - eapply put_constructor_outputs_agree.
      + exact (Hprevious (Some (Id a)) Hprevious_id).
      + now rewrite <- Hnew_id. }
  split.
  - intros g args output Hrow. unfold holds. rewrite Hkind.
    apply Hrows_new in Hrow as [Hrow | [-> [-> ->]]].
    + exact (Hrows g args output Hrow).
    + exact Hupdated.
  - split.
    + intros a b Hrelated.
      eapply (@equality_closure_den V M nu
        (fun x y => same w x y \/ (previous = Some (Some (Id x)) /\ co = Some (Id y)))).
      * exact Hgenerators.
      * exact (Hsame_new a b Hrelated).
    + unfold lat_closed in *. now rewrite Hkind.
Qed.

End PutView.

(** * Finite logs of asserted identifier equalities *)

Section EqualityLogFacts.

(** A log denotes the equivalence relation generated by its recorded pairs. *)
Definition equality_log (edges : list (positive * positive)) : positive -> positive -> Prop :=
  clos_refl_sym_trans positive (fun a b => In (a, b) edges).

(** Every recorded pair belongs to the generated equality relation. *)
Lemma equality_log_edge : forall edges a b, In (a, b) edges -> equality_log edges a b.
Proof.
  intros edges a b Hedge. apply rst_step. exact Hedge.
Qed.

(** A log relates every identifier to itself. *)
Lemma equality_log_refl : forall edges a, equality_log edges a a.
Proof.
  intros edges a. apply rst_refl.
Qed.

(** Log equality is symmetric. *)
Lemma equality_log_sym : forall edges a b,
  equality_log edges a b -> equality_log edges b a.
Proof.
  intros edges a b Hrelated. now apply rst_sym.
Qed.

(** Log equality is transitive. *)
Lemma equality_log_trans : forall edges a b c,
  equality_log edges a b -> equality_log edges b c -> equality_log edges a c.
Proof.
  intros edges a b c Hleft Hright. eapply rst_trans; eassumption.
Qed.

(** An empty log relates exactly identical identifiers. *)
Lemma equality_log_empty : forall a b, equality_log [] a b <-> a = b.
Proof.
  intros a b. split.
  - intro Hrelated. induction Hrelated as
      [a b Hedge|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
    + contradiction.
    + reflexivity.
    + symmetry. exact IH.
    + congruence.
  - intros ->. apply equality_log_refl.
Qed.

(** Adding recorded pairs can only add generated equalities. *)
Lemma equality_log_incl : forall edges edges', incl edges edges' ->
  forall a b, equality_log edges a b -> equality_log edges' a b.
Proof.
  intros edges edges' Hinclude a b Hrelated. induction Hrelated as
    [a b Hedge|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
  - apply equality_log_edge. exact (Hinclude (a, b) Hedge).
  - apply equality_log_refl.
  - now apply equality_log_sym.
  - eapply equality_log_trans; eassumption.
Qed.

(** Prepending a pair closes the old relation together with that requested equality. *)
Lemma equality_log_cons : forall i j edges a b,
  equality_log ((i, j) :: edges) a b <->
  clos_refl_sym_trans positive
    (fun x y => equality_log edges x y \/ (x, y) = (i, j)) a b.
Proof.
  intros i j edges a b. split.
  - intro Hrelated. induction Hrelated as
      [a b Hedge|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
    + apply rst_step. destruct Hedge as [Hnew|Hold].
      * right. symmetry. exact Hnew.
      * left. apply equality_log_edge. exact Hold.
    + apply rst_refl.
    + now apply rst_sym.
    + eapply rst_trans; eassumption.
  - intro Hrelated. induction Hrelated as
      [a b [Hold|Hnew]|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
    + eapply equality_log_incl; [|exact Hold]. intros edge Hin. right. exact Hin.
    + apply equality_log_edge. left. symmetry. exact Hnew.
    + apply equality_log_refl.
    + now apply equality_log_sym.
    + eapply equality_log_trans; eassumption.
Qed.

(** Recording an equality already in the log's closure does not change that closure. *)
Lemma equality_log_redundant : forall i j edges, equality_log edges i j ->
  forall a b, equality_log ((i, j) :: edges) a b <-> equality_log edges a b.
Proof.
  intros i j edges Hknown a b. rewrite equality_log_cons. split.
  - intro Hrelated. induction Hrelated as
      [a b [Hold|Hnew]|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
    + exact Hold.
    + injection Hnew as -> ->. exact Hknown.
    + apply equality_log_refl.
    + now apply equality_log_sym.
    + eapply equality_log_trans; eassumption.
  - intro Hrelated. apply rst_step. left. exact Hrelated.
Qed.

(** A nontrivial generated equality has allocated endpoints when every logged pair does. *)
Lemma equality_log_allocated : forall edges (allocated : positive -> Prop),
  Forall (fun edge => allocated (fst edge) /\ allocated (snd edge)) edges ->
  forall a b, equality_log edges a b -> a = b \/ (allocated a /\ allocated b).
Proof.
  intros edges allocated Hendpoints a b Hrelated. induction Hrelated as
    [a b Hedge|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
  - right. rewrite Forall_forall in Hendpoints.
    exact (Hendpoints (a, b) Hedge).
  - left. reflexivity.
  - destruct IH as [Heq|[Ha Hb]].
    + left. symmetry. exact Heq.
    + right. split; assumption.
  - destruct IHleft as [Hab|[Ha Hb]].
    + subst b. exact IHright.
    + destruct IHright as [Hbc|[Hb' Hc]].
      * subst c. right. split; assumption.
      * right. split; assumption.
Qed.

(** An identifier outside all logged endpoints remains a singleton equality class. *)
Lemma equality_log_fresh : forall edges (allocated : positive -> Prop),
  Forall (fun edge => allocated (fst edge) /\ allocated (snd edge)) edges ->
  forall fresh, ~ allocated fresh ->
  forall other, equality_log edges fresh other <-> fresh = other.
Proof.
  intros edges allocated Hendpoints fresh Hfresh other. split.
  - intro Hrelated.
    destruct (equality_log_allocated edges allocated Hendpoints fresh other Hrelated)
      as [Heq|[Hallocated _]]; [exact Heq|contradiction].
  - intros ->. apply equality_log_refl.
Qed.

(** Related identifiers agree on whether they are a fresh identifier. *)
Lemma equality_log_fresh_occurs : forall edges (allocated : positive -> Prop),
  Forall (fun edge => allocated (fst edge) /\ allocated (snd edge)) edges ->
  forall fresh, ~ allocated fresh ->
  forall a b, equality_log edges a b -> (a = fresh <-> b = fresh).
Proof.
  intros edges allocated Hendpoints fresh Hfresh a b Hrelated.
  destruct (equality_log_allocated edges allocated Hendpoints a b Hrelated)
    as [->|[Ha Hb]]; [reflexivity|].
  split; intro Heq; subst; contradiction.
Qed.

End EqualityLogFacts.

(** * Declaration tables built in source order *)

Section DeclarationLookupFacts.

(** A right fold writes the first declaration last, matching the frozen first-match lookup. *)
Lemma declaration_trie_lookup : forall ds f,
  PTrieCode.get f
    (fold_right (fun d table => PTrieCode.set (name d) (out d) table) PTrieCode.empty ds) =
  lookup_kind ds f.
Proof.
  induction ds as [|d ds IH]; intro f; cbn [fold_right lookup_kind].
  - apply PTrie.get_empty.
  - destruct (Pos.eqb_spec (name d) f) as [Heq|Hneq].
    + subst f. apply PTrie.get_set_same.
    + rewrite PTrie.get_set_other by congruence. apply IH.
Qed.

(** A successful declaration lookup lies below the stored maximum function name. *)
Lemma lookup_kind_name_bound : forall ds f o, lookup_kind ds f = Some o ->
  (f <= fold_right (fun d bound => Pos.max (name d) bound) 1%positive ds)%positive.
Proof.
  induction ds as [|d ds IH]; intros f o Hlookup;
    cbn [lookup_kind fold_right] in Hlookup |- *; [discriminate|].
  destruct (Pos.eqb_spec (name d) f) as [Heq|Hneq].
  - subst f. apply Pos.le_max_l.
  - eapply Pos.le_trans; [eapply IH; exact Hlookup|apply Pos.le_max_r].
Qed.

End DeclarationLookupFacts.
