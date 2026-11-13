(** * Meaning of stored engine facts

    These lemmas connect the frozen view semantics to interpretations in a model.
    For example, equal identifiers in a satisfying view have the same denotation.
    Builds on: Syntax, Model and Stdlib lists. *)

From Stdlib Require Import List PArith NArith PeanoNat Lia Relations.Relation_Operators Sorting.Permutation.
From Argent Require Import Time Loop.
From Galois.Base Require Import UnionFindSig KeySig MapSig Trie UnionFind Loop.
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

  (** A queued old loser cannot become a representative after another union. *)
  Lemma union_keeps_nonrepresentative : forall i j u x,
    U.wf u -> U.repr u x <> x -> U.repr (snd (U.union i j u)) x <> x.
  Proof.
    intros i j u x Hwf Hnonroot.
    destruct (U.union i j u) as [roots next] eqn:Hunion.
    destruct roots as [[winner loser] |]; cbn [snd].
    - destruct (U.union_some i j u winner loser next Hwf Hunion)
        as [_ [Hroots Hrepr]].
      assert (Hwinner : U.repr u winner = winner).
      { destruct Hroots as [[-> _] | [-> _]]; now apply U.repr_idem. }
      rewrite Hrepr. destruct (Pos.eqb (U.repr u x) loser); [| exact Hnonroot].
      intro Hequal. apply Hnonroot. now rewrite <- Hequal.
    - now rewrite (proj2 (U.union_none i j u next Hwf Hunion) x).
  Qed.

  (** A newly returned loser was a root, so it is absent from any old nonroot-only queue. *)
  Lemma union_loser_was_representative : forall i j u winner loser next,
    U.wf u -> U.union i j u = (Some (winner, loser), next) -> U.repr u loser = loser.
  Proof.
    intros i j u winner loser next Hwf Hunion.
    destruct (U.union_some i j u winner loser next Hwf Hunion)
      as [_ [Hroots _]].
    destruct Hroots as [[_ ->] | [_ ->]]; now apply U.repr_idem.
  Qed.

  (** Linking distinct roots makes the returned loser a nonrepresentative immediately. *)
  Lemma union_loser_is_nonrepresentative : forall i j u winner loser next,
    U.wf u -> U.union i j u = (Some (winner, loser), next) -> U.repr next loser <> loser.
  Proof.
    intros i j u winner loser next Hwf Hunion.
    destruct (U.union_some i j u winner loser next Hwf Hunion)
      as [Hdifferent [Hroots Hrepr]].
    rewrite Hrepr, (union_loser_was_representative i j u winner loser next Hwf Hunion),
      Pos.eqb_refl.
    destruct Hroots as [[-> ->] | [-> ->]]; congruence.
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

(** Pointwise inclusion of generators preserves their equivalence closures. *)
Lemma equality_closure_mono : forall (R S : positive -> positive -> Prop),
  (forall a b, R a b -> S a b) ->
  forall a b, clos_refl_sym_trans positive R a b -> clos_refl_sym_trans positive S a b.
Proof.
  intros R S Hinclude a b Hrelated. induction Hrelated as
    [a b Hedge|a|a b Hrelated IH|a b c Hleft IHleft Hright IHright].
  - apply rst_step. exact (Hinclude a b Hedge).
  - apply rst_refl.
  - now apply rst_sym.
  - eapply rst_trans; eassumption.
Qed.

(** Pointwise equivalent generators have pointwise equivalent closures. *)
Lemma equality_closure_equiv : forall (R S : positive -> positive -> Prop),
  (forall a b, R a b <-> S a b) ->
  forall a b, clos_refl_sym_trans positive R a b <-> clos_refl_sym_trans positive S a b.
Proof.
  intros R S Hequiv a b. split; intro Hrelated.
  - eapply equality_closure_mono; [|exact Hrelated].
    intros x y Hedge. exact (proj1 (Hequiv x y) Hedge).
  - eapply equality_closure_mono; [|exact Hrelated].
    intros x y Hedge. exact (proj2 (Hequiv x y) Hedge).
Qed.

(** The log's old equality relation can be replaced by an equivalent forest observation. *)
Lemma equality_log_cons_transport : forall edges i j (R : positive -> positive -> Prop),
  (forall a b, equality_log edges a b <-> R a b) ->
  forall a b, equality_log ((i, j) :: edges) a b <->
    clos_refl_sym_trans positive (fun x y => R x y \/ (x, y) = (i, j)) a b.
Proof.
  intros edges i j R Hequiv a b. rewrite equality_log_cons.
  apply equality_closure_equiv. intros x y. now rewrite Hequiv.
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

(** * Observations of finite-map updates *)

Module FiniteMapFacts (K : KEY) (M : MAP K).

  (** Insertion replaces the selected binding and preserves every other binding. *)
  Lemma set_binding_iff : forall A k (v : A) m q out,
    M.get q (M.set k v m) = Some out <->
      (M.get q m = Some out /\ q <> k) \/ (q = k /\ out = v).
  Proof.
    intros A k v m q out. destruct (K.eqb_spec q k) as [->|Hneq].
    - rewrite M.get_set_same. split.
      + intro Hvalue. injection Hvalue as Hvalue.
        right. split; [reflexivity|symmetry; exact Hvalue].
      + intros [[_ Hfalse]|[_ Hvalue]].
        * contradiction.
        * now rewrite Hvalue.
    - rewrite M.get_set_other by exact Hneq. split.
      + intro Hvalue. left. split; assumption.
      + intros [[Hvalue _]|[Heq _]]; [exact Hvalue|contradiction].
  Qed.

  (** Inserting at an absent key keeps every old binding and adds exactly the new pair. *)
  Lemma set_fresh_binding_iff : forall A k (v : A) m q out, M.get k m = None ->
    (M.get q (M.set k v m) = Some out <->
      M.get q m = Some out \/ (q = k /\ out = v)).
  Proof.
    intros A k v m q out Hfresh. rewrite set_binding_iff. split.
    - intros [[Hvalue _]|Hnew]; [left; exact Hvalue|right; exact Hnew].
    - intros [Hvalue|Hnew]; [left|right; exact Hnew].
      split; [exact Hvalue|]. intro Heq. subst q. congruence.
  Qed.

  (** Rewriting a consistent map with its existing value leaves the map unchanged. *)
  Lemma get_set_id : forall A k (v : A) m, M.wf m -> M.get k m = Some v ->
    M.set k v m = m.
  Proof.
    intros A k v m Hwf Hvalue. apply M.ext.
    - apply M.wf_set. exact Hwf.
    - exact Hwf.
    - intro q. destruct (K.eqb_spec q k) as [->|Hneq].
      + rewrite M.get_set_same. symmetry. exact Hvalue.
      + apply M.get_set_other. exact Hneq.
  Qed.

  (** Removing a key preserves precisely the bindings at every other key. *)
  Lemma remove_binding_iff : forall A k (m : M.t A) q out,
    M.get q (M.remove k m) = Some out <-> M.get q m = Some out /\ q <> k.
  Proof.
    intros A k m q out. destruct (K.eqb_spec q k) as [-> | Hneq].
    - rewrite M.get_remove_same. split; [discriminate | tauto].
    - rewrite M.get_remove_other by exact Hneq. tauto.
  Qed.

  (** Distinct enumerated keys also make the complete binding pairs distinct. *)
  Lemma elements_nodup_pairs : forall A (m : M.t A), M.wf m -> NoDup (M.elements m).
  Proof.
    intros A m Hwf. apply NoDup_map_inv with (f := @fst K.t A).
    exact (M.elements_nodup A m Hwf).
  Qed.

  (** A replacement removes its optional old binding and adds its new binding to one shared remainder. *)
  Lemma set_elements_decomposition : forall A (m : M.t A) k previous v,
    M.wf m -> M.get k m = previous ->
    exists rest,
      Permutation (M.elements m) (option_list (option_map (pair k) previous) ++ rest) /\
      Permutation (M.elements (M.set k v m)) ((k, v) :: rest) /\
      NoDup (map fst rest) /\ ~ In k (map fst rest).
  Proof.
    intros A m k previous v Hwf Hprevious.
    set (rest := M.elements (M.remove k m)).
    assert (Hremove : M.wf (M.remove k m)) by (now apply M.wf_remove).
    assert (Hdistinct : NoDup (map fst rest)) by (apply M.elements_nodup; exact Hremove).
    assert (Hrest : forall q out, In (q, out) rest <-> M.get q m = Some out /\ q <> k).
    { intros q out. unfold rest. rewrite M.elements_spec by exact Hremove.
      apply remove_binding_iff. }
    assert (Habsent : ~ In k (map fst rest)).
    { intro Hin. apply in_map_iff in Hin. destruct Hin as [[q out] [Heq Hin]].
      cbn [fst] in Heq. subst q. apply Hrest in Hin. tauto. }
    assert (Hpairdistinct : NoDup rest).
    { apply NoDup_map_inv with (f := @fst K.t A). exact Hdistinct. }
    assert (Hnewdistinct : forall value, NoDup ((k, value) :: rest)).
    { intro value. constructor; [| exact Hpairdistinct]. intro Hin.
      apply Habsent. apply in_map with (f := @fst K.t A) in Hin. exact Hin. }
    exists rest. split.
    - apply NoDup_Permutation.
      + now apply elements_nodup_pairs.
      + destruct previous; cbn [option_map option_list app];
          [apply Hnewdistinct | exact Hpairdistinct].
      + intros [q out]. rewrite M.elements_spec by exact Hwf.
        destruct previous as [before |]; cbn [option_map option_list app In]; rewrite Hrest.
        * destruct (K.eqb_spec q k) as [-> | Hneq].
          -- rewrite Hprevious. intuition congruence.
          -- intuition congruence.
        * split; [intro Hget; split; [exact Hget | congruence] | tauto].
    - split.
      + apply NoDup_Permutation.
        * apply elements_nodup_pairs. now apply M.wf_set.
        * apply Hnewdistinct.
        * intros [q out]. rewrite M.elements_spec by (now apply M.wf_set).
          rewrite set_binding_iff. cbn [In]. rewrite Hrest. intuition congruence.
      + split; assumption.
  Qed.

  (** Deletion exposes the actual enumerated remainder and its optional removed binding. *)
  Lemma remove_elements_decomposition : forall A (m : M.t A) k previous,
    M.wf m -> M.get k m = previous ->
    Permutation (M.elements m)
      (option_list (option_map (pair k) previous) ++ M.elements (M.remove k m)).
  Proof.
    intros A m k previous Hwf Hprevious.
    assert (Hremove : M.wf (M.remove k m)) by (now apply M.wf_remove).
    assert (Hrest : forall q out, In (q, out) (M.elements (M.remove k m)) <->
        M.get q m = Some out /\ q <> k).
    { intros q out. rewrite M.elements_spec by exact Hremove.
      apply remove_binding_iff. }
    apply NoDup_Permutation.
    - now apply elements_nodup_pairs.
    - destruct previous as [before |]; cbn [option_map option_list app].
      + constructor.
        * intro Hin. apply Hrest in Hin. tauto.
        * now apply elements_nodup_pairs.
      + now apply elements_nodup_pairs.
    - intros [q out]. rewrite M.elements_spec by exact Hwf.
      destruct previous as [before |]; cbn [option_map option_list app In]; rewrite Hrest.
      + destruct (K.eqb_spec q k) as [-> | Hneq].
        * rewrite Hprevious. intuition congruence.
        * intuition congruence.
      + split; [intro Hget; split; [exact Hget | congruence] | tauto].
  Qed.

End FiniteMapFacts.

(** * Allocation counts in the concrete union-find implementation *)

Module UnionFindCodeFacts.

  (** Adding an existing member preserves the entire forest record. *)
  Lemma add_present : forall x u, UnionFind.mem u x -> UnionFindCode.add x u = u.
  Proof.
    intros x u Hmember. unfold UnionFind.mem in Hmember.
    unfold UnionFindCode.add.
    destruct (PTrieCode.get x (parents u)); [reflexivity|contradiction].
  Qed.

  (** An absent key creates exactly one new membership-counter entry. *)
  Lemma count_add_absent : forall x u, ~ UnionFind.mem u x ->
    count (UnionFindCode.add x u) = N.succ (count u).
  Proof.
    intros x u Habsent. unfold UnionFind.mem in Habsent.
    unfold UnionFindCode.add.
    destruct (PTrieCode.get x (parents u)) as [parent|] eqn:Hparent.
    - exfalso. apply Habsent. discriminate.
    - reflexivity.
  Qed.

  (** Path compression keeps the membership counter unchanged. *)
  Lemma count_find : forall x u,
    count (snd (UnionFindCode.find x u)) = count u.
  Proof. reflexivity. Qed.

  (** A union's two insertions account for all changes to its membership counter. *)
  Lemma count_union_add : forall x y u,
    count (snd (UnionFindCode.union x y u)) =
    count (UnionFindCode.add y (UnionFindCode.add x u)).
  Proof.
    intros x y u. unfold UnionFindCode.union.
    destruct (Pos.eqb _ _); [|destruct (N.leb _ _)];
      cbn [snd UnionFindCode.link count]; rewrite !count_find; reflexivity.
  Qed.

  (** Uniting two existing members preserves the allocation count. *)
  Lemma count_union_present : forall x y u, UnionFind.mem u x -> UnionFind.mem u y ->
    count (snd (UnionFindCode.union x y u)) = count u.
  Proof.
    intros x y u Hx Hy. rewrite count_union_add.
    rewrite (add_present x u Hx), (add_present y u Hy). reflexivity.
  Qed.

  (** A well-formed forest's parent edges stay within its members. *)
  Lemma parent_member : forall u x, UnionFind.wf u -> UnionFind.mem u x ->
    UnionFind.mem u (UnionFindCode.parent_of x u).
  Proof.
    intros u x [_ [Hparents _]] Hmember.
    unfold UnionFindCode.parent_of.
    destruct (PTrieCode.get x (parents u)) as [parent|] eqn:Hparent.
    - exact (Hparents x parent Hparent).
    - exact Hmember.
  Qed.

  (** Following any number of parent edges keeps a member inside the forest. *)
  Lemma repr_member : forall u x, UnionFind.wf u -> UnionFind.mem u x ->
    UnionFind.mem u (UnionFind.repr u x).
  Proof.
    intros u x Hwf Hmember. unfold UnionFind.repr.
    induction (UnionFind.card u) as [|steps IH]; cbn [Nat.iter].
    - exact Hmember.
    - apply parent_member; assumption.
  Qed.

  (** An absent identifier has no parent edge and therefore represents itself. *)
  Lemma repr_absent : forall u x, ~ UnionFind.mem u x -> UnionFind.repr u x = x.
  Proof.
    intros u x Habsent.
    assert (Hparent : UnionFindCode.parent_of x u = x).
    { unfold UnionFindCode.parent_of.
      destruct (PTrieCode.get x (parents u)) as [parent|] eqn:Hlookup; [|reflexivity].
      exfalso. apply Habsent. unfold UnionFind.mem. rewrite Hlookup. discriminate. }
    unfold UnionFind.repr.
    induction (UnionFind.card u) as [|steps IH]; cbn [Nat.iter]; [reflexivity|].
    exact (eq_trans (f_equal (fun y => UnionFindCode.parent_of y u) IH) Hparent).
  Qed.

  (** No other identifier has the representative of an absent identifier. *)
  Lemma repr_eq_absent : forall u x fresh, UnionFind.wf u -> ~ UnionFind.mem u fresh ->
    (UnionFind.repr u x = UnionFind.repr u fresh <-> x = fresh).
  Proof.
    intros u x fresh Hwf Hfresh. split; [|intros ->; reflexivity].
    rewrite (repr_absent u fresh Hfresh). intro Heq.
    destruct (PTrieCode.get x (parents u)) as [parent|] eqn:Hlookup.
    - assert (Hmember : UnionFind.mem u x).
      { unfold UnionFind.mem. rewrite Hlookup. discriminate. }
      pose proof (repr_member u x Hwf Hmember) as Hroot.
      rewrite Heq in Hroot. contradiction.
    - assert (Habsent : ~ UnionFind.mem u x).
      { unfold UnionFind.mem. rewrite Hlookup. tauto. }
      rewrite (repr_absent u x Habsent) in Heq. exact Heq.
  Qed.

  (** An allocation interval also bounds the representative of every allocated identifier. *)
  Lemma repr_allocated : forall u bound, UnionFind.wf u ->
    (forall i, UnionFind.mem u i <-> (Npos i <= bound)%N) ->
    forall i, (Npos i <= bound)%N -> (Npos (UnionFind.repr u i) <= bound)%N.
  Proof.
    intros u bound Hwf Hmembers i Hi. apply Hmembers.
    apply repr_member; [exact Hwf|now apply Hmembers].
  Qed.

  (** A bounded allocation interval also bounds every key stored in the forest. *)
  Lemma width_allocated : forall u bound,
    (forall i, UnionFind.mem u i -> (Npos i <= bound)%N) ->
    UnionFind.width u <= N.size_nat bound.
  Proof.
    intros u bound Hallocated.
    assert (Hsupport : forall i, In i (UnionFind.support u) ->
      Pos.size_nat i <= N.size_nat bound).
    { intros i Hin. unfold UnionFind.support in Hin.
      apply in_map_iff in Hin. destruct Hin as [[key parent] [Heq Hin]].
      cbn [fst] in Heq. subst i.
      apply PTrie.elements_spec in Hin.
      assert (Hmember : UnionFind.mem u key).
      { unfold UnionFind.mem. rewrite Hin. discriminate. }
      specialize (Hallocated key Hmember).
      destruct bound as [|bound]; [lia|].
      cbn [N.size_nat]. destruct (Pos.eq_dec key bound) as [->|Hneq]; [reflexivity|].
      apply Pos.size_nat_monotone. lia. }
    unfold UnionFind.width. revert Hsupport.
    induction (UnionFind.support u) as [|i keys IH]; intro Hsupport; cbn [fold_right].
    - lia.
    - apply Nat.max_lub.
      + apply Hsupport. now left.
      + apply IH. intros j Hj. apply Hsupport. now right.
  Qed.

  (** Adding the next positive identifier extends a contiguous allocation interval by one. *)
  Lemma members_add_next : forall u bound, UnionFind.wf u ->
    (forall i, UnionFind.mem u i <-> (Npos i <= bound)%N) ->
    forall i, UnionFind.mem (UnionFindCode.add (N.succ_pos bound) u) i <->
      (Npos i <= N.succ bound)%N.
  Proof.
    intros u bound Hwf Hmembers i. rewrite UnionFind.mem_add by exact Hwf.
    rewrite Hmembers.
    assert (Hnext : Npos (N.succ_pos bound) = N.succ bound).
    { destruct bound; reflexivity. }
    split.
    - intros [Hi | Heq]; [lia | subst i; lia].
    - intro Hi. destruct (N.eq_dec (Npos i) (N.succ bound)) as [Heq|Hneq].
      + right. rewrite <- Hnext in Heq. now injection Heq.
      + left. lia.
  Qed.

  (** Union of allocated endpoints preserves the exact membership interval. *)
  Lemma members_union_present : forall x y u bound, UnionFind.wf u ->
    (forall i, UnionFind.mem u i <-> (Npos i <= bound)%N) ->
    (Npos x <= bound)%N -> (Npos y <= bound)%N ->
    forall i, UnionFind.mem (snd (UnionFindCode.union x y u)) i <->
      (Npos i <= bound)%N.
  Proof.
    intros x y u bound Hwf Hmembers Hx Hy i.
    rewrite UnionFind.mem_union by exact Hwf. rewrite Hmembers.
    split.
    - intros [Hi | [Hix | Hiy]]; [exact Hi | subst i; exact Hx | subst i; exact Hy].
    - intro Hi. now left.
  Qed.

End UnionFindCodeFacts.

Section FilteredProjectionFacts.

(** Filtering retains a permutation because each source occurrence is treated alike. *)
Lemma filter_permutation : forall A (test : A -> bool) xs ys,
  Permutation xs ys -> Permutation (filter test xs) (filter test ys).
Proof.
  intros A test xs ys Hperm. induction Hperm; cbn [filter].
  - constructor.
  - destruct (test x); [now constructor | exact IHHperm].
  - destruct (test x), (test y); cbn; try apply Permutation_refl.
    apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

(** Counting a projected value can be performed directly on the source rows. *)
Lemma filtered_projection_count : forall A B (test : A -> bool)
  (project : A -> B) (eqb : B -> B -> bool) u rows,
  length (filter (eqb u) (map project (filter test rows))) =
    length (filter (fun r => andb (test r) (eqb u (project r))) rows).
Proof.
  intros A B test project eqb u rows.
  induction rows as [|r rows IH]; cbn [filter map length]; [reflexivity |].
  destruct (test r); cbn [filter map length andb].
  - destruct (eqb u (project r)); cbn [length]; now rewrite IH.
  - exact IH.
Qed.

(** A duplicate-free source provides an exact finite witness for a projection count. *)
Lemma filtered_projection_witness : forall A B (test : A -> bool)
  (project : A -> B) (eqb : B -> B -> bool),
  (forall x y, reflect (x = y) (eqb x y)) -> forall u rows,
  NoDup rows -> exists rs,
    NoDup rs /\
    (forall r, In r rs <-> In r rows /\ test r = true /\ project r = u) /\
    length (filter (eqb u) (map project (filter test rows))) = length rs.
Proof.
  intros A B test project eqb Hreflect u rows Hnodup.
  exists (filter (fun r => andb (test r) (eqb u (project r))) rows).
  split; [now apply NoDup_filter |]. split.
  - intro r. rewrite filter_In, Bool.andb_true_iff.
    destruct (Hreflect u (project r)); intuition congruence.
  - apply filtered_projection_count.
Qed.

(** Every duplicate-free witness for the same source rows has the counted length. *)
Lemma filtered_projection_witness_length : forall A B (test : A -> bool)
  (project : A -> B) (eqb : B -> B -> bool),
  (forall x y, reflect (x = y) (eqb x y)) -> forall u rows rs,
  NoDup rows -> NoDup rs ->
  (forall r, In r rs <-> In r rows /\ test r = true /\ project r = u) ->
  length (filter (eqb u) (map project (filter test rows))) = length rs.
Proof.
  intros A B test project eqb Hreflect u rows rs Hrows Hrs Hmembers.
  destruct (filtered_projection_witness A B test project eqb Hreflect u rows Hrows)
    as [witness [Hnodup [Hwitness Hcount]]].
  rewrite Hcount. apply Permutation_length, NoDup_Permutation; try assumption.
  intro r. rewrite Hwitness, Hmembers. reflexivity.
Qed.

End FilteredProjectionFacts.

(** * Finite occurrence measures for a deferred repair queue *)

Module RebuildFuelFacts.

  Definition entries_for {E : Type} (owner : positive) (entries : list (positive * E)) :=
    filter (fun xe => Pos.eqb (fst xe) owner) entries.

  Definition without_owner {E : Type} (owner : positive) (entries : list (positive * E)) :=
    filter (fun xe => negb (Pos.eqb (fst xe) owner)) entries.

  Definition transfer {E : Type} (source target : positive)
      (entries : list (positive * E)) :=
    map (fun xe => if Pos.eqb (fst xe) source then (target, snd xe) else xe) entries.

  Definition occurrence_credit {E : Type} (credit : positive -> nat)
      (entries : list (positive * E)) : nat :=
    fold_right (fun xe n => credit (fst xe) + n) 0 entries.

  Definition queued_work {E : Type} (queue : list positive)
      (entries : list (positive * E)) : nat :=
    fold_right (fun x n => length (entries_for x entries) + 1 + n) 0 queue.

  (** Moving a bucket changes ownership without creating or deleting an occurrence. *)
  Lemma transfer_length : forall E source target (entries : list (positive * E)),
    length (transfer source target entries) = length entries.
  Proof.
    intros E source target entries. apply length_map.
  Qed.

  (** Owners in one class have the same remaining rank credit after a bucket transfer. *)
  Lemma transfer_credit : forall E credit source target (entries : list (positive * E)),
    credit source = credit target ->
    occurrence_credit credit (transfer source target entries) = occurrence_credit credit entries.
  Proof.
    intros E credit source target entries Heq.
    unfold transfer, occurrence_credit.
    induction entries as [| [x e] entries IH]; cbn [map fold_right fst snd];
      [reflexivity |].
    destruct (Pos.eqb x source) eqn:Hx; cbn [fst].
    - apply Pos.eqb_eq in Hx. subst x. now rewrite IH, Heq.
    - now rewrite IH.
  Qed.

  (** A transfer leaves every other owner's bucket unchanged. *)
  Lemma transfer_other : forall E source target query (entries : list (positive * E)),
    query <> source -> query <> target ->
    entries_for query (transfer source target entries) = entries_for query entries.
  Proof.
    intros E source target query entries Hsource Htarget.
    assert (Hsq : Pos.eqb source query = false) by (apply Pos.eqb_neq; congruence).
    assert (Htq : Pos.eqb target query = false) by (apply Pos.eqb_neq; congruence).
    unfold transfer, entries_for.
    induction entries as [| [x e] entries IH]; cbn [map filter fst snd];
      [reflexivity |].
    destruct (Pos.eqb x source) eqn:Hx; cbn [fst].
    - apply Pos.eqb_eq in Hx. subst x. now rewrite Hsq, Htq.
    - destruct (Pos.eqb x query); cbn; congruence.
  Qed.

  (** A queue that contains neither endpoint sees the same buckets after transfer. *)
  Lemma queued_transfer_away : forall E queue source target (entries : list (positive * E)),
    ~ In source queue -> ~ In target queue ->
    queued_work queue (transfer source target entries) = queued_work queue entries.
  Proof.
    intros E queue. induction queue as [| x queue IH]; intros source target entries Hsource Htarget.
    - reflexivity.
    - change (length (entries_for x (transfer source target entries)) + 1 +
        queued_work queue (transfer source target entries) =
        length (entries_for x entries) + 1 + queued_work queue entries).
      rewrite transfer_other by (cbn in *; intuition).
      rewrite IH by (cbn in *; intuition). reflexivity.
  Qed.

  (** Popping a loser exchanges its queued bucket for active entries and spends one unit. *)
  Lemma queue_transfer_measure : forall E credit source target queue
      (entries : list (positive * E)) classes,
    credit source = credit target -> ~ In source queue -> ~ In target queue ->
    occurrence_credit credit (transfer source target entries) +
      queued_work queue (transfer source target entries) +
      length (map snd (entries_for source entries)) + classes + 1 =
    occurrence_credit credit entries + queued_work (source :: queue) entries + classes.
  Proof.
    intros E credit source target queue entries classes Hcredit Hsource Htarget.
    rewrite transfer_credit by exact Hcredit.
    rewrite queued_transfer_away by assumption. rewrite length_map.
    change (occurrence_credit credit entries + queued_work queue entries +
      length (entries_for source entries) + classes + 1 =
      occurrence_credit credit entries +
        (length (entries_for source entries) + 1 + queued_work queue entries) + classes).
    lia.
  Qed.

  (** Selecting and excluding one owner partition the occurrence inventory. *)
  Lemma owner_partition : forall E owner (entries : list (positive * E)),
    length (entries_for owner entries) + length (without_owner owner entries) = length entries.
  Proof.
    intros E owner entries. unfold entries_for, without_owner.
    induction entries as [| [x e] entries IH]; cbn [filter fst length]; [reflexivity |].
    destruct (Pos.eqb x owner); cbn [negb length]; lia.
  Qed.

  (** Removing another owner's occurrences leaves the selected bucket unchanged. *)
  Lemma without_other : forall E owner query (entries : list (positive * E)),
    query <> owner -> entries_for query (without_owner owner entries) = entries_for query entries.
  Proof.
    intros E owner query entries Hneq.
    unfold entries_for, without_owner.
    induction entries as [| [x e] entries IH]; cbn [filter fst]; [reflexivity |].
    destruct (Pos.eqb x owner) eqn:Hx; cbn [negb filter fst].
    - apply Pos.eqb_eq in Hx. subst x.
      assert (Hfalse : Pos.eqb owner query = false) by (apply Pos.eqb_neq; congruence).
      now rewrite Hfalse.
    - destruct (Pos.eqb x query); cbn; congruence.
  Qed.

  (** Removing an owner outside the queue changes none of its queued buckets. *)
  Lemma queued_without_away : forall E queue owner (entries : list (positive * E)),
    ~ In owner queue -> queued_work queue (without_owner owner entries) = queued_work queue entries.
  Proof.
    intros E queue. induction queue as [| x queue IH]; intros owner entries Hnot.
    - reflexivity.
    - change (length (entries_for x (without_owner owner entries)) + 1 +
        queued_work queue (without_owner owner entries) =
        length (entries_for x entries) + 1 + queued_work queue entries).
      rewrite without_other by (cbn in *; intuition).
      rewrite IH by (cbn in *; intuition). reflexivity.
  Qed.

  (** A duplicate-free queue counts each stored occurrence at most once. *)
  Lemma queued_work_bound : forall E queue (entries : list (positive * E)),
    NoDup queue -> queued_work queue entries <= length entries + length queue.
  Proof.
    intros E queue entries Hnodup. revert entries.
    induction Hnodup as [| x queue Hnot Hnodup IH]; intro entries.
    - cbn [queued_work fold_right length]. lia.
    - specialize (IH (without_owner x entries)).
      rewrite queued_without_away in IH by exact Hnot.
      pose proof (owner_partition E x entries) as Hpartition.
      change (length (entries_for x entries) + 1 + queued_work queue entries <=
        length entries + S (length queue)). lia.
  Qed.

  (** A pointwise rank bound bounds the complete occurrence credit. *)
  Lemma occurrence_credit_bound : forall E credit (entries : list (positive * E)) bits,
    (forall xe, In xe entries -> credit (fst xe) <= bits) ->
    occurrence_credit credit entries <= bits * length entries.
  Proof.
    intros E credit entries. induction entries as [| xe entries IH]; intros bits Hbound.
    - cbn [occurrence_credit fold_right length]. lia.
    - assert (Hhead := Hbound xe (or_introl eq_refl)).
      assert (Htail : occurrence_credit credit entries <= bits * length entries).
      { apply IH. intros e Hin. apply Hbound. now right. }
      change (credit (fst xe) + occurrence_credit credit entries <= bits * S (length entries)). nia.
  Qed.

  (** The released fuel formula covers rank credit, queued work and represented classes. *)
  Lemma initial_measure_fuel : forall E credit queue (entries : list (positive * E)) bits classes,
    NoDup queue -> (forall xe, In xe entries -> credit (fst xe) <= bits) ->
    classes <= length entries ->
    occurrence_credit credit entries + queued_work queue entries + classes <
      (bits + 2) * (length entries + 1) + length queue + 1.
  Proof.
    intros E credit queue entries bits classes Hqueue Hcredit Hclasses.
    pose proof (queued_work_bound E queue entries Hqueue).
    pose proof (occurrence_credit_bound E credit entries bits Hcredit). nia.
  Qed.

End RebuildFuelFacts.

(** * Semantic invariants of the actual binary-fuel driver *)

Module LoopNFacts.

  (** Accessibility recursion preserves any invariant respected by its actual callback. *)
  Lemma loop_preserves : forall S R (lt : S -> S -> Prop)
      (step : forall s, {s1 : S | lt s1 s} + R) (Inv : S -> Prop) (Post : R -> Prop),
    (forall s s1 (Hlt : lt s1 s), Inv s -> step s = inl (exist _ s1 Hlt) -> Inv s1) ->
    (forall s r, Inv s -> step s = inr r -> Post r) ->
    forall s (Hacc : Acc lt s), Inv s -> Post (loop lt step s Hacc).
  Proof.
    intros S R lt step Inv Post Hgo Hstop s Hacc.
    induction Hacc as [s Hacc IH] using Acc_ind_dep. intro Hinv.
    cbn [loop Acc_inv]. destruct (step s) as [[s1 Hlt] | r] eqn:Hstep.
    - apply IH. eapply Hgo; eassumption.
    - eapply Hstop; eassumption.
  Qed.

  (** Both an exhausted state and a stopped result retain their callback invariants. *)
  Lemma loopN_preserves : forall S R (step : S -> S + R)
      (Inv : S -> Prop) (Post : R -> Prop),
    (forall s s1, Inv s -> step s = inl s1 -> Inv s1) ->
    (forall s r, Inv s -> step s = inr r -> Post r) ->
    forall fuel s, Inv s ->
    match loopN step fuel s with inl s1 => Inv s1 | inr r => Post r end.
  Proof.
    intros S R step Inv Post Hgo Hstop fuel s Hinitial. unfold loopN.
    apply (loop_preserves (N * S) (S + R) loopN_lt (loopN_step step)
      (fun fs => Inv (snd fs))
      (fun result => match result with inl s1 => Inv s1 | inr r => Post r end)).
    - intros [[| p] current] next Hlt Hinv Hstep; cbn [loopN_step] in Hstep;
        [discriminate |].
      destruct (step current) as [current' | result] eqn:Hcallback; [| discriminate].
      inversion Hstep; subst. eapply Hgo; eassumption.
    - intros [[| p] current] result Hinv Hstep; cbn [loopN_step] in Hstep.
      + injection Hstep as Hresult. subst result. exact Hinv.
      + destruct (step current) as [current' | value] eqn:Hcallback; [discriminate |].
        injection Hstep as Hresult. subst result. eapply Hstop; eassumption.
    - exact Hinitial.
  Qed.

  (** A stopped callback determines the accessibility loop's result immediately. *)
  Lemma loop_stop : forall S R (lt : S -> S -> Prop)
      (step : forall s, {s1 : S | lt s1 s} + R) s (Hacc : Acc lt s) r,
    step s = inr r -> loop lt step s Hacc = r.
  Proof.
    intros S R lt step s [Hacc] r Hstop. cbn [loop]. now rewrite Hstop.
  Qed.

  (** Any positive fuel returns an immediate stop without modifying its result. *)
  Lemma loopN_stop : forall S R (step : S -> S + R) fuel s r,
    (0 < fuel)%N -> step s = inr r -> loopN step fuel s = inr r.
  Proof.
    intros S R step fuel s r Hfuel Hstop. unfold loopN. apply loop_stop.
    destruct fuel as [| p]; [lia |]. cbn [loopN_step]. now rewrite Hstop.
  Qed.

  (** The accessibility loop is monotone in the supplied callback clock. *)
  Lemma T_loop_mono : forall S R (lt : S -> S -> Prop)
      (step : forall s, {s1 : S | lt s1 s} + R) (T_step T_step' : S -> N),
    (forall s, (T_step s <= T_step' s)%N) -> forall s (Hacc : Acc lt s),
    (T_loop lt step T_step s Hacc <= T_loop lt step T_step' s Hacc)%N.
  Proof.
    intros S R lt step T_step T_step' Hmono s Hacc.
    induction Hacc as [s Hacc IH] using Acc_ind_dep.
    time_unfold @T_loop. cbn [Acc_inv].
    destruct (step s) as [[s1 Hlt] | r].
    - specialize (IH s1 Hlt). specialize (Hmono s). lia.
    - specialize (Hmono s). lia.
  Qed.

  (** The binary driver's local clock adds identical overhead to either callback bound. *)
  Lemma T_loopN_step_mono : forall S R (step : S -> S + R) (T_step T_step' : S -> N),
    (forall s, (T_step s <= T_step' s)%N) -> forall fs,
    (T_loopN_step step T_step fs <= T_loopN_step step T_step' fs)%N.
  Proof.
    intros S R step T_step T_step' Hmono [[| p] s]; time_unfold @T_loopN_step.
    - lia.
    - specialize (Hmono s). destruct (step s); lia.
  Qed.

  (** Raising a pointwise callback bound raises the actual derived binary-loop clock. *)
  Lemma T_loopN_mono : forall S R (step : S -> S + R) (T_step T_step' : S -> N),
    (forall s, (T_step s <= T_step' s)%N) -> forall fuel s,
    (T_loopN step T_step fuel s <= T_loopN step T_step' fuel s)%N.
  Proof.
    intros S R step T_step T_step' Hmono fuel s. time_unfold @T_loopN.
    apply N.add_le_mono_l. apply T_loop_mono. now apply T_loopN_step_mono.
  Qed.

  (** Pointwise-equal callback clocks give exactly equal loop clocks without extensionality. *)
  Lemma T_loopN_clock_ext : forall S R (step : S -> S + R) (T_step T_step' : S -> N),
    (forall s, T_step s = T_step' s) -> forall fuel s,
    T_loopN step T_step fuel s = T_loopN step T_step' fuel s.
  Proof.
    intros S R step T_step T_step' Hequal fuel s. apply N.le_antisymm;
      apply T_loopN_mono; intro current; now rewrite Hequal.
  Qed.

  (** Pointwise-equal callbacks and clocks give the same accessibility-loop clock. *)
  Lemma T_loop_congr : forall S R (lt : S -> S -> Prop)
      (step step' : forall s, {s1 : S | lt s1 s} + R) (T_step T_step' : S -> N),
    (forall s, step s = step' s) -> (forall s, T_step s = T_step' s) ->
    forall s (Hacc : Acc lt s),
    T_loop lt step T_step s Hacc = T_loop lt step' T_step' s Hacc.
  Proof.
    intros S R lt step step' T_step T_step' Hstep Htime s Hacc.
    induction Hacc as [s Hacc IH] using Acc_ind_dep.
    time_unfold @T_loop. cbn [Acc_inv]. rewrite (Hstep s), (Htime s).
    destruct (step' s) as [[s1 Hlt] | r]; [now rewrite (IH s1 Hlt) | reflexivity].
  Qed.

  (** The binary wrapper preserves pointwise callback equality, including its decrease evidence. *)
  Lemma loopN_step_congr : forall S R (step step' : S -> S + R),
    (forall s, step s = step' s) -> forall fs, loopN_step step fs = loopN_step step' fs.
  Proof.
    intros S R step step' Hstep [[| p] s]; cbn [loopN_step]; [reflexivity |].
    now rewrite Hstep.
  Qed.

  (** The binary wrapper's derived clocks agree whenever its callbacks and their clocks agree. *)
  Lemma T_loopN_step_congr : forall S R (step step' : S -> S + R) (T_step T_step' : S -> N),
    (forall s, step s = step' s) -> (forall s, T_step s = T_step' s) -> forall fs,
    T_loopN_step step T_step fs = T_loopN_step step' T_step' fs.
  Proof.
    intros S R step step' T_step T_step' Hstep Htime [[| p] s]; time_unfold @T_loopN_step.
    - reflexivity.
    - now rewrite Hstep, Htime.
  Qed.

  (** Exact clock congruence requires only pointwise equality, with no extensionality axiom. *)
  Lemma T_loopN_congr : forall S R (step step' : S -> S + R) (T_step T_step' : S -> N),
    (forall s, step s = step' s) -> (forall s, T_step s = T_step' s) -> forall fuel s,
    T_loopN step T_step fuel s = T_loopN step' T_step' fuel s.
  Proof.
    intros S R step step' T_step T_step' Hstep Htime fuel s. time_unfold @T_loopN.
    apply f_equal. apply T_loop_congr.
    - now apply loopN_step_congr.
    - now apply T_loopN_step_congr.
  Qed.

End LoopNFacts.

(** * Stored occurrence buckets *)

Module OccurrenceBucketCode (K : KEY_OPS) (M : MAP_OPS K).

  (** An absent bucket contributes no occurrence. *)
  Definition bucket {A} (owner : K.t) (m : M.t (list A)) : list A :=
    match M.get owner m with Some occurrences => occurrences | None => [] end.

  (** Registration retains one entry for each occurrence, including repeated entries. *)
  Definition add {A} (owner : K.t) (entry : A) (m : M.t (list A)) : M.t (list A) :=
    M.set owner (entry :: bucket owner m) m.

  (** Transfer visits the source bucket and leaves the total occurrence inventory unchanged. *)
  Definition transfer {A} (source target : K.t) (m : M.t (list A)) : M.t (list A) :=
    if K.eqb source target then m else
      M.set target (rev_append (bucket source m) (bucket target m)) (M.remove source m).

  (** Each supplied occurrence is registered once without deduplication. *)
  Fixpoint register {A} (occurrences : list (K.t * A)) (m : M.t (list A)) : M.t (list A) :=
    match occurrences with
    | [] => m
    | (owner, entry) :: rest => register rest (add owner entry m)
    end.

End OccurrenceBucketCode.

Module OccurrenceBucketFacts (K : KEY) (M : MAP K).
  Include OccurrenceBucketCode K M.
  Module Maps := FiniteMapFacts K M.

  Section Inventory.
  Context {A : Type}.

  (** The specification enumeration labels every stored occurrence with its bucket owner. *)
  Definition entries (m : M.t (list A)) : list (K.t * A) :=
    flat_map (fun binding => map (pair (fst binding)) (snd binding)) (M.elements m).

  (** Forgetting bucket owners still retains the complete multiset of entries. *)
  Definition inventory (m : M.t (list A)) : list A := flat_map snd (M.elements m).

  Definition count (m : M.t (list A)) : nat := length (entries m).

  (** Registration and transfer preserve the public map invariant. *)
  Lemma wf_add : forall owner (entry : A) (m : M.t (list A)),
    M.wf m -> M.wf (add owner entry m).
  Proof.
    intros owner entry m Hwf. unfold add. now apply M.wf_set.
  Qed.

  Lemma wf_transfer : forall source target (m : M.t (list A)),
    M.wf m -> M.wf (transfer source target m).
  Proof.
    intros source target m Hwf. unfold transfer. destruct (K.eqb source target); [exact Hwf |].
    apply M.wf_set. now apply M.wf_remove.
  Qed.

  Lemma wf_register : forall (occurrences : list (K.t * A)) (m : M.t (list A)),
    M.wf m -> M.wf (register occurrences m).
  Proof.
    induction occurrences as [| [owner entry] rest IH]; intros m Hwf; cbn [register].
    - exact Hwf.
    - apply IH. now apply wf_add.
  Qed.

  (** Enumerated membership is exactly membership in the owner's keyed bucket. *)
  Lemma entries_member : forall m owner entry, M.wf m ->
    (In (owner, entry) (entries m) <-> In entry (bucket owner m)).
  Proof.
    intros m owner entry Hwf. unfold entries. rewrite in_flat_map. split.
    - intros [[key occurrences] [Hbinding Hin]].
      apply in_map_iff in Hin as [value [Hequal Hin]]. cbn [fst snd] in Hequal, Hin.
      injection Hequal as -> ->. apply M.elements_spec in Hbinding; [| exact Hwf].
      unfold bucket. now rewrite Hbinding.
    - unfold bucket. destruct (M.get owner m) as [occurrences |] eqn:Hget;
        [| contradiction]. intro Hin. exists (owner, occurrences). split.
      + now apply M.elements_spec.
      + cbn [fst snd]. now apply in_map.
  Qed.

  (** Dropping the owner labels preserves every entry and every repetition. *)
  Lemma entries_inventory : forall m, map snd (entries m) = inventory m.
  Proof.
    intro m. unfold entries, inventory. induction (M.elements m) as [| [owner occurrences] rest IH].
    - reflexivity.
    - cbn [flat_map fst snd]. rewrite map_app, map_map, IH.
      change (map (fun x : A => x) occurrences ++ flat_map snd rest =
        occurrences ++ flat_map snd rest). now rewrite map_id.
  Qed.

  Lemma inventory_length : forall m, length (inventory m) = count m.
  Proof.
    intro m. unfold count. rewrite <- entries_inventory, length_map. reflexivity.
  Qed.

  (** One optional map binding contributes precisely its optional bucket contents. *)
  Lemma optional_inventory : forall (owner : K.t) (previous : option (list A)),
    flat_map snd (option_list (option_map (pair owner) previous)) =
      match previous with Some occurrences => occurrences | None => [] end.
  Proof.
    intros owner [occurrences |]; cbn [option_list option_map flat_map snd]; now rewrite ?app_nil_r.
  Qed.

  (** Replacing one bucket retains exactly the same inventory outside that bucket. *)
  Lemma inventory_set_decomposition : forall m owner occurrences, M.wf m ->
    exists rest,
      Permutation (inventory m) (bucket owner m ++ rest) /\
      Permutation (inventory (M.set owner occurrences m)) (occurrences ++ rest).
  Proof.
    intros m owner occurrences Hwf.
    destruct (Maps.set_elements_decomposition _ m owner (M.get owner m) occurrences Hwf eq_refl)
      as [rest [Hbefore [Hafter _]]]. exists (flat_map snd rest). split.
    - assert (Hflat : Permutation (inventory m)
        (flat_map snd (option_list (option_map (pair owner) (M.get owner m)) ++ rest))).
      { unfold inventory. now apply Permutation_flat_map. }
      rewrite flat_map_app, optional_inventory in Hflat. exact Hflat.
    - unfold inventory. change (Permutation (flat_map snd (M.elements (M.set owner occurrences m)))
        (flat_map snd ((owner, occurrences) :: rest))). now apply Permutation_flat_map.
  Qed.

  (** Each registration increases the exact inventory count by one, even for a duplicate entry. *)
  Lemma count_add : forall owner entry m, M.wf m -> count (add owner entry m) = S (count m).
  Proof.
    intros owner entry m Hwf.
    destruct (inventory_set_decomposition m owner (entry :: bucket owner m) Hwf)
      as [rest [Hbefore Hafter]].
    apply Permutation_length in Hbefore. apply Permutation_length in Hafter.
    rewrite !length_app in Hbefore, Hafter. cbn [length] in Hafter.
    unfold add. rewrite <- !inventory_length. lia.
  Qed.

  (** A registration adds exactly its selected owner-entry pair. *)
  Lemma entries_add : forall m owner entry query value, M.wf m ->
    (In (query, value) (entries (add owner entry m)) <->
      In (query, value) (entries m) \/ (query = owner /\ value = entry)).
  Proof.
    intros m owner entry query value Hwf.
    rewrite !entries_member by (try exact Hwf; now apply wf_add).
    unfold add, bucket. destruct (K.eqb_spec query owner) as [-> | Hdifferent].
    - rewrite M.get_set_same. cbn [In]. intuition congruence.
    - rewrite M.get_set_other by exact Hdifferent. intuition congruence.
  Qed.

  (** Repeated registration increases the count by exactly the number of supplied occurrences. *)
  Lemma count_register : forall occurrences m, M.wf m ->
    count (register occurrences m) = length occurrences + count m.
  Proof.
    induction occurrences as [| [owner entry] rest IH]; intros m Hwf; cbn [register length].
    - reflexivity.
    - rewrite IH by (now apply wf_add). rewrite count_add by exact Hwf. lia.
  Qed.

  (** Every supplied pair remains represented, including pairs repeated in the input list. *)
  Lemma entries_register : forall occurrences m query value, M.wf m ->
    (In (query, value) (entries (register occurrences m)) <->
      In (query, value) (entries m) \/ In (query, value) occurrences).
  Proof.
    induction occurrences as [| [owner entry] rest IH]; intros m query value Hwf;
      cbn [register In].
    - tauto.
    - rewrite IH by (now apply wf_add). rewrite entries_add by exact Hwf.
      intuition congruence.
  Qed.

  (** A stored binary count can be maintained using only the number of new occurrences. *)
  Lemma register_count_consistent : forall occurrences m n,
    M.wf m -> N.to_nat n = count m ->
    N.to_nat (n + N.of_nat (length occurrences)) = count (register occurrences m).
  Proof.
    intros occurrences m n Hwf Hcount.
    rewrite N2Nat.inj_add, Nat2N.id, count_register by exact Hwf. lia.
  Qed.

  (** An empty map has no stored occurrences and therefore needs a zero count. *)
  Lemma entries_empty : entries (@M.empty (list A)) = [].
  Proof.
    destruct (entries (@M.empty (list A))) as [| [owner entry] rest] eqn:Hentries;
      [reflexivity |]. exfalso.
    assert (Hin : In (owner, entry) (entries (@M.empty (list A)))).
    { rewrite Hentries. now left. }
    apply (entries_member _ owner entry (M.wf_empty (list A))) in Hin.
    unfold bucket in Hin. rewrite M.get_empty in Hin. contradiction.
  Qed.

  Lemma count_empty : count (@M.empty (list A)) = 0.
  Proof.
    unfold count. now rewrite entries_empty.
  Qed.

  (** Registration adds precisely one value to the complete occurrence multiset. *)
  Lemma inventory_add : forall owner entry m, M.wf m ->
    Permutation (inventory (add owner entry m)) (entry :: inventory m).
  Proof.
    intros owner entry m Hwf. unfold add.
    destruct (inventory_set_decomposition m owner (entry :: bucket owner m) Hwf)
      as [rest [Hbefore Hafter]].
    eapply Permutation_trans; [exact Hafter |].
    apply perm_skip. now apply Permutation_sym.
  Qed.

  (** Removing a bucket partitions the inventory into that bucket and the exact remaining map. *)
  Lemma inventory_remove_decomposition : forall m owner, M.wf m ->
    Permutation (inventory m) (bucket owner m ++ inventory (M.remove owner m)).
  Proof.
    intros m owner Hwf.
    pose proof (Maps.remove_elements_decomposition _ m owner (M.get owner m) Hwf eq_refl) as Hparts.
    assert (Hflat : Permutation (inventory m)
      (flat_map snd (option_list (option_map (pair owner) (M.get owner m)) ++
        M.elements (M.remove owner m)))).
    { unfold inventory. now apply Permutation_flat_map. }
    rewrite flat_map_app, optional_inventory in Hflat. exact Hflat.
  Qed.

  (** Reversing a source bucket while appending does not change any occurrence multiplicity. *)
  Lemma reverse_append_inventory : forall (first second : list A),
    Permutation (rev_append first second) (first ++ second).
  Proof.
    intro first. induction first as [| entry first IH]; intro second; cbn [rev_append app].
    - reflexivity.
    - eapply Permutation_trans; [exact (IH (entry :: second)) |].
      apply Permutation_sym. apply Permutation_middle.
  Qed.

  Lemma reverse_append_member : forall (first second : list A) entry,
    In entry (rev_append first second) <-> In entry first \/ In entry second.
  Proof.
    intros first second entry. pose proof (reverse_append_inventory first second) as Hperm. split.
    - intro Hin. apply in_app_iff. eapply Permutation_in; eassumption.
    - intro Hin. eapply Permutation_in; [apply Permutation_sym; exact Hperm |].
      now apply in_app_iff.
  Qed.

  (** Moving a bucket changes ownership but preserves the complete multiset of entries. *)
  Lemma inventory_transfer : forall source target m, M.wf m ->
    Permutation (inventory (transfer source target m)) (inventory m).
  Proof.
    intros source target m Hwf. unfold transfer.
    destruct (K.eqb_spec source target) as [Hequal | Hdifferent]; [reflexivity |].
    set (removed := M.remove source m).
    assert (Hremoved : M.wf removed) by (unfold removed; now apply M.wf_remove).
    assert (Htarget : bucket target removed = bucket target m).
    { unfold removed, bucket. now rewrite M.get_remove_other by congruence. }
    pose proof (inventory_remove_decomposition m source Hwf) as Hsource. fold removed in Hsource.
    destruct (inventory_set_decomposition removed target
      (rev_append (bucket source m) (bucket target m)) Hremoved)
      as [rest [Hbefore Hafter]]. rewrite Htarget in Hbefore.
    eapply Permutation_trans; [exact Hafter |].
    eapply Permutation_trans.
    - apply Permutation_app_tail. apply reverse_append_inventory.
    - replace ((bucket source m ++ bucket target m) ++ rest)
        with (bucket source m ++ (bucket target m ++ rest)) by (now rewrite app_assoc).
      apply Permutation_sym. eapply Permutation_trans; [exact Hsource |].
      now apply Permutation_app_head.
  Qed.

  (** Transfer needs no change to the exact stored occurrence count. *)
  Lemma count_transfer : forall source target m, M.wf m ->
    count (transfer source target m) = count m.
  Proof.
    intros source target m Hwf. pose proof (inventory_transfer source target m Hwf) as Hperm.
    apply Permutation_length in Hperm. now rewrite !inventory_length in Hperm.
  Qed.

  (** A transfer preserves every other owner and moves precisely the source occurrences to the target. *)
  Lemma bucket_transfer_member : forall source target (m : M.t (list A)) query value,
    In value (bucket query (transfer source target m)) <->
      (In value (bucket query m) /\ query <> source) \/
      (query = target /\ In value (bucket source m)).
  Proof.
    intros source target m query value. unfold transfer.
    destruct (K.eqb_spec source target) as [-> | Hdifferent].
    - destruct (K.eqb_spec query target) as [-> | Hquery]; intuition congruence.
    - unfold bucket at 1. destruct (K.eqb_spec query target) as [-> | Htarget].
      + rewrite M.get_set_same, reverse_append_member. intuition congruence.
      + rewrite M.get_set_other by exact Htarget.
        destruct (K.eqb_spec query source) as [-> | Hsource].
        * rewrite M.get_remove_same. cbn [In]. intuition congruence.
        * rewrite M.get_remove_other by exact Hsource. fold (bucket query m). intuition congruence.
  Qed.

  (** The labeled specification inventory exposes exactly the same transfer relation. *)
  Lemma entries_transfer : forall source target m query value, M.wf m ->
    (In (query, value) (entries (transfer source target m)) <->
      (In (query, value) (entries m) /\ query <> source) \/
      (query = target /\ In (source, value) (entries m))).
  Proof.
    intros source target m query value Hwf.
    rewrite (entries_member (transfer source target m) query value
      (wf_transfer source target m Hwf)).
    rewrite (entries_member m query value Hwf), (entries_member m source value Hwf).
    apply bucket_transfer_member.
  Qed.

  (** No bucket contains more occurrences than the complete stored inventory. *)
  Lemma bucket_length_le_count : forall m owner, M.wf m -> length (bucket owner m) <= count m.
  Proof.
    intros m owner Hwf. pose proof (inventory_remove_decomposition m owner Hwf) as Hperm.
    apply Permutation_length in Hperm. rewrite length_app, inventory_length in Hperm. lia.
  Qed.

  End Inventory.
End OccurrenceBucketFacts.
