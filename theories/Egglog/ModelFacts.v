(** * Meaning of stored engine facts

    These lemmas connect the frozen view semantics to interpretations in a model.
    For example, equal identifiers in a satisfying view have the same denotation.
    Builds on: Syntax, Model and Stdlib lists. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model DatabaseSig.

Import List.ListNotations.

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

End ModelFacts.
