(** * Relational leastness needs relational comparison views

    A comparison view with an identifier output can satisfy a relational put under the
    released definition of [present]. For example, the rule with no query atoms that inserts
    the nullary relation [1] is closed in a view containing only its identifier-output row.
    Builds on: Model, Sorts and RunSig. *)

From Stdlib Require Import List PArith NArith Lia.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.

Import List.ListNotations.

Definition leastness_program {V : Type} : program V :=
  Program V [Decl 1%positive [] ORel] [Rule V [] [Put 1%positive [] None]].

Definition leastness_comparison {V : Type} : view (V := V) :=
  {| row := fun f k o => f = 1%positive /\ k = [] /\ o = Some (Id 1%positive);
     same := eq;
     kind := lookup_kind [Decl 1%positive [] ORel] |}.

(** The comparison has the declared relation kind despite its wrongly sorted row. *)
Example leastness_comparison_kind {V : Type} :
  kind (@leastness_comparison V) 1%positive = Some ORel.
Proof.
  reflexivity.
Qed.

(** Relational closure alone does not require the output of the witnessing row to be absent. *)
Example leastness_comparison_closed {V : Type}
    (prim : positive -> list V -> option V) (merge : positive -> V -> V -> V) :
  closed prim merge leastness_program leastness_comparison.
Proof.
  intros r s Hr Hmatch.
  destruct Hr as [<- | []].
  cbn [actions present].
  exists [], (Some (Id 1%positive)).
  split; [constructor |].
  repeat split.
Qed.

(** The comparison omits the relation row that leastness claims it must contain. *)
Example leastness_comparison_missing {V : Type} :
  ~ row (@leastness_comparison V) 1%positive [] None.
Proof.
  intros [_ [_ Hout]].
  discriminate.
Qed.

(** The empty-query rule derives the missing relation row from any seed view. *)
Example leastness_derivation {V : Type} (prim : positive -> list V -> option V)
    (seed : view (V := V)) :
  derives prim leastness_program seed 1%positive [].
Proof.
  eapply derive_rule with (r := Rule V [] [Put 1%positive [] None])
    (s := fun _ => None).
  - now left.
  - constructor.
  - constructor. constructor.
Qed.

(** These four public run laws force a relation row in the result but exclude that row
    from a closed extension of its empty seed. The contradiction identifies a defect in
    [run_least], rather than supplying a proof of any implementation obligation. *)
Module PublicLeastnessCounterexample (V : VALUE) (I : INDEX V) (J : JOIN V I)
    (D : DATABASE V I) (R : RUN V I J D).
  Definition p : program V.t := leastness_program.
  Definition cp : compiled V.t := R.plan p.
  Definition seed : D.t := D.init (decls V.t p) (Syntax.slots V.t cp).

  Lemma p_sorted : program_ok p.
  Proof.
    constructor; [|constructor].
    exists ctx_empty. split; [constructor |].
    cbn [actions actions_ok].
    exists [], ORel. repeat split; constructor.
  Qed.

  Lemma seed_loaded : R.loaded p cp seed.
  Proof.
    split.
    - intro f.
      exact (proj1 (proj2 (proj2 (D.init_view (decls V.t p)
        (Syntax.slots V.t cp) f [] None 1%positive 1%positive)))).
    - split.
      + exact (proj1 (proj2 (proj2 (proj2 (D.init_view (decls V.t p)
          (Syntax.slots V.t cp) 1%positive [] None 1%positive 1%positive))))).
      + intros f k o Hrow.
        exfalso.
        exact (proj1 (proj1 (D.init_view (decls V.t p)
          (Syntax.slots V.t cp) f k o 1%positive 1%positive)) Hrow).
  Qed.

  Lemma seed_no_ids : R.no_ids seed.
  Proof.
    split.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (D.init_view (decls V.t p)
        (Syntax.slots V.t cp) 1%positive [] None 1%positive 1%positive)))))).
    - intros f k o Hrow.
      exfalso.
      exact (proj1 (proj1 (D.init_view (decls V.t p)
        (Syntax.slots V.t cp) f k o 1%positive 1%positive)) Hrow).
  Qed.

  Lemma seed_included : R.includes (D.view seed) leastness_comparison.
  Proof.
    intros f k o Hrow.
    exfalso.
    exact (proj1 (proj1 (D.init_view (decls V.t p)
      (Syntax.slots V.t cp) f k o 1%positive 1%positive)) Hrow).
  Qed.

  Lemma public_leastness_conflict : False.
  Proof.
    assert (Hplan : R.plans_ok p cp) by (apply R.plan_checked; exact p_sorted).
    assert (Hwf : D.wf seed) by apply D.wf_init.
    assert (Hrel : relational_fragment p = true) by reflexivity.
    assert (Hprim : prim_free p = true) by reflexivity.
    set (lim := Limits (N.of_nat (2 * R.herbrand p seed + 2)) 0%N).
    assert (Hfuel : N.to_nat (max_iter lim) >= 2 * R.herbrand p seed + 2).
    { unfold lim. cbn [max_iter]. rewrite Nat2N.id. lia. }
    pose proof (R.run_terminates p cp lim seed Hplan Hwf seed_loaded Hrel Hprim
      seed_no_ids Hfuel) as Hstop.
    destruct (R.run p cp lim seed) as [st result] eqn:Hrun.
    cbn [fst] in Hstop. subst st.
    pose proof (R.run_wf p cp lim seed Hplan Hwf seed_loaded) as Hresult.
    rewrite Hrun in Hresult. cbn [snd] in Hresult.
    destruct Hresult as [Hwf_result [Hcanonical [Hkinds [Hslots Hsorted]]]].
    pose proof (R.run_closed p cp lim seed result Hplan Hwf seed_loaded Hrun) as Hclosed.
    specialize (Hclosed (Rule V.t [] [Put 1%positive [] None]) (fun _ => None)).
    assert (Hin : In (Rule V.t [] [Put 1%positive [] None]) (rules V.t p)) by now left.
    assert (Hmatch : matches V.prim (D.view result) [] (fun _ => None)) by constructor.
    specialize (Hclosed Hin Hmatch).
    cbn [actions present] in Hclosed.
    destruct Hclosed as [k [o [Hterms [Hrow _]]]].
    inversion Hterms; subst k.
    destruct (Hsorted 1%positive [] o Hrow) as [out [Hargs [Hkind Hout]]].
    rewrite Hkinds in Hkind. cbn [p leastness_program program_kind decls lookup_kind] in Hkind.
    injection Hkind as <-.
    destruct o as [c |]; [destruct c; discriminate |].
    pose proof (R.run_least p cp lim seed result Hplan Hwf seed_loaded Hrel seed_no_ids
      Hrun leastness_comparison (leastness_comparison_closed V.prim V.merge)
      seed_included 1%positive [] None Hrow) as Hmissing.
    exact (leastness_comparison_missing Hmissing).
  Qed.
End PublicLeastnessCounterexample.
