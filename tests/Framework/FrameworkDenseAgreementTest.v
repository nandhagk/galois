(** * Agreement clients and a missing-exit counterexample

    A counter ignores an extra boolean component while preserving every trace and ending.
    For example, the two initial boolean values have the same behaviour.
    Builds on: FrameworkDenseAgreement and FrameworkDenseForwardTest. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns.
From Galois.Framework Require Import FrameworkDense FrameworkDenseAgreement.
From Galois.Tests.Framework Require Import FrameworkDenseForwardTest.
Import List.ListNotations.

Module TaggedCounter.

Definition m : semantics (DenseCounter.state * bool) unit :=
  Semantics (fun s => fst s = DenseCounter.C0)
    (fun s l t => step DenseCounter.m (fst s) l (fst t) /\ snd t = snd s).

Definition lk : Link.t (DenseCounter.state * bool) unit bool unit :=
  Link.Make (fun s => DenseCounter.point (fst s))
    (fun s _ _ _ => fst s = DenseCounter.C0)
    (fun s _ _ => fst s = DenseCounter.C1).

Definition en : endings (DenseCounter.state * bool) :=
  Endings (fun s => fst s = DenseCounter.C2) (fun _ => False) (fun _ => False).

Definition D : Dense.t bool unit bool :=
  Dense.of_pure DenseCounter.cfg Backward bool_lattice (fun _ => None) (fun _ a => a).

Definition sigma (_ : bool) := false.

Definition R : agreement bool (DenseCounter.state * bool) :=
  Agreement bool (DenseCounter.state * bool)
    (fun a s t => fst s = fst t /\ (a = true -> snd s = snd t)).

Lemma link_ok : link_laws m (Cfg.graph (Dense.cfg D)) lk.
Proof.
  constructor.
  - exact (cfg_wf DenseCounter.link_ok).
  - intros [s b] Hi; change (s = DenseCounter.C0) in Hi; subst s; vm_compute; tauto.
  - intros [s b] l [t c] Hr [Hstep Hbit]; destruct s; cbn in Hstep.
    + right; exists tt; reflexivity.
    + left; reflexivity.
    + contradiction.
  - intros [] [s b] l [t c] Hr [Hstep Hbit] Htaken.
    change (s = DenseCounter.C0) in Htaken; subst s.
    change (l = [tt] /\ t = DenseCounter.C1) in Hstep.
    destruct Hstep as [-> ->]; vm_compute; tauto.
  - intros [s b] l [t c] Hr [Hstep Hbit] Hstay.
    change (s = DenseCounter.C1) in Hstay; subst s.
    change (l = [] /\ t = DenseCounter.C2) in Hstep.
    destruct Hstep as [-> ->]; reflexivity.
Qed.

Lemma agree_ok : agreement_laws bool_lattice R.
Proof.
  constructor.
  - intros a s; split; reflexivity.
  - intros [] [] s t Hab Hrel; vm_compute in Hab; try discriminate; try exact Hrel.
    destruct Hrel as [Hstage Hbit]; split; [exact Hstage|discriminate].
Qed.

Lemma agree_symmetric : DenseAgreement.agreement_symmetric R.
Proof.
  intros a s t [Hstage Hbit]; split; [symmetry; exact Hstage|].
  intro Ha; symmetry; apply Hbit; exact Ha.
Qed.

Lemma post : post_solution (Dense.lat D) (Dense.system D) sigma.
Proof.
  apply (proj2 (Dense.post_solution_iff D sigma bool_laws)); split.
  - intros n a Hn Ha; discriminate Ha.
  - intros e He; reflexivity.
Qed.

Lemma steps : DenseAgreement.step_agrees m D lk R (reachable_state m) sigma.
Proof.
  split.
  - intros e t s l s' Hr Hstep Hs Ht Hpoint Htaken [Hstage Hbit].
    exists (fst s', snd t); split.
    + split.
      * change (step DenseCounter.m (fst t) l (fst s')).
        rewrite <- Hstage; exact (proj1 Hstep).
      * reflexivity.
    + split.
      * change (fst t = DenseCounter.C0).
        rewrite <- Hstage; exact Htaken.
      * split; [reflexivity|discriminate].
  - intros t s l s' Hr Hstep Hs Ht Hpoint Hstay [Hstage Hbit].
    exists (fst s', snd t); split.
    + split.
      * change (step DenseCounter.m (fst t) l (fst s')).
        rewrite <- Hstage; exact (proj1 Hstep).
      * reflexivity.
    + split.
      * change (fst t = DenseCounter.C1).
        rewrite <- Hstage; exact Hstay.
      * split; [reflexivity|discriminate].
Qed.

Lemma ends : DenseAgreement.ends_agree en D lk R (reachable_state m).
Proof.
  intros s t Hs Ht Hpoint [Hstage Hbit].
  change ((fst s = DenseCounter.C2 <-> fst t = DenseCounter.C2) /\
    (False <-> False) /\ (False <-> False)).
  rewrite Hstage; tauto.
Qed.

Example agreement_positive :
  same_behaviour m en (DenseCounter.C0, false) m en (DenseCounter.C0, true).
Proof.
  eapply (DenseAgreement.agreement_same_behaviour m en D lk (fun _ => R)
    (reachable_state m) sigma).
  - reflexivity.
  - exact bool_laws.
  - exact link_ok.
  - exact agree_ok.
  - exact agree_symmetric.
  - apply DenseAgreement.reachable_invariant.
  - exact steps.
  - exact ends.
  - exact post.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [reflexivity|discriminate].
Qed.

Example absent_boundary :
  DenseAgreement.exit_fact D true = false /\
  leb (Dense.lat D) (DenseAgreement.exit_fact D true) (sigma true) = true.
Proof.
  split; [vm_compute; reflexivity|].
  apply DenseAgreement.boundary_bound.
  - reflexivity.
  - exact bool_laws.
  - exact post.
  - vm_compute; tauto.
Qed.

Definition nonterminal_seed : Dense.t bool unit bool :=
  Dense.of_pure DenseCounter.cfg Backward bool_lattice
    (fun n => if n then None else Some true) (fun _ a => a).

Example listed_nonterminal_boundary :
  leb (Dense.lat nonterminal_seed) (DenseAgreement.exit_fact nonterminal_seed false)
    (negb false) = true.
Proof.
  eapply DenseAgreement.boundary_bound.
  - reflexivity.
  - exact bool_laws.
  - apply (proj2 (Dense.post_solution_iff nonterminal_seed negb bool_laws)); split.
    + intros [] a Hn Ha; vm_compute in Ha; try discriminate; inversion Ha; reflexivity.
    + intros [] He; reflexivity.
  - vm_compute; tauto.
Qed.

End TaggedCounter.

Module SlowFast.

Definition fast : semantics DenseCounter.state unit :=
  Semantics (fun s => s = DenseCounter.C0)
    (fun s l t => s = DenseCounter.C0 /\ l = [tt] /\ t = DenseCounter.C2).
Definition fast_link : Link.t DenseCounter.state unit bool unit :=
  Link.Make DenseCounter.point (fun s _ _ _ => s = DenseCounter.C0)
    (fun _ _ _ => False).
Definition slow_end : endings DenseCounter.state :=
  Endings (fun s => s = DenseCounter.C2) (fun _ => False) (fun _ => False).
Definition fast_end : endings DenseCounter.state :=
  Endings (fun s => DenseCounter.point s = true) (fun _ => False) (fun _ => False).
Definition R : agreement bool DenseCounter.state :=
  Agreement bool DenseCounter.state (fun _ s t => DenseCounter.point s = DenseCounter.point t).
Definition rank (s : DenseCounter.state) (_ : DenseCounter.state) :=
  match s with DenseCounter.C1 => 1 | _ => 0 end.

Lemma fast_link_ok : link_laws fast (Cfg.graph DenseCounter.cfg) fast_link.
Proof.
  constructor.
  - exact (cfg_wf DenseCounter.link_ok).
  - intros s ->; vm_compute; tauto.
  - intros s l t Hr [-> [-> ->]]; right; exists tt; reflexivity.
  - intros [] s l t Hr [-> [-> ->]] Htaken; vm_compute; tauto.
  - intros s l t Hr Hstep Hstay; contradiction Hstay.
Qed.

Lemma agree_ok : agreement_laws bool_lattice R.
Proof.
  constructor.
  - intros a s; reflexivity.
  - intros a b s t Hab Hrel; exact Hrel.
Qed.

Lemma slow_forth :
  DenseAgreement.forth_agrees DenseCounter.m fast TaggedCounter.D
    DenseCounter.lk fast_link R (reachable_state DenseCounter.m) (reachable_state fast)
    TaggedCounter.sigma rank.
Proof.
  split.
  - intros [] t s l s' Hr Hstep Hs Ht Hpoint Htaken Hagree.
    change (s = DenseCounter.C0) in Htaken; subst s.
    change (l = [tt] /\ s' = DenseCounter.C1) in Hstep; destruct Hstep as [-> ->].
    destruct t; try discriminate Hpoint.
    exists DenseCounter.C0, DenseCounter.C2; split; [constructor|].
    split; [repeat split; reflexivity|split; reflexivity].
  - intros t s l s' Hr Hstep Hs Ht Hpoint Hstay Hagree.
    change (s = DenseCounter.C1) in Hstay; subst s.
    change (l = [] /\ s' = DenseCounter.C2) in Hstep; destruct Hstep as [-> ->].
    left; split; [reflexivity|]; split; [exact Hagree|vm_compute; auto].
Qed.

Lemma fast_forth :
  DenseAgreement.forth_agrees fast DenseCounter.m TaggedCounter.D
    fast_link DenseCounter.lk (DenseAgreement.agreement_swap R)
    (reachable_state fast) (reachable_state DenseCounter.m)
    TaggedCounter.sigma (fun _ _ => 0).
Proof.
  split.
  - intros [] t s l s' Hr [-> [-> ->]] Hs Ht Hpoint Htaken Hagree.
    destruct t; try discriminate Hpoint.
    exists DenseCounter.C0, DenseCounter.C1; split; [constructor|].
    split; [split; reflexivity|split; reflexivity].
  - intros t s l s' Hr Hstep Hs Ht Hpoint Hstay; contradiction Hstay.
Qed.

Lemma slow_not_stuck s : ~ stuck DenseCounter.m slow_end s.
Proof.
  intros [Hrun [Hfinal Hrest]]; destruct s.
  - apply Hrun; exists [tt], DenseCounter.C1; split; reflexivity.
  - apply Hrun; exists [], DenseCounter.C2; split; reflexivity.
  - apply Hfinal; reflexivity.
Qed.

Lemma fast_not_stuck s : ~ stuck fast fast_end s.
Proof.
  intros [Hrun [Hfinal Hrest]]; destruct s.
  - apply Hrun; exists [tt], DenseCounter.C2; repeat split; reflexivity.
  - apply Hfinal; reflexivity.
  - apply Hfinal; reflexivity.
Qed.

Lemma slow_ends :
  DenseAgreement.ends_forth DenseCounter.m fast slow_end fast_end TaggedCounter.D
    DenseCounter.lk fast_link R (reachable_state DenseCounter.m) (reachable_state fast).
Proof.
  intros s t k Hs Ht Hpoint Hagree Hend; destruct k.
  - change (s = DenseCounter.C2) in Hend; subst s.
    exists t; split; [constructor|exact Hpoint].
  - contradiction Hend.
  - contradiction Hend.
  - exfalso; exact (slow_not_stuck s Hend).
Qed.

Lemma fast_ends :
  DenseAgreement.ends_forth fast DenseCounter.m fast_end slow_end TaggedCounter.D
    fast_link DenseCounter.lk (DenseAgreement.agreement_swap R)
    (reachable_state fast) (reachable_state DenseCounter.m).
Proof.
  intros s t k Hs Ht Hpoint Hagree Hend; destruct k.
  - exists DenseCounter.C2; split; [|reflexivity].
    change (DenseCounter.point s = true) in Hend.
    change (DenseCounter.point t = DenseCounter.point s) in Hpoint.
    destruct t; try constructor.
    + cbn in Hpoint; congruence.
    + apply exec_one; split; reflexivity.
  - contradiction Hend.
  - contradiction Hend.
  - exfalso; exact (fast_not_stuck s Hend).
Qed.

Example two_program_stuttering_positive :
  same_behaviour DenseCounter.m slow_end DenseCounter.C0 fast fast_end DenseCounter.C0.
Proof.
  eapply (DenseAgreement.agreement_simulation2 DenseCounter.m fast slow_end fast_end
    TaggedCounter.D DenseCounter.lk fast_link (fun _ => R)
    (reachable_state DenseCounter.m) (reachable_state fast) TaggedCounter.sigma
    rank (fun _ _ => 0)).
  - reflexivity.
  - exact bool_laws.
  - exact DenseCounter.link_ok.
  - exact fast_link_ok.
  - exact agree_ok.
  - apply DenseAgreement.reachable_invariant.
  - apply DenseAgreement.reachable_invariant.
  - split; [exact slow_forth|exact fast_forth].
  - split; [exact slow_ends|exact fast_ends].
  - exact TaggedCounter.post.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example unmatched_stay_boundary :
  rank DenseCounter.C2 DenseCounter.C2 < rank DenseCounter.C1 DenseCounter.C2.
Proof.
  vm_compute; auto.
Qed.

End SlowFast.

Module MissingExit.

Definition m : semantics bool unit := Semantics (fun _ => True) (fun _ _ _ => False).
Definition en : endings bool :=
  Endings (fun s => s = true) (fun _ => False) (fun _ => False).
Definition cfg : Cfg.t unit unit :=
  Cfg.Make (Graph.of_pure [tt] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt))
    unit_encoding unit_encoding.
Definition lk : Link.t bool unit unit unit :=
  Link.Make (fun _ => tt) (fun _ _ _ _ => False) (fun _ _ _ => False).
Definition D := Dense.of_pure cfg Backward bool_lattice (fun _ => None) (fun _ a => a).
Definition R : agreement bool bool := Agreement bool bool (fun _ _ _ => True).
Definition sigma (_ : unit) := false.

Lemma link_ok : link_laws m (Cfg.graph cfg) lk.
Proof.
  constructor.
  - constructor.
    + constructor; [vm_compute; tauto|constructor].
    + intros [] Hn; vm_compute; tauto.
    + intros [] [] He; contradiction.
    + intros [] [] Hn He; contradiction.
  - intros s Hi; vm_compute; tauto.
  - intros s l t Hr Hstep; contradiction.
  - intros e s l t Hr Hstep; contradiction.
  - intros s l t Hr Hstep; contradiction.
Qed.

Example all_nonexit_premises :
  link_laws m (Cfg.graph cfg) lk /\
  agreement_laws bool_lattice R /\
  DenseAgreement.agreement_symmetric R /\
  DenseAgreement.step_agrees m D lk R (reachable_state m) sigma /\
  post_solution (Dense.lat D) (Dense.system D) sigma.
Proof.
  split; [exact link_ok|]; split.
  - constructor; intros; exact I.
  - split; [intros a s t H; exact I|]; split.
    + split; intros; intros s l s' Hr Hstep; contradiction.
    + apply (proj2 (Dense.post_solution_iff D sigma bool_laws)); split.
      * intros n a Hn Ha; discriminate Ha.
      * intros e He; change (In e []) in He; contradiction.
Qed.

Example missing_exit_negative :
  ~ DenseAgreement.ends_agree en D lk R (reachable_state m) /\
  ~ same_behaviour m en true m en false.
Proof.
  assert (Hr : forall b, reachable_state m b).
  { intro b; exists b, []; split; [exact I|constructor]. }
  split.
  - intro Hends.
    destruct (Hends true false (Hr true) (Hr false) eq_refl I) as [Hfinal _].
    pose proof (proj1 Hfinal eq_refl) as Hbad; discriminate Hbad.
  - intro Hsame.
    destruct (proj1 (same_finish _ _ _ _ _ _ Hsame EndFinal [])
      (ex_intro _ true (conj (exec_refl true) eq_refl))) as [t [Hrun Hfinal]].
    inversion Hrun as [|s l s' tr u Hstep Htail]; subst.
    + discriminate Hfinal.
    + contradiction.
Qed.

Example initial_agreement_boundary :
  initial m true /\ initial m false /\ agree R (sigma tt) true false.
Proof.
  vm_compute; tauto.
Qed.

End MissingExit.
