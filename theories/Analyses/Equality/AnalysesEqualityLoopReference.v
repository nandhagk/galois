(** * Costed finite-round loop reference

    The reference preserves total definition queries, including values outside the inventory.
    For example, one round recognizes an unlisted pure nullary definition inside the loop.
    Builds on: AnalysesEqualityProblem and CostLoop. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramSsa
  ProgramStrict.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem.
Import List.ListNotations Cost.Notations Numbering.

Local Open Scope nat_scope.

Module NumberingLoopReference.

Section Reference.
Context {N E V K G : Type} (np : problem N E V K G) (lp : loop_info N).
Let syntax := ssa np.

(** Each body query charges both dictionary invocations and their supplied costs. *)
Definition inside_c x : Cost.t bool :=
  Cost.step ;;
  let* home := Ssa.home_c syntax x in
  Cost.step ;;
  body_c lp home.

(** The costed body observation is the supplied loop predicate at the supplied definition home. *)
Theorem inside_value x : Cost.value (inside_c x) = body lp (Ssa.home syntax x).
Proof.
  reflexivity.
Qed.

Definition initial x := negb (body lp (Ssa.home syntax x)).

Definition initial_c x := Cost.map negb (inside_c x).

(** The round is the original total-query operation, parameter and impurity rule. *)
Definition round (previous : V -> bool) x :=
  if body lp (Ssa.home syntax x) then
    match Ssa.def syntax x with
    | Op op args => pure np op && forallb previous args
    | _ => false
    end
  else true.

Definition round_c (previous : V -> Cost.t bool) x : Cost.t bool :=
  let* inside := inside_c x in
  if inside then
    Cost.step ;;
    let* def := Ssa.def_c syntax x in
    match def with
    | Op op args =>
      Cost.step ;;
      let* pure := pure_c np op in
      if pure then forallb_c (fun y => Cost.step ;; previous y) args else Cost.ret false
    | _ => Cost.ret false
    end
  else Cost.ret true.

(** One costed reference round returns the exact legacy boolean round result. *)
Theorem round_value previous x :
  Cost.value (round_c previous x) = round (fun y => Cost.value (previous y)) x.
Proof.
  unfold round_c, round; rewrite Cost.value_bind, inside_value.
  destruct (body lp (Ssa.home syntax x)); [|reflexivity].
  autorewrite with galois_cost; fold (Ssa.def syntax x).
  destruct (Ssa.def syntax x) as [op args|b i|]; [|reflexivity|reflexivity].
  autorewrite with galois_cost; unfold pure.
  destruct (Cost.value (pure_c np op)); [|reflexivity].
  rewrite value_forallb_c; reflexivity.
Qed.

Local Lemma forallb_ext (f g : V -> bool) xs :
  (forall x, f x = g x) -> forallb f xs = forallb g xs.
Proof.
  intro Hsame; induction xs as [|x rest IH]; [reflexivity|].
  cbn [forallb]; now rewrite Hsame, IH.
Qed.

(** Pointwise equality of previous observations is preserved by a reference round. *)
Theorem round_ext f g x :
  (forall y, f y = g y) -> round f x = round g x.
Proof.
  intro Hsame; unfold round.
  destruct (body lp (Ssa.home syntax x)); [|reflexivity].
  destruct (Ssa.def syntax x); try reflexivity.
  rewrite (forallb_ext _ _ _ Hsame); reflexivity.
Qed.

(** This structural definition is the pure round-reference specification, not a fuel driver. *)
Fixpoint after (count : nat) (previous : V -> bool) x : bool :=
  match count with
  | 0 => previous x
  | S n => after n (round previous) x
  end.

(** The finite reference preserves pointwise equality without functional extensionality. *)
Theorem after_ext count f g x :
  (forall y, f y = g y) -> after count f x = after count g x.
Proof.
  revert f g; induction count as [|count IH]; intros f g Hsame; [apply Hsame|].
  cbn [after]; apply IH; intro y; now apply round_ext.
Qed.

(** The total reference performs exactly one round per supplied inventory occurrence. *)
Definition invariant_in_ref x := after (length (Ssa.values syntax)) initial x.

Definition function := V -> Cost.t bool.

(** A reference driver callback builds one charged round closure and always continues. *)
Definition advance_c (previous : function) : Cost.t (function + function) :=
  Cost.ret (inl (round_c previous)).

Definition selected (result : function + function) :=
  match result with
  | inl f => f
  | inr f => f
  end.

(** The existing Cost driver agrees with the round reference at every arbitrary query. *)
Theorem runs_value count previous result :
  runs advance_c count previous result ->
  forall x, Cost.value (selected result x) =
    after count (fun y => Cost.value (previous y)) x.
Proof.
  intro Hrun; induction Hrun as [previous|count previous final Hstop|
    count previous next result Hnext Hrun IH]; intro x.
  - reflexivity.
  - discriminate.
  - change (@inl function function (round_c previous) = inl next) in Hnext.
    injection Hnext as <-.
    cbn [after]; rewrite IH.
    apply after_ext; intro y; apply round_value.
Qed.

(** Count zero observes the initial predicate directly, so the empty boundary is unchanged. *)
Definition count_c count x : Cost.t bool :=
  match count with
  | 0 => initial_c x
  | S n =>
    let* result := iterate advance_c (Pos.of_succ_nat n) initial_c in
    Cost.step ;;
    selected result x
  end.

(** The costed reference count retains the full arbitrary-query behaviour of the specification. *)
Theorem count_value count x : Cost.value (count_c count x) = after count initial x.
Proof.
  destruct count as [|n]; [reflexivity|].
  unfold count_c; rewrite Cost.value_bind.
  autorewrite with galois_cost.
  pose proof (runs_value _ _ _ (iterate_value advance_c (Pos.of_succ_nat n) initial_c) x)
    as Hrun.
  rewrite SuccNat2Pos.id_succ in Hrun.
  etransitivity; [exact Hrun|].
  apply after_ext; intro y; reflexivity.
Qed.

(** Fallback preparation charges inventory counting and all actually demanded reference callbacks. *)
Definition reference_c x : Cost.t bool :=
  let* count := length_c (Ssa.values syntax) in count_c count x.

(** The costed fallback agrees unconditionally with the original total-query finite reference. *)
Theorem reference_agrees x : Cost.value (reference_c x) = invariant_in_ref x.
Proof.
  unfold reference_c, invariant_in_ref; rewrite Cost.value_bind, value_length_c.
  apply count_value.
Qed.

(** A recognized inside-body value is always an actually pure operation definition. *)
Definition shape x : Prop :=
  body lp (Ssa.home syntax x) = false \/
  exists op args, Ssa.def syntax x = Op op args /\ pure np op = true.

Local Lemma round_shape previous x : round previous x = true -> shape x.
Proof.
  unfold round, shape; destruct (body lp (Ssa.home syntax x)) eqn:Hinside.
  - destruct (Ssa.def syntax x) as [op args|b i|] eqn:Hdef; try discriminate.
    intro Htrue; apply andb_true_iff in Htrue as [Hp _].
    right; exists op, args; split; [reflexivity|exact Hp].
  - intros _; now left.
Qed.

Local Lemma after_shape count previous :
  (forall x, previous x = true -> shape x) ->
  forall x, after count previous x = true -> shape x.
Proof.
  revert previous; induction count as [|count IH]; intros previous Hprevious x Hx.
  - now apply Hprevious.
  - cbn [after] in Hx; apply (IH (round previous)); [apply round_shape|exact Hx].
Qed.

(** The total reference retains the legacy outside-or-pure shape guarantee on arbitrary inputs. *)
Theorem invariant_in_ref_shape x : invariant_in_ref x = true -> shape x.
Proof.
  unfold invariant_in_ref; apply after_shape.
  intros y Hy; unfold initial in Hy; left; now apply negb_true_iff.
Qed.

End Reference.

Section Semantics.
Context {S O N E V K G C : Type} (m : semantics S O)
  (np : problem N E V K G) (sl : SsaLink.t S O N E V C)
  (eval : K -> list C -> option C) (holds : G -> list C -> Prop)
  (lp : loop_info N) (x : V).
Let syntax := ssa np.
Let inside := fun s => body lp (Link.point (SsaLink.link sl) s) = true.
Hypothesis Hssa : ssa_laws m syntax sl eval holds.
Hypothesis Hstrict : strict_ssa_laws m syntax sl.
Hypothesis Hloop : loop_laws m np sl eval.

Local Lemma exec_in_start s events t : exec_in m inside s events t -> inside s.
Proof.
  intro Hrun; destruct Hrun; assumption.
Qed.

Local Lemma values_determined s args cs ds :
  Forall2 (fun y c => SsaLink.val sl s y = Some c) args cs ->
  Forall2 (fun y d => SsaLink.val sl s y = Some d) args ds -> cs = ds.
Proof.
  intro Hcs; revert ds; induction Hcs as [|y c args cs Hc Hcs IH]; intros ds Hds.
  - inversion Hds; reflexivity.
  - inversion Hds as [|y' d args' ds' Hd Hds']; subst.
    f_equal; [congruence|apply IH; exact Hds'].
Qed.

Local Lemma outside_frame s events t :
  body lp (Ssa.home syntax x) = false ->
  reachable_state m s -> exec_in m inside s events t ->
  SsaLink.val sl t x = SsaLink.val sl s x.
Proof.
  intros Houtside Hreachable Hrun; revert Hreachable.
  induction Hrun as [s Hinside|s events u rest t Hinside Hstep Hrun IH]; intro Hreachable.
  - reflexivity.
  - rewrite (IH (reachable_state_step m _ _ _ Hreachable Hstep)).
    destruct (edge_covers (link_ok Hssa) _ _ _ Hreachable Hstep) as [Hstay|[e Htaken]].
    + apply (frame_in_stay Hstrict x s events u Hreachable Hstep Hstay).
      intro Heq; unfold inside in Hinside; rewrite Heq, Houtside in Hinside; discriminate.
    + apply (frame_on_edge Hstrict e x s events u Hreachable Hstep Htaken).
      pose proof (exec_in_start _ _ _ Hrun) as Hu.
      intro Heq; unfold inside in Hu; rewrite <- Heq, Houtside in Hu; discriminate.
Qed.

Local Lemma operation_step s events t op args :
  Ssa.def syntax x = Op op args -> pure np op = true ->
  reachable_state m s -> step m s events t ->
  SsaLink.val sl t x = SsaLink.val sl s x \/
  exists cs c, Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs /\
    eval op cs = Some c /\ SsaLink.val sl t x = Some c.
Proof.
  intros Hdef Hp Hreachable Hstep; destruct (SsaLink.val sl t x) as [c|] eqn:Hpost.
  - destruct (value_origin Hssa x c s events t Hreachable Hstep Hpost)
      as [Hsame|[Hoperation|[Hparameter|Harbitrary]]].
    + left; symmetry; exact Hsame.
    + destruct Hoperation as [other [operands [cs [Hother [Hcs Heval]]]]].
      rewrite Hdef in Hother; injection Hother as <- <-.
      right; exists cs, c; split; [exact Hcs|split; [exact Heval|reflexivity]].
    + destruct Hparameter as [e [b [i [z [Hparameter _]]]]].
      rewrite Hdef in Hparameter; discriminate.
    + rewrite Hdef in Harbitrary; discriminate.
  - destruct (SsaLink.val sl s x) as [c|] eqn:Hpre; [|left; reflexivity].
    assert (Hchanged : SsaLink.val sl t x <> SsaLink.val sl s x).
    { rewrite Hpost, Hpre; discriminate. }
    destruct (loop_op_binding Hloop s events t x op args Hreachable Hstep Hdef Hp Hchanged)
      as [cs [d [_ [_ Hsome]]]].
    rewrite Hpost in Hsome; discriminate.
Qed.

Local Lemma arguments_transport op args s events t cs :
  body lp (Ssa.home syntax x) = true -> Ssa.def syntax x = Op op args -> pure np op = true ->
  loop_operands_stable m np sl lp x ->
  reachable_state m s -> exec_in m inside s events t ->
  Forall2 (fun y d => SsaLink.val sl t y = Some d) args cs ->
  Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs.
Proof.
  intros Hinside Hdef Hp Hstable Hreachable Hrun Hargs.
  assert (Hsame : forall y, In y args -> SsaLink.val sl s y = SsaLink.val sl t y).
  { intros y Hy; exact (Hstable op args y s events t Hinside Hdef Hp Hy Hreachable Hrun). }
  clear Hdef.
  revert Hsame; induction Hargs as [|y d args cs Hd Hargs IH]; intro Hsame.
  - constructor.
  - constructor.
    + rewrite (Hsame y (or_introl eq_refl)); exact Hd.
    + apply IH; intros z Hz; apply Hsame; now right.
Qed.

Local Lemma operation_run op args s events t :
  body lp (Ssa.home syntax x) = true -> Ssa.def syntax x = Op op args -> pure np op = true ->
  loop_operands_stable m np sl lp x ->
  reachable_state m s -> exec_in m inside s events t ->
  SsaLink.val sl t x = SsaLink.val sl s x \/
  exists cs c, Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs /\
    eval op cs = Some c /\ SsaLink.val sl t x = Some c.
Proof.
  intros Hinside Hdef Hp Hstable Hreachable Hrun; revert Hreachable.
  induction Hrun as [s Hs|s first u rest t Hs Hstep Hrun IH]; intro Hreachable.
  - left; reflexivity.
  - destruct (IH (reachable_state_step m _ _ _ Hreachable Hstep))
      as [Hsame|[cs [c [Hargs [Heval Hval]]]]].
    + destruct (operation_step s first u op args Hdef Hp Hreachable Hstep)
        as [Hpreserved|[cs [c [Hargs [Heval Hval]]]]].
      * left; congruence.
      * right; exists cs, c; split; [exact Hargs|split; [exact Heval|congruence]].
    + right; exists cs, c; split; [|split; assumption].
      apply (arguments_transport op args s (first ++ []) u cs
        Hinside Hdef Hp Hstable Hreachable).
      * pose proof (exec_in_start _ _ _ Hrun) as Hu.
        exact (exec_in_step s first u [] u Hs Hstep (exec_in_refl u Hu)).
      * exact Hargs.
Qed.

(** Once a recognized invariant changes in a restricted loop run, it cannot change again.
    This retains the legacy three-run, stable-direct-operands and option-valued payload domain. *)
Theorem invariant_in_ref_sound :
  loop_info_wf (Cfg.graph (Ssa.cfg syntax)) lp -> invariant_in_ref np lp x = true ->
  loop_operands_stable m np sl lp x ->
  forall s events1 u1 events2 u2 events3 u3, reachable_state m s ->
    exec_in m inside s events1 u1 ->
    exec_in m inside u1 events2 u2 ->
    exec_in m inside u2 events3 u3 ->
    SsaLink.val sl u1 x <> SsaLink.val sl u2 x ->
    SsaLink.val sl u2 x = SsaLink.val sl u3 x.
Proof.
  intros Hwf Hinvariant Hstable s events1 u1 events2 u2 events3 u3 Hreachable
    Hrun1 Hrun2 Hrun3 Hchanged.
  assert (Hr1 : reachable_state m u1).
  { eapply reachable_state_exec; [exact Hreachable|eapply exec_in_exec; exact Hrun1]. }
  assert (Hr2 : reachable_state m u2).
  { eapply reachable_state_exec; [exact Hr1|eapply exec_in_exec; exact Hrun2]. }
  destruct (invariant_in_ref_shape np lp x Hinvariant) as [Houtside|[op [args [Hdef Hp]]]].
  - exfalso; apply Hchanged; symmetry; eapply outside_frame; eassumption.
  - destruct (body lp (Ssa.home syntax x)) eqn:Hinside.
    2: { exfalso; apply Hchanged; symmetry; eapply outside_frame; eassumption. }
    destruct (operation_run op args _ _ _ Hinside Hdef Hp Hstable Hr1 Hrun2)
      as [Hsame|[cs [c [Hcs [Hec Hc]]]]].
    + exfalso; apply Hchanged; symmetry; exact Hsame.
    + destruct (operation_run op args _ _ _ Hinside Hdef Hp Hstable Hr2 Hrun3)
        as [Hsame|[ds [d [Hds [Hed Hd]]]]].
      * symmetry; exact Hsame.
      * pose proof (arguments_transport op args _ _ _ ds
          Hinside Hdef Hp Hstable Hr1 Hrun2 Hds) as Hds'.
        pose proof (values_determined u1 args cs ds Hcs Hds') as Heq.
        subst ds; congruence.
Qed.

End Semantics.

End NumberingLoopReference.
