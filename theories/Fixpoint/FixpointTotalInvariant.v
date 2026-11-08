(** * Joining state invariants

    The pending list covers every constraint that can have become invalid after an update.
    For example, changing a declared read requeues that reader before its old check is reused.
    Builds on: FixpointTotalKernel, FixpointLeast and public query determinacy. *)

From Stdlib Require Import List Bool Arith NArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointIndex FixpointAnalysis FixpointTotalQueue FixpointTotalKernel.
Import List.ListNotations.

Module TotalInvariant.

Section Invariant.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a) (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).

Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let SS := Analysis.static a.

(** All stored observations satisfy the invariant used by the height witness. *)
Definition good (m : assignment X A) : Prop :=
  Map.wf EX m /\ forall x, Terminates.inv HT (lookup EX L m x).

(** A constraint is valid when every evaluated contribution lies below its destination. *)
Definition valid c (m : assignment X A) : Prop :=
  forall x b, In (x, b) (fst (Eval.outputs S c (lookup EX L m))) ->
    leb L b (lookup EX L m x) = true.

(** State validity keeps finite-map laws, listed queue support and every unqueued row valid. *)
Definition invariant (s : TotalKernel.state X C A) : Prop :=
  good (TotalKernel.current s) /\
  TotalQueue.wf EC (TotalKernel.queue s) /\
  incl (TotalQueue.pending (TotalKernel.queue s)) (System.constraints S) /\
  forall c, In c (System.constraints S) ->
    ~ In c (TotalQueue.pending (TotalKernel.queue s)) -> valid c (TotalKernel.current s).

(** A shared join update keeps invariant values and is pointwise ascending. *)
Theorem rule_good m x b :
  good m -> Terminates.inv HT b ->
  good (fst (Update.rule EX L (join_c L) m x b)) /\
  fun_leb L (lookup EX L m) (lookup EX L (fst (Update.rule EX L (join_c L) m x b))).
Proof.
  intros [Hwf Hinv] Hb; split.
  - split; [apply Update.rule_wf, Hwf|].
    intro y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
    destruct (leb L b (lookup EX L m x)); [apply Hinv|].
    destruct (eqb EX y x); [|apply Hinv].
    rewrite <- join_equation; apply Terminates.inv_join; [apply Hinv|exact Hb].
  - intro y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
    destruct (leb L b (lookup EX L m x)); [apply (leb_refl (Analysis.lattice_law HL))|].
    destruct (eqb EX y x) eqn:Hsame; [|apply (leb_refl (Analysis.lattice_law HL))].
    apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hsame; subst y.
    rewrite <- join_equation; apply (join_upper_l (Analysis.lattice_law HL)).
Qed.

(** A shared join update bounds its incoming contribution at the updated key. *)
Theorem rule_bounds m x b :
  Map.wf EX m ->
  leb L b (lookup EX L (fst (Update.rule EX L (join_c L) m x b)) x) = true.
Proof.
  intro Hwf; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
  destruct (leb L b (lookup EX L m x)) eqn:Hbelow; [exact Hbelow|].
  rewrite eqb_refl, <- join_equation; apply (join_upper_r (Analysis.lattice_law HL)).
Qed.

(** Index coverage makes every requeued row a listed constraint. *)
Theorem update_good s x b :
  good (TotalKernel.current s) -> TotalQueue.wf EC (TotalKernel.queue s) ->
  incl (TotalQueue.pending (TotalKernel.queue s)) (System.constraints S) ->
  Terminates.inv HT b ->
  good (TotalKernel.current (TotalKernel.update a ix s (x, b))) /\
  TotalQueue.wf EC (TotalKernel.queue (TotalKernel.update a ix s (x, b))) /\
  incl (TotalQueue.pending (TotalKernel.queue (TotalKernel.update a ix s (x, b))))
    (System.constraints S) /\
  fun_leb L (lookup EX L (TotalKernel.current s))
    (lookup EX L (TotalKernel.current (TotalKernel.update a ix s (x, b)))).
Proof.
  intros Hg Hq Hlisted Hb; rewrite TotalKernel.update_equation; cbn [fst snd].
  fold EX EC L.
  destruct (rule_good _ x b Hg Hb) as [Hg' Hle].
  split; [exact Hg'|]; cbn [TotalKernel.queue TotalKernel.current].
  destruct (snd (Update.rule EX L (join_c L) (TotalKernel.current s) x b)).
  - split; [apply TotalQueue.push_many_wf; [apply Analysis.row_laws, HL|exact Hq]|].
    split; [|exact Hle]; intros c Hc.
    apply (TotalQueue.push_many_member EC (Analysis.row_laws HL) _ _ c Hq) in Hc.
    destruct Hc as [Hc|Hc].
    + exact (proj1 (proj1 (readers_agree HI x c) Hc)).
    + apply Hlisted, Hc.
  - split; [exact Hq|]; split; assumption.
Qed.

(** Every pending row survives output application until the next explicit pop. *)
Theorem update_retains s x b c :
  TotalQueue.wf EC (TotalKernel.queue s) ->
  In c (TotalQueue.pending (TotalKernel.queue s)) ->
  In c (TotalQueue.pending (TotalKernel.queue (TotalKernel.update a ix s (x, b)))).
Proof.
  intros Hq Hc; rewrite TotalKernel.update_equation; cbn [fst snd TotalKernel.queue].
  fold EX EC L.
  destruct (snd (Update.rule _ _ _ _ _ _)); [|exact Hc].
  apply (TotalQueue.push_many_member EC (Analysis.row_laws HL) _ _ c Hq); now right.
Qed.

(** If a reader is absent after an update, its declared reads have not changed. *)
Theorem update_unqueued_reads s x b c :
  Map.wf EX (TotalKernel.current s) -> TotalQueue.wf EC (TotalKernel.queue s) ->
  In c (System.constraints S) ->
  ~ In c (TotalQueue.pending (TotalKernel.queue (TotalKernel.update a ix s (x, b)))) ->
  forall y, In y (deps SS c) ->
    lookup EX L (TotalKernel.current (TotalKernel.update a ix s (x, b))) y =
      lookup EX L (TotalKernel.current s) y.
Proof.
  intros Hwf Hq Hc Hnot y Hy.
  rewrite TotalKernel.update_equation in Hnot |- *; cbn [fst snd TotalKernel.queue
    TotalKernel.current] in Hnot |- *.
  fold EX EC L in Hnot |- *.
  set (r := Update.rule EX L (join_c L) (TotalKernel.current s) x b) in *.
  destruct (snd r) eqn:Hchange.
  - assert (Hne : y <> x).
    { intro Heq; subst y; apply Hnot.
      apply (TotalQueue.push_many_member EC (Analysis.row_laws HL) _ _ c Hq); left.
      apply (readers_agree HI); now split. }
    rewrite (proj2 (Update.rule_spec EX L (join_c L) _ x b Hwf)).
    destruct (leb L b (lookup EX L (TotalKernel.current s) x)); [reflexivity|].
    rewrite (proj2 (eqb_false_iff EX (Analysis.key_laws HL) y x) Hne); reflexivity.
  - exact (f_equal (fun m => lookup EX L m y)
      (Update.rule_unchanged EX L (join_c L) (TotalKernel.current s) x b Hchange)).
Qed.

(** Output application has the same current map as the shared ordered update fold. *)
Theorem updates_current outs s :
  TotalKernel.current (TotalKernel.updates a ix outs s) =
    fst (Update.apply EX L (join_c L) outs (TotalKernel.current s)).
Proof.
  revert s; induction outs as [|[x b] outs IH]; intro s.
  - rewrite TotalKernel.updates_equation, Update.apply_equation; reflexivity.
  - rewrite TotalKernel.updates_equation, IH.
    rewrite (Update.apply_equation EX L (join_c L) ((x, b) :: outs)
      (TotalKernel.current s)).
    rewrite TotalKernel.update_equation; reflexivity.
Qed.

(** Output application keeps good values, queue support and the order relation. *)
Theorem updates_good outs s :
  good (TotalKernel.current s) -> TotalQueue.wf EC (TotalKernel.queue s) ->
  incl (TotalQueue.pending (TotalKernel.queue s)) (System.constraints S) ->
  (forall x b, In (x, b) outs -> Terminates.inv HT b) ->
  good (TotalKernel.current (TotalKernel.updates a ix outs s)) /\
  TotalQueue.wf EC (TotalKernel.queue (TotalKernel.updates a ix outs s)) /\
  incl (TotalQueue.pending (TotalKernel.queue (TotalKernel.updates a ix outs s)))
    (System.constraints S) /\
  fun_leb L (lookup EX L (TotalKernel.current s))
    (lookup EX L (TotalKernel.current (TotalKernel.updates a ix outs s))).
Proof.
  revert s; induction outs as [|[x b] outs IH]; intros s Hg Hq Hlisted Houts;
    rewrite TotalKernel.updates_equation.
  - split; [exact Hg|]; split; [exact Hq|]; split; [exact Hlisted|].
    intro y; apply (leb_refl (Analysis.lattice_law HL)).
  - destruct (update_good s x b Hg Hq Hlisted (Houts x b (or_introl eq_refl)))
      as [Hg' [Hq' [Hlisted' Hle]]].
    destruct (IH _ Hg' Hq' Hlisted' (fun y d Hd => Houts y d (or_intror Hd)))
      as [Hg'' [Hq'' [Hlisted'' Hle']]].
    split; [exact Hg''|]; split; [exact Hq''|]; split; [exact Hlisted''|].
    intro y; eapply (leb_trans (Analysis.lattice_law HL)); [apply Hle|apply Hle'].
Qed.

(** Missing readers have unchanged declared inputs throughout output application. *)
Theorem updates_unqueued outs s c :
  good (TotalKernel.current s) -> TotalQueue.wf EC (TotalKernel.queue s) ->
  incl (TotalQueue.pending (TotalKernel.queue s)) (System.constraints S) ->
  (forall x b, In (x, b) outs -> Terminates.inv HT b) ->
  In c (System.constraints S) ->
  ~ In c (TotalQueue.pending (TotalKernel.queue (TotalKernel.updates a ix outs s))) ->
  ~ In c (TotalQueue.pending (TotalKernel.queue s)) /\
  forall y, In y (deps SS c) ->
    lookup EX L (TotalKernel.current (TotalKernel.updates a ix outs s)) y =
      lookup EX L (TotalKernel.current s) y.
Proof.
  revert s; induction outs as [|[x b] outs IH]; intros s Hg Hq Hlisted Houts Hc Hnot.
  - rewrite TotalKernel.updates_equation in Hnot |- *; split; [exact Hnot|reflexivity].
  - rewrite TotalKernel.updates_equation in Hnot |- *.
    destruct (update_good s x b Hg Hq Hlisted (Houts x b (or_introl eq_refl)))
      as [Hg' [Hq' [Hlisted' Hle]]].
    destruct (IH _ Hg' Hq' Hlisted' (fun y d Hd => Houts y d (or_intror Hd)) Hc Hnot)
      as [Hnot' Hagree].
    split.
    + intro Hin; apply Hnot', update_retains; assumption.
    + intros y Hy; rewrite (Hagree y Hy).
      apply (update_unqueued_reads s x b c);
        [exact (proj1 Hg)|exact Hq|exact Hc|exact Hnot'|exact Hy].
Qed.

(** Every frozen contribution is bounded after its complete output fold. *)
Theorem updates_bounds outs s :
  good (TotalKernel.current s) -> TotalQueue.wf EC (TotalKernel.queue s) ->
  incl (TotalQueue.pending (TotalKernel.queue s)) (System.constraints S) ->
  (forall x b, In (x, b) outs -> Terminates.inv HT b) ->
  forall x b, In (x, b) outs ->
    leb L b (lookup EX L (TotalKernel.current (TotalKernel.updates a ix outs s)) x) = true.
Proof.
  revert s; induction outs as [|[x b] outs IH]; intros s Hg Hq Hlisted Houts y d Hin.
  - contradiction.
  - rewrite TotalKernel.updates_equation.
    destruct (update_good s x b Hg Hq Hlisted (Houts x b (or_introl eq_refl)))
      as [Hg' [Hq' [Hlisted' Hle]]].
    assert (Htail : forall y d, In (y, d) outs -> Terminates.inv HT d).
    { intros z e He; apply (Houts z e); now right. }
    destruct Hin as [Heq|Hin].
    + injection Heq as <- <-.
      destruct (updates_good outs _ Hg' Hq' Hlisted' Htail) as [_ [_ [_ Hle']]].
      eapply (leb_trans (Analysis.lattice_law HL)); [|apply Hle'].
      rewrite TotalKernel.update_equation; cbn [TotalKernel.current fst snd].
      apply rule_bounds, (proj1 Hg).
    + apply IH; assumption.
Qed.

Local Lemma determined c m n :
  (forall y, In y (deps SS c) -> lookup EX L m y = lookup EX L n y) ->
  Eval.outputs S c (lookup EX L m) = Eval.outputs S c (lookup EX L n).
Proof.
  intro Hagree.
  destruct (Query.query_determined (System.rhs S c) (lookup EX L m) (lookup EX L n))
    as [Hv [Hr Hs]].
  - intros y Hy; apply Hagree,
      (System.reads_within (Analysis.static_law HL) c (lookup EX L m)), Hy.
  - rewrite !Eval.outputs_spec, Hv, Hr, Hs; reflexivity.
Qed.

(** Every completed transition keeps the queue-coverage invariant. *)
Theorem step_preserved s t :
  invariant s -> TotalKernel.step a ix s = inl t -> invariant t.
Proof.
  intros [Hg [Hq [Hlisted Hvalid]]] Hstep; rewrite TotalKernel.step_equation in Hstep.
  fold EX EC L S SS in Hstep.
  destruct (TotalQueue.pop EC (TotalKernel.queue s)) as [[c rest]|] eqn:Hpop;
    [|discriminate].
  apply TotalKernel.continuing_eq in Hstep; subst t.
  destruct (TotalQueue.pop_spec EC (Analysis.row_laws HL) _ _ c Hq Hpop) as [Hr Hqueue].
  assert (Hc : In c (System.constraints S)).
  { apply Hlisted; rewrite Hqueue; now left. }
  assert (Hrest : incl (TotalQueue.pending rest) (System.constraints S)).
  { intros d Hd; apply Hlisted; rewrite Hqueue; now right. }
  set (outs := fst (Eval.outputs S c (lookup EX L (TotalKernel.current s)))).
  assert (Houts : forall x b, In (x, b) outs -> Terminates.inv HT b).
  { intros x b Hb; exact (Terminates.inv_closed HT _ (proj2 Hg) c Hc (x, b) Hb). }
  fold EX EC L S SS; fold outs.
  destruct (updates_good outs (TotalKernel.State (TotalKernel.current s) rest)
    Hg Hr Hrest Houts) as [Hg' [Hq' [Hlisted' Hle]]].
  split; [exact Hg'|]; split; [exact Hq'|]; split; [exact Hlisted'|].
  intros d Hd Hnot.
  destruct (updates_unqueued outs (TotalKernel.State (TotalKernel.current s) rest)
    d Hg Hr Hrest Houts Hd Hnot) as [Habsent Hagree].
  assert (Heval : Eval.outputs S d
      (lookup EX L (TotalKernel.current
        (TotalKernel.updates a ix outs (TotalKernel.State (TotalKernel.current s) rest)))) =
      Eval.outputs S d (lookup EX L (TotalKernel.current s))).
  { apply determined, Hagree. }
  intros x b Hb; fold EX L S in Hb; fold outs in Hb; rewrite Heval in Hb.
  destruct (eqb EC d c) eqn:Hsame.
  - apply (eqb_true_iff EC (Analysis.row_laws HL)) in Hsame; subst d.
    apply updates_bounds; assumption.
  - eapply (leb_trans (Analysis.lattice_law HL)); [|apply Hle].
    assert (Hnotold : ~ In d (TotalQueue.pending (TotalKernel.queue s))).
    { rewrite Hqueue; cbn [In]; intros [Heq|Hin].
      - subst d; rewrite eqb_refl in Hsame; discriminate.
      - apply Habsent, Hin. }
    exact (Hvalid d Hd Hnotold x b Hb).
Qed.

(** A stopped invariant state is a global post-solution. *)
Theorem step_post s m :
  invariant s -> TotalKernel.step a ix s = inr m ->
  post_solution L S (lookup EX L m).
Proof.
  intros [Hg [Hq [Hlisted Hvalid]]] Hstop; rewrite TotalKernel.step_equation in Hstop.
  fold EX EC L S SS in Hstop.
  destruct (TotalQueue.pop EC (TotalKernel.queue s)) as [[c rest]|] eqn:Hpop;
    [discriminate|].
  injection Hstop as <-.
  rewrite TotalQueue.pop_equation in Hpop.
  destruct (TotalQueue.pending (TotalKernel.queue s)) as [|c cs] eqn:Hqueue;
    [|discriminate].
  intros c Hc; specialize (Hvalid c Hc ltac:(cbn [In]; tauto)).
  split.
  - apply Hvalid; rewrite Eval.outputs_spec; cbn; now left.
  - intros x b Hb; apply Hvalid; rewrite Eval.outputs_spec; cbn; now right.
Qed.

(** Preparation establishes the semantic invariant at the actual bottom start. *)
Theorem initial_invariant : invariant (TotalKernel.initial a).
Proof.
  rewrite TotalKernel.initial_equation; split; cbn [TotalKernel.current TotalKernel.queue].
  - split; [apply Map.wf_empty|]; intro x; rewrite lookup_empty; apply Terminates.inv_bot.
  - assert (Hq : TotalQueue.wf EC
      (TotalQueue.push_many EC (System.constraints S) TotalQueue.empty)).
    { apply TotalQueue.push_many_wf; [apply Analysis.row_laws, HL|apply TotalQueue.empty_wf]. }
    split; [exact Hq|]; split.
    + intros c Hc; apply (TotalQueue.push_many_member EC (Analysis.row_laws HL)
        _ _ c (TotalQueue.empty_wf EC)) in Hc.
      destruct Hc as [Hc|Hc]; [exact Hc|exact (False_rect _ Hc)].
    + intros c Hc Habsent; exfalso; apply Habsent.
      apply (TotalQueue.push_many_member EC (Analysis.row_laws HL)
        _ _ c (TotalQueue.empty_wf EC)); now left.
Qed.

End Invariant.

End TotalInvariant.
Import TotalInvariant.
