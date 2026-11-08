(** * Widening path weights

    Removing edges into widening points gives finite path weights for worklist debt.
    These weights and the resulting evaluation budget are exponential in the worst case.
    For example, repeated diamonds can double the number of non-widening paths at each level.
    Builds on: FixpointCycles, FixpointWorklistCost and LatticeHeight. *)

From Stdlib Require Import List Bool Arith Lia Relations.Relation_Operators Init.Wf.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver FixpointCycles FixpointKleene FixpointWorklist FixpointWorklistProof
  FixpointWorklistCost.
Import List.ListNotations WorklistProof WorklistCost.

Local Open Scope nat_scope.

Module WorklistWiden.

Local Lemma sum_app {B} (f : B -> nat) xs ys :
  sum f (xs ++ ys) = sum f xs + sum f ys.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (f x + sum f (xs ++ ys) = (f x + sum f xs) + sum f ys).
  rewrite IH; lia.
Qed.

Local Lemma sum_flat_map {B D} (f : D -> nat) (g : B -> list D) xs :
  sum f (flat_map g xs) = sum (fun x => sum f (g x)) xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (sum f (g x ++ flat_map g xs) =
    sum f (g x) + sum (fun y => sum f (g y)) xs).
  rewrite sum_app, IH; reflexivity.
Qed.

Local Lemma sum_ext {B} (f g : B -> nat) xs :
  (forall x, In x xs -> f x = g x) -> sum f xs = sum g xs.
Proof.
  induction xs as [|x xs IH]; intro Heq; [reflexivity|].
  change (f x + sum f xs = g x + sum g xs).
  rewrite (Heq x (or_introl eq_refl)); f_equal.
  apply IH; intros y Hy; apply Heq; now right.
Qed.

Section FinitePaths.
Context {B : Type} (R : B -> B -> Prop) (universe : list B).
Hypothesis Hclosed : forall y x, R y x -> In y universe.
Hypothesis Hacyclic : forall x, ~ clos_trans B R x x.

Local Fixpoint path (x : B) xs : Prop :=
  match xs with
  | [] => True
  | y :: rest => R y x /\ path y rest
  end.

Local Lemma path_member x y xs :
  path x xs -> In y xs -> clos_trans B R y x.
Proof.
  revert x; induction xs as [|z xs IH]; intros x Hpath Hin; [contradiction|].
  destruct Hpath as [Hz Hrest]; destruct Hin as [Heq|Hin].
  - subst y; apply t_step, Hz.
  - eapply t_trans; [apply (IH z Hrest Hin)|apply t_step, Hz].
Qed.

Local Lemma path_nodup x xs : path x xs -> NoDup (x :: xs).
Proof.
  revert x; induction xs as [|y xs IH]; intros x Hpath.
  - constructor; [intro Hin; exact Hin|constructor].
  - destruct Hpath as [Hy Hrest]; constructor.
    + intro Hin; apply (Hacyclic x); apply (path_member x x (y :: xs)).
      * split; assumption.
      * exact Hin.
    + apply IH, Hrest.
Qed.

Local Lemma path_closed x xs : path x xs -> incl xs universe.
Proof.
  revert x; induction xs as [|y xs IH]; intros x Hpath z Hin; [contradiction|].
  destruct Hpath as [Hy Hrest]; destruct Hin as [Heq|Hin].
  - subst z; eapply Hclosed, Hy.
  - exact (IH y Hrest z Hin).
Qed.

Local Lemma bounded_path_acc n x :
  (forall xs, length xs = n -> ~ path x xs) -> Acc R x.
Proof.
  revert x; induction n as [|n IH]; intros x Hbound.
  - exfalso; apply (Hbound [] eq_refl); exact I.
  - constructor; intros y Hy; apply IH; intros xs Hlength Hpath.
    apply (Hbound (y :: xs)); [cbn; now rewrite Hlength|now split].
Qed.

(** A finite successor presentation without nonempty cycles is well-founded. *)
Theorem finite_wf : well_founded R.
Proof.
  intro x; apply (bounded_path_acc (S (length universe))).
  intros xs Hlength Hpath.
  pose proof (path_nodup x xs Hpath) as Hnodup.
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  pose proof (NoDup_incl_length Htail (path_closed x xs Hpath)); lia.
Qed.

End FinitePaths.

Local Fixpoint evidence_sum {B} (xs : list B) :
    (forall x, In x xs -> nat) -> nat :=
  match xs as ys return (forall x, In x ys -> nat) -> nat with
  | [] => fun _ => 0
  | x :: rest => fun f =>
    f x (or_introl eq_refl) + evidence_sum rest (fun y Hy => f y (or_intror Hy))
  end.

Local Lemma evidence_sum_ext {B} xs (f g : forall x : B, In x xs -> nat) :
  (forall x Hx, f x Hx = g x Hx) -> evidence_sum xs f = evidence_sum xs g.
Proof.
  revert f g; induction xs as [|x xs IH]; intros f g Heq; cbn [evidence_sum].
  - reflexivity.
  - f_equal; [apply Heq|apply IH; intros y Hy; apply Heq].
Qed.

Local Lemma evidence_sum_plain {B} (xs : list B) (f : B -> nat) :
  evidence_sum xs (fun x _ => f x) = sum f xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (f x + evidence_sum xs (fun y _ => f y) = f x + sum f xs).
  now rewrite IH.
Qed.

Section Weights.
Context {X C A : Type} (a : Analysis.t X C A) (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix)
  (HC : cuts_every_cycle (Analysis.static a) (Policy.widen_at (Analysis.policy a))).
Let EX := Analysis.key_enc a.
Let S := Analysis.system a.
Let selected := Policy.widen_at (Analysis.policy a).

(** Non-cut outputs retain the static output list's order and multiplicity. *)
Definition noncut_outputs c :=
  filter (fun x => negb (selected x)) (System.target S c :: side_targets (Analysis.static a) c).

(** A successor expands every actual reader occurrence into its declared non-cut outputs. *)
Definition successors x := flat_map noncut_outputs (readers_of EX ix x).

Local Lemma successor_flow x y :
  In y (successors x) -> flows (Analysis.static a) x y /\ selected y = false.
Proof.
  intro Hin; apply in_flat_map in Hin; destruct Hin as [c [Hr Ho]].
  apply (readers_agree HI) in Hr; destruct Hr as [Hc Hread].
  apply filter_In in Ho; destruct Ho as [Hout Hselect]; apply negb_true_iff in Hselect.
  split; [exists c; split; [exact Hc|]; split; [exact Hread|]|exact Hselect].
  destruct Hout as [Heq|Hin]; [now left|now right].
Qed.

Local Lemma successor_closed x y :
  In y (successors x) -> In y (unknowns a).
Proof.
  intro Hin; apply in_flat_map in Hin; destruct Hin as [c [Hr Ho]].
  apply (readers_agree HI) in Hr; apply filter_In in Ho.
  unfold unknowns; rewrite Kleene.output_keys_spec, in_flat_map.
  exists c; split; [exact (proj1 Hr)|exact (proj1 Ho)].
Qed.

Local Lemma successor_wf : well_founded (fun y x => In y (successors x)).
Proof.
  apply (finite_wf _ (unknowns a)); [intros y x; apply successor_closed|].
  intros x Hcycle; apply (HC x).
  assert (Hreverse : forall u v,
    clos_trans X (fun y x => In y (successors x)) u v ->
    clos_trans X (fun y z => flows (Analysis.static a) y z /\ selected z = false) v u).
  { intros u v Hpath; induction Hpath as [u v Hedge|u v w Huv IH1 Hvw IH2].
    - apply t_step, successor_flow, Hedge.
    - eapply t_trans; [exact IH2|exact IH1]. }
  exact (Hreverse x x Hcycle).
Qed.

Local Definition weight_body x (rec : forall y, In y (successors x) -> nat) :=
  length (readers_of EX ix x) + evidence_sum (successors x) rec.

(** Unknown weights count reader occurrences and all downstream paths avoiding cuts. *)
Definition unknown_weight : X -> nat :=
  Fix successor_wf (fun _ => nat) weight_body.

(** The well-founded weight has its finite successor-sum equation. *)
Theorem unknown_weight_equation x :
  unknown_weight x =
    length (readers_of EX ix x) + sum unknown_weight (successors x).
Proof.
  unfold unknown_weight at 1; rewrite Fix_eq.
  - unfold weight_body; rewrite evidence_sum_plain; reflexivity.
  - intros y f g Heq; unfold weight_body; f_equal.
    apply evidence_sum_ext, Heq.
Qed.

(** A constraint pays for itself and every non-cut path leaving one of its declared outputs. *)
Definition constraint_weight c := 1 + sum unknown_weight (noncut_outputs c).

(** A reader-bucket weight is exactly the corresponding unknown's path weight. *)
Theorem reader_weight x :
  sum constraint_weight (readers_of EX ix x) = unknown_weight x.
Proof.
  rewrite unknown_weight_equation; unfold successors; rewrite sum_flat_map.
  unfold constraint_weight.
  induction (readers_of EX ix x) as [|c cs IH].
  - reflexivity.
  - change (1 + sum unknown_weight (noncut_outputs c) +
      sum (fun d => 1 + sum unknown_weight (noncut_outputs d)) cs =
      Datatypes.S (length cs) + (sum unknown_weight (noncut_outputs c) +
        sum (fun d => sum unknown_weight (noncut_outputs d)) cs)).
    lia.
Qed.

(** Popping one row pays strictly more than every reader it can add without spending cut credit. *)
Theorem constraint_weight_dominates c :
  sum constraint_weight (flat_map (readers_of EX ix) (noncut_outputs c)) <
    constraint_weight c.
Proof.
  rewrite sum_flat_map; unfold constraint_weight at 2.
  assert (Heq : sum (fun x => sum constraint_weight (readers_of EX ix x))
    (noncut_outputs c) = sum unknown_weight (noncut_outputs c)).
  { apply sum_ext; intros x Hx; apply reader_weight. }
  rewrite Heq; lia.
Qed.

End Weights.

Local Lemma sum_filter {B} (f : B -> nat) p xs :
  sum f (filter p xs) = sum (fun x => if p x then f x else 0) xs.
Proof.
  unfold sum; induction xs as [|x xs IH]; [reflexivity|].
  cbn [filter fold_right]; destruct (p x); cbn [fold_right]; now rewrite IH.
Qed.

Local Lemma sum_incl {B} (f : B -> nat) xs ys :
  NoDup xs -> incl xs ys -> sum f xs <= sum f ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros ys Hnodup Hincl.
  - change (0 <= sum f ys); lia.
  - inversion Hnodup as [|? ? Hfresh Htail]; subst.
    destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [before [after Heq]].
    subst ys; rewrite sum_app.
    change (f x + sum f xs <= sum f before + (f x + sum f after)).
    assert (Hincl' : incl xs (before ++ after)).
    { intros y Hy; specialize (Hincl y (or_intror Hy)).
      apply in_app_or in Hincl; apply in_or_app.
      destruct Hincl as [Hin|[Heq|Hin]].
      - now left.
      - subst y; contradiction.
      - now right. }
    specialize (IH (before ++ after) Htail Hincl'); rewrite sum_app in IH; lia.
Qed.

(** The queue universe removes row duplicates solely for proof-side weight accounting. *)
Definition rows {X C A} (a : Analysis.t X C A) :=
  distinct (Analysis.row_enc a) (System.constraints (Analysis.system a)).

(** Queue debt counts each live row once, independently of duplicate declarations. *)
Definition queue_weight {X C A} (a : Analysis.t X C A) (weight : C -> nat)
    (s : Worklist.state X C A) :=
  sum (fun c => if FinSet.mem (Analysis.row_enc a) c (Worklist.queued s)
    then weight c else 0) (rows a).

(** The queue debt is bounded by the sum of all row weights. *)
Theorem queue_weight_bound {X C A} (a : Analysis.t X C A) weight s :
  queue_weight a weight s <= sum weight (rows a).
Proof.
  apply sum_le; intros c Hc; destruct (FinSet.mem _ _ _); lia.
Qed.

(** Set inclusion pays for newly queued rows even when the additions list repeats them. *)
Theorem queue_weight_adds {X C A} (a : Analysis.t X C A) weight s next adds :
  (forall c, FinSet.mem (Analysis.row_enc a) c (Worklist.queued next) = true ->
    FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = true \/ In c adds) ->
  queue_weight a weight next <= queue_weight a weight s + sum weight adds.
Proof.
  intro Hsupport; unfold queue_weight; rewrite <- !sum_filter, <- sum_app.
  apply sum_incl; [apply NoDup_filter, distinct_nodup|].
  intros c Hin; apply filter_In in Hin; destruct Hin as [Hc Hpending].
  apply in_or_app; destruct (Hsupport c Hpending) as [Hold|Hadd].
  - left; apply filter_In; now split.
  - now right.
Qed.

Section PopWeight.
Context {X C A : Type} (a : Analysis.t X C A)
  (HE : encoding_laws (Analysis.row_enc a)).
Let EC := Analysis.row_enc a.

Local Lemma weight_remove xs (weight : C -> nat) keys c :
  NoDup xs -> In c xs -> FinSet.wf EC keys -> FinSet.mem EC c keys = true ->
  sum (fun d => if FinSet.mem EC d keys then weight d else 0) xs =
    weight c + sum (fun d =>
      if FinSet.mem EC d (FinSet.remove EC c keys) then weight d else 0) xs.
Proof.
  induction xs as [|d xs IH]; intros Hnodup Hin Hwf Hc; [contradiction|].
  inversion Hnodup as [|? ? Hfresh Htail]; subst.
  destruct Hin as [Heq|Hin].
  - subst d.
    change ((if FinSet.mem EC c keys then weight c else 0) +
      sum (fun d => if FinSet.mem EC d keys then weight d else 0) xs =
      weight c + ((if FinSet.mem EC c (FinSet.remove EC c keys) then weight c else 0) +
        sum (fun d => if FinSet.mem EC d (FinSet.remove EC c keys) then weight d else 0) xs)).
    rewrite Hc, FinSet.mem_remove, eqb_refl by exact Hwf.
    assert (Hsame : sum (fun d => if FinSet.mem EC d keys then weight d else 0) xs =
      sum (fun d => if FinSet.mem EC d (FinSet.remove EC c keys) then weight d else 0) xs).
    { apply sum_ext; intros d Hd; rewrite FinSet.mem_remove by exact Hwf.
      rewrite (proj2 (eqb_false_iff EC HE d c)) by (intro Heq; subst d; contradiction).
      reflexivity. }
    rewrite Hsame; reflexivity.
  - assert (Hdc : d <> c) by (intro Heq; subst d; contradiction).
    change ((if FinSet.mem EC d keys then weight d else 0) +
      sum (fun d => if FinSet.mem EC d keys then weight d else 0) xs =
      weight c + ((if FinSet.mem EC d (FinSet.remove EC c keys) then weight d else 0) +
        sum (fun d => if FinSet.mem EC d (FinSet.remove EC c keys) then weight d else 0) xs)).
    rewrite FinSet.mem_remove by exact Hwf.
    rewrite (proj2 (eqb_false_iff EC HE d c) Hdc).
    cbn [negb andb].
    specialize (IH Htail Hin Hwf Hc); lia.
Qed.

(** Removing a listed popped row removes exactly its weight from the queue debt. *)
Theorem popped_weight s p c q weight :
  structural a s -> In c (System.constraints (Analysis.system a)) ->
  Heap.pop EC (Worklist.queue s) = Some (p, c, q) ->
  queue_weight a weight s =
    weight c + queue_weight a weight
      (Worklist.State (Worklist.current s) q
        (FinSet.remove EC c (Worklist.queued s)) (Worklist.delays s)
        (Datatypes.S (Worklist.evaluations s))).
Proof.
  intros Hs Hc Hpop; apply weight_remove.
  - apply distinct_nodup.
  - apply (distinct_spec EC HE), Hc.
  - exact (queued_wf Hs).
  - rewrite (queued_live Hs); unfold present; fold EC.
    rewrite (Heap.pop_priority EC HE _ _ _ _ (heap_wf Hs) Hpop); reflexivity.
Qed.

End PopWeight.

(** The widening budget multiplies rank-and-delay credits by finite path-weight debt. *)
Definition widening_budget {X C A} (a : Analysis.t X C A)
    (W : widening_rank (Analysis.lat a)) (weight : C -> nat) :=
  (1 + length (unknowns a) * (Policy.delay (Analysis.policy a) + wbound W)) *
    (1 + sum weight (rows a)).

End WorklistWiden.
Import WorklistWiden.
