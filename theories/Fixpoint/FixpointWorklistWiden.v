(** * Widening path weights

    Removing edges into widening points gives finite path weights for worklist debt.
    These weights and the resulting evaluation budget are exponential in the worst case.
    For example, repeated diamonds can double the number of non-widening paths at each level.
    Builds on: FixpointCycles, FixpointWorklistCost and LatticeHeight. *)

From Stdlib Require Import List Bool Arith PArith Lia Relations.Relation_Operators Init.Wf.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver FixpointCycles FixpointKleene FixpointWorklist
  FixpointWorklistProof FixpointWorklistCost.
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

(** Rank-or-delay credit is independent of a solver's state and scheduling representation. *)
Definition local_credit {A} {L : lattice A} (W : widening_rank L) remaining value :=
  match remaining with
  | O => wrank W value
  | S n => S n + wbound W
  end.

(** A selected strict update consumes credit through a delayed join or an immediate widening. *)
Theorem delayed_rank_credit_progress {A} (L : lattice A) (W : widening_rank L)
    remaining old value :
  leb L value old = false ->
  local_credit W (Nat.pred remaining)
    (match remaining with
     | O => widen L old value
     | S _ => join L old value
     end) <
  local_credit W remaining old.
Proof.
  intro Hbelow; destruct remaining as [|[|n]]; cbn [Nat.pred local_credit].
  - exact (widen_rank_progress W old value I I Hbelow).
  - pose proof (wrank_bounded W (join L old value) I); lia.
  - lia.
Qed.

Section RankCredits.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (W : widening_rank (Analysis.lat a)).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let selected := Policy.widen_at (Analysis.policy a).
Let look := lookup EX L.

(** Every selected change consumes local rank-or-delay credit, including the last delayed join. *)
Theorem local_credit_progress x remaining old value :
  selected x = true -> leb L value old = false ->
  local_credit W (Nat.pred remaining)
    (Cost.value (Worklist.operation_c a x remaining old value)) <
  local_credit W remaining old.
Proof.
  intros Hselected Hbelow; rewrite Worklist.operation_equation.
  fold selected L; rewrite Hselected.
  exact (delayed_rank_credit_progress L W remaining old value Hbelow).
Qed.

(** The proof-side delay observation uses the same default as the computational update. *)
Definition remaining (s : Worklist.state X C A) x :=
  Map.find_or EX (Policy.delay (Analysis.policy a)) x (Worklist.delays s).

(** Only cut sites contribute rank credit. *)
Definition site_credit (s : Worklist.state X C A) x :=
  if selected x then local_credit W (remaining s x) (look (Worklist.current s) x) else 0.

(** Repeated declared outputs conservatively contribute repeated cut credits. *)
Definition cut_credit s := sum (site_credit s) (unknowns a).

Local Lemma changed_site_credit (s : Worklist.state X C A) x value :
  structural a s -> In x (unknowns a) -> leb L value (look (Worklist.current s) x) = false ->
  let n := remaining s x in
  let raised := Cost.value (Worklist.operation_c a x n (look (Worklist.current s) x) value) in
  let next := Worklist.State
    (Map.set EX x raised (Worklist.current s)) (Worklist.queue s) (Worklist.queued s)
    (Map.set EX x (Nat.pred n) (Worklist.delays s)) (Worklist.evaluations s) in
  cut_credit next <= cut_credit s /\
  (cut_credit next = cut_credit s -> selected x = false).
Proof.
  intros Hs Hx Hbelow; cbn zeta.
  set (n := remaining s x).
  set (raised := Cost.value (Worklist.operation_c a x n (look (Worklist.current s) x) value)).
  set (next := Worklist.State
    (Map.set EX x raised (Worklist.current s)) (Worklist.queue s) (Worklist.queued s)
    (Map.set EX x (Nat.pred n) (Worklist.delays s)) (Worklist.evaluations s)).
  assert (Hother : forall y, y <> x -> site_credit next y = site_credit s y).
  { intros y Hy; unfold site_credit, remaining, next; cbn [Worklist.current Worklist.delays].
    rewrite Map.find_or_equation, Map.get_set_other by
      first [exact (Analysis.key_laws HL)|exact (delays_wf Hs)|exact Hy].
    rewrite <- Map.find_or_equation.
    unfold look; rewrite lookup_equation, Map.get_set_other by
      first [exact (Analysis.key_laws HL)|exact (values_wf Hs)|exact Hy].
    rewrite <- lookup_equation; reflexivity. }
  assert (Hself : site_credit next x =
    if selected x then local_credit W (Nat.pred n) raised else 0).
  { unfold site_credit, remaining, next; cbn [Worklist.current Worklist.delays].
    rewrite Map.find_or_equation, Map.get_set_same by exact (delays_wf Hs).
    unfold look; rewrite lookup_equation, Map.get_set_same by exact (values_wf Hs).
    reflexivity. }
  assert (Hpoint : forall y, In y (unknowns a) -> site_credit next y <= site_credit s y).
  { intros y Hy; destruct (eqb EX y x) eqn:Hyx.
    - apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hyx; subst y.
      rewrite Hself; unfold site_credit.
      destruct (selected x) eqn:Hselected; [|reflexivity].
      pose proof (local_credit_progress x n (look (Worklist.current s) x) value
        Hselected Hbelow) as Hprogress.
      fold raised in Hprogress; fold n; lia.
    - apply (eqb_false_iff EX (Analysis.key_laws HL)) in Hyx.
      rewrite Hother by exact Hyx; reflexivity. }
  split; [apply sum_le, Hpoint|].
  intro Heq; destruct (selected x) eqn:Hselected; [|reflexivity].
  assert (Hstrict : site_credit next x + 1 <= site_credit s x).
  { rewrite Hself; unfold site_credit; rewrite Hselected.
    pose proof (local_credit_progress x n (look (Worklist.current s) x) value
      Hselected Hbelow) as Hprogress.
    fold raised in Hprogress; fold n; lia. }
  pose proof (sum_drop (site_credit s) (site_credit next) (unknowns a) x 1
    Hx Hpoint Hstrict) as Hdrop.
  unfold cut_credit in Heq; lia.
Qed.

Local Lemma enqueue_credit cs s :
  structural a s -> cut_credit (Worklist.enqueue a cs s) = cut_credit s.
Proof.
  intro Hs; destruct (enqueue_properties a (Analysis.row_laws HL) cs s Hs)
    as [_ [Hm [Hd _]]].
  unfold cut_credit; apply sum_ext; intros x Hx.
  unfold site_credit, remaining; rewrite Hm, Hd; reflexivity.
Qed.

(** Newly added readers require a non-cut site when propagation leaves cut credit unchanged. *)
Theorem update_credit_support ix s x value :
  structural a s -> In x (unknowns a) ->
  let next := Worklist.update a ix s (x, value) in
  structural a next /\ cut_credit next <= cut_credit s /\
  forall c, FinSet.mem (Analysis.row_enc a) c (Worklist.queued next) = true ->
    FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = true \/
    (In c (readers_of EX ix x) /\ (cut_credit next = cut_credit s -> selected x = false)).
Proof.
  intros Hs Hx; cbn zeta.
  pose proof (proj1 (update_properties a HL ix s x value Hs)) as Hstruct.
  split; [exact Hstruct|].
  rewrite Worklist.update_equation; cbn zeta; fold EX L.
  fold (remaining s x).
  rewrite Update.rule_equation; fold look.
  destruct (leb L value (look (Worklist.current s) x)) eqn:Hbelow.
  - cbn [snd]; split; [reflexivity|]; intros c Hc; now left.
  - cbn [fst snd].
    set (n := remaining s x).
    set (raised := Cost.value (Worklist.operation_c a x n (look (Worklist.current s) x) value)).
    set (base := Worklist.State
      (Map.set EX x raised (Worklist.current s)) (Worklist.queue s) (Worklist.queued s)
      (Map.set EX x (Nat.pred n) (Worklist.delays s)) (Worklist.evaluations s)).
    assert (Hb : structural a base).
    { constructor; cbn [base Worklist.current Worklist.queue Worklist.queued Worklist.delays].
      - apply Map.wf_set, (values_wf Hs).
      - apply Map.wf_set, (delays_wf Hs).
      - exact (heap_wf Hs).
      - exact (queued_wf Hs).
      - apply (queued_live Hs). }
    destruct (changed_site_credit s x value Hs Hx Hbelow) as [Hle Hcut].
    fold n raised base in Hle, Hcut.
    rewrite (enqueue_credit (readers_of EX ix x) base Hb).
    split; [exact Hle|].
    intros c Hc.
    destruct (enqueue_properties a (Analysis.row_laws HL) (readers_of EX ix x) base Hb)
      as [_ [_ [_ [_ Hmem]]]].
    apply Hmem in Hc; destruct Hc as [Hreader|Hold].
    + right; split; [exact Hreader|exact Hcut].
    + now left.
Qed.

(** An output fold charges changed cut sites before adding their readers. *)
Theorem updates_credit_support ix outs s :
  structural a s -> (forall x value, In (x, value) outs -> In x (unknowns a)) ->
  let next := Worklist.updates a ix outs s in
  structural a next /\ cut_credit next <= cut_credit s /\
  forall c, FinSet.mem (Analysis.row_enc a) c (Worklist.queued next) = true ->
    FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = true \/
    exists x value, In (x, value) outs /\ In c (readers_of EX ix x) /\
      (cut_credit next = cut_credit s -> selected x = false).
Proof.
  revert s; induction outs as [|[x value] outs IH]; intros s Hs Houts; cbn zeta;
    rewrite Worklist.updates_equation.
  - split; [exact Hs|]; split; [reflexivity|]; intros c Hc; now left.
  - destruct (update_credit_support ix s x value Hs (Houts x value (or_introl eq_refl)))
      as [Hmid [Hle1 Hsupport1]].
    destruct (IH _ Hmid (fun y v Hy => Houts y v (or_intror Hy)))
      as [Hnext [Hle2 Hsupport2]].
    split; [exact Hnext|]; split; [lia|].
    intros c Hc; destruct (Hsupport2 c Hc) as [Hkeep|[y [v [Hin [Hr Hcut]]]]].
    + destruct (Hsupport1 c Hkeep) as [Hold|[Hr Hcut]]; [now left|].
      right; exists x, value; split; [now left|]; split; [exact Hr|].
      intro Heq; apply Hcut; lia.
    + right; exists y, v; split; [now right|]; split; [exact Hr|].
      intro Heq; apply Hcut; lia.
Qed.

End RankCredits.

Section Widening.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (W : widening_rank (Analysis.lat a)) (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix)
  (HC : cuts_every_cycle (Analysis.static a) (Policy.widen_at (Analysis.policy a))).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let weight := constraint_weight a ix HI HC.
Let debt_cap := sum weight (rows a).
Let credits := cut_credit a W.

(** Each cut credit reserves the full queue debt while equal-credit steps decrease that debt. *)
Definition widening_potential s := credits s * (1 + debt_cap) + queue_weight a weight s.

Local Lemma step_widen_credit s next :
  worklist_invariant a ix s -> Worklist.step a ix s = inl next ->
  widening_potential next < widening_potential s.
Proof.
  intros Hinv Hstep; pose proof (valid_state Hinv) as Hs.
  rewrite Worklist.step_equation in Hstep; fold EX EC L S in Hstep.
  destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|] eqn:Hpop;
    [|discriminate].
  set (base := Worklist.State (Worklist.current s) q
    (FinSet.remove EC c (Worklist.queued s)) (Worklist.delays s)
    (Datatypes.S (Worklist.evaluations s))).
  set (outs := fst (Eval.outputs S c (lookup EX L (Worklist.current s)))).
  assert (Hresult : next = Worklist.updates a ix outs base).
  { injection Hstep as Hresult; symmetry; exact Hresult. }
  subst next.
  assert (Hb : structural a base) by exact (popped_structural a s p c q Hs Hpop).
  assert (Hc : In c (System.constraints S)).
  { apply (queue_listed Hinv c); rewrite (queued_live Hs); unfold present; fold EC.
    rewrite (Heap.pop_priority EC (Analysis.row_laws HL) _ _ _ _ (heap_wf Hs) Hpop).
    reflexivity. }
  destruct (updates_credit_support a HL W ix outs base Hb) as [_ [Hle Hsupport]].
  - intros x value Hin; exact (output_unknown a HL c (Worklist.current s) x value Hc Hin).
  - assert (Hbase : credits base = credits s) by reflexivity.
    fold credits in Hle, Hsupport; rewrite Hbase in Hle.
    destruct (Nat.lt_ge_cases (credits (Worklist.updates a ix outs base)) (credits s))
      as [Hdrop|Hequal].
    + pose proof (queue_weight_bound a weight (Worklist.updates a ix outs base)) as Hcap.
      fold debt_cap in Hcap; unfold widening_potential; nia.
    + assert (Heq : credits (Worklist.updates a ix outs base) = credits s) by lia.
      assert (Hadds : queue_weight a weight (Worklist.updates a ix outs base) <=
        queue_weight a weight base +
        sum weight (flat_map (readers_of EX ix) (noncut_outputs a c))).
      { apply queue_weight_adds; intros d Hd.
        destruct (Hsupport d Hd) as [Hold|[x [value [Hin [Hr Hselected]]]]].
        - now left.
        - right; apply in_flat_map; exists x; split; [|exact Hr].
          apply filter_In; split.
          + unfold outs in Hin; rewrite Eval.outputs_spec in Hin; cbn [fst] in Hin.
            destruct Hin as [Hprimary|Hside].
            * injection Hprimary as <- <-; now left.
            * right; apply (System.sides_within (Analysis.static_law HL) c
                (lookup EX L (Worklist.current s))).
              apply in_map_iff; exists (x, value); now split.
          + apply negb_true_iff, Hselected; now rewrite Hbase. }
      pose proof (popped_weight a (Analysis.row_laws HL) s p c q weight Hs Hc Hpop)
        as Hpopweight.
      fold EC base in Hpopweight.
      pose proof (constraint_weight_dominates a ix HI HC c) as Hdominates.
      fold EX weight in Hdominates.
      unfold widening_potential; rewrite Heq; lia.
Qed.

Local Lemma sum_constant {B} (xs : list B) k : sum (fun _ => k) xs = length xs * k.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (k + sum (fun _ : B => k) xs = Datatypes.S (length xs) * k).
  rewrite IH; lia.
Qed.

Local Lemma initial_credit :
  credits (Worklist.initial a) <=
    length (unknowns a) * (Policy.delay (Analysis.policy a) + wbound W).
Proof.
  unfold credits, cut_credit.
  rewrite <- sum_constant.
  apply sum_le; intros x Hx.
  unfold site_credit, remaining.
  rewrite (initial_delays a (Analysis.row_laws HL)).
  rewrite Map.find_or_equation, Map.get_empty.
  rewrite (proj1 (initial_frames a (Analysis.row_laws HL))).
  rewrite lookup_empty.
  destruct (Policy.widen_at (Analysis.policy a) x); [|lia].
  destruct (Policy.delay (Analysis.policy a)); cbn [local_credit].
  - exact (wrank_bounded W (bot L) I).
  - lia.
Qed.

(** The initial potential is strictly below the explicit rank-and-path-weight budget. *)
Theorem initial_widening_potential :
  widening_potential (Worklist.initial a) < widening_budget a W weight.
Proof.
  pose proof initial_credit as Hcredit.
  pose proof (queue_weight_bound a weight (Worklist.initial a)) as Hdebt.
  unfold widening_potential, widening_budget, debt_cap in *; nia.
Qed.

Local Lemma widening_runs_credit n s next :
  runs (Worklist.step_c a ix) n s (inl next) ->
  worklist_invariant a ix s ->
  widening_potential next + n <= widening_potential s.
Proof.
  intro Hrun; remember (inl next) as result eqn:Heq.
  induction Hrun as [s|n s m Hstop|n s mid result Hnext Hrun IH]; intro Hinv.
  - injection Heq as <-; lia.
  - discriminate.
  - pose proof (step_widen_credit s mid Hinv Hnext) as Hdrop.
    pose proof (IH Heq (step_invariant a HL ix HI s mid Hinv Hnext)); lia.
Qed.

(** Every actual widening evaluation prefix is strictly below the rank-and-path budget. *)
Theorem worklist_widen_evals_bound n next :
  runs (Worklist.step_c a ix) n (Worklist.initial a) (inl next) ->
  n < widening_budget a W weight.
Proof.
  intro Hrun.
  pose proof (widening_runs_credit n _ next Hrun (initial_invariant a HL ix HI)).
  pose proof initial_widening_potential; lia.
Qed.

End Widening.

(** The widening budget includes the final empty-pop probe for the actual priority driver. *)
Theorem worklist_widen_fuel_enough {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (W : widening_rank (Analysis.lat a))
    (HC : cuts_every_cycle (Analysis.static a) (Policy.widen_at (Analysis.policy a))) fuel :
  let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  let HI := index_system_laws (Analysis.key_enc a) (Analysis.key_laws HL)
    (Analysis.system a) (Analysis.static a) in
  widening_budget a W (constraint_weight a ix HI HC) <= Pos.to_nat fuel ->
  exists m, Worklist.run a fuel = Outcome.Solved m.
Proof.
  cbn zeta; intro Hfuel; rewrite Worklist.run_equation.
  set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  set (HI := index_system_laws (Analysis.key_enc a) (Analysis.key_laws HL)
    (Analysis.system a) (Analysis.static a)).
  pose proof (iterate_value (Worklist.step_c a ix) fuel (Worklist.initial a)) as Hrun.
  destruct (Cost.value (iterate _ _ _)) as [next|done].
  - pose proof (worklist_widen_evals_bound a HL W ix HI HC _ _ Hrun).
    fold ix HI in Hfuel; lia.
  - exists done; reflexivity.
Qed.

End WorklistWiden.
Import WorklistWiden.
