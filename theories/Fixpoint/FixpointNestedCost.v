(** * Nested iteration budgets

    Rank capacity pays for changed evaluations and saved frame credit pays for repeated traversals.
    For example, a side-target contributor counts once in each bucket visited by the code.
    Builds on: FixpointNestedProof, LatticeHeight, LatticeKit and CostLoop. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeKit.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver FixpointNested FixpointNestedProof.
Import List.ListNotations.

Local Open Scope nat_scope.

Module NestedCost.

(** Declared output occurrences bound rank capacity without assuming unique static summaries. *)
Definition universe {X C A} (a : Analysis.t X C A) : list X :=
  flat_map (fun c => System.target (Analysis.system a) c ::
    side_targets (Analysis.static a) c) (System.constraints (Analysis.system a)).

(** Scheduled size is the bucket-length sum over the multiplicity-preserving code inventory. *)
Theorem scheduled_inventory {X C} (EX : encoding X) (ix : sys_index X C) p :
  Nested.scheduled EX ix p =
    fold_right (fun x total => length (contributors_of EX ix x) + total) 0
      (Nested.vertices p).
Proof.
  assert (Happ : forall xs ys,
    fold_right (fun x total => length (contributors_of EX ix x) + total) 0 (xs ++ ys) =
      fold_right (fun x total => length (contributors_of EX ix x) + total) 0 xs +
      fold_right (fun x total => length (contributors_of EX ix x) + total) 0 ys).
  { intros xs ys; induction xs; cbn; lia. }
  induction p; cbn [Nested.scheduled Nested.vertices fold_right].
  - reflexivity.
  - now rewrite IHp.
  - rewrite Happ.
    rewrite <- IHp1, <- IHp2; lia.
Qed.

(** The prepared size counts declared output incidence with the original row multiplicities. *)
Theorem scheduled_incidence {X C A} (EX : encoding X) (HE : encoding_laws EX)
    (S : System.t X C A) (SS : System.static S) p :
  Nested.scheduled EX (index_system EX S SS) p =
    fold_right (fun x total => length (filter (fun c =>
      eqb EX x (System.target S c) || existsb (eqb EX x) (side_targets SS c))
      (System.constraints S)) + total) 0 (Nested.vertices p).
Proof.
  rewrite scheduled_inventory; induction (Nested.vertices p) as [|x xs IH];
    cbn [fold_right]; [reflexivity|].
  rewrite (contributors_occurrences EX HE S SS x), IH; reflexivity.
Qed.

Section Rank.
Context {X C A : Type} (a : Analysis.t X C A) (Hl : Analysis.laws a)
  (HT : Terminates.t a).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let R := Terminates.hgt HT.

(** Good assignments satisfy the finite-height invariant at every lookup. *)
Definition good (m : assignment X A) : Prop :=
  Map.wf EX m /\ forall x, Terminates.inv HT (lookup EX L m x).

Definition rank_sum (m : assignment X A) : nat :=
  msum (universe a) (fun x => rank R (lookup EX L m x)).

(** The empty assignment starts inside the termination invariant. *)
Theorem good_empty : good Map.empty.
Proof.
  split; [apply Map.wf_empty|].
  intro x; rewrite lookup_empty; apply Terminates.inv_bot.
Qed.

(** Finite output occurrences bound every invariant assignment's rank sum. *)
Theorem rank_bound m : good m -> rank_sum m <= length (universe a) * bound R.
Proof.
  intros [_ Hinv]; unfold rank_sum.
  rewrite <- msum_constant; apply msum_bounded.
  intros x Hx; apply (rank_bounded R), Hinv.
Qed.

Local Lemma rule_good m x b :
  good m -> Terminates.inv HT b ->
  good (fst (Update.rule EX L (join_c L) m x b)).
Proof.
  intros [Hwf Hinv] Hb; split; [apply Update.rule_wf, Hwf|].
  intro y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
  destruct (leb L b (lookup EX L m x)); [apply Hinv|].
  destruct (eqb EX y x); [|apply Hinv].
  rewrite <- join_equation; apply Terminates.inv_join; [apply Hinv|exact Hb].
Qed.

Local Lemma rule_ascending m x b :
  Map.wf EX m ->
  fun_leb L (lookup EX L m) (lookup EX L (fst (Update.rule EX L (join_c L) m x b))).
Proof.
  intros Hwf y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)).
  destruct (leb L b (lookup EX L m x)); [apply (leb_refl (Analysis.lattice_law Hl))|].
  destruct (eqb EX y x) eqn:Hy; [|apply (leb_refl (Analysis.lattice_law Hl))].
  apply (eqb_true_iff EX (Analysis.key_laws Hl)) in Hy; subst y.
  rewrite <- join_equation; apply (join_upper_l (Analysis.lattice_law Hl)).
Qed.

Local Lemma rank_monotone m n :
  good m -> good n -> fun_leb L (lookup EX L m) (lookup EX L n) ->
  rank_sum m <= rank_sum n.
Proof.
  intros [_ Hm] [_ Hn] Hle; apply msum_bounded.
  intros x Hx; apply (LatticeHeight.rank_monotone R); [apply Hm|apply Hn|apply Hle].
Qed.

Local Lemma rule_grows m x b :
  good m -> Terminates.inv HT b -> In x (universe a) ->
  snd (Update.rule EX L (join_c L) m x b) = true ->
  rank_sum m < rank_sum (fst (Update.rule EX L (join_c L) m x b)).
Proof.
  intros Hg Hb Hx Hchanged.
  pose proof (rule_good m x b Hg Hb) as Hnext.
  pose proof (rule_ascending m x b (proj1 Hg)) as Hup.
  unfold rank_sum; apply msum_grows.
  - intros y Hy; apply (LatticeHeight.rank_monotone R).
    + apply (proj2 Hg).
    + apply (proj2 Hnext).
    + apply Hup.
  - exists x; split; [exact Hx|].
    rewrite Update.rule_equation in Hchanged |- *.
    destruct (leb L b (lookup EX L m x)) eqn:Hbelow; [discriminate|].
    cbn [fst]; rewrite !lookup_equation, Map.get_set by exact (proj1 Hg).
    rewrite eqb_refl; rewrite <- join_equation.
    apply (join_rank_grows R); [apply (proj2 Hg)|exact Hb|].
    destruct (leb L (join L (lookup EX L m x) b) (lookup EX L m x)) eqn:Hjoin;
      [|exact Hjoin].
    pose proof (leb_trans (Analysis.lattice_law Hl) _ _ _
      (join_upper_r (Analysis.lattice_law Hl) _ _) Hjoin) as Hbad.
    change (leb L b (lookup EX L m x) = true) in Hbad.
    congruence.
Qed.

Local Lemma apply_good outs m :
  good m -> (forall x b, In (x, b) outs -> Terminates.inv HT b) ->
  good (fst (Update.apply EX L (join_c L) outs m)).
Proof.
  revert m; induction outs as [|[x b] outs IH]; intros m Hg Houts;
    rewrite Update.apply_equation; [exact Hg|].
  cbn [fst]; apply IH.
  - apply rule_good; [exact Hg|exact (Houts x b (or_introl eq_refl))].
  - intros y d Hin; exact (Houts y d (or_intror Hin)).
Qed.

Local Lemma apply_ascending outs m :
  Map.wf EX m ->
  fun_leb L (lookup EX L m) (lookup EX L (fst (Update.apply EX L (join_c L) outs m))).
Proof.
  revert m; induction outs as [|[x b] outs IH]; intros m Hwf;
    rewrite Update.apply_equation; cbn [fst].
  - intro y; apply (leb_refl (Analysis.lattice_law Hl)).
  - intro y; eapply (leb_trans (Analysis.lattice_law Hl)).
    + apply rule_ascending, Hwf.
    + apply IH, Update.rule_wf, Hwf.
Qed.

Local Lemma apply_grows outs m :
  good m -> (forall x b, In (x, b) outs -> Terminates.inv HT b /\ In x (universe a)) ->
  snd (Update.apply EX L (join_c L) outs m) = true ->
  rank_sum m < rank_sum (fst (Update.apply EX L (join_c L) outs m)).
Proof.
  revert m; induction outs as [|[x b] outs IH]; intros m Hg Houts;
    rewrite Update.apply_equation; [discriminate|].
  cbn [snd fst]; rewrite orb_true_iff; intro Hchanged.
  destruct (Houts x b (or_introl eq_refl)) as [Hb Hx].
  pose proof (rule_good m x b Hg Hb) as Hfirst.
  assert (Htail : forall y d, In (y, d) outs -> Terminates.inv HT d /\ In y (universe a)).
  { intros y d Hin; apply Houts; now right. }
  pose proof (apply_good outs _ Hfirst (fun y d Hin => proj1 (Htail y d Hin))) as Hfinal.
  pose proof (rank_monotone _ _ Hg Hfirst (rule_ascending m x b (proj1 Hg))) as Hle1.
  pose proof (rank_monotone _ _ Hfirst Hfinal (apply_ascending outs _ (proj1 Hfirst))) as Hle2.
  destruct Hchanged as [Hchanged|Hchanged].
  - pose proof (rule_grows m x b Hg Hb Hx Hchanged); lia.
  - pose proof (IH _ Hfirst Htail Hchanged); lia.
Qed.

Local Lemma outputs_invariant m c :
  good m -> In c (System.constraints S) ->
  forall x b, In (x, b) (fst (Eval.outputs S c (lookup EX L m))) ->
    Terminates.inv HT b /\ In x (universe a).
Proof.
  intros [_ Hinv] Hc x b Hb; split.
  - exact (Terminates.inv_closed HT _ Hinv c Hc (x, b) Hb).
  - unfold universe; apply in_flat_map; exists c; split; [exact Hc|].
    rewrite Eval.outputs_spec in Hb; cbn [fst] in Hb.
    destruct Hb as [Heq|Hb]; [injection Heq as <- <-; now left|].
    right; apply (System.sides_within (Analysis.static_law Hl) c (lookup EX L m)).
    apply in_map_iff; exists (x, b); now split.
Qed.

(** A listed joining evaluation stays invariant and increases rank whenever its flag is set. *)
Theorem evaluation_progress hs delay c m counts :
  Analysis.joining a -> good m -> In c (System.constraints S) ->
  let next := Nested.updates a hs delay (fst (Eval.outputs S c (lookup EX L m))) m counts in
  good (fst (fst next)) /\
  rank_sum m <= rank_sum (fst (fst next)) /\
  (snd next = true -> rank_sum m < rank_sum (fst (fst next))).
Proof.
  intros Hjoining Hg Hc; cbn zeta.
  pose proof (NestedProof.updates_join a hs delay
    (fst (Eval.outputs S c (lookup EX L m))) m counts Hjoining) as Hjoin.
  pose proof (f_equal fst Hjoin) as Hmap.
  pose proof (f_equal snd Hjoin) as Hflag; cbn [fst snd] in Hmap, Hflag.
  rewrite Hmap, Hflag.
  assert (Houts := outputs_invariant m c Hg Hc).
  assert (Hgood := apply_good _ m Hg (fun x b Hin => proj1 (Houts x b Hin))).
  split; [exact Hgood|]; split.
  - apply rank_monotone; [exact Hg|exact Hgood|apply apply_ascending, (proj1 Hg)].
  - apply apply_grows; [exact Hg|exact Houts].
Qed.

End Rank.

Section Geometry.
Context {X C A : Type} (EX : encoding X) (ix : sys_index X C) (root : Nested.code X).

(** Traversal work counts row dispatches, syntax transitions and frame returns. *)
Fixpoint work (p : Nested.code X) : nat :=
  match p with
  | Nested.End => 0
  | Nested.Visit x rest => 1 + length (contributors_of EX ix x) + work rest
  | Nested.Component h body rest =>
    3 + length (contributors_of EX ix h) + work body + work rest
  end.

Let W := work root.
Let d := Nested.depth root.

Fixpoint frame_bounds (fs : list (Nested.Frame.t X)) : Prop :=
  match fs with
  | [] => True
  | f :: rest =>
    work (Nested.Frame.pass f) <= W /\ work (Nested.Frame.rest f) <= W /\
    Nested.depth (Nested.Frame.pass f) + S (length rest) <= d /\
    Nested.depth (Nested.Frame.rest f) + length rest <= d /\ frame_bounds rest
  end.

(** Frame bounds relate each saved continuation to the actual root's work and depth. *)
Definition control (s : Nested.State.t X C A) : Prop :=
  work (Nested.State.pointer s) <= W /\
  Nested.depth (Nested.State.pointer s) + length (Nested.State.frames s) <= d /\
  frame_bounds (Nested.State.frames s).

Fixpoint suffix_work (fs : list (Nested.Frame.t X)) : nat :=
  match fs with
  | [] => 0
  | f :: rest => 1 + work (Nested.Frame.rest f) + suffix_work rest
  end.

Fixpoint frame_credit (epoch : N) (fs : list (Nested.Frame.t X)) : nat :=
  match fs with
  | [] => 0
  | f :: rest =>
    (if N.eqb (Nested.Frame.epoch f) epoch then 0 else 1 + work (Nested.Frame.pass f)) +
      frame_credit epoch rest
  end.

Definition credit (epoch outer : N) fs :=
  frame_credit epoch fs + if N.eqb outer epoch then 0 else 1 + W.

(** Administrative credit includes the actual ready bucket and every suspended suffix. *)
Definition admin (s : Nested.State.t X C A) :=
  length (Nested.State.ready s) + work (Nested.State.pointer s) +
    suffix_work (Nested.State.frames s) + 1 +
    credit (Nested.State.epoch s) (Nested.State.outer s) (Nested.State.frames s).

Local Lemma frame_credit_bound epoch fs :
  frame_bounds fs -> frame_credit epoch fs <= length fs * (W + 1).
Proof.
  induction fs as [|f fs IH]; intro Hb; [cbn; lia|].
  destruct Hb as [Hp [_ [_ [_ Hb]]]].
  specialize (IH Hb); cbn [frame_credit length].
  destruct (N.eqb (Nested.Frame.epoch f) epoch); nia.
Qed.

Local Lemma credit_bound epoch outer fs :
  frame_bounds fs -> credit epoch outer fs <= (length fs + 1) * (W + 1).
Proof.
  intro Hb; pose proof (frame_credit_bound epoch fs Hb).
  unfold credit; destruct (N.eqb outer epoch); nia.
Qed.

(** The actual empty start has one traversal's administrative credit. *)
Theorem start_admin : admin (@Nested.start X C A root) = W + 1.
Proof.
  change (0 + W + 0 + 1 + (0 + 0) = W + 1); lia.
Qed.

(** The actual empty start satisfies all structural frame bounds. *)
Theorem start_control : control (@Nested.start X C A root).
Proof.
  change (W <= W /\ d + 0 <= d /\ True); repeat split; lia.
Qed.

Context (a : Analysis.t X C A) (hs : FinSet.t X) (delay : N).
Hypothesis Hkey : Analysis.key_enc a = EX.

(** The explicit stack never exceeds the code's nesting depth. *)
Theorem step_control s next :
  control s -> Nested.step a root ix hs delay s = inl next -> control next.
Proof.
  intros [Hp [Hd Hb]] Hstep.
  unfold Nested.step, Nested.step_c in Hstep.
  destruct (Nested.State.ready s) as [|c rest].
  2: { autorewrite with galois_cost in Hstep; injection Hstep as <-; exact (conj Hp (conj Hd Hb)). }
  destruct (Nested.State.pointer s) as [|x rest|h body rest] eqn:Hptr.
  - destruct (Nested.State.frames s) as [|f fs] eqn:Hframes.
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s));
        [discriminate|].
      injection Hstep as <-; apply start_control.
    + cbn [frame_bounds] in Hb; destruct Hb as [Hpass [Hrest [Hdp [Hdr Hb]]]].
      destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
        injection Hstep as <-; unfold control; cbn.
      * auto.
      * split; [exact Hpass|]; split; [exact Hdp|].
        cbn [frame_bounds Nested.Frame.pass Nested.Frame.head Nested.Frame.body
          Nested.Frame.rest]; auto.
  - autorewrite with galois_cost in Hstep; injection Hstep as <-.
    unfold control; cbn; split.
    + cbn [work] in Hp; lia.
    + cbn [Nested.depth] in Hd; auto.
  - injection Hstep as <-; unfold control; cbn [Nested.State.pointer Nested.State.frames].
    cbn [work Nested.depth] in Hp, Hd.
    split; [cbn [work]; lia|].
    split; [cbn [Nested.depth length]; lia|].
    cbn [frame_bounds Nested.Frame.pass Nested.Frame.head Nested.Frame.body
      Nested.Frame.rest work Nested.depth]; repeat split; try lia; exact Hb.
Qed.

(** A row transition either consumes one credit or replenishes bounded restart credit. *)
Theorem evaluation_admin s c rest :
  control s -> Nested.State.ready s = c :: rest ->
  let next := Nested.updates a hs delay
    (fst (Eval.outputs (Analysis.system a) c
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Nested.State.values s))))
    (Nested.State.values s) (Nested.State.counters s) in
  let state := Nested.State.Make (fst (fst next)) (snd (fst next)) (Nested.State.pointer s)
    rest (Nested.State.frames s)
    (if snd next then N.succ (Nested.State.epoch s) else Nested.State.epoch s)
    (Nested.State.outer s) (N.succ (Nested.State.evals s)) in
  if snd next then admin state + 1 <= admin s + (d + 1) * (W + 1)
  else admin state + 1 = admin s.
Proof.
  intros [_ [Hd Hb]] Hready; cbn zeta.
  set (next := Nested.updates _ _ _ _ _ _).
  destruct (snd next); unfold admin;
    cbn [Nested.State.ready Nested.State.pointer Nested.State.frames
      Nested.State.epoch Nested.State.outer]; rewrite Hready; cbn [length].
  - pose proof (credit_bound (N.succ (Nested.State.epoch s)) (Nested.State.outer s)
      (Nested.State.frames s) Hb); nia.
  - lia.
Qed.

(** Every frame-only continuation strictly consumes administrative credit. *)
Theorem administrative_progress s next :
  control s -> Nested.State.ready s = [] ->
  Nested.step a root ix hs delay s = inl next ->
  Nested.State.values next = Nested.State.values s /\ admin next < admin s.
Proof.
  intros [_ [_ Hb]] Hready Hstep.
  unfold Nested.step, Nested.step_c in Hstep; rewrite Hready in Hstep.
  destruct (Nested.State.pointer s) as [|x rest|h body rest] eqn:Hptr.
  - destruct (Nested.State.frames s) as [|f fs] eqn:Hframes.
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s)) eqn:Hclean;
        [discriminate|].
      injection Hstep as <-; split; [reflexivity|].
      unfold admin, credit; rewrite Hready, Hptr, Hframes, Hclean.
      cbn [suffix_work frame_credit Nested.State.ready Nested.State.pointer
        Nested.State.frames Nested.State.epoch Nested.State.outer].
      rewrite N.eqb_refl; unfold W; lia.
    + destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s)) eqn:Hclean;
        injection Hstep as <-; split; try reflexivity;
        unfold admin, credit; rewrite Hready, Hptr, Hframes;
        cbn [suffix_work frame_credit Nested.State.ready Nested.State.pointer
          Nested.State.frames Nested.State.epoch Nested.State.outer
          Nested.Frame.epoch Nested.Frame.rest]; rewrite Hclean.
      * lia.
      * cbn [Nested.Frame.pass]; rewrite N.eqb_refl; lia.
  - autorewrite with galois_cost in Hstep.
    rewrite Hkey in Hstep; fold (contributors_of EX ix x) in Hstep.
    injection Hstep as <-; split; [reflexivity|].
    unfold admin; rewrite Hready, Hptr; cbn [work length Nested.State.ready
      Nested.State.pointer Nested.State.frames Nested.State.epoch Nested.State.outer].
    lia.
  - injection Hstep as <-; split; [reflexivity|].
    unfold admin, credit; rewrite Hready, Hptr.
    cbn [work suffix_work frame_credit Nested.State.ready Nested.State.pointer
      Nested.State.frames Nested.State.epoch Nested.State.outer Nested.Frame.epoch
      Nested.Frame.rest Nested.Frame.pass]; rewrite N.eqb_refl; lia.
Qed.

(** Administrative transitions leave the actual delay-counter map unchanged. *)
Theorem administrative_counters s next :
  Nested.State.ready s = [] -> Nested.step a root ix hs delay s = inl next ->
  Nested.State.counters next = Nested.State.counters s.
Proof.
  intros Hready Hstep; unfold Nested.step, Nested.step_c in Hstep.
  rewrite Hready in Hstep.
  destruct (Nested.State.pointer s) as [|x rest|h body rest].
  - destruct (Nested.State.frames s) as [|f fs].
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s));
        [discriminate|injection Hstep as <-; reflexivity].
    + destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
        injection Hstep as <-; reflexivity.
  - autorewrite with galois_cost in Hstep; injection Hstep as <-; reflexivity.
  - injection Hstep as <-; reflexivity.
Qed.

End Geometry.

Section EvaluationGeometry.
Context {X C A : Type} (EX : encoding X) (ix : sys_index X C) (root : Nested.code X).
Let M := Nested.scheduled EX ix root.
Let d := Nested.depth root.

(** Scheduled frame bounds retain the exact bucket measure of every saved pass. *)
Definition schedule_bounds (s : Nested.State.t X C A) : Prop :=
  Nested.scheduled EX ix (Nested.State.pointer s) <= M /\
  Forall (fun f => Nested.scheduled EX ix (Nested.Frame.pass f) <= M /\
    Nested.scheduled EX ix (Nested.Frame.rest f) <= M) (Nested.State.frames s).

Fixpoint suffix_evals (fs : list (Nested.Frame.t X)) : nat :=
  match fs with
  | [] => 0
  | f :: rest => Nested.scheduled EX ix (Nested.Frame.rest f) + suffix_evals rest
  end.

Fixpoint restart_evals (epoch : N) (fs : list (Nested.Frame.t X)) : nat :=
  match fs with
  | [] => 0
  | f :: rest =>
    (if N.eqb (Nested.Frame.epoch f) epoch then 0
      else Nested.scheduled EX ix (Nested.Frame.pass f)) + restart_evals epoch rest
  end.

Definition eval_credit epoch outer fs :=
  restart_evals epoch fs + if N.eqb outer epoch then 0 else M.

(** Evaluation credit charges rows only and gives syntax transitions zero evaluation weight. *)
Definition eval_work (s : Nested.State.t X C A) : nat :=
  length (Nested.State.ready s) + Nested.scheduled EX ix (Nested.State.pointer s) +
    suffix_evals (Nested.State.frames s) +
    eval_credit (Nested.State.epoch s) (Nested.State.outer s) (Nested.State.frames s).

Local Lemma restart_evals_bound epoch fs :
  Forall (fun f => Nested.scheduled EX ix (Nested.Frame.pass f) <= M /\
    Nested.scheduled EX ix (Nested.Frame.rest f) <= M) fs ->
  restart_evals epoch fs <= length fs * M.
Proof.
  intro Hb; induction Hb as [|f fs [Hp Hrest] Hfs IH]; cbn [restart_evals length].
  - lia.
  - destruct (N.eqb (Nested.Frame.epoch f) epoch); nia.
Qed.

Local Lemma eval_credit_bound epoch outer fs :
  Forall (fun f => Nested.scheduled EX ix (Nested.Frame.pass f) <= M /\
    Nested.scheduled EX ix (Nested.Frame.rest f) <= M) fs ->
  eval_credit epoch outer fs <= (length fs + 1) * M.
Proof.
  intro Hb; pose proof (restart_evals_bound epoch fs Hb).
  unfold eval_credit; destruct (N.eqb outer epoch); nia.
Qed.

(** The start's evaluation credit is exactly the scheduled bucket-occurrence measure. *)
Theorem start_eval_work : eval_work (@Nested.start X C A root) = M.
Proof.
  change (0 + M + 0 + (0 + 0) = M); lia.
Qed.

(** The empty start retains the full scheduled root inventory and has no saved frames. *)
Theorem start_schedule_bounds : schedule_bounds (@Nested.start X C A root).
Proof.
  split; [apply Nat.le_refl|constructor].
Qed.

Context (a : Analysis.t X C A) (hs : FinSet.t X) (delay : N).
Hypothesis Hkey : Analysis.key_enc a = EX.

(** All reached code pointers and saved passes retain the scheduled root bound. *)
Theorem step_schedule_bounds s next :
  schedule_bounds s -> Nested.step a root ix hs delay s = inl next ->
  schedule_bounds next.
Proof.
  intros [Hp Hfs] Hstep; unfold Nested.step, Nested.step_c in Hstep.
  destruct (Nested.State.ready s) as [|c rest].
  2: { autorewrite with galois_cost in Hstep; injection Hstep as <-; now split. }
  destruct (Nested.State.pointer s) as [|x rest|h body rest] eqn:Hptr.
  - destruct (Nested.State.frames s) as [|f fs] eqn:Hframes.
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s));
        [discriminate|]; injection Hstep as <-; split; [apply Nat.le_refl|constructor].
    + inversion Hfs as [|g gs [Hpass Hrest] Htail]; subst g gs.
      destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
        injection Hstep as <-; split; [exact Hrest|exact Htail|exact Hpass|].
      constructor; [exact (conj Hpass Hrest)|exact Htail].
  - autorewrite with galois_cost in Hstep; injection Hstep as <-; split; [|exact Hfs].
    cbn [Nested.scheduled] in Hp; cbn [Nested.State.pointer]; lia.
  - injection Hstep as <-; split.
    + cbn [Nested.State.pointer Nested.scheduled]; cbn [Nested.scheduled] in Hp; lia.
    + constructor; [|exact Hfs]; cbn [Nested.Frame.pass Nested.Frame.head Nested.Frame.body
        Nested.Frame.rest Nested.scheduled]; cbn [Nested.scheduled] in Hp; split; lia.
Qed.

(** Administrative transitions do not add any row evaluations to the remaining work. *)
Theorem administrative_eval_work s next :
  Nested.State.ready s = [] -> Nested.step a root ix hs delay s = inl next ->
  Nested.State.evals next = Nested.State.evals s /\ eval_work next = eval_work s.
Proof.
  intros Hready Hstep; unfold Nested.step, Nested.step_c in Hstep; rewrite Hready in Hstep.
  destruct (Nested.State.pointer s) as [|x rest|h body rest] eqn:Hptr.
  - destruct (Nested.State.frames s) as [|f fs] eqn:Hframes.
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s)) eqn:Hclean;
        [discriminate|]; injection Hstep as <-; split; [reflexivity|].
      unfold eval_work, eval_credit; rewrite Hready, Hptr, Hframes, Hclean.
      cbn [Nested.State.ready Nested.State.pointer Nested.State.frames Nested.State.epoch
        Nested.State.outer suffix_evals restart_evals Nested.scheduled].
      rewrite N.eqb_refl; unfold M; lia.
    + destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s)) eqn:Hclean;
        injection Hstep as <-; split; try reflexivity;
        unfold eval_work, eval_credit; rewrite Hready, Hptr, Hframes;
        cbn [Nested.State.ready Nested.State.pointer Nested.State.frames Nested.State.epoch
          Nested.State.outer suffix_evals restart_evals Nested.scheduled
          Nested.Frame.epoch Nested.Frame.rest]; rewrite Hclean.
      * lia.
      * cbn [Nested.Frame.pass Nested.Frame.head Nested.Frame.body]; rewrite N.eqb_refl; lia.
  - autorewrite with galois_cost in Hstep; rewrite Hkey in Hstep.
    fold (contributors_of EX ix x) in Hstep.
    injection Hstep as <-; split; [reflexivity|].
    unfold eval_work; rewrite Hready, Hptr.
    cbn [Nested.State.ready Nested.State.pointer Nested.State.frames Nested.State.epoch
      Nested.State.outer Nested.scheduled length]; lia.
  - injection Hstep as <-; split; [reflexivity|].
    unfold eval_work, eval_credit; rewrite Hready, Hptr.
    cbn [Nested.State.ready Nested.State.pointer Nested.State.frames Nested.State.epoch
      Nested.State.outer suffix_evals restart_evals Nested.scheduled
      Nested.Frame.epoch Nested.Frame.rest Nested.Frame.pass Nested.Frame.head Nested.Frame.body].
    rewrite N.eqb_refl; lia.
Qed.

(** One changed evaluation can replenish at most one scheduled pass per active depth. *)
Theorem evaluation_eval_work s c rest :
  schedule_bounds s -> length (Nested.State.frames s) <= d ->
  Nested.State.ready s = c :: rest ->
  let r := Nested.updates a hs delay
    (fst (Eval.outputs (Analysis.system a) c
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Nested.State.values s))))
    (Nested.State.values s) (Nested.State.counters s) in
  let next := Nested.State.Make (fst (fst r)) (snd (fst r)) (Nested.State.pointer s)
    rest (Nested.State.frames s)
    (if snd r then N.succ (Nested.State.epoch s) else Nested.State.epoch s)
    (Nested.State.outer s) (N.succ (Nested.State.evals s)) in
  if snd r then eval_work next + 1 <= eval_work s + (d + 1) * M
  else eval_work next + 1 = eval_work s.
Proof.
  intros [_ Hfs] Hd Hready; cbn zeta.
  set (r := Nested.updates a hs delay
    (fst (Eval.outputs (Analysis.system a) c
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Nested.State.values s))))
    (Nested.State.values s) (Nested.State.counters s)).
  destruct (snd r); unfold eval_work;
    cbn [Nested.State.ready Nested.State.pointer Nested.State.frames
      Nested.State.epoch Nested.State.outer]; rewrite Hready; cbn [length].
  - pose proof (eval_credit_bound (N.succ (Nested.State.epoch s))
      (Nested.State.outer s) (Nested.State.frames s) Hfs); nia.
  - lia.
Qed.

End EvaluationGeometry.

Section Joining.
Context {X C A : Type} (a : Analysis.t X C A) (Hl : Analysis.laws a)
  (HT : Terminates.t a) (Hjoining : Analysis.joining a) (root : Nested.code X).
Let EX := Analysis.key_enc a.
Let ix := index_system EX (Analysis.system a) (Analysis.static a).
Let hs := FinSet.of_list EX (Nested.heads root).
Let delay := N.of_nat (Policy.delay (Analysis.policy a)).
Let W := work EX ix root.
Let d := Nested.depth root.
Let capacity := length (universe a) * bound (Terminates.hgt HT).
Let B := (d + 1) * (W + 1).

(** The maintained joining invariant combines geometry, the lattice invariant and listed rows. *)
Definition valid (s : Nested.State.t X C A) : Prop :=
  control EX ix root s /\ good a HT (Nested.State.values s) /\
  incl (Nested.State.ready s) (System.constraints (Analysis.system a)).

(** Rank capacity pays for every restart flag an evaluation can set. *)
Definition potential (s : Nested.State.t X C A) : nat :=
  B * (capacity - rank_sum a HT (Nested.State.values s)) + admin EX ix root s.

(** Initial fuel credit includes every syntax transition and ready row dispatch. *)
Definition fuel_budget : nat := (W + 1) * (1 + (d + 1) * capacity).

Local Lemma start_valid : valid (Nested.start root).
Proof.
  split; [apply start_control|]; split; [apply good_empty|].
  intros c Hin; contradiction.
Qed.

Local Lemma start_potential : potential (Nested.start root) <= fuel_budget.
Proof.
  unfold potential; rewrite start_admin.
  unfold fuel_budget, B; nia.
Qed.

(** Every actual joining continuation decreases the combined frame and rank potential. *)
Theorem joining_step s next :
  valid s -> Nested.step a root ix hs delay s = inl next ->
  valid next /\ potential next < potential s.
Proof.
  intros [Hcontrol [Hg Hlisted]] Hstep.
  pose proof (step_control EX ix root a hs delay s next Hcontrol Hstep) as Hcontrol'.
  pose proof Hstep as Htransition.
  split; [split; [exact Hcontrol'|]|].
  all: unfold Nested.step, Nested.step_c in Hstep;
    destruct (Nested.State.ready s) as [|c rest] eqn:Hready.
  - assert (Hmap : Nested.State.values next = Nested.State.values s).
    { destruct (administrative_progress EX ix root a hs delay eq_refl s next
        Hcontrol Hready Htransition) as [Hmap Hadmin]; exact Hmap. }
    split; [now rewrite Hmap|].
    destruct (Nested.State.pointer s);
      [destruct (Nested.State.frames s) as [|f fs];
        [destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s))|
         destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s))]| |];
      autorewrite with galois_cost in Hstep; try discriminate;
      injection Hstep as <-; cbn; try (intros row Hrow; contradiction).
    intros row Hrow.
    exact (proj1 (proj1 (contributors_agree
      (index_system_laws EX (Analysis.key_laws Hl) _ _) _ row) Hrow)).
  - autorewrite with galois_cost in Hstep.
    rewrite (Eval.outputs_c_spec (Analysis.system a) c _
      (lookup EX (Analysis.lat a) (Nested.State.values s))) in Hstep by reflexivity.
    fold (Nested.updates a hs delay
      (fst (Eval.outputs (Analysis.system a) c
        (lookup EX (Analysis.lat a) (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)) in Hstep.
    injection Hstep as <-; split.
    + exact (proj1 (evaluation_progress a Hl HT hs delay c
        (Nested.State.values s) (Nested.State.counters s) Hjoining Hg
        (Hlisted c (or_introl eq_refl)))).
    + intros row Hrow; apply Hlisted; now right.
  - pose proof (administrative_progress EX ix root a hs delay eq_refl s next
      Hcontrol Hready Htransition) as [Hmap Hadmin].
    unfold potential; rewrite Hmap; lia.
  - assert (Hc : In c (System.constraints (Analysis.system a))).
    { apply Hlisted; now left. }
    pose proof (evaluation_progress a Hl HT hs delay c
      (Nested.State.values s) (Nested.State.counters s) Hjoining Hg Hc) as Hprogress.
    pose proof (evaluation_admin EX ix root a hs delay s c rest Hcontrol Hready) as Hadmin.
    autorewrite with galois_cost in Hstep.
    rewrite (Eval.outputs_c_spec (Analysis.system a) c _
      (lookup EX (Analysis.lat a) (Nested.State.values s))) in Hstep by reflexivity.
    fold (Nested.updates a hs delay
      (fst (Eval.outputs (Analysis.system a) c
        (lookup EX (Analysis.lat a) (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)) in Hstep.
    injection Hstep as <-.
    cbn zeta in Hprogress, Hadmin.
    fold EX in Hprogress, Hadmin.
    set (r := Nested.updates a hs delay
      (fst (Eval.outputs (Analysis.system a) c
        (lookup EX (Analysis.lat a) (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)) in *.
    destruct Hprogress as [Hgood [Hnondecreasing Hstrict]].
    pose proof (rank_bound a HT _ Hg) as Hold.
    pose proof (rank_bound a HT _ Hgood) as Hnew.
    change (B * (capacity - rank_sum a HT (fst (fst r))) +
      admin EX ix root
        (Nested.State.Make (fst (fst r)) (snd (fst r)) (Nested.State.pointer s) rest
          (Nested.State.frames s)
          (if snd r then N.succ (Nested.State.epoch s) else Nested.State.epoch s)
          (Nested.State.outer s) (N.succ (Nested.State.evals s))) <
      B * (capacity - rank_sum a HT (Nested.State.values s)) + admin EX ix root s).
    destruct (snd r) eqn:Hchanged.
    + specialize (Hstrict eq_refl); unfold B, capacity in *; nia.
    + unfold B, capacity in *; nia.
Qed.

Local Lemma exhausted_progress n s last :
  runs (Nested.step_c a root ix hs delay) n s (inl last) -> valid s ->
  valid last /\ potential last + n <= potential s.
Proof.
  intro Hrun; remember (inl last) as result eqn:Hresult.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH]; intro HI.
  - injection Hresult as <-; split; [exact HI|lia].
  - discriminate.
  - destruct (joining_step s next HI Hnext) as [Hvalid Hless].
    destruct (IH Hresult Hvalid) as [Hlast Hbound]; split; [exact Hlast|lia].
Qed.

(** More fuel than the proved initial potential forces the real nested iterator to stop. *)
Theorem nested_fuel_enough fuel :
  Nested.code_ok a root -> fuel_budget < Pos.to_nat fuel ->
  exists m, Nested.run a root fuel = Outcome.Solved m.
Proof.
  intros [Hcover Hcuts] Hfuel.
  rewrite Nested.run_equation.
  rewrite (proj2 (NestedProof.cover_spec a root (Analysis.key_laws Hl)) Hcover).
  fold EX ix hs delay.
  pose proof (iterate_value (Nested.step_c a root ix hs delay) fuel
    (Nested.start root)) as Hrun.
  destruct (Cost.value (iterate _ _ _)) as [last|done].
  - destruct (exhausted_progress _ _ _ Hrun start_valid) as [_ Hbound].
    pose proof start_potential; lia.
  - exists done; reflexivity.
Qed.

(** Joining termination supplies a concrete adequate fuel threshold for the actual engine. *)
Theorem nested_adequate :
  Nested.code_ok a root ->
  exists fuel m, Nested.run a root fuel = Outcome.Solved m.
Proof.
  intro Hcode; exists (Pos.of_succ_nat fuel_budget).
  apply nested_fuel_enough; [exact Hcode|rewrite SuccNat2Pos.id_succ; lia].
Qed.

Let M := Nested.scheduled EX ix root.
Let EB := (d + 1) * M.

Definition eval_potential (s : Nested.State.t X C A) :=
  EB * (capacity - rank_sum a HT (Nested.State.values s)) + eval_work EX ix root s.

(** The exact occurrence budget allows repeated vertices, row entries and side contributors. *)
Definition eval_budget := M * (1 + (d + 1) * capacity).

Local Lemma count_step s next :
  valid s -> schedule_bounds EX ix root s ->
  Nested.step a root ix hs delay s = inl next ->
  schedule_bounds EX ix root next /\
  N.to_nat (Nested.State.evals next) + eval_potential next <=
    N.to_nat (Nested.State.evals s) + eval_potential s.
Proof.
  intros [Hcontrol [Hg Hlisted]] Hschedule Hstep.
  split; [exact (step_schedule_bounds EX ix root a hs delay s next Hschedule Hstep)|].
  pose proof Hstep as Htransition.
  unfold Nested.step, Nested.step_c in Hstep.
  destruct (Nested.State.ready s) as [|c rest] eqn:Hready.
  - destruct (administrative_progress EX ix root a hs delay eq_refl s next
      Hcontrol Hready Htransition) as [Hmap Hadmin].
    destruct (administrative_eval_work EX ix root a hs delay eq_refl s next
      Hready Htransition) as [Hevals Hwork].
    unfold eval_potential; rewrite Hmap, Hevals, Hwork; lia.
  - assert (Hc : In c (System.constraints (Analysis.system a))) by
      (apply Hlisted; now left).
    pose proof (evaluation_progress a Hl HT hs delay c
      (Nested.State.values s) (Nested.State.counters s) Hjoining Hg Hc) as Hprogress.
    assert (Hdepth : length (Nested.State.frames s) <= d).
    { destruct Hcontrol as [_ [Hd Hfs]]; unfold d; lia. }
    pose proof (evaluation_eval_work EX ix root a hs delay s c rest
      Hschedule Hdepth Hready) as Hwork.
    autorewrite with galois_cost in Hstep.
    rewrite (Eval.outputs_c_spec (Analysis.system a) c _
      (lookup EX (Analysis.lat a) (Nested.State.values s))) in Hstep by reflexivity.
    injection Hstep as <-.
    cbn zeta in Hprogress, Hwork; fold EX in Hprogress, Hwork.
    set (r := Nested.updates a hs delay
      (fst (Eval.outputs (Analysis.system a) c
        (lookup EX (Analysis.lat a) (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)) in *.
    destruct Hprogress as [Hgood [Hnondecreasing Hstrict]].
    pose proof (rank_bound a HT _ Hg) as Hold.
    pose proof (rank_bound a HT _ Hgood) as Hnew.
    change (N.to_nat (N.succ (Nested.State.evals s)) +
      (EB * (capacity - rank_sum a HT (fst (fst r))) +
        eval_work EX ix root
          (Nested.State.Make (fst (fst r)) (snd (fst r)) (Nested.State.pointer s) rest
            (Nested.State.frames s)
            (if snd r then N.succ (Nested.State.epoch s) else Nested.State.epoch s)
            (Nested.State.outer s) (N.succ (Nested.State.evals s)))) <=
      N.to_nat (Nested.State.evals s) +
        (EB * (capacity - rank_sum a HT (Nested.State.values s)) + eval_work EX ix root s)).
    rewrite N2Nat.inj_succ.
    destruct (snd r).
    + specialize (Hstrict eq_refl); unfold EB, capacity, M, d in *; nia.
    + unfold EB, capacity, M, d in *; nia.
Qed.

Local Lemma prefix_account n last :
  runs (Nested.step_c a root ix hs delay) n (Nested.start root) (inl last) ->
  N.to_nat (Nested.State.evals last) + eval_potential last <= eval_budget.
Proof.
  intro Hrun.
  set (I := fun s => valid s /\ schedule_bounds EX ix root s /\
    N.to_nat (Nested.State.evals s) + eval_potential s <= eval_budget).
  assert (Hstep : forall s, I s ->
    match Cost.value (Nested.step_c a root ix hs delay s) with
    | inl next => I next
    | inr _ => True
    end).
  { intros s [Hv [Hs Hcount]]; fold (Nested.step a root ix hs delay s).
    destruct (Nested.step a root ix hs delay s) as [next|done] eqn:Hstep; [|constructor].
    destruct (joining_step s next Hv Hstep) as [Hvalid Hless].
    destruct (count_step s next Hv Hs Hstep) as [Hschedule Hbound].
    split; [exact Hvalid|]; split; [exact Hschedule|lia]. }
  assert (Hstart : I (Nested.start root)).
  { split; [exact start_valid|]; split; [apply start_schedule_bounds|].
    unfold eval_potential; rewrite start_eval_work.
    change (0 + (EB * (capacity - rank_sum a HT Map.empty) + M) <= eval_budget).
    unfold eval_budget, EB; nia. }
  exact (proj2 (proj2 (NestedProof.runs_property _ I (fun _ => True)
    Hstep _ _ _ Hrun Hstart))).
Qed.

(** Every actual continuation prefix has at most M times the depth-height occurrence factor. *)
Theorem nested_prefix_evals_bound n last :
  runs (Nested.step_c a root ix hs delay) n (Nested.start root) (inl last) ->
  N.to_nat (Nested.State.evals last) <= eval_budget.
Proof.
  intro Hrun; pose proof (prefix_account n last Hrun); lia.
Qed.

(** The real fueled iterator either exhausts below the bound or stops after a bounded prefix. *)
Theorem nested_evals_bound fuel :
  match Cost.value (iterate (Nested.step_c a root ix hs delay) fuel (Nested.start root)) with
  | inl last => N.to_nat (Nested.State.evals last) <= eval_budget
  | inr done =>
    exists used last, used < Pos.to_nat fuel /\
      runs (Nested.step_c a root ix hs delay) used (Nested.start root) (inl last) /\
      Nested.step a root ix hs delay last = inr done /\
      N.to_nat (Nested.State.evals last) <= eval_budget
  end.
Proof.
  pose proof (iterate_value (Nested.step_c a root ix hs delay) fuel
    (Nested.start root)) as Hrun.
  destruct (Cost.value (iterate _ _ _)) as [last|done].
  - exact (nested_prefix_evals_bound _ _ Hrun).
  - destruct (runs_inr_stop _ _ _ _ Hrun) as [used [last [Hused [Hprefix Hstop]]]].
    exists used, last; repeat split; try assumption.
    exact (nested_prefix_evals_bound _ _ Hprefix).
Qed.

(** A prefix witness restricts callback envelopes to states reached by this actual machine. *)
Definition prefix (s : Nested.State.t X C A) : Prop :=
  exists n, runs (Nested.step_c a root ix hs delay) n (Nested.start root) (inl s).

Local Lemma prefix_step s next :
  prefix s -> Nested.step a root ix hs delay s = inl next -> prefix next.
Proof.
  intros [n Hprefix] Hstep; exists (n + 1).
  eapply runs_append; [exact Hprefix|].
  eapply runs_next; [exact Hstep|apply runs_zero].
Qed.

(** Named local envelopes retain complete evaluator, update, lookup and preparation charges. *)
Record cost_model (evaluation_k bucket_k setup_k : N) : Prop := CostModel {
  evaluation_charge : forall s c rest, prefix s -> valid s ->
    Nested.State.ready s = c :: rest ->
    (Cost.ticks (Eval.outputs_c (Analysis.system a)
      (lookup_c EX (Analysis.lat a) (Nested.State.values s)) c) +
     Cost.ticks (Nested.updates_c a hs delay
       (fst (Eval.outputs (Analysis.system a) c
         (lookup EX (Analysis.lat a) (Nested.State.values s))))
       (Nested.State.values s) (Nested.State.counters s)) <= evaluation_k)%N;
  bucket_charge : forall s x rest, prefix s -> valid s ->
    Nested.State.ready s = [] -> Nested.State.pointer s = Nested.Visit x rest ->
    (Cost.ticks (contributors_of_c EX ix x) <= bucket_k)%N;
  preparation_charge :
    (Cost.ticks (Nested.vertices_c root) +
     Cost.ticks (FinSet.of_list_c EX (Nested.vertices root)) +
     Cost.ticks (Nested.cover_c a (FinSet.of_list EX (Nested.vertices root))
       (System.constraints (Analysis.system a))) +
     Cost.ticks (Nested.heads_c root) +
     Cost.ticks (FinSet.of_list_c EX (Nested.heads root)) +
     Cost.ticks (Nested.delay_c (Policy.delay (Analysis.policy a))) +
     Cost.ticks (index_system_c EX (Analysis.system a) (Analysis.static a)) <= setup_k)%N
}.

(** The per-evaluation envelope also covers bucket dispatch; binary driver charges stay separate. *)
Definition nested_k (evaluation_k bucket_k : N) : N := (evaluation_k + bucket_k)%N.

Local Lemma step_charge evaluation_k bucket_k setup_k
    (HM : cost_model evaluation_k bucket_k setup_k) s :
  prefix s -> valid s ->
  (Cost.ticks (Nested.step_c a root ix hs delay s) <= nested_k evaluation_k bucket_k)%N.
Proof.
  intros Hprefix Hv; unfold Nested.step_c.
  destruct (Nested.State.ready s) as [|c rest] eqn:Hready.
  - destruct (Nested.State.pointer s) as [|x rest|h body rest] eqn:Hptr.
    + destruct (Nested.State.frames s) as [|f fs].
      * destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s));
          cbn; unfold nested_k; lia.
      * destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
          cbn; unfold nested_k; lia.
    + autorewrite with galois_cost.
      pose proof (bucket_charge _ _ _ HM s x rest Hprefix Hv Hready Hptr).
      unfold nested_k; unfold EX in *; lia.
    + cbn; unfold nested_k; lia.
  - rewrite Cost.ticks_bind.
    rewrite (Eval.outputs_c_spec (Analysis.system a) c _
      (lookup EX (Analysis.lat a) (Nested.State.values s))) by reflexivity.
    rewrite Cost.ticks_bind, Cost.ticks_ret, N.add_0_r.
    pose proof (evaluation_charge _ _ _ HM s c rest Hprefix Hv Hready).
    unfold nested_k; unfold EX in *; lia.
Qed.

(** The full costed iterator spends the proved initial potential plus binary descent overhead. *)
Theorem nested_loop_cost fuel evaluation_k bucket_k setup_k :
  cost_model evaluation_k bucket_k setup_k ->
  (Cost.ticks (iterate (Nested.step_c a root ix hs delay) fuel (Nested.start root)) <=
    (nested_k evaluation_k bucket_k + 2) * (N.of_nat fuel_budget + 1) +
      2 * N.pos (Pos.size fuel))%N.
Proof.
  intro HM.
  assert (Hlocal : forall s, valid s /\ prefix s ->
    (Cost.ticks (Nested.step_c a root ix hs delay s) <= nested_k evaluation_k bucket_k)%N /\
    match Cost.value (Nested.step_c a root ix hs delay s) with
    | inl next => (valid next /\ prefix next) /\
      (N.of_nat (potential next) < N.of_nat (potential s))%N
    | inr _ => True
    end).
  { intros s [Hv Hp]; split; [exact (step_charge _ _ _ HM s Hp Hv)|].
    fold (Nested.step a root ix hs delay s).
    destruct (Nested.step a root ix hs delay s) as [next|done] eqn:Hstep; [|constructor].
    destruct (joining_step s next Hv Hstep) as [Hvalid Hless].
    split; [split; [exact Hvalid|exact (prefix_step s next Hp Hstep)]|lia]. }
  pose proof (iterate_cost (Nested.step_c a root ix hs delay)
    (fun s => valid s /\ prefix s) (fun s => N.of_nat (potential s))
    (nested_k evaluation_k bucket_k) fuel (Nested.start root) Hlocal
    ltac:(split; [exact start_valid|exists 0; apply runs_zero])) as Hcost.
  assert (Hstart : (N.of_nat (potential (Nested.start root)) <= N.of_nat fuel_budget)%N).
  { pose proof start_potential; lia. }
  cbn beta in Hcost; nia.
Qed.

(** Setup and the actual loop share one bound that retains arbitrary callback envelopes. *)
Theorem nested_cost fuel evaluation_k bucket_k setup_k :
  Nested.code_ok a root -> cost_model evaluation_k bucket_k setup_k ->
  (Cost.ticks (Nested.run_c a root fuel) <= setup_k +
    (nested_k evaluation_k bucket_k + 2) * (N.of_nat fuel_budget + 1) +
      2 * N.pos (Pos.size fuel))%N.
Proof.
  intros [Hcover Hcuts] HM.
  pose proof (nested_loop_cost fuel _ _ _ HM) as Hloop.
  pose proof (preparation_charge _ _ _ HM) as Hsetup.
  unfold Nested.run_c; autorewrite with galois_cost.
  rewrite Nested.vertices_equation.
  fold EX.
  fold (FinSet.of_list EX (Nested.vertices root)).
  pose proof (proj2 (NestedProof.cover_spec a root (Analysis.key_laws Hl)) Hcover) as Hcovered.
  fold EX in Hcovered; rewrite Hcovered.
  autorewrite with galois_cost; rewrite Nested.heads_equation, Nested.delay_equation.
  fold (FinSet.of_list EX (Nested.heads root)).
  fold (index_system EX (Analysis.system a) (Analysis.static a)).
  fold hs delay ix.
  nia.
Qed.

End Joining.

Section RankedPolicies.
Context {X C A : Type} (a : Analysis.t X C A) (root : Nested.code X)
  (HE : encoding_laws (Analysis.key_enc a))
  (P : assignment X A -> Map.t X N -> Prop)
  (rho : assignment X A -> Map.t X N -> nat).
Let EX := Analysis.key_enc a.
Let ix := index_system EX (Analysis.system a) (Analysis.static a).
Let hs := FinSet.of_list EX (Nested.heads root).
Let delay := N.of_nat (Policy.delay (Analysis.policy a)).
Let W := work EX ix root.
Let B := (Nested.depth root + 1) * (W + 1).

(** Local rank/debt laws concern a single listed evaluation and its real ordered update fold. *)
Record evaluation_laws : Prop := EvaluationLaws {
  invariant_empty : P Map.empty Map.empty;
  evaluation_credit : forall m counts c, P m counts ->
    In c (System.constraints (Analysis.system a)) ->
    let r := Nested.updates a hs delay
      (fst (Eval.outputs (Analysis.system a) c (lookup EX (Analysis.lat a) m))) m counts in
    P (fst (fst r)) (snd (fst r)) /\
      rho (fst (fst r)) (snd (fst r)) <= rho m counts /\
      (snd r = true -> rho (fst (fst r)) (snd (fst r)) < rho m counts)
}.

Definition ranked_state (s : Nested.State.t X C A) : Prop :=
  control EX ix root s /\ P (Nested.State.values s) (Nested.State.counters s) /\
  incl (Nested.State.ready s) (System.constraints (Analysis.system a)).

Definition ranked_potential (s : Nested.State.t X C A) :=
  B * rho (Nested.State.values s) (Nested.State.counters s) + admin EX ix root s.

(** A local evaluation credit pays for the real machine's frame restarts under any policy. *)
Theorem ranked_step (HL : evaluation_laws) s next :
  ranked_state s -> Nested.step a root ix hs delay s = inl next ->
  ranked_state next /\ ranked_potential next < ranked_potential s.
Proof.
  intros [Hcontrol [HP Hlisted]] Hstep.
  pose proof (step_control EX ix root a hs delay s next Hcontrol Hstep) as Hcontrol'.
  pose proof Hstep as Htransition.
  split; [split; [exact Hcontrol'|]|].
  all: unfold Nested.step, Nested.step_c in Hstep;
    destruct (Nested.State.ready s) as [|c rest] eqn:Hready.
  - destruct (administrative_progress EX ix root a hs delay eq_refl s next
      Hcontrol Hready Htransition) as [Hmap Hadmin].
    pose proof (administrative_counters ix root a hs delay s next
      Hready Htransition) as Hcounts.
    split; [now rewrite Hmap, Hcounts|].
    destruct (Nested.State.pointer s);
      [destruct (Nested.State.frames s) as [|f fs];
        [destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s))|
         destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s))]| |];
      autorewrite with galois_cost in Hstep; try discriminate;
      injection Hstep as <-; cbn; try (intros row Hbad; contradiction).
    intros row Hc; exact (proj1 (proj1
      (contributors_agree (index_system_laws EX HE _ _) _ row) Hc)).
  - autorewrite with galois_cost in Hstep.
    rewrite (Eval.outputs_c_spec (Analysis.system a) c _
      (lookup EX (Analysis.lat a) (Nested.State.values s))) in Hstep by reflexivity.
    injection Hstep as <-; split.
    + exact (proj1 (evaluation_credit HL (Nested.State.values s) (Nested.State.counters s)
        c HP (Hlisted c (or_introl eq_refl)))).
    + intros row Hrow; apply Hlisted; now right.
  - destruct (administrative_progress EX ix root a hs delay eq_refl s next
      Hcontrol Hready Htransition) as [Hmap Hadmin].
    pose proof (administrative_counters ix root a hs delay s next
      Hready Htransition) as Hcounts.
    unfold ranked_potential; rewrite Hmap, Hcounts; lia.
  - pose proof (evaluation_credit HL (Nested.State.values s) (Nested.State.counters s)
      c HP (Hlisted c (or_introl eq_refl))) as Hprogress.
    pose proof (evaluation_admin EX ix root a hs delay s c rest Hcontrol Hready) as Hadmin.
    autorewrite with galois_cost in Hstep.
    rewrite (Eval.outputs_c_spec (Analysis.system a) c _
      (lookup EX (Analysis.lat a) (Nested.State.values s))) in Hstep by reflexivity.
    injection Hstep as <-; cbn zeta in Hprogress, Hadmin.
    fold EX in Hprogress, Hadmin.
    set (r := Nested.updates a hs delay
      (fst (Eval.outputs (Analysis.system a) c
        (lookup EX (Analysis.lat a) (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)) in *.
    destruct Hprogress as [Hnext [Hnonincrease Hstrict]].
    change (B * rho (fst (fst r)) (snd (fst r)) +
      admin EX ix root
        (Nested.State.Make (fst (fst r)) (snd (fst r)) (Nested.State.pointer s) rest
          (Nested.State.frames s)
          (if snd r then N.succ (Nested.State.epoch s) else Nested.State.epoch s)
          (Nested.State.outer s) (N.succ (Nested.State.evals s))) <
      B * rho (Nested.State.values s) (Nested.State.counters s) + admin EX ix root s).
    destruct (snd r).
    + specialize (Hstrict eq_refl); unfold B, W in *; nia.
    + unfold B, W in *; nia.
Qed.

Local Lemma ranked_exhaustion (HL : evaluation_laws) n s last :
  runs (Nested.step_c a root ix hs delay) n s (inl last) -> ranked_state s ->
  ranked_potential last + n <= ranked_potential s.
Proof.
  intro Hrun; remember (inl last) as result eqn:Hresult.
  induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH]; intro HI.
  - injection Hresult as <-; lia.
  - discriminate.
  - destruct (ranked_step HL s next HI Hnext) as [Hvalid Hless].
    pose proof (IH Hresult Hvalid); lia.
Qed.

(** Local credit laws derive a stopping fuel threshold without assuming any whole-run bound. *)
Theorem ranked_fuel_enough (HL : evaluation_laws) fuel :
  Nested.code_ok a root ->
  (W + 1) * (1 + (Nested.depth root + 1) * rho Map.empty Map.empty) < Pos.to_nat fuel ->
  exists m, Nested.run a root fuel = Outcome.Solved m.
Proof.
  intros [Hcover Hcuts] Hfuel; rewrite Nested.run_equation.
  rewrite (proj2 (NestedProof.cover_spec a root HE) Hcover); fold EX ix hs delay.
  pose proof (iterate_value (Nested.step_c a root ix hs delay) fuel
    (Nested.start root)) as Hrun.
  destruct (Cost.value (iterate _ _ _)) as [last|done].
  - assert (HI : ranked_state (Nested.start root)).
    { split; [apply start_control|]; split; [apply (invariant_empty HL)|].
      intros c Hbad; contradiction. }
    pose proof (ranked_exhaustion HL _ _ _ Hrun HI) as Hbound.
    unfold ranked_potential in Hbound; rewrite start_admin in Hbound.
    cbn [Nested.start Nested.State.values Nested.State.counters] in Hbound.
    unfold B in Hbound; nia.
  - exists done; reflexivity.
Qed.

(** Local rank/debt progress also bounds actual widening-loop ticks without cloning the driver. *)
Theorem nested_widen_cost (HL : evaluation_laws) fuel k :
  (forall s, ranked_state s ->
    (exists n, runs (Nested.step_c a root ix hs delay) n (Nested.start root) (inl s)) ->
    (Cost.ticks (Nested.step_c a root ix hs delay s) <= k)%N) ->
  (Cost.ticks (iterate (Nested.step_c a root ix hs delay) fuel (Nested.start root)) <=
    (k + 2) * (N.of_nat ((W + 1) *
      (1 + (Nested.depth root + 1) * rho Map.empty Map.empty)) + 1) +
    2 * N.pos (Pos.size fuel))%N.
Proof.
  intro Hcost.
  set (I := fun s => ranked_state s /\
    exists n, runs (Nested.step_c a root ix hs delay) n (Nested.start root) (inl s)).
  assert (Hlocal : forall s, I s ->
    (Cost.ticks (Nested.step_c a root ix hs delay s) <= k)%N /\
    match Cost.value (Nested.step_c a root ix hs delay s) with
    | inl next => I next /\
      (N.of_nat (ranked_potential next) < N.of_nat (ranked_potential s))%N
    | inr _ => True
    end).
  { intros s [HI Hprefix]; split; [exact (Hcost s HI Hprefix)|].
    fold (Nested.step a root ix hs delay s).
    destruct (Nested.step a root ix hs delay s) as [next|done] eqn:Hstep; [|constructor].
    destruct (ranked_step HL s next HI Hstep) as [Hnext Hless].
    split; [split; [exact Hnext|]|lia].
    destruct Hprefix as [n Hprefix]; exists (n + 1).
    eapply runs_append; [exact Hprefix|].
    eapply runs_next; [exact Hstep|apply runs_zero]. }
  assert (Hstart : I (Nested.start root)).
  { split.
    - split; [apply start_control|]; split; [apply (invariant_empty HL)|].
      intros c Hbad; contradiction.
    - exists 0; apply runs_zero. }
  pose proof (iterate_cost (Nested.step_c a root ix hs delay) I
    (fun s => N.of_nat (ranked_potential s)) k fuel (Nested.start root)
    Hlocal Hstart) as Hloop.
  cbn beta in Hloop; unfold ranked_potential in Hloop; rewrite start_admin in Hloop.
  cbn [Nested.start Nested.State.values Nested.State.counters] in Hloop.
  fold W in Hloop.
  replace (B * rho Map.empty Map.empty + (W + 1)) with
    ((W + 1) * (1 + (Nested.depth root + 1) * rho Map.empty Map.empty)) in Hloop by
      (unfold B; nia).
  exact Hloop.
Qed.

(** Widening rank/debt weights give a fuel budget whose weight growth has no polynomial bound. *)
Theorem nested_widen_note (HL : evaluation_laws) {inv}
    (WR : widening_rank_on (Analysis.lat a) inv) (weight : C -> nat) fuel :
  (forall m counts, P m counts -> forall x, inv (lookup EX (Analysis.lat a) m x)) ->
  Nested.code_ok a root ->
  rho Map.empty Map.empty <=
    (1 + msum (Nested.heads root) (fun _ =>
      wrank WR (bot (Analysis.lat a)) + Policy.delay (Analysis.policy a))) *
    (1 + msum (System.constraints (Analysis.system a)) weight) ->
  (W + 1) * (1 + (Nested.depth root + 1) *
    ((1 + msum (Nested.heads root) (fun _ =>
      wrank WR (bot (Analysis.lat a)) + Policy.delay (Analysis.policy a))) *
     (1 + msum (System.constraints (Analysis.system a)) weight))) < Pos.to_nat fuel ->
  exists m, Nested.run a root fuel = Outcome.Solved m.
Proof.
  intros Hinv Hcode Hinitial Hfuel; apply (ranked_fuel_enough HL fuel Hcode); nia.
Qed.

End RankedPolicies.

End NestedCost.
Import NestedCost.
