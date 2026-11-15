(** * Fixed-budget interval computations

    The executable interval tower cuts every raw result to the endpoint budget.
    For example, an eight-bit upper endpoint of 256 becomes positive infinity.
    Builds on: CutInterval, Interval, Thresholds and ZLang. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import ValueSig IntervalSig CutIntervalSig CutInterval Interval
  ThresholdsSig Thresholds ZLang.
Import List.ListNotations.
Local Open Scope Z_scope.

Module Budget8 <: INTERVAL_CUTOFF.
  Definition bits := 8%nat.
End Budget8.
Module Raw := IntervalCode ZLangCode ThresholdsCode.
Module Cut := CutIntervalCode Budget8 ZLangCode ThresholdsCode Raw.

Example bounded_and_malformed :
  cut_raw (Cut.cut (I (Fin (-12)) (Fin 24))) = I (Fin (-12)) (Fin 24) /\
  cut_interval_ok 8 (cut_raw (Cut.cut (I (Fin (-12)) (Fin 24)))) = true /\
  cut_raw (Cut.cut (I (Fin 2) (Fin 1))) = IBot /\
  cut_raw (Cut.cut (I PosInf PosInf)) = IBot.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example outward_endpoints :
  cut_raw (Cut.cut (I (Fin 256) (Fin 300))) = I NegInf PosInf /\
  cut_raw (Cut.cut (I (Fin (-300)) (Fin (-256)))) = I NegInf PosInf /\
  cut_raw (Cut.cut (I (Fin (-256)) (Fin 10))) = I NegInf (Fin 10) /\
  cut_raw (Cut.cut (I (Fin 10) (Fin 256))) = I (Fin 10) PosInf.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example literal_and_add_overflow :
  cut_raw (Cut.forward (ZConst 256) []) = I NegInf PosInf /\
  cut_raw (Cut.forward ZAdd [Cut.cut (I (Fin 200) (Fin 200));
                             Cut.cut (I (Fin 100) (Fin 100))]) = I NegInf PosInf.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example unrestricted_threshold_is_cut :
  cut_raw (Cut.widen (ThresholdsCode.make [1000])
    (Cut.cut (I (Fin 0) (Fin 0))) (Cut.cut (I (Fin 0) (Fin 1)))) =
    I (Fin 0) PosInf.
Proof. vm_compute. reflexivity. Qed.

Example backward_overflow_keeps_operand :
  map cut_raw (Cut.backward ZAdd (Cut.cut (I (Fin 255) (Fin 255)))
    [Cut.cut (I (Fin 0) PosInf); Cut.cut (I (Fin (-255)) (Fin (-255)))]) =
  [I (Fin 0) PosInf; I (Fin (-255)) (Fin (-255))].
Proof. vm_compute. reflexivity. Qed.

Example guard_overflow_keeps_operand :
  map cut_raw (Cut.guard (ZGuardCmp Lt)
    [Cut.cut (I (Fin 255) (Fin 255)); Cut.cut (I (Fin 0) PosInf)]) =
  [I (Fin 255) (Fin 255); I (Fin 0) PosInf].
Proof. vm_compute. reflexivity. Qed.

(** The raw functional interface does not pin its carrier labels to endpoint meaning.
    This lawful two-point domain calls IBot top and every I constructor bottom. *)
Module PermutedRaw <: INTERVAL ZLang Thresholds.
  Definition t := itv.
  Definition wparam := ttree.
  Definition bot : t := I NegInf PosInf.
  Definition top : t := IBot.
  Definition is_bot (a : t) := match a with IBot => false | I _ _ => true end.
  Definition leb (a b : t) := orb (is_bot a) (negb (is_bot b)).
  Definition join (a b : t) := if is_bot a then b else a.
  Definition meet (a b : t) := if is_bot a then a else b.
  Definition widen (_ : wparam) (a b : t) := if leb b a then a else b.
  Definition narrow (_ b : t) := b.
  Definition forward (_ : ZLang.op) (_ : list t) := top.
  Definition backward (_ : ZLang.op) (_ : t) (xs : list t) := xs.
  Definition guard (_ : ZLang.guard) (xs : list t) := xs.
  Definition point (_ : itv) : option Z := None.
  Definition abst (_ : Z) : itv := top.
  Definition add (_ _ : itv) := top.
  Definition sub := add.
  Definition mul := add.
  Definition udiv := add.
  Definition urem := add.
  Definition bitand := add.
  Definition bitor := add.
  Definition shl := add.
  Definition add_back (_ : itv) (a b : itv) := (a, b).
  Definition sub_back := add_back.
  Definition mul_back := add_back.
  Definition udiv_back := add_back.
  Definition urem_back := add_back.
  Definition ult_back := add_back.
  Definition signed_split (_ : positive) (_ : itv) := [top].
  Definition cmp (_ : comparison) (_ _ : itv) := top.
  Include INTERVAL_SPEC ZLang Thresholds.
  Definition gamma (a : t) (_ : Z) := match a with IBot => True | I _ _ => False end.
  Definition wrank (_ : wparam) (_ : t) := 0%nat.

  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros []; reflexivity.
  Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [] [] [] Hab Hbc; cbv [leb is_bot orb negb] in *; congruence.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [] b Hbot; [discriminate|reflexivity].
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros []; reflexivity.
  Qed.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
  Lemma widen_ub_l : forall q a b, leb a (widen q a b) = true.
  Proof.
    intros q [] []; reflexivity.
  Qed.
  Lemma widen_ub_r : forall q a b, leb b (widen q a b) = true.
  Proof.
    intros q [] []; reflexivity.
  Qed.
  Lemma widen_stable : forall q a b, leb b a = true -> widen q a b = a.
  Proof.
    intros q a b Hle; unfold widen; now rewrite Hle.
  Qed.
  Lemma wrank_widen : forall q a b, is_bot a = false -> leb b a = false ->
    (wrank q (widen q a b) < wrank q a)%nat.
  Proof.
    intros q [] [] Hbot Hle; discriminate.
  Qed.
  Lemma wrank_widen_le : forall q a b, is_bot a = false ->
    (wrank q (widen q a b) <= wrank q a)%nat.
  Proof.
    intros; apply Nat.le_refl.
  Qed.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle; split; [apply leb_refl|exact Hle].
  Qed.
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. intros [] [] c Hle Hgamma; cbn [gamma] in *; try exact Logic.I;
    try contradiction; discriminate. Qed.
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof.
    intros c Hgamma; exact Hgamma.
  Qed.
  Lemma gamma_top : forall c, gamma top c.
  Proof.
    intro c; exact Logic.I.
  Qed.
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof.
    intros [] [] c Ha Hb; cbn [gamma] in *; try contradiction; exact Logic.I.
  Qed.
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof.
    intros [] c Hbot Hgamma; [discriminate|exact Hgamma].
  Qed.
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof.
    intros [] [] Hab Hbot; cbv [leb is_bot orb negb] in *; congruence.
  Qed.
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> ZLang.eval o cs = Some c -> gamma (forward o xs) c.
  Proof.
    intros; exact Logic.I.
  Qed.
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> ZLang.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof.
    intros o r xs cs c Hgamma; exact (fun _ _ => Hgamma).
  Qed.
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof.
    intros o r xs; induction xs; constructor; [apply leb_refl|exact IHxs].
  Qed.
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> ZLang.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof.
    intros g xs cs Hgamma; exact (fun _ => Hgamma).
  Qed.
  Lemma guard_refines : forall g xs, Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof.
    intros g xs; induction xs; constructor; [apply leb_refl|exact IHxs].
  Qed.
End PermutedRaw.

Module PermutedCut := CutIntervalCode Budget8 ZLang Thresholds PermutedRaw.

(** A fully lawful raw functional domain can invalidate the cutoff's bottom laws. *)
Example raw_functional_interface_does_not_fix_cutoff_bottom :
  PermutedCut.leb PermutedCut.bot PermutedCut.top = false /\
  PermutedCut.is_bot PermutedCut.bot = false.
Proof. split; reflexivity. Qed.
