(** * Fixed-budget integer interval operations

    Raw results are normalized and cut outward before entering the carrier.
    For example, a large upper endpoint becomes positive infinity.
    Builds on: CutIntervalSig and the shared interval operations. *)

From Stdlib Require Import List ZArith Bool.
From Argent Require Import Time Std.
From Galois.Domains Require Import ValueSig IntervalSig ThresholdsSig CutIntervalSig.

Definition pack_cut (bits : nat) (raw : itv) : cut_itv bits :=
  match cut_interval_ok bits raw as ok return cut_interval_ok bits raw = ok -> cut_itv bits with
  | true => fun proof => exist _ raw proof
  | false => fun _ => exist _ IBot eq_refl
  end eq_refl.
TimeFun pack_cut.

Module CutIntervalCode (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_OPS)
    (T : THRESHOLDS_OPS) (R : INTERVAL_OPS L T) <: CUT_INTERVAL_OPS C L.
  Definition t := cut_itv C.bits.
  Definition wparam := ttree.

  Definition cut (a : itv) : t :=
    pack_cut C.bits (cut_interval C.bits a).

  Definition bot : t := exist _ IBot eq_refl.
  Definition top : t := exist _ (I NegInf PosInf) eq_refl.
  Definition leb (a b : t) := R.leb (cut_raw a) (cut_raw b).
  Definition is_bot (a : t) := R.is_bot (cut_raw a).
  Definition join (a b : t) := cut (R.join (cut_raw a) (cut_raw b)).
  Definition meet (a b : t) := cut (R.meet (cut_raw a) (cut_raw b)).
  Definition widen q (a b : t) := cut (R.widen q (cut_raw a) (cut_raw b)).
  Definition narrow (a b : t) := cut (R.narrow (cut_raw a) (cut_raw b)).
  Definition forward o (xs : list t) := cut (R.forward o (map cut_raw xs)).
  Definition backward o (r : t) (xs : list t) := map cut (R.backward o (cut_raw r) (map cut_raw xs)).
  Definition guard g (xs : list t) := map cut (R.guard g (map cut_raw xs)).
End CutIntervalCode.

Module CutInterval (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE)
    (T : THRESHOLDS) (R : INTERVAL L T) <: CUT_INTERVAL C L.
  Include CutIntervalCode C L T R.
  Include CUT_INTERVAL_SPEC C L.
  Definition gamma := in_cut.
  Definition wrank q (a : t) := R.interval_wrank q (cut_raw a).
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* STUB *)
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. Admitted. (* STUB *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof. Admitted. (* STUB *)
  Lemma gamma_top : forall c, gamma top c.
  Proof. Admitted. (* STUB *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof. Admitted. (* STUB *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted. (* STUB *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted. (* STUB *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted. (* STUB *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted. (* STUB *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted. (* STUB *)
  Lemma cut_agrees : forall a, cut_raw (cut a) = cut_interval C.bits a.
  Proof. Admitted. (* STUB *)
  Lemma carrier_invariant : forall (a : t),
    cut_shape_ok (cut_raw a) = true /\ interval_bits (cut_raw a) <= C.bits.
  Proof. Admitted. (* STUB *)
  Lemma cut_fixed : forall (a : t), cut_raw (cut (cut_raw a)) = cut_raw a.
  Proof. Admitted. (* STUB *)
  Lemma cut_sound : forall a z,
    (match a with IBot => False | I lo hi => in_bnd lo hi z end) ->
    (match cut_raw (cut a) with IBot => False | I lo hi => in_bnd lo hi z end).
  Proof. Admitted. (* STUB *)
End CutInterval.
