(** * Fixed-budget integer interval operations

    Raw results are normalized and cut outward before entering the carrier.
    For example, a large upper endpoint becomes positive infinity.
    Builds on: CutIntervalSig and the shared interval operations. *)

From Stdlib Require Import List ZArith Bool.
From Argent Require Import Time Tactics Std.
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

Module CutIntervalT (C : INTERVAL_CUTOFF) (L : Z_LANGUAGE_T)
    (T : THRESHOLDS_T) (R : INTERVAL_ALL L T)
    <: CUT_INTERVAL_ALL C L T R.
  Include CutInterval C L T R.

  TimeFun cut.
  TimeFun bot.
  TimeFun top.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun forward.
  TimeFun backward.
  TimeFun guard.

  Definition size (a : t) : nat := interval_bits (cut_raw a).
  Definition wsize (q : wparam) : nat :=
    (T.depth q + 1) * (T.tree_bits q + 1) + C.bits.
  Definition wunits (_ : t) : nat := 0.
  Definition work := transfer_work.
  Definition gwork := guard_work.

  Definition c_val : N := 1%N. (* STUB *)
  Definition c_lat : N := c_val.
  Definition c_cut : N := 1%N. (* STUB *)
  Definition k_cut : N := 1%N. (* STUB *)

  (** The lattice constant pays for at least one call. *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  (** Inclusion testing costs at most the combined abstract sizes. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Joining costs at most the combined abstract sizes. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Meeting costs at most the combined abstract sizes. *)
  Lemma T_meet_le : forall a b,
    (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Bottom testing costs at most the abstract size. *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widening charges both values and the widening parameters. *)
  Lemma T_widen_le : forall q a b,
    (T_widen q a b <= c_val * N.of_nat (size a + size b + wsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Narrowing charges both abstract values. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Forward transfer is bounded by operator work. *)
  Lemma T_forward_le : forall o xs,
    (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Backward transfer charges operator work and the requested result. *)
  Lemma T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Guard transfer is bounded by guard work. *)
  Lemma T_guard_le : forall g xs,
    (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Forward results fit within the charged operator work. *)
  Lemma forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Meet results fit within the combined operand sizes. *)
  Lemma meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Join results fit within the combined operand sizes. *)
  Lemma join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widening results fit within operand and parameter sizes. *)
  Lemma widen_size : forall q a b,
    (N.of_nat (size (widen q a b)) <=
      c_val * N.of_nat (size a + size b + wsize q + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Backward results fit within charged work and request size. *)
  Lemma backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Guard results fit within the charged guard work. *)
  Lemma guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Operator work accounts for every operand size. *)
  Lemma work_sizes : forall o xs,
    fold_right Nat.add 0%nat (map size xs) <= work o xs.
  Proof. Admitted. (* STUB *)
  (** Guard work accounts for every operand size. *)
  Lemma gwork_sizes : forall g xs,
    fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
  Proof. Admitted. (* STUB *)

  (** The cutoff pays for shape comparisons and endpoint bit scans. *)
  Lemma T_cut_le : forall a,
    (T_cut a <= c_cut * N.of_nat (interval_bits a + C.bits + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The representation measure counts the largest finite endpoint. *)
  Lemma size_raw : forall a, size a = interval_bits (cut_raw a).
  Proof. Admitted. (* STUB *)
  (** The fixed cutoff bounds every value independently of operations and thresholds. *)
  Lemma size_bound : forall a, size a <= C.bits.
  Proof. Admitted. (* STUB *)
  (** Forward and backward work includes literals, list traversal and cutoff scans. *)
  Lemma work_agrees : forall o xs, work o xs = transfer_work o xs.
  Proof. Admitted. (* STUB *)
  (** Guard work includes operand traversal and cutoff scans. *)
  Lemma gwork_agrees : forall g xs, gwork g xs = guard_work g xs.
  Proof. Admitted. (* STUB *)
  (** Widening pays for unrestricted threshold values and their search paths. *)
  Lemma wsize_agrees : forall q,
    wsize q = (T.depth q + 1) * (T.tree_bits q + 1) + C.bits.
  Proof. Admitted. (* STUB *)
  (** Each finite side contributes at most one plus the threshold count. *)
  Lemma rank_bound : forall q a, wrank q a <= 2 * (length (T.vals q) + 1).
  Proof. Admitted. (* STUB *)

  (** Concrete membership uses the projected inclusive interval. *)
  Lemma F_gamma : forall a z, gamma a z <-> in_cut a z.
  Proof. Admitted. (* STUB *)
  (** Inclusion compares normalized bounded projections directly. *)
  Lemma F_leb : forall a b, leb a b = R.leb (cut_raw a) (cut_raw b).
  Proof. Admitted. (* STUB *)
  (** Bottom has the normalized empty representation. *)
  Lemma F_bot : cut_raw bot = IBot.
  Proof. Admitted. (* STUB *)
  (** Top has two infinite endpoints. *)
  Lemma F_top : cut_raw top = I NegInf PosInf.
  Proof. Admitted. (* STUB *)
  (** Bottom recognition agrees with the raw domain. *)
  Lemma F_is_bot : forall a, is_bot a = R.is_bot (cut_raw a).
  Proof. Admitted. (* STUB *)
  (** Joining cuts the raw join before it enters the bounded carrier. *)
  Lemma F_join : forall a b,
    cut_raw (join a b) = cut_interval C.bits (R.join (cut_raw a) (cut_raw b)).
  Proof. Admitted. (* STUB *)
  (** Meeting cuts the normalized raw intersection. *)
  Lemma F_meet : forall a b,
    cut_raw (meet a b) = cut_interval C.bits (R.meet (cut_raw a) (cut_raw b)).
  Proof. Admitted. (* STUB *)
  (** Every threshold parameter is accepted and its result is cut outward. *)
  Lemma F_widen : forall q a b,
    cut_raw (widen q a b) = cut_interval C.bits (R.widen q (cut_raw a) (cut_raw b)).
  Proof. Admitted. (* STUB *)
  (** Narrowing cuts the raw narrowed result. *)
  Lemma F_narrow : forall a b,
    cut_raw (narrow a b) = cut_interval C.bits (R.narrow (cut_raw a) (cut_raw b)).
  Proof. Admitted. (* STUB *)
  (** Forward transfer cuts every raw result, including constants and shifts. *)
  Lemma F_forward : forall o xs,
    cut_raw (forward o xs) = cut_interval C.bits (R.forward o (map cut_raw xs)).
  Proof. Admitted. (* STUB *)
  (** Backward transfer cuts each result in its original operand position. *)
  Lemma F_backward : forall o r xs,
    map cut_raw (backward o r xs) =
      map (cut_interval C.bits) (R.backward o (cut_raw r) (map cut_raw xs)).
  Proof. Admitted. (* STUB *)
  (** Guard refinement cuts each returned operand. *)
  Lemma F_guard : forall g xs,
    map cut_raw (guard g xs) =
      map (cut_interval C.bits) (R.guard g (map cut_raw xs)).
  Proof. Admitted. (* STUB *)
  (** Widening rank counts thresholds beyond the retained finite endpoints. *)
  Lemma F_rank : forall q a, wrank q a = R.interval_wrank q (cut_raw a).
  Proof. Admitted. (* STUB *)
  (** Normalization and outward cutoff cannot increase the raw threshold rank. *)
  Lemma F_cut_rank : forall q a,
    R.interval_wrank q (cut_interval C.bits a) <= R.interval_wrank q a.
  Proof. Admitted. (* STUB *)
  (** The total raw helper clock includes all endpoint inspections. *)
  Lemma T_cut_helper : forall a,
    (T_cut_interval C.bits a <=
      k_cut * N.of_nat (interval_bits a + C.bits + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Packing the Boolean subtype adds constant overhead to the raw cutoff helper. *)
  Lemma T_cut_pack : forall a,
    (T_cut a <= k_cut * (T_cut_interval C.bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Forward timing includes projection traversal and cutting the actual raw result. *)
  Lemma T_forward_source : forall o xs,
    (T_forward o xs <= k_cut *
      (R.T_forward o (map cut_raw xs) +
       T_cut_interval C.bits (R.forward o (map cut_raw xs)) +
       N.of_nat (length xs) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Backward timing includes every returned cutoff and both list traversals. *)
  Lemma T_backward_source : forall o r xs,
    (T_backward o r xs <= k_cut *
      (R.T_backward o (cut_raw r) (map cut_raw xs) +
       fold_right N.add 0%N
         (map (fun a => (T_cut_interval C.bits a + 1)%N)
           (R.backward o (cut_raw r) (map cut_raw xs))) +
       N.of_nat (length xs) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Guard timing includes every returned cutoff and both list traversals. *)
  Lemma T_guard_source : forall g xs,
    (T_guard g xs <= k_cut *
      (R.T_guard g (map cut_raw xs) +
       fold_right N.add 0%N
         (map (fun a => (T_cut_interval C.bits a + 1)%N)
           (R.guard g (map cut_raw xs))) + N.of_nat (length xs) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Widening timing includes cutting the threshold-selected endpoints. *)
  Lemma T_widen_source : forall q a b,
    (T_widen q a b <= k_cut *
      (R.T_widen q (cut_raw a) (cut_raw b) +
       T_cut_interval C.bits (R.widen q (cut_raw a) (cut_raw b)) + 1))%N.
  Proof. Admitted. (* STUB *)
End CutIntervalT.
