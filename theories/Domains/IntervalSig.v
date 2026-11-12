(** * Interval domain interfaces

    Integer intervals use infinite endpoints and threshold widening.
    For example, thresholds 0 and 8 let an increasing upper bound jump from 3 to 8.
    Builds on: ValueSig, WordSig and ThresholdsSig. *)

From Stdlib Require Import ZArith List.
From Argent Require Import Time Std BigO.
From Galois.Bits Require Import Word.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig WordSig ThresholdsSig.

Local Open Scope nat_scope.

Inductive itv : Type :=
  | IBot
  | I (lo hi : bnd).

Definition interval_finite_helper (a : itv) : option (Z * Z) :=
  match a with
  | I (Fin lo) (Fin hi) => Some (lo, hi)
  | _ => None
  end.
TimeFun interval_finite_helper.

Inductive zview :=
  | ZAdd
  | ZSub
  | ZMul
  | ZDiv
  | ZRem
  | ZAnd
  | ZOr
  | ZShl
  | ZCmp (c : comparison)
  | ZConst (z : Z)
  | ZOther.

Inductive zguardview :=
  | ZGuardCmp (c : comparison)
  | ZGuardUlt
  | ZGuardOther.

(** Viewed integer operators use their mathematical primitive on valid operands. *)
Definition zview_eval (k : zview) (xs : list Z) : option Z :=
  match k, xs with
  | ZAdd, x :: y :: nil => Some (x + y)%Z
  | ZSub, x :: y :: nil => Some (x - y)%Z
  | ZMul, x :: y :: nil => Some (x * y)%Z
  | ZDiv, x :: y :: nil =>
    if andb (0 <=? x)%Z (0 <? y)%Z then Some (x / y)%Z else None
  | ZRem, x :: y :: nil =>
    if andb (0 <=? x)%Z (0 <? y)%Z then Some (x mod y)%Z else None
  | ZAnd, x :: y :: nil => Some (Z.land x y)
  | ZOr, x :: y :: nil => Some (Z.lor x y)
  | ZShl, x :: y :: nil => if (0 <=? y)%Z then Some (Z.shiftl x y) else None
  | ZCmp c, x :: y :: nil =>
    Some (if match Z.compare x y, c with Eq, Eq | Lt, Lt | Gt, Gt => true | _, _ => false end
      then 1 else 0)%Z
  | ZConst z, nil => Some z
  | _, _ => None
  end.

TimeFun zview_eval.

(** Viewed guards compare exactly two integer operands. *)
Definition zguard_holds (k : zguardview) (xs : list Z) : Prop :=
  match k, xs with
  | ZGuardCmp c, x :: y :: nil => Z.compare x y = c
  | ZGuardUlt, x :: y :: nil => (0 <= x /\ 0 <= y /\ x < y)%Z
  | _, _ => False
  end.

Module Type Z_LANGUAGE_OPS.
  Include LANG_OPS with Definition val := Z.
  Parameter view : op -> zview.
  Parameter gview : guard -> zguardview.
End Z_LANGUAGE_OPS.

Module Type Z_LANGUAGE_BASE := Z_LANGUAGE_OPS <+ LANG_LAWS.

Module Type Z_LANGUAGE_LAWS (Import L : Z_LANGUAGE_BASE).
  (** Viewed operators agree with their integer primitive. *)
  Parameter view_eval : forall o xs,
    view o <> ZOther -> eval o xs = zview_eval (view o) xs.
  (** Viewed guards agree with their integer comparison. *)
  Parameter gview_holds : forall g xs,
    gview g <> ZGuardOther -> (holds g xs <-> zguard_holds (gview g) xs).
End Z_LANGUAGE_LAWS.

Module Type Z_LANGUAGE := Z_LANGUAGE_BASE <+ Z_LANGUAGE_LAWS.
Module Type Z_LANGUAGE_T := Z_LANGUAGE <+ LANG_TIME.

Module Type INTERVAL_SCALAR_SPEC (T : THRESHOLDS_OPS).
  Definition bound_leb (a b : bnd) : bool :=
    match a, b with
    | NegInf, _ => true
    | _, PosInf => true
    | Fin x, Fin y => Z.leb x y
    | _, _ => false
    end.
  Definition bound_min a b := if bound_leb a b then a else b.
  Definition bound_max a b := if bound_leb a b then b else a.
  Definition widen_lower ts old next :=
    if bound_leb old next then old else
      match next with
      | NegInf => NegInf
      | Fin z => match T.below ts z with Some u => Fin u | None => NegInf end
      | PosInf => PosInf
      end.
  Definition widen_upper ts old next :=
    if bound_leb next old then old else
      match next with
      | NegInf => NegInf
      | Fin z => match T.above ts z with Some u => Fin u | None => PosInf end
      | PosInf => PosInf
      end.
  Definition narrow_bound old next :=
    match old with
    | Fin _ => old
    | _ => next
    end.
  Definition interval_leb (a b : itv) :=
    match a, b with
    | IBot, _ => true
    | I _ _, IBot => false
    | I l h, I l' h' => andb (bound_leb l' l) (bound_leb h h')
    end.
  Definition interval_join (a b : itv) :=
    match a, b with
    | IBot, _ => b
    | _, IBot => a
    | I l h, I l' h' => I (bound_min l l') (bound_max h h')
    end.
  Definition interval_widen ts (a b : itv) :=
    match a, b with
    | IBot, _ => b
    | _, IBot => a
    | I l h, I l' h' => I (widen_lower ts l l') (widen_upper ts h h')
    end.
  Definition interval_narrow (a b : itv) :=
    match a, b with
    | IBot, _ => IBot
    | _, IBot => a
    | I l h, I l' h' => I (narrow_bound l l') (narrow_bound h h')
    end.
  Definition bounds_nonempty lo hi :=
    match lo, hi with
    | PosInf, _ => false
    | _, NegInf => false
    | _, _ => bound_leb lo hi
    end.
  Definition interval_meet (a b : itv) :=
    match a, b with
    | I l h, I l' h' =>
      let lo := bound_max l l' in
      let hi := bound_min h h' in
      if bounds_nonempty lo hi then I lo hi else IBot
    | _, _ => IBot
    end.
  Definition interval_finite := interval_finite_helper.
  Definition interval_singleton a :=
    match interval_finite a with
    | Some (lo, hi) => if Z.eqb lo hi then Some lo else None
    | None => None
    end.
  Definition interval_is_bot (a : itv) : bool :=
    match a with IBot => true | _ => false end.
  Definition interval_stable_widen ts a b :=
    if interval_leb b a then a else interval_widen ts a b.
End INTERVAL_SCALAR_SPEC.

Module Type INTERVAL_SCALAR_OPS (T : THRESHOLDS_OPS) := INTERVAL_SCALAR_SPEC T.

(** Raw interval size counts the largest finite endpoint. *)
Definition interval_bits (a : itv) : nat :=
  match a with
  | IBot => 0
  | I lo hi => Nat.max
      (match lo with Fin z => Z.size_nat z | _ => 0 end)
      (match hi with Fin z => Z.size_nat z | _ => 0 end)
  end.

Module Type INTERVAL_SCALAR_TIME (T : THRESHOLDS_T) (Import S : INTERVAL_SCALAR_OPS T).
  Parameter T_interval_leb T_interval_join T_interval_meet T_interval_narrow : itv -> itv -> N.
  Parameter T_interval_is_bot T_interval_singleton : itv -> N.
  Parameter T_interval_stable_widen : ttree -> itv -> itv -> N.
  Parameter c_scalar : N.
  (** Scalar inclusion charges the raw endpoint bits. *)
  Parameter T_interval_leb_le : forall a b,
    (T_interval_leb a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  (** Scalar join charges the raw endpoint bits. *)
  Parameter T_interval_join_le : forall a b,
    (T_interval_join a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  (** Scalar meet charges the raw endpoint bits. *)
  Parameter T_interval_meet_le : forall a b,
    (T_interval_meet a b <= c_scalar * N.of_nat (interval_bits a + interval_bits b + 1))%N.
  (** Scalar narrowing reads the endpoint constructors. *)
  Parameter T_interval_narrow_le : forall a b, (T_interval_narrow a b <= c_scalar)%N.
  (** Scalar bottom recognition reads the interval constructor. *)
  Parameter T_interval_is_bot_le : forall a, (T_interval_is_bot a <= c_scalar)%N.
  (** Scalar point recognition compares both finite endpoints. *)
  Parameter T_interval_singleton_le : forall a,
    (T_interval_singleton a <= c_scalar * N.of_nat (interval_bits a + 1))%N.
  (** Scalar widening pays for inclusion and the threshold search paths. *)
  Parameter T_interval_stable_widen_le : forall ts a b,
    (T_interval_stable_widen ts a b <= c_scalar * N.of_nat
      (interval_bits a + interval_bits b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1))%N.
  (** Widening selects endpoints from its operands, thresholds and infinities. *)
  Parameter interval_stable_widen_bits : forall ts a b,
    interval_bits (interval_stable_widen ts a b) <=
      interval_bits a + interval_bits b + T.tree_bits ts.
End INTERVAL_SCALAR_TIME.

Module Type INTERVAL_SCALAR_T (T : THRESHOLDS_T) :=
  INTERVAL_SCALAR_OPS T <+ INTERVAL_SCALAR_TIME T.

(** Clipping intersects a raw interval with the unsigned word range. *)
Definition interval_payload_clip (meet : itv -> itv -> itv) (w : positive) (a : itv) : itv :=
  meet a (I (Fin 0) (Fin (Word.modulus w - 1))).
TimeFun interval_payload_clip.

Module Type INTERVAL_OPS (L : Z_LANGUAGE_OPS) (T : THRESHOLDS_OPS).
  Include VALUE_DOMAIN_OPS L with Definition t := itv with Definition wparam := ttree.
  Parameter point : itv -> option Z.
  Parameter abst : Z -> itv.
  Parameter add sub mul udiv urem bitand bitor shl : itv -> itv -> itv.
  Parameter add_back sub_back mul_back udiv_back urem_back ult_back :
    itv -> itv -> itv -> itv * itv.
  Parameter signed_split : positive -> itv -> list itv.
  Parameter cmp : comparison -> itv -> itv -> itv.
End INTERVAL_OPS.

Module Type INTERVAL_SPEC (L : Z_LANGUAGE_OPS) (T : THRESHOLDS)
    (Import D : INTERVAL_OPS L T).
  Definition in_itv (a : itv) (z : Z) : Prop :=
    match a with IBot => False | I lo hi => in_bnd lo hi z end.
  Definition bnd_bits (b : bnd) : nat :=
    match b with Fin z => Z.size_nat z | _ => 0 end.
  Definition itv_bits (a : itv) : nat :=
    match a with IBot => 0 | I lo hi => Nat.max (bnd_bits lo) (bnd_bits hi) end.
  Definition count_gt (ts : ttree) (z : Z) : nat :=
    length (filter (fun u => (z <? u)%Z) (T.vals ts)).
  Definition count_lt (ts : ttree) (z : Z) : nat :=
    length (filter (fun u => (u <? z)%Z) (T.vals ts)).
  Definition interval_wrank (ts : ttree) (a : itv) : nat :=
    match a with
    | IBot => 0
    | I lo hi =>
      (match hi with
       | Fin z => 1 + count_gt ts z
       | NegInf => S (length (T.vals ts))
       | PosInf => 0
       end) +
      (match lo with
       | Fin z => 1 + count_lt ts z
       | PosInf => S (length (T.vals ts))
       | NegInf => 0
       end)
    end.
  Definition binary_work (a b : itv) : nat := (itv_bits a + itv_bits b + 1) ^ 2.
  Definition shift_cutoff (a b : itv) : itv :=
    let k := Z.of_nat (itv_bits a + itv_bits b + 1) in
    match a, b with
    | IBot, _ | _, IBot => IBot
    | I (Fin la) ha, I (Fin lb) hb =>
      if andb (0 <=? la)%Z (0 <=? lb)%Z then
        match ha, hb with
        | Fin ha, Fin hb =>
          if andb (lb <=? k)%Z (hb <=? k)%Z then
            I (Fin (Z.shiftl la lb)) (Fin (Z.shiftl ha hb))
          else I (Fin la) PosInf
        | _, _ => I (Fin la) PosInf
        end
      else I NegInf PosInf
    | _, _ => I NegInf PosInf
    end.
  Definition opt_lo (z : option Z) : bnd := match z with Some z => Fin z | None => NegInf end.
  Definition opt_hi (z : option Z) : bnd := match z with Some z => Fin z | None => PosInf end.
End INTERVAL_SPEC.

Module Type INTERVAL (L : Z_LANGUAGE) (T : THRESHOLDS) :=
  INTERVAL_OPS L T <+ INTERVAL_SPEC L T <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+
  HAS_MEET_LAWS <+ WIDENING_LAWS <+ VALUE_DOMAIN_LAWS L.

Module Type INTERVAL_TIME (L : Z_LANGUAGE_T) (T : THRESHOLDS_T)
    (Import D : INTERVAL L T).
  Include VALUE_DOMAIN_TIME L D.
  Parameter T_point : itv -> N.
  Parameter T_abst : Z -> N.
  Parameter T_add T_sub T_mul T_udiv T_urem T_bitand T_bitor T_shl : itv -> itv -> N.
  Parameter T_add_back T_sub_back T_mul_back T_udiv_back T_urem_back T_ult_back :
    itv -> itv -> itv -> N.
  Parameter T_signed_split : positive -> itv -> N.
  Parameter T_cmp : comparison -> itv -> itv -> N.
  Parameter c_interval : N.
  (** Interval size records the largest endpoint bit size. *)
  Parameter size_bits : forall a, size a = itv_bits a.
  (** Point recognition charges both endpoint comparisons. *)
  Parameter T_point_le : forall a, (T_point a <= c_interval * N.of_nat ((size a + 1)%nat))%N.
  (** A singleton interval shares its integer argument. *)
  Parameter T_abst_le : forall z, (T_abst z <= c_interval)%N.
  (** Addition charges linear endpoint arithmetic. *)
  Parameter T_add_le : forall a b, (T_add a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  (** Subtraction charges linear endpoint arithmetic. *)
  Parameter T_sub_le : forall a b, (T_sub a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  (** Multiplication has the published quadratic endpoint bound. *)
  Parameter T_mul_le : forall a b, (T_mul a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  (** Unsigned division has the published quadratic endpoint bound. *)
  Parameter T_udiv_le : forall a b, (T_udiv a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  (** Unsigned remainder has the published quadratic endpoint bound. *)
  Parameter T_urem_le : forall a b, (T_urem a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  (** Bitwise conjunction has the published quadratic endpoint bound. *)
  Parameter T_bitand_le : forall a b, (T_bitand a b <= c_interval * N.of_nat ((binary_work a
    b)%nat))%N.
  (** Bitwise disjunction has the published quadratic endpoint bound. *)
  Parameter T_bitor_le : forall a b, (T_bitor a b <= c_interval * N.of_nat ((binary_work a
    b)%nat))%N.
  (** Shift transfer has the published quadratic endpoint bound. *)
  Parameter T_shl_le : forall a b, (T_shl a b <= c_interval * N.of_nat ((binary_work a b)%nat))%N.
  (** Comparison charges linear endpoint comparisons. *)
  Parameter T_cmp_le : forall c a b, (T_cmp c a b <= c_interval * N.of_nat ((size a + size b +
    1)%nat))%N.
  (** Backward addition charges the result and both operands. *)
  Parameter T_add_back_le : forall r a b, (T_add_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  (** Backward subtraction charges the result and both operands. *)
  Parameter T_sub_back_le : forall r a b, (T_sub_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  (** Backward multiplication charges the result and both operands. *)
  Parameter T_mul_back_le : forall r a b, (T_mul_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  (** Backward unsigned division charges the result and both operands. *)
  Parameter T_udiv_back_le : forall r a b, (T_udiv_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  (** Backward unsigned remainder charges the result and both operands. *)
  Parameter T_urem_back_le : forall r a b, (T_urem_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  (** Backward comparison charges the result and both operands. *)
  Parameter T_ult_back_le : forall r a b, (T_ult_back r a b <=
    c_interval * N.of_nat (((size r + size a + size b + 1) ^ 2)%nat))%N.
  (** Signed splitting charges the width and endpoints. *)
  Parameter T_signed_split_le : forall w a, (T_signed_split w a <=
    c_interval * N.of_nat (((Pos.to_nat w + size a + 1) ^ 2)%nat))%N.
  (** Threshold widening charges a search path and endpoint bit sizes. *)
  Parameter T_widen_thresholds_le : forall ts a b, (T_widen ts a b <=
    c_interval * N.of_nat
      ((size a + size b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1)%nat))%N.
  (** Multiplication has the published quadratic endpoint bound. *)
  Parameter mul_bigO : (bigO (fun _ => True)
    (fun ab => N.of_nat ((binary_work (fst ab) (snd ab))%nat))
    (fun ab => T_mul (fst ab) (snd ab)))%N.
End INTERVAL_TIME.

Module Type INTERVAL_T (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) :=
  INTERVAL L T <+ INTERVAL_TIME L T.

Module Type INTERVAL_PLAN (L : Z_LANGUAGE_T) (T : THRESHOLDS_T)
    (Import D : INTERVAL_T L T).
  Parameter k_interval_arith k_interval_back k_interval_widen : N.
  (** Interval concretization is inclusive endpoint membership. *)
  Parameter F1_gamma : forall a z, gamma a z <-> in_itv a z.
  (** Widening uses the count of thresholds beyond each finite endpoint. *)
  Parameter F2_wrank : forall ts a, wrank ts a = interval_wrank ts a.
  (** Each endpoint contributes at most one plus the threshold count. *)
  Parameter F3_wrank_le : forall ts a, wrank ts a <= 2 * (length (T.vals ts) + 1).
  (** Raising a finite upper endpoint to its next threshold removes one rank unit. *)
  Parameter F4_count_gt : forall ts z u, In u (T.vals ts) ->
    (z < u)%Z -> count_gt ts u < count_gt ts z.
  (** Lowering a finite lower endpoint to its previous threshold removes one rank unit. *)
  Parameter F5_count_lt : forall ts z u, In u (T.vals ts) ->
    (u < z)%Z -> count_lt ts u < count_lt ts z.
  (** Widening parameter size pays for a threshold search path. *)
  Parameter F_wsize : forall ts, wsize ts = (T.depth ts + 1) * (T.tree_bits ts + 1).
  (** Shift transfer computes finite endpoints below the cutoff and a sound infinity above it. *)
  Parameter F_shl_cutoff : forall a b, shl a b = shift_cutoff a b.
  (** Viewed forward transfer dispatches to the proved interval primitives. *)
  Parameter F_forward_view : forall o xs, forward o xs =
    match L.view o, xs with
    | ZConst z, nil => abst z
    | ZAdd, a :: b :: nil => add a b
    | ZSub, a :: b :: nil => sub a b
    | ZMul, a :: b :: nil => mul a b
    | ZDiv, a :: b :: nil => udiv a b
    | ZRem, a :: b :: nil => urem a b
    | ZAnd, a :: b :: nil => bitand a b
    | ZOr, a :: b :: nil => bitor a b
    | ZShl, a :: b :: nil => shl a b
    | ZCmp c, a :: b :: nil => cmp c a b
    | _, _ => top
    end.
  (** Viewed strict guards dispatch to unsigned comparison refinement. *)
  Parameter F_guard_lt : forall g a b, L.gview g = ZGuardUlt ->
    guard g (a :: b :: nil) =
      let result := ult_back (I (Fin 1) (Fin 1)) a b in
      fst result :: snd result :: nil.
  (** Cutoff shifting keeps the published quadratic endpoint bound. *)
  Parameter T3_shl : forall a b,
    (T_shl a b <= k_interval_arith * N.of_nat (binary_work a b))%N.
  (** Addition retains every sum of represented operands. *)
  Parameter F6_add_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (add a b) (x + y).
  (** Subtraction retains every difference of represented operands. *)
  Parameter F7_sub_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (sub a b) (x - y).
  (** Multiplication retains every product of represented operands. *)
  Parameter F8_mul_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (mul a b) (x * y).
  (** Unsigned division retains each defined quotient of nonnegative operands. *)
  Parameter F9_udiv_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= x)%Z -> (0 < y)%Z -> in_itv (udiv a b) (Z.div x y).
  (** Unsigned remainder retains each defined remainder of nonnegative operands. *)
  Parameter F10_urem_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= x)%Z -> (0 < y)%Z -> in_itv (urem a b) (Z.modulo x y).
  (** Bitwise conjunction retains every represented pair of operands. *)
  Parameter F11_and_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (bitand a b) (Z.land x y).
  (** Bitwise disjunction retains every represented pair of operands. *)
  Parameter F12_or_sound : forall a b x y, in_itv a x -> in_itv b y ->
    in_itv (bitor a b) (Z.lor x y).
  (** Left shifting retains represented operands for every nonnegative shift. *)
  Parameter F13_shl_sound : forall a b x y, in_itv a x -> in_itv b y ->
    (0 <= y)%Z -> in_itv (shl a b) (Z.shiftl x y).
  (** Unsigned comparison refinement descends in both operands. *)
  Parameter F22_ult_back_lower : forall r a b,
    leb (fst (ult_back r a b)) a = true /\ leb (snd (ult_back r a b)) b = true.
  (** Comparison contains the Boolean result as zero or one. *)
  Parameter F14_cmp_sound : forall c a b x y, in_itv a x -> in_itv b y ->
    in_itv (cmp c a b) (match Z.compare x y, c with Eq, Eq | Lt, Lt | Gt, Gt => 1 | _, _ => 0 end).
  (** Signed splitting retains the signed view of every normalized word. *)
  Parameter F15_signed_split_sound : forall w a x, in_itv a x ->
    (0 <= x < 2 ^ Zpos w)%Z ->
    exists b, In b (signed_split w a) /\
      in_itv b (if (x <? 2 ^ (Zpos w - 1))%Z then x else x - 2 ^ Zpos w).
  (** Backward addition retains operands consistent with its result. *)
  Parameter F16_add_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x + y) ->
    in_itv (fst (add_back r a b)) x /\ in_itv (snd (add_back r a b)) y.
  (** Backward subtraction retains operands consistent with its result. *)
  Parameter F17_sub_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x - y) ->
    in_itv (fst (sub_back r a b)) x /\ in_itv (snd (sub_back r a b)) y.
  (** Backward multiplication retains operands consistent with its result. *)
  Parameter F18_mul_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> in_itv r (x * y) ->
    in_itv (fst (mul_back r a b)) x /\ in_itv (snd (mul_back r a b)) y.
  (** Backward division retains operands consistent with a defined unsigned quotient. *)
  Parameter F19_udiv_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 < y)%Z -> in_itv r (Z.div x y) ->
    in_itv (fst (udiv_back r a b)) x /\ in_itv (snd (udiv_back r a b)) y.
  (** Backward remainder retains operands consistent with a defined unsigned remainder. *)
  Parameter F20_urem_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 < y)%Z -> in_itv r (Z.modulo x y) ->
    in_itv (fst (urem_back r a b)) x /\ in_itv (snd (urem_back r a b)) y.
  (** Backward unsigned comparison retains operands with the specified Boolean result. *)
  Parameter F21_ult_back_sound : forall r a b x y,
    in_itv a x -> in_itv b y -> (0 <= x)%Z -> (0 <= y)%Z ->
    in_itv r (if (x <? y)%Z then 1 else 0) ->
    in_itv (fst (ult_back r a b)) x /\ in_itv (snd (ult_back r a b)) y.
  (** Endpoint arithmetic bounds multiplication before dispatch overhead. *)
  Parameter T1_mul : forall a b, (T_mul a b <= k_interval_arith * N.of_nat (binary_work a b))%N.
  (** Threshold searches bound widening before dispatch overhead. *)
  Parameter T2_widen : forall ts a b,
    (T_widen ts a b <= k_interval_widen * N.of_nat
      (size a + size b + (T.depth ts + 1) * (T.tree_bits ts + 1) + 1))%N.
End INTERVAL_PLAN.

Module Type INTERVAL_ALL (L : Z_LANGUAGE_T) (T : THRESHOLDS_T) :=
  INTERVAL_T L T <+ INTERVAL_PLAN L T.

Module Type INTERVAL_PAYLOAD (L : WORD_LANGUAGE) :=
  WORD_PAYLOAD L with Definition p := itv.
Module Type INTERVAL_PAYLOAD_T (L : WORD_LANGUAGE_T) :=
  WORD_PAYLOAD_T L with Definition p := itv.

Module Type INTERVAL_PAYLOAD_SPEC (T : THRESHOLDS) (S : INTERVAL_SCALAR_OPS T).
  Definition count_gt (ts : ttree) (z : Z) : nat :=
    length (filter (fun u => (z <? u)%Z) (T.vals ts)).
  Definition count_lt (ts : ttree) (z : Z) : nat :=
    length (filter (fun u => (u <? z)%Z) (T.vals ts)).
  Definition payload_wrank (ts : ttree) (w : positive) (a : itv) : nat :=
    match interval_payload_clip S.interval_meet w a with
    | IBot => 0
    | I lo hi =>
      (match hi with
       | Fin z => if (z =? Word.modulus w - 1)%Z then 0 else 1 + count_gt ts z
       | _ => 0
       end) +
      (match lo with
       | Fin z => if (z =? 0)%Z then 0 else 1 + count_lt ts z
       | _ => 0
       end)
    end.
End INTERVAL_PAYLOAD_SPEC.

Module Type INTERVAL_PAYLOAD_BASE (L : WORD_LANGUAGE) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) :=
  (INTERVAL_PAYLOAD L with Definition pwparam := ttree) <+ INTERVAL_PAYLOAD_SPEC T S.

Module Type INTERVAL_PAYLOAD_PINS (L : WORD_LANGUAGE) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) (Import P : INTERVAL_PAYLOAD_BASE L T S).
  (** Payload inclusion reads both operands through the word range. *)
  Parameter F_pleb : forall w a b, pleb w a b = S.interval_leb
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  (** Payload bottom recognition reads the clipped interval. *)
  Parameter F_pis_bot : forall w a, pis_bot w a =
    S.interval_is_bot (interval_payload_clip S.interval_meet w a).
  (** Payload join combines clipped operands. *)
  Parameter F_pjoin : forall w a b, pjoin w a b = S.interval_join
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  (** Payload meet combines clipped operands. *)
  Parameter F_pmeet : forall w a b, pmeet w a b = S.interval_meet
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  (** Payload widening retains stable raw values and clips unstable results. *)
  Parameter F_pwiden : forall q w a b, pwiden q w a b =
    if pleb w b a then a else interval_payload_clip S.interval_meet w
      (S.interval_stable_widen q (interval_payload_clip S.interval_meet w a)
        (interval_payload_clip S.interval_meet w b)).
  (** Payload narrowing combines clipped operands. *)
  Parameter F_pnarrow : forall w a b, pnarrow w a b = S.interval_narrow
    (interval_payload_clip S.interval_meet w a) (interval_payload_clip S.interval_meet w b).
  (** Payload rank treats unsigned word boundaries as terminal endpoints. *)
  Parameter F_pwrank : forall q w a, pwrank q w a = payload_wrank q w a.
  (** Payload bottom is the empty interval. *)
  Parameter F_pbot : forall w, pbot w = IBot.
  (** Payload top is the inclusive unsigned word range. *)
  Parameter F_ptop : forall w, ptop w = I (Fin 0) (Fin (Word.modulus w - 1)).
  (** Payload constants are wrapped singleton intervals. *)
  Parameter F_pconst : forall w z, pconst w z = I (Fin (L.wrap w z)) (Fin (L.wrap w z)).
  (** Payload points are recognized after clipping. *)
  Parameter F_ppoint : forall w a, ppoint w a =
    S.interval_singleton (interval_payload_clip S.interval_meet w a).
  (** Payload concretization intersects raw endpoints with normalized words. *)
  Parameter F_pgamma : forall w a z, pgamma w a z <-> L.is_word w z /\
    match a with IBot => False | I lo hi => in_bnd lo hi z end.
End INTERVAL_PAYLOAD_PINS.

Module Type INTERVAL_PAYLOAD_PINNED (L : WORD_LANGUAGE) (T : THRESHOLDS)
    (S : INTERVAL_SCALAR_OPS T) :=
  INTERVAL_PAYLOAD_BASE L T S <+ INTERVAL_PAYLOAD_PINS L T S.

Module Type INTERVAL_PAYLOAD_PINNED_T (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T) :=
  INTERVAL_PAYLOAD_PINNED L T S <+ WORD_PAYLOAD_TIME L.

Module Type INTERVAL_PAYLOAD_PLAN (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T) (Import P : INTERVAL_PAYLOAD_PINNED_T L T S).
  Parameter k_payload_clip : N.
  (** Payload size charges its width and the raw endpoint bits. *)
  Parameter F_psize : forall w a, psize w a = Pos.to_nat w + interval_bits a + 1.
  (** Widening parameter size charges a threshold search path. *)
  Parameter F_pwsize : forall q, pwsize q = (T.depth q + 1) * (T.tree_bits q + 1).
  (** Payload rank never exceeds the scalar threshold envelope. *)
  Parameter F_pwrank_le : forall q w a, pwrank q w a <= 2 * (length (T.vals q) + 1).
  (** Constructing the unsigned modulus charges the resulting word width. *)
  Parameter T_modulus_le : forall w,
    (Word.T_modulus w <= k_payload_clip * N.of_nat (Pos.to_nat w + 1))%N.
  (** Concrete wrapping charges the width and raw literal bits. *)
  Parameter T_wrap_le : forall w z,
    (Word.T_wrap w z <= k_payload_clip *
      N.of_nat ((Pos.to_nat w + Z.size_nat z + 1) ^ 2))%N.
  (** Clipping pays for the word bound and the raw endpoint bits. *)
  Parameter T_clip_le : forall w a,
    (T_interval_payload_clip S.interval_meet S.T_interval_meet w a <=
      k_payload_clip * N.of_nat (psize w a + 1))%N.
End INTERVAL_PAYLOAD_PLAN.

Module Type INTERVAL_PAYLOAD_ALL (L : WORD_LANGUAGE_T) (T : THRESHOLDS_T)
    (S : INTERVAL_SCALAR_T T) :=
  INTERVAL_PAYLOAD_PINNED_T L T S <+ INTERVAL_PAYLOAD_PLAN L T S.

Module Type INTERVAL_WORD_TABLE (L : WORD_LANGUAGE) (D : INTERVAL_PAYLOAD L) :=
  WORD_TABLE L D.
Module Type INTERVAL_WORD_TABLE_T (L : WORD_LANGUAGE_T) (D : INTERVAL_PAYLOAD_T L) :=
  WORD_TABLE_T L D.
