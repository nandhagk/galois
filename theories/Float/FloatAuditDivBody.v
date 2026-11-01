(** * Operand-retaining Float primitive body equations

    This file fixes finite division, rounding and every numeric one-bit alignment invocation.
    For example, a positive alignment amount executes that many successive shift-record steps.
    Builds on: Rocq SpecFloat, pinned Flocq rounding helpers and the shared fixed weights. *)

From Stdlib Require Import List NArith PArith ZArith Bool Lia Floats.SpecFloat.
From Flocq Require Import Calc.Round IEEE754.BinarySingleNaN.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

Inductive float_body_event : Type :=
  | FloatBodyCase (site : nat)
  | FloatBodyBuild (site : nat)
  | FloatBodyAdd (a b : Z)
  | FloatBodySub (a b : Z)
  | FloatBodyCompare (a b : Z)
  | FloatBodyDivide (a b : Z)
  | FloatBodyMultiply (a b : Z)
  | FloatBodyParity (value : Z)
  | FloatBodyShift (value amount : Z)
  | FloatBodyPower (base exponent : Z)
  | FloatBodyConvert (value : Z)
  | FloatBodyDigits (value : Z)
  | FloatBodyRoundChoice (rounding : mode) (negative : bool) (value : Z) (loc : location)
  | FloatBodyShiftOne (before after : shr_record).

(** Binary iterator equations retain each actual before/after record and binary-fuel case. *)
Fixpoint float_body_shift_iter (fuel : positive) (input : shr_record)
    : shr_record * list float_body_event :=
  match fuel with
  | xH =>
    let out := shr_1 input in
    (out, [FloatBodyCase 0; FloatBodyShiftOne input out])
  | xO p =>
    let '(mid, first) := float_body_shift_iter p input in
    let '(out, second) := float_body_shift_iter p mid in
    (out, FloatBodyCase 0 :: first ++ second)
  | xI p =>
    let initial := shr_1 input in
    let '(mid, first) := float_body_shift_iter p initial in
    let '(out, second) := float_body_shift_iter p mid in
    (out, [FloatBodyCase 0; FloatBodyShiftOne input initial] ++ first ++ second)
  end.

Definition float_body_exponent (prec emax value : Z) : Z * list float_body_event :=
  let precise := (value - prec)%Z in
  let minimum := emin prec emax in
  (fexp prec emax value,
    [FloatBodySub value prec; FloatBodySub 3 emax; FloatBodySub (3 - emax)%Z prec;
      FloatBodyCompare precise minimum]).

(** Alignment retains its actual numeric amount and every completed shift invocation. *)
Definition float_body_align (prec emax mantissa exponent : Z) (loc : location)
    : (shr_record * Z) * list float_body_event :=
  let record := shr_record_of_loc mantissa loc in
  let digits := Zdigits2 mantissa in
  let magnitude := (digits + exponent)%Z in
  let '(target, exponent_events) := float_body_exponent prec emax magnitude in
  let amount := (target - exponent)%Z in
  let prefix := [FloatBodyCase 1; FloatBodyBuild 2; FloatBodyDigits mantissa;
    FloatBodyAdd digits exponent] ++ exponent_events ++ [FloatBodySub target exponent;
      FloatBodyCase 3] in
  match amount with
  | Zpos p =>
    let '(out, shifts) := float_body_shift_iter p record in
    ((out, (exponent + amount)%Z), prefix ++ shifts ++
      [FloatBodyAdd exponent amount; FloatBodyBuild 4])
  | _ => ((record, exponent), prefix ++ [FloatBodyBuild 4])
  end.

Definition float_body_choice (rounding : mode) (negative : bool) (mantissa : Z) (loc : location)
    : Z * list float_body_event :=
  let increment :=
    match rounding with
    | mode_NE => round_N (negb (Z.even mantissa)) loc
    | mode_ZR => false
    | mode_DN => round_sign_DN negative loc
    | mode_UP => round_sign_UP negative loc
    | mode_NA => round_N true loc
    end in
  let prefix := [FloatBodyRoundChoice rounding negative mantissa loc; FloatBodyCase 5] in
  if increment then ((mantissa + 1)%Z, prefix ++ [FloatBodyAdd mantissa 1])
  else (mantissa, prefix).

Definition float_body_fit (prec emax : Z) (rounding : mode) (negative : bool)
    (mantissa : positive) (exponent : Z) : spec_float * list float_body_event :=
  let limit := (emax - prec)%Z in
  let prefix := [FloatBodySub emax prec; FloatBodyCompare exponent limit; FloatBodyCase 6] in
  if (exponent <=? limit)%Z then
    (S754_finite negative mantissa exponent, prefix ++ [FloatBodyBuild 7]) else
  let infinite := overflow_to_inf rounding negative in
  if infinite then
    (S754_infinity negative, prefix ++ [FloatBodyCase 8; FloatBodyCase 9; FloatBodyBuild 10])
  else
    let power := (2 ^ prec)%Z in
    let maximum := (power - 1)%Z in
    let final_exponent := (emax - prec)%Z in
    (S754_finite negative (Z.to_pos maximum) final_exponent,
      prefix ++ [FloatBodyCase 8; FloatBodyCase 9; FloatBodyPower 2 prec;
        FloatBodySub power 1; FloatBodyConvert maximum; FloatBodySub emax prec; FloatBodyBuild 7]).

(** Rounding performs both real alignments around its exact rounding choice. *)
Definition float_body_round (prec emax : Z) (rounding : mode) (negative : bool)
    (mantissa exponent : Z) (loc : location) : spec_float * list float_body_event :=
  let '((first, e1), first_trace) := float_body_align prec emax mantissa exponent loc in
  let first_mantissa := shr_m first in
  let first_loc := loc_of_shr_record first in
  let '(chosen, choice_trace) := float_body_choice rounding negative first_mantissa first_loc in
  let '((second, e2), second_trace) := float_body_align prec emax chosen e1 loc_Exact in
  let prefix := first_trace ++ [FloatBodyCase 11; FloatBodyCase 12] ++ choice_trace ++
    second_trace ++ [FloatBodyCase 13; FloatBodyCase 14] in
  match shr_m second with
  | Z0 => (S754_zero negative, prefix ++ [FloatBodyBuild 15])
  | Zpos p =>
    let '(out, fitted) := float_body_fit prec emax rounding negative p e2 in
    (out, prefix ++ fitted)
  | Zneg _ => (S754_nan, prefix ++ [FloatBodyBuild 16])
  end.

Definition float_body_location (divisor remainder : Z) : location * list float_body_event :=
  let even := Z.even divisor in
  let prefix := [FloatBodyParity divisor; FloatBodyCase 17;
    FloatBodyCompare remainder 0; FloatBodyCase 18] in
  if (remainder =? 0)%Z then (loc_Exact, prefix) else
  let twice := (2 * remainder)%Z in
  if even then
    (loc_Inexact (Z.compare twice divisor), prefix ++ [FloatBodyMultiply 2 remainder;
      FloatBodyCompare twice divisor])
  else
    let incremented := (twice + 1)%Z in
    (loc_Inexact (
      match Z.compare incremented divisor with
      | Gt => Gt
      | _ => Lt
      end),
      prefix ++ [FloatBodyMultiply 2 remainder; FloatBodyAdd twice 1;
        FloatBodyCompare incremented divisor; FloatBodyCase 19]).

(** Finite-core equations retain the actual scaling shift, dividend, divisor and location. *)
Definition float_body_core (prec emax m1 e1 m2 e2 : Z)
    : (Z * Z * location) * list float_body_event :=
  let d1 := Zdigits2 m1 in
  let d2 := Zdigits2 m2 in
  let lhs := (d1 + e1)%Z in
  let rhs := (d2 + e2)%Z in
  let input := (lhs - rhs)%Z in
  let '(desired, exponent_trace) := float_body_exponent prec emax input in
  let difference := (e1 - e2)%Z in
  let target := Z.min desired difference in
  let amount := (difference - target)%Z in
  let '(dividend, shifted) :=
    match amount with
    | Z0 => (m1, [])
    | Zpos _ => (Z.shiftl m1 amount, [FloatBodyShift m1 amount])
    | Zneg _ => (0%Z, [])
    end in
  let '(quotient, remainder) := Z.div_eucl dividend m2 in
  let '(loc, location_trace) := float_body_location m2 remainder in
  ((quotient, target, loc), [FloatBodyDigits m1; FloatBodyDigits m2;
    FloatBodyAdd d1 e1; FloatBodyAdd d2 e2; FloatBodySub lhs rhs] ++ exponent_trace ++
    [FloatBodySub e1 e2; FloatBodyCompare desired difference; FloatBodySub difference target;
      FloatBodyCase 20] ++ shifted ++ [FloatBodyDivide dividend m2; FloatBodyCase 21] ++
    location_trace).

(** All numeric leaf charges are fixed and positive on their actual operands. *)
Definition float_body_event_work (event : float_body_event) : nat :=
  match event with
  | FloatBodyAdd a b | FloatBodySub a b | FloatBodyCompare a b => audit_binary_weight a b
  | FloatBodyDivide a b => audit_divide_weight a b
  | FloatBodyMultiply a b => audit_multiply_weight a b
  | FloatBodyParity value => S (audit_z_bits value)
  | FloatBodyShift value amount => audit_shift_weight value amount
  | FloatBodyPower base exponent =>
    (1 + audit_z_bits base * S (Z.to_nat (Z.max 0 exponent)))%nat
  | FloatBodyConvert value | FloatBodyDigits value => S (audit_z_bits value)
  | FloatBodyRoundChoice rounding _ value loc =>
    ((
      match rounding with
      | mode_NE => S (audit_z_bits value)
      | _ => 1%nat
      end) +
      (
      match loc with
      | loc_Exact => 1%nat
      | _ => 2%nat
      end) + 2)%nat
  | FloatBodyShiftOne input _ =>
    (6 +
      match shr_m input with
      | Z0 => 0%nat
      | Zpos _ | Zneg _ => 1%nat
      end)%nat
  | _ => 1%nat
  end.

Definition float_body_work (events : list float_body_event) : nat :=
  fold_right (fun event total => (float_body_event_work event + total)%nat) 0%nat events.

(** Finite source correspondence retains exact finite-core output before rounding. *)
Definition float_body_core_erases_type : Prop := forall prec emax m1 e1 m2 e2,
  fst (float_body_core prec emax m1 e1 m2 e2) = SFdiv_core_binary prec emax m1 e1 m2 e2.

(** Both alignment and rounding bodies erase to the pinned numeric helpers. *)
Definition float_body_round_erases_type : Prop := forall prec emax rounding negative m e loc,
  fst (float_body_round prec emax rounding negative m e loc) =
    binary_round_aux prec emax rounding negative m e loc.

(** The actual positive shift amount is the exact number of recorded one-bit calls. *)
Definition float_body_shift_count_type : Prop := forall fuel input,
  length (filter (fun event =>
    match event with
    | FloatBodyShiftOne _ _ => true
    | _ => false
    end)
      (snd (float_body_shift_iter fuel input))) = Pos.to_nat fuel.

(** This operand-size envelope prices arbitrary numeric shift lengths independently of bit length.
  *)
Definition float_body_shift_bound_type : Prop := forall fuel input,
  (float_body_work (snd (float_body_shift_iter fuel input)) <= 10 * Pos.to_nat fuel)%nat.

(** Erasing the trace leaves the binary iterator's record. *)
Lemma float_body_shift_iter_erases : forall fuel input,
  fst (float_body_shift_iter fuel input) = iter_pos shr_1 fuel input.
Proof.
  induction fuel as [fuel IH | fuel IH |]; intro input; cbn [float_body_shift_iter iter_pos].
  - destruct (float_body_shift_iter fuel (shr_1 input)) as [mid first] eqn:Hfirst.
    destruct (float_body_shift_iter fuel mid) as [out second] eqn:Hsecond.
    simpl in *; rewrite <- (IH (shr_1 input)), Hfirst; simpl.
    rewrite <- (IH mid), Hsecond; reflexivity.
  - destruct (float_body_shift_iter fuel input) as [mid first] eqn:Hfirst.
    destruct (float_body_shift_iter fuel mid) as [out second] eqn:Hsecond.
    simpl in *; rewrite <- (IH input), Hfirst; simpl.
    rewrite <- (IH mid), Hsecond; reflexivity.
  - reflexivity.
Qed.

(** Alignment erases to the pinned exponent adjustment. *)
Lemma float_body_align_erases : forall prec emax m e loc,
  fst (float_body_align prec emax m e loc) = shr_fexp prec emax m e loc.
Proof.
  intros prec emax m e loc.
  unfold float_body_align, float_body_exponent, shr_fexp, shr.
  destruct (fexp prec emax (Zdigits2 m + e) - e)%Z as [|p|p]; simpl; try reflexivity.
  destruct (float_body_shift_iter p (shr_record_of_loc m loc)) as [out events] eqn:Hshift.
  pose proof (float_body_shift_iter_erases p (shr_record_of_loc m loc)) as Herase.
  rewrite Hshift in Herase; simpl in Herase; now rewrite Herase.
Qed.

(** The finite-core trace erases to the pinned division helper. *)
Theorem float_body_core_erases : forall prec emax m1 e1 m2 e2 : Z,
  fst (float_body_core prec emax m1 e1 m2 e2) =
    SFdiv_core_binary prec emax m1 e1 m2 e2.
Proof.
  intros prec emax m1 e1 m2 e2.
  unfold float_body_core, float_body_exponent,
    SFdiv_core_binary, float_body_location, new_location, new_location_even, new_location_odd.
  destruct (e1 - e2 - Z.min (fexp prec emax (Zdigits2 m1 + e1 - (Zdigits2 m2 + e2)))
    (e1 - e2))%Z; cbn [fst];
    match goal with
    |- context [Z.div_eucl ?a ?b] => destruct (Z.div_eucl a b) as [q r]
    end; simpl;
    destruct (Z.even m2); destruct (r =? 0)%Z; cbn [fst]; try reflexivity;
    destruct (Z.compare (2 * r + 1) m2)%Z; reflexivity.
Qed.

(** Rounding-choice traces erase to the pinned choice function. *)
Lemma float_body_choice_erases : forall rounding negative mantissa loc,
  fst (float_body_choice rounding negative mantissa loc) =
    choice_mode rounding negative mantissa loc.
Proof.
  intros rounding negative mantissa loc.
  destruct rounding; unfold float_body_choice, choice_mode, cond_incr;
    destruct (round_N (negb (Z.even mantissa)) loc) eqn:Hnearest;
    destruct (round_sign_DN negative loc) eqn:Hdown;
    destruct (round_sign_UP negative loc) eqn:Hup;
    destruct (round_N true loc) eqn:Haway; reflexivity.
Qed.

(** Fitting traces preserve finite, infinity, and maximum-finite outcomes. *)
Lemma float_body_fit_erases : forall prec emax rounding negative mantissa exponent,
  fst (float_body_fit prec emax rounding negative mantissa exponent) =
    binary_fit_aux prec emax rounding negative mantissa exponent.
Proof.
  intros prec emax rounding negative mantissa exponent.
  unfold float_body_fit, binary_fit_aux, binary_overflow.
  destruct (exponent <=? emax - prec)%Z; simpl; try reflexivity.
  destruct (overflow_to_inf rounding negative); reflexivity.
Qed.

(** Both rounding alignments and the intervening choice erase to Flocq's helper. *)
Theorem float_body_round_erases :
  forall (prec emax : Z) (rounding : mode) (negative : bool) (m e : Z) (loc : location),
    fst (float_body_round prec emax rounding negative m e loc) =
      binary_round_aux prec emax rounding negative m e loc.
Proof.
  intros prec emax rounding negative m e loc.
  unfold float_body_round, binary_round_aux.
  destruct (float_body_align prec emax m e loc) as [[first e1] first_trace] eqn:Hfirst.
  pose proof (float_body_align_erases prec emax m e loc) as Efirst.
  rewrite Hfirst in Efirst; simpl in Efirst; rewrite <- Efirst.
  destruct (float_body_choice rounding negative (shr_m first) (loc_of_shr_record first))
    as [chosen choice_trace] eqn:Hchoice.
  pose proof (float_body_choice_erases rounding negative (shr_m first)
    (loc_of_shr_record first)) as Echoice.
  rewrite Hchoice in Echoice; simpl in Echoice; rewrite <- Echoice.
  destruct (float_body_align prec emax chosen e1 loc_Exact) as [[second e2] second_trace]
    eqn:Hsecond.
  pose proof (float_body_align_erases prec emax chosen e1 loc_Exact) as Esecond.
  rewrite Hsecond in Esecond; simpl in Esecond; rewrite <- Esecond.
  destruct (shr_m second) as [|p|p]; simpl; try reflexivity.
  destruct (float_body_fit prec emax rounding negative p e2) as [out events] eqn:Hfit.
  pose proof (float_body_fit_erases prec emax rounding negative p e2) as Efit.
  rewrite Hfit in Efit; simpl in Efit; exact Efit.
Qed.

(** Work is additive across trace segments. *)
Lemma float_body_work_app : forall first second,
  float_body_work (first ++ second) = (float_body_work first + float_body_work second)%nat.
Proof.
  unfold float_body_work; induction first as [|event rest IH]; intro second; cbn; try reflexivity.
  rewrite IH; lia.
Qed.

(** Each recorded one-bit call is counted once, even for malformed records. *)
Theorem float_body_shift_count : forall (fuel : positive) (input : shr_record),
  length (filter (fun event =>
    match event with
    | FloatBodyShiftOne _ _ => true
    | _ => false
    end)
    (snd (float_body_shift_iter fuel input))) = Pos.to_nat fuel.
Proof.
  induction fuel as [fuel IH | fuel IH |]; intro input; cbn [float_body_shift_iter].
  - destruct (float_body_shift_iter fuel (shr_1 input)) as [mid first] eqn:Hfirst.
    destruct (float_body_shift_iter fuel mid) as [out second] eqn:Hsecond.
    specialize (IH (shr_1 input)) as IFirst.
    specialize (IH mid) as ISecond.
    rewrite Hfirst in IFirst; rewrite Hsecond in ISecond; cbn in IFirst, ISecond.
    cbn; rewrite filter_app, length_app, IFirst, ISecond, Pos2Nat.inj_xI; lia.
  - destruct (float_body_shift_iter fuel input) as [mid first] eqn:Hfirst.
    destruct (float_body_shift_iter fuel mid) as [out second] eqn:Hsecond.
    specialize (IH input) as IFirst.
    specialize (IH mid) as ISecond.
    rewrite Hfirst in IFirst; rewrite Hsecond in ISecond; cbn in IFirst, ISecond.
    cbn; rewrite filter_app, length_app, IFirst, ISecond, Pos2Nat.inj_xO; lia.
  - reflexivity.
Qed.

(** Dispatch and shift costs total at most nine units per shift, less one. *)
Lemma float_body_shift_work_strong : forall fuel input,
  (float_body_work (snd (float_body_shift_iter fuel input)) + 1 <= 9 * Pos.to_nat fuel)%nat.
Proof.
  induction fuel as [fuel IH | fuel IH |]; intro input; cbn [float_body_shift_iter].
  - destruct (float_body_shift_iter fuel (shr_1 input)) as [mid first] eqn:Hfirst.
    destruct (float_body_shift_iter fuel mid) as [out second] eqn:Hsecond.
    specialize (IH (shr_1 input)) as IFirst.
    specialize (IH mid) as ISecond.
    rewrite Hfirst in IFirst; rewrite Hsecond in ISecond.
    change (float_body_work first + 1 <= 9 * Pos.to_nat fuel)%nat in IFirst.
    change (float_body_work second + 1 <= 9 * Pos.to_nat fuel)%nat in ISecond.
    change (1 + ((6 +
      match shr_m input with
      | Z0 => 0
      | _ => 1
      end) +
      float_body_work (first ++ second)) + 1 <= 9 * Pos.to_nat (xI fuel))%nat.
    rewrite float_body_work_app.
    rewrite Pos2Nat.inj_xI; destruct (shr_m input); lia.
  - destruct (float_body_shift_iter fuel input) as [mid first] eqn:Hfirst.
    destruct (float_body_shift_iter fuel mid) as [out second] eqn:Hsecond.
    specialize (IH input) as IFirst.
    specialize (IH mid) as ISecond.
    rewrite Hfirst in IFirst; rewrite Hsecond in ISecond.
    change (float_body_work first + 1 <= 9 * Pos.to_nat fuel)%nat in IFirst.
    change (float_body_work second + 1 <= 9 * Pos.to_nat fuel)%nat in ISecond.
    change (1 + float_body_work (first ++ second) + 1 <= 9 * Pos.to_nat (xO fuel))%nat.
    rewrite float_body_work_app.
    rewrite Pos2Nat.inj_xO; lia.
  - change (1 + ((6 +
      match shr_m input with
      | Z0 => 0
      | _ => 1
      end) + 0) + 1 <= 9)%nat.
    destruct input as [m r s]; destruct m; cbn; lia.
Qed.

(** Each shift and its binary dispatch fit in ten units per invocation. *)
Theorem float_body_shift_bound : forall (fuel : positive) (input : shr_record),
  (float_body_work (snd (float_body_shift_iter fuel input)) <= 10 * Pos.to_nat fuel)%nat.
Proof.
  intros fuel input.
  pose proof (float_body_shift_work_strong fuel input).
  lia.
Qed.
