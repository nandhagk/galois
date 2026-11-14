(** * Certified polyhedral states

    Fourier-Motzkin elimination tracks combinations of the input constraints.
    For example, eliminating x from x + y <= 3 and -x <= -1 gives y <= 2.
    Builds on: PolySig, LinCertSig and the concrete binary trie. *)
From Stdlib Require Import List ZArith NArith QArith Qfield Bool Lia Ring ArithRing Lqa Wf_nat.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig LinCert PolySig.
Import List.ListNotations.
Local Open Scope nat_scope.

Module Z.
  TimeFun Z.sgn.
End Z.

Module List.
  TimeFun List.find.
  TimeFun List.flat_map.
End List.

(** A strict flag belongs to an inequality and records a positive strict summand. *)
Record poly_row (X : Type) := PolyRow {
  poly_constraint : lcons X;
  poly_multipliers : list Z;
  poly_strict : bool
}.

Arguments poly_constraint {X} _.
Arguments poly_multipliers {X} _.
Arguments poly_strict {X} _.
TimeFun poly_constraint.
TimeFun poly_multipliers.
TimeFun poly_strict.

(** Repeated keys are summed before a row participates in elimination. *)
Definition poly_add_term {X} (encode : X -> positive)
    (acc : PTrieCode.t (X * Z)) (p : X * Z) : PTrieCode.t (X * Z) :=
  let key := encode (fst p) in
  let old := match PTrieCode.get key acc with Some q => snd q | None => 0%Z end in
  PTrieCode.set key (fst p, (old + snd p)%Z) acc.

TimeFun poly_add_term.

Definition poly_normal_coef {X} (encode : X -> positive) (xs : list (X * Z))
    : list (X * Z) :=
  PTrieCode.fold_values
    (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc)
    (fold_left (poly_add_term encode) xs PTrieCode.empty) nil.

TimeFun poly_normal_coef.

Definition poly_normal_row {X} (encode : X -> positive) (r : lcons X) : lcons X :=
  LCons X (poly_normal_coef encode (lhs r)) (lrel r) (rhs r).

TimeFun poly_normal_row.

Definition poly_coefficient {X} (eqb : X -> X -> bool) (x : X) (r : lcons X) : Z :=
  fold_right (fun p z => if eqb (fst p) x then (snd p + z)%Z else z) 0%Z (lhs r).

TimeFun poly_coefficient.

Definition poly_scale_coef {X} (a : Z) (xs : list (X * Z)) : list (X * Z) :=
  map (fun p => (fst p, (a * snd p)%Z)) xs.

TimeFun poly_scale_coef.

Fixpoint poly_weighted (a : Z) (ms : list Z) (b : Z) (ns : list Z) : list Z :=
  match ms, ns with
  | m :: ms, n :: ns => (a * m + b * n)%Z :: poly_weighted a ms b ns
  | _, _ => nil
  end.

TimeFun poly_weighted.

Definition poly_eq_used {X} (a : Z) (r : lcons X) : bool :=
  match lrel r with REq => true | RLe => Z.eqb a 0 end.

TimeFun poly_eq_used.

(** Only equality rows can carry a negative multiplier in an elimination step. *)
Definition poly_add_rows {X} (encode : X -> positive)
    (a : Z) (p : poly_row X) (b : Z) (q : poly_row X) : poly_row X :=
  let r := poly_constraint p in
  let s := poly_constraint q in
  PolyRow X
    (LCons X
      (poly_normal_coef encode (poly_scale_coef a (lhs r) ++ poly_scale_coef b (lhs s)))
      (if poly_eq_used a r && poly_eq_used b s then REq else RLe)
      (a * rhs r + b * rhs s)%Z)
    (poly_weighted a (poly_multipliers p) b (poly_multipliers q))
    (((0 <? a)%Z && poly_strict p) || ((0 <? b)%Z && poly_strict q)).

TimeFun poly_add_rows.

Definition poly_pad_row {X} (r : poly_row X) : poly_row X :=
  PolyRow X (poly_constraint r) (0%Z :: poly_multipliers r) (poly_strict r).

TimeFun poly_pad_row.

(** The initial multiplier vectors are the rows of the identity matrix. *)
Fixpoint poly_initial {X} (encode : X -> positive) (P : list (lcons X * bool))
    : list (poly_row X) :=
  match P with
  | nil => nil
  | p :: ps =>
    PolyRow X (poly_normal_row encode (fst p))
      (1%Z :: map (fun _ => 0%Z) ps) (snd p) ::
      map poly_pad_row (poly_initial encode ps)
  end.

TimeFun poly_initial.

Definition poly_pivot {X} (eqb : X -> X -> bool) (x : X) (r : poly_row X) : bool :=
  match lrel (poly_constraint r) with
  | REq => negb (Z.eqb (poly_coefficient eqb x (poly_constraint r)) 0)
  | RLe => false
  end.

TimeFun poly_pivot.

Definition poly_cancel {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (x : X) (p r : poly_row X) : poly_row X :=
  let a := poly_coefficient eqb x (poly_constraint p) in
  let b := poly_coefficient eqb x (poly_constraint r) in
  if Z.eqb b 0 then r
  else poly_add_rows encode (- Z.sgn a * b)%Z p (Z.abs a) r.

TimeFun poly_cancel.

(** An equality pivot eliminates directly; otherwise every opposite-sign pair is combined. *)
Definition poly_step {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (x : X) (P : list (poly_row X)) : list (poly_row X) :=
  match find (poly_pivot eqb x) P with
  | Some p => map (poly_cancel encode eqb x p) P
  | None =>
    let pos := filter (fun r => (0 <? poly_coefficient eqb x (poly_constraint r))%Z) P in
    let neg := filter (fun r => (poly_coefficient eqb x (poly_constraint r) <? 0)%Z) P in
    filter (fun r => Z.eqb (poly_coefficient eqb x (poly_constraint r)) 0) P ++
      flat_map (fun p => map (fun q =>
        poly_add_rows encode (- poly_coefficient eqb x (poly_constraint q))%Z p
          (poly_coefficient eqb x (poly_constraint p)) q) neg) pos
  end.

TimeFun poly_step.

Definition poly_variables {X} (encode : X -> positive) (P : list (lcons X)) : list X :=
  PTrieCode.fold_values (fun acc x => x :: acc)
    (fold_left (fun acc r =>
      fold_left (fun acc p => PTrieCode.set (encode (fst p)) (fst p) acc) (lhs r) acc)
      P PTrieCode.empty) nil.

TimeFun poly_variables.

Fixpoint poly_run {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (xs : list X) (P : list (poly_row X)) : list (poly_row X) :=
  match xs with
  | nil => P
  | x :: xs => poly_run encode eqb xs (poly_step encode eqb x P)
  end.

TimeFun poly_run.

Definition poly_contradiction {X} (r : poly_row X) : bool :=
  let c := poly_constraint r in
  match lhs c with
  | nil =>
    match lrel c with
    | REq => negb (Z.eqb (rhs c) 0)
    | RLe => (rhs c <? 0)%Z || (poly_strict r && (rhs c <=? 0)%Z)
    end
  | _ :: _ => false
  end.

TimeFun poly_contradiction.

Definition poly_negate {X} (r : lcons X) : lcons X :=
  LCons X (poly_scale_coef (-1)%Z (lhs r)) RLe (- rhs r)%Z.

TimeFun poly_negate.

Definition poly_substitute {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (x : X) (f : lin X) (r : lcons X) : lcons X :=
  let a := poly_coefficient eqb x r in
  LCons X
    (poly_normal_coef encode
      (filter (fun p => negb (eqb (fst p) x)) (lhs r) ++ poly_scale_coef a (coef f)))
    (lrel r) (rhs r - a * cst f)%Z.

TimeFun poly_substitute.

Definition poly_lower (z : Z) (b : bnd) : bnd :=
  match b with NegInf => Fin z | Fin n => Fin (Z.max z n) | PosInf => PosInf end.

TimeFun poly_lower.

Definition poly_upper (z : Z) (b : bnd) : bnd :=
  match b with PosInf => Fin z | Fin n => Fin (Z.min z n) | NegInf => NegInf end.

TimeFun poly_upper.

(** Positive division by one returns the original numerator and zero remainder. *)
Lemma poly_pos_div_one : forall p, Z.pos_div_eucl p 1 = (Z.pos p, 0%Z).
Proof.
  intro p. induction p as [p IH|p IH|]; cbn [Z.pos_div_eucl];
    rewrite ?IH; reflexivity.
Qed.

(** Appending a one bit to a doubled positive integer has constant addition cost. *)
Lemma T_poly_add_low_bit : forall p, (Z.T_add (2 * Z.pos p) 1 <= 4)%N.
Proof.
  intro p. change (Z.T_add (Z.pos (xO p)) 1 <= 4)%N.
  time_unfold Z.T_add. time_unfold Pos.T_add. cbn. lia.
Qed.

(** The positive unit-divisor loop costs a fixed amount per numerator bit. *)
Lemma T_poly_pos_div_one : forall p,
  (Z.T_pos_div_eucl p 1 <= 32 * N.of_nat (Pos.size_nat p))%N.
Proof.
  intro p. induction p as [p IH|p IH|].
  - time_unfold Z.T_pos_div_eucl. rewrite poly_pos_div_one.
    cbn [fst snd].
    pose proof (Z.T_mul_two_le (Z.pos p)) as Hdouble.
    pose proof (T_poly_add_low_bit p) as Hbit.
    cbn [Pos.size_nat]. rewrite Nat2N.inj_succ. time_simpl.
    change (2 * 0)%Z with 0%Z. change (0 + 1)%Z with 1%Z.
    change (1 <? 1)%Z with false. cbn [fst].
    change (Z.T_mul 2 0) with 1%N. change (Z.T_add 0 1) with 1%N.
    pose proof (Z.T_ltb_le 1 1) as Hcompare.
    pose proof (Z.T_sub_le 1 1) as Hsubtract.
    change (Z.T_ltb 1 1 <= 5)%N in Hcompare.
    change (Z.T_sub 1 1 <= 9)%N in Hsubtract. nia.
  - time_unfold Z.T_pos_div_eucl. rewrite poly_pos_div_one.
    cbn [fst snd]. pose proof (Z.T_mul_two_le (Z.pos p)) as Hdouble.
    cbn [Pos.size_nat]. rewrite Nat2N.inj_succ. time_simpl.
    change (2 * 0)%Z with 0%Z. change (0 <? 1)%Z with true.
    change (Z.T_mul 2 0) with 1%N. change (Z.T_ltb 0 1) with 2%N. nia.
  - vm_compute. congruence.
Qed.

(** Signed unit division only adds constant sign-handling work to that scan. *)
Lemma T_poly_div_one : forall z,
  (Z.T_div z 1 <= 40 * (N.of_nat (Z.size_nat z) + 1))%N.
Proof.
  intros [|p|p]; time_unfold Z.T_div; time_unfold Z.T_div_eucl.
  - cbn [Z.size_nat N.of_nat]. time_simpl. lia.
  - pose proof (T_poly_pos_div_one p). cbn [Z.size_nat]. time_simpl. nia.
  - pose proof (T_poly_pos_div_one p). rewrite poly_pos_div_one.
    cbn [fst snd Z.size_nat]. pose proof (Z.T_opp_le (Z.pos p)). time_simpl. nia.
Qed.

(** Rational coefficient evaluation keeps every raw occurrence. *)
Definition poly_eval_coef_Q {X} (v : X -> Q) (xs : list (X * Z)) : Q :=
  fold_right (fun p q => (inject_Z (snd p) * v (fst p) + q)%Q) 0%Q xs.

Local Open Scope Q_scope.

(** Finite lower bounds have an attained greatest numerical endpoint. *)
Lemma poly_Q_max_member : forall (p : Q * bool) ps,
  exists m, In m (p :: ps) /\ forall q, In q (p :: ps) -> fst q <= fst m.
Proof.
  intros p ps. revert p. induction ps as [|q ps IH]; intro p.
  - exists p. split; [now left|]. intros q [Heq|Hfalse]; [subst q; apply Qle_refl|contradiction].
  - destruct (IH q) as [m [Hmember Hbound]].
    destruct (Qle_bool (fst p) (fst m)) eqn:Hcompare.
    + apply Qle_bool_iff in Hcompare. exists m. split; [now right|].
      intros r [Heq|Hin]; [subst r; exact Hcompare|now apply Hbound].
    + assert (Hreverse : fst m <= fst p).
      { assert (Hnot : ~ fst p <= fst m).
        { intro Hle. apply Qle_bool_iff in Hle. congruence. }
        pose proof (Qnot_le_lt _ _ Hnot). lra. }
      exists p. split; [now left|]. intros r [Heq|Hin].
      * subst r. apply Qle_refl.
      * eapply Qle_trans; [now apply Hbound|exact Hreverse].
Qed.

(** Finite upper bounds have an attained least numerical endpoint. *)
Lemma poly_Q_min_member : forall (p : Q * bool) ps,
  exists m, In m (p :: ps) /\ forall q, In q (p :: ps) -> fst m <= fst q.
Proof.
  intros p ps. revert p. induction ps as [|q ps IH]; intro p.
  - exists p. split; [now left|]. intros q [Heq|Hfalse]; [subst q; apply Qle_refl|contradiction].
  - destruct (IH q) as [m [Hmember Hbound]].
    destruct (Qle_bool (fst p) (fst m)) eqn:Hcompare.
    + apply Qle_bool_iff in Hcompare. exists p. split; [now left|].
      intros r [Heq|Hin]; [subst r; apply Qle_refl|].
      eapply Qle_trans; [exact Hcompare|now apply Hbound].
    + assert (Hreverse : fst m <= fst p).
      { assert (Hnot : ~ fst p <= fst m).
        { intro Hle. apply Qle_bool_iff in Hle. congruence. }
        pose proof (Qnot_le_lt _ _ Hnot). lra. }
      exists m. split; [now right|]. intros r [Heq|Hin];
        [subst r; exact Hreverse|now apply Hbound].
Qed.

(** A strict flag makes its endpoint open. *)
Definition poly_lower_at (q : Q) (bound : Q * bool) : Prop :=
  if snd bound then fst bound < q else fst bound <= q.
Definition poly_upper_at (q : Q) (bound : Q * bool) : Prop :=
  if snd bound then q < fst bound else q <= fst bound.
Definition poly_bounds_compatible (lo hi : Q * bool) : Prop :=
  if snd lo || snd hi then fst lo < fst hi else fst lo <= fst hi.

(** Pairwise compatibility of finitely many open or closed bounds gives a rational point. *)
Lemma poly_Q_interval_model : forall lowers uppers,
  (forall lo hi, In lo lowers -> In hi uppers -> poly_bounds_compatible lo hi) ->
  exists q, Forall (poly_lower_at q) lowers /\ Forall (poly_upper_at q) uppers.
Proof.
  intros [|lo lowers] [|hi uppers] Hcompatible.
  - exists 0. split; constructor.
  - destruct (poly_Q_min_member hi uppers) as [least [Hleast Hbound]].
    exists (fst least - 1). split; [constructor|].
    apply Forall_forall. intros upper Hin. specialize (Hbound upper Hin).
    unfold poly_upper_at. destruct (snd upper); lra.
  - destruct (poly_Q_max_member lo lowers) as [greatest [Hgreatest Hbound]].
    exists (fst greatest + 1). split; [|constructor].
    apply Forall_forall. intros lower Hin. specialize (Hbound lower Hin).
    unfold poly_lower_at. destruct (snd lower); lra.
  - destruct (poly_Q_max_member lo lowers) as [greatest [Hgreatest Hlower]].
    destruct (poly_Q_min_member hi uppers) as [least [Hleast Hupper]].
    pose proof (Hcompatible greatest least Hgreatest Hleast) as Hbetween.
    assert (Horder : fst greatest <= fst least).
    { unfold poly_bounds_compatible in Hbetween.
      destruct (snd greatest || snd least); lra. }
    set (q := (fst greatest + fst least) * (1#2)).
    assert (Hmidpoint : 2 * q == fst greatest + fst least).
    { unfold q. ring. }
    exists q. split; apply Forall_forall.
    + intros lower Hin. pose proof (Hlower lower Hin) as Hbound.
      pose proof (Hcompatible lower least Hin Hleast) as Hstrict.
      unfold poly_lower_at. destruct (snd lower) eqn:Hflag.
      * unfold poly_bounds_compatible in Hstrict. rewrite Hflag in Hstrict.
        cbn [orb] in Hstrict. lra.
      * lra.
    + intros upper Hin. pose proof (Hupper upper Hin) as Hbound.
      pose proof (Hcompatible greatest upper Hgreatest Hin) as Hstrict.
      unfold poly_upper_at. destruct (snd upper) eqn:Hflag.
      * unfold poly_bounds_compatible in Hstrict. rewrite Hflag, orb_true_r in Hstrict. lra.
      * lra.
Qed.

Local Close Scope Q_scope.

(** Magnitude is used only to prove binary-size bounds. *)
Definition poly_magnitude (z : Z) : nat := Z.to_nat (Z.abs z).

(** An integer magnitude is strictly below the power determined by its binary width. *)
Lemma poly_magnitude_upper : forall z, poly_magnitude z < 2 ^ Z.size_nat z.
Proof.
  intros [|p|p].
  - change (0 < 1). lia.
  - exact (Pos.size_nat_upper p).
  - exact (Pos.size_nat_upper p).
Qed.

(** A strict power-of-two bound bounds an integer's binary width. *)
Lemma poly_size_least : forall z k, poly_magnitude z < 2 ^ k -> Z.size_nat z <= k.
Proof.
  intros [|p|p] k Hbound; cbn [poly_magnitude Z.abs Z.to_nat Z.size_nat] in *;
    try lia; now apply Pos.size_nat_least.
Qed.

(** The magnitude of a sum is at most the sum of its magnitudes. *)
Lemma poly_magnitude_add : forall x y,
  poly_magnitude (x + y) <= poly_magnitude x + poly_magnitude y.
Proof.
  intros x y. unfold poly_magnitude.
  rewrite <- Z2Nat.inj_add by apply Z.abs_nonneg.
  apply Z2Nat.inj_le; try apply Z.abs_nonneg; try lia.
Qed.

(** Addition uses at most one bit beyond the wider operand. *)
Lemma poly_size_add : forall x y,
  Z.size_nat (x + y) <= Nat.max (Z.size_nat x) (Z.size_nat y) + 1.
Proof.
  intros x y. apply poly_size_least.
  pose proof (poly_magnitude_upper x) as Hx.
  pose proof (poly_magnitude_upper y) as Hy.
  pose proof (poly_magnitude_add x y) as Hsum.
  set (bits := Nat.max (Z.size_nat x) (Z.size_nat y)).
  assert (Hxp : 2 ^ Z.size_nat x <= 2 ^ bits).
  { apply Nat.pow_le_mono_r; unfold bits; lia. }
  assert (Hyp : 2 ^ Z.size_nat y <= 2 ^ bits).
  { apply Nat.pow_le_mono_r; unfold bits; lia. }
  replace (bits + 1) with (S bits) by lia. rewrite Nat.pow_succ_r by lia. lia.
Qed.

(** A product uses at most the combined widths of its operands. *)
Lemma poly_size_mul : forall x y,
  Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.mul Z.size_nat]; try lia; apply Pos.size_nat_mul.
Qed.

(** Negation preserves an integer's binary width. *)
Lemma poly_size_opp : forall z, Z.size_nat (- z) = Z.size_nat z.
Proof.
  intros [|p|p]; reflexivity.
Qed.

(** Absolute value preserves an integer's binary width. *)
Lemma poly_size_abs : forall z, Z.size_nat (Z.abs z) = Z.size_nat z.
Proof.
  intros [|p|p]; reflexivity.
Qed.

(** Multiplication by a negated sign cannot increase the other operand's width. *)
Lemma poly_size_sign_mul : forall a b,
  Z.size_nat (- Z.sgn a * b) <= Z.size_nat b.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.sgn Z.opp Z.mul Z.size_nat Pos.mul]; lia.
Qed.

(** A unit-vector weighted entry uses at most one extra bit. *)
Lemma poly_unit_combination_size : forall a b m n bits,
  Z.size_nat a <= bits -> Z.size_nat b <= bits ->
  (m = 0%Z \/ m = 1%Z) -> (n = 0%Z \/ n = 1%Z) ->
  Z.size_nat (a * m + b * n) <= bits + 1.
Proof.
  intros a b m n bits Ha Hb Hm Hn.
  destruct Hm as [Hm|Hm], Hn as [Hn|Hn]; subst m n;
    rewrite ?Z.mul_0_r, ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_0_r;
    try solve [cbn [Z.size_nat]; lia].
  pose proof (poly_size_add a b). lia.
Qed.

(** Combining equal-length multiplier vectors preserves their length. *)
Lemma poly_weighted_length : forall a ms b ns,
  length ms = length ns -> length (poly_weighted a ms b ns) = length ms.
Proof.
  intros a ms. induction ms as [|m ms IH]; intros b [|n ns] Hlength;
    cbn [poly_weighted length] in *; try lia.
  f_equal. apply IH. lia.
Qed.

(** Combining two unit vectors bounds every resulting multiplier. *)
Lemma poly_weighted_units : forall a ms b ns bits,
  Z.size_nat a <= bits -> Z.size_nat b <= bits ->
  Forall (fun m => m = 0%Z \/ m = 1%Z) ms ->
  Forall (fun n => n = 0%Z \/ n = 1%Z) ns ->
  Forall (fun z => Z.size_nat z <= bits + 1) (poly_weighted a ms b ns).
Proof.
  intros a ms. induction ms as [|m ms IH]; intros b ns bits Ha Hb Hms Hns.
  - constructor.
  - destruct ns as [|n ns]; [constructor|]. cbn [poly_weighted].
    inversion Hms as [|? ? Hm Htailm]. inversion Hns as [|? ? Hn Htailn].
    constructor.
    + eapply poly_unit_combination_size; eassumption.
    + eapply IH; eassumption.
Qed.

(** Every initial multiplier vector has the input length and contains only zero or one. *)
Lemma poly_initial_units : forall A (encode : A -> positive) P,
  Forall (fun r => length (poly_multipliers r) = length P /\
    Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers r))
    (poly_initial encode P).
Proof.
  intros A encode P. induction P as [|p ps IH]; cbn [poly_initial].
  - constructor.
  - constructor.
    + cbn [poly_multipliers length]. split; [now rewrite length_map|].
      constructor; [right; reflexivity|].
      apply Forall_map, Forall_forall. intros r Hin. left. reflexivity.
    + apply Forall_map, Forall_forall. intros r Hin.
      rewrite Forall_forall in IH. destruct (IH r Hin) as [Hlength Hunit].
      cbn [poly_pad_row poly_multipliers length]. split; [lia|].
      constructor; [left; reflexivity|exact Hunit].
Qed.

(** Each stored source key agrees with the address used to find it. *)
Definition poly_addressed {A} (encode : A -> positive) (m : ptrie (A * Z)) : Prop :=
  forall key p, PTrieCode.get key m = Some p -> encode (fst p) = key.

(** An empty coefficient accumulator satisfies address agreement. *)
Lemma poly_addressed_empty : forall A (encode : A -> positive),
  poly_addressed encode PTrieCode.empty.
Proof.
  intros A encode key p Hget. rewrite PTrie.get_empty in Hget. discriminate.
Qed.

(** Accumulating one coefficient preserves agreement between keys and addresses. *)
Lemma poly_addressed_add : forall A (encode : A -> positive) m p,
  poly_addressed encode m -> poly_addressed encode (poly_add_term encode m p).
Proof.
  intros A encode m p Hwf key q Hget. unfold poly_add_term in Hget.
  destruct (Pos.eq_dec key (encode (fst p))) as [Heq|Hneq].
  - subst key. rewrite PTrie.get_set_same in Hget.
    injection Hget as Hsame. subst q. reflexivity.
  - rewrite PTrie.get_set_other in Hget by exact Hneq. exact (Hwf _ _ Hget).
Qed.

(** Accumulating a list preserves agreement between keys and addresses. *)
Lemma poly_addressed_fold : forall A (encode : A -> positive) xs m,
  poly_addressed encode m -> poly_addressed encode (fold_left (poly_add_term encode) xs m).
Proof.
  intros A encode xs. induction xs as [|p xs IH]; intros m Hwf; cbn [fold_left].
  - exact Hwf.
  - apply IH. now apply poly_addressed_add.
Qed.

(** Distinct trie addresses imply distinct source keys in an addressed accumulator. *)
Lemma poly_values_nodup : forall A (encode : A -> positive) m,
  poly_addressed encode m -> NoDup (map fst (map snd (PTrieCode.elements m))).
Proof.
  intros A encode m Hwf. apply NoDup_map_inv with (f := encode). rewrite !map_map.
  assert (Hkeys : map (fun p => encode (fst (snd p))) (PTrieCode.elements m) =
    map fst (PTrieCode.elements m)).
  { apply map_ext_in. intros [key p] Hin. cbn [fst snd].
    apply Hwf. apply (proj1 (PTrie.elements_spec _ m key p)). exact Hin. }
  rewrite Hkeys. apply PTrie.elements_nodup.
Qed.

(** Folding trie entries after projection is the same as folding their values. *)
Lemma poly_fold_values_list : forall A B (step : B -> A -> B) (xs : list (positive * A)) b,
  fold_left (fun acc p => step acc (snd p)) xs b = fold_left step (map snd xs) b.
Proof.
  intros A B step xs. induction xs as [|p xs IH]; intro b; cbn [fold_left map].
  - reflexivity.
  - apply IH.
Qed.

(** The normalization fold reverses the nonzero entries before its accumulator. *)
Lemma poly_fold_normalized : forall A (xs acc : list (A * Z)),
  fold_left (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) xs acc =
    rev (filter (fun p => negb (Z.eqb (snd p) 0)) xs) ++ acc.
Proof.
  intros A xs. induction xs as [|p xs IH]; intro acc; cbn [fold_left filter].
  - reflexivity.
  - destruct (Z.eqb (snd p) 0); cbn [negb rev].
    + apply IH.
    + rewrite IH, <- app_assoc. reflexivity.
Qed.

(** Filtering preserves uniqueness after projecting each retained entry. *)
Lemma poly_nodup_map_filter : forall A B (f : A -> B) test xs,
  NoDup (map f xs) -> NoDup (map f (filter test xs)).
Proof.
  intros A B f test xs. induction xs as [|a xs IH]; intro Hunique.
  - constructor.
  - inversion Hunique as [|b bs Hnot Htail]; subst b bs.
    cbn [filter]. destruct (test a) eqn:Htest; cbn [map].
    + constructor; [|now apply IH].
      intro Hin. apply Hnot. apply in_map_iff in Hin as [p [Heq Hin]].
      apply filter_In in Hin as [Hin _]. apply in_map_iff. exists p. auto.
    + now apply IH.
Qed.

(** Normalization retains at most one coefficient for each source key. *)
Lemma poly_normal_coef_nodup : forall A (encode : A -> positive) xs,
  NoDup (map fst (poly_normal_coef encode xs)).
Proof.
  intros A encode xs. unfold poly_normal_coef.
  rewrite PTrieT.F9_fold_values.
  rewrite (poly_fold_values_list _ _
    (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) _ nil).
  rewrite poly_fold_normalized, app_nil_r, map_rev.
  apply NoDup_rev. apply poly_nodup_map_filter. apply poly_values_nodup with (encode := encode).
  apply poly_addressed_fold. apply poly_addressed_empty.
Qed.

(** Updating a coefficient preserves an old source key or stores the new source key. *)
Lemma poly_add_term_key : forall A (encode : A -> positive) m p key q,
  PTrieCode.get key (poly_add_term encode m p) = Some q ->
  fst q = fst p \/
    exists old, PTrieCode.get key m = Some old /\ fst q = fst old.
Proof.
  intros A encode m p key q Hget. unfold poly_add_term in Hget.
  destruct (Pos.eq_dec key (encode (fst p))) as [Heq|Hneq].
  - subst key. rewrite PTrie.get_set_same in Hget.
    injection Hget as Hsame. subst q. left. reflexivity.
  - rewrite PTrie.get_set_other in Hget by exact Hneq.
    right. exists q. auto.
Qed.

(** Every accumulated key comes from the input list or the initial accumulator. *)
Lemma poly_fold_keys : forall A (encode : A -> positive) xs m key q,
  PTrieCode.get key (fold_left (poly_add_term encode) xs m) = Some q ->
  In (fst q) (map fst xs) \/
    exists old, PTrieCode.get key m = Some old /\ fst q = fst old.
Proof.
  intros A encode xs. induction xs as [|p xs IH]; intros m key q Hget;
    cbn [fold_left] in Hget.
  - right. exists q. auto.
  - destruct (IH _ _ _ Hget) as [Htail|[old [Hold Hkey]]].
    + left. right. exact Htail.
    + destruct (poly_add_term_key A encode m p key old Hold)
        as [Hhead|[prior [Hprior Hprior_key]]].
      * left. left. congruence.
      * right. exists prior. split; [exact Hprior|congruence].
Qed.

(** A retained normalized term is a nonzero binding in the coefficient accumulator. *)
Lemma poly_normal_coef_lookup : forall A (encode : A -> positive) xs q,
  In q (poly_normal_coef encode xs) ->
  exists key,
    PTrieCode.get key (fold_left (poly_add_term encode) xs PTrieCode.empty) = Some q /\
    snd q <> 0%Z.
Proof.
  intros A encode xs q Hin. unfold poly_normal_coef in Hin.
  rewrite PTrieT.F9_fold_values in Hin.
  rewrite (poly_fold_values_list _ _
    (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) _ nil) in Hin.
  rewrite poly_fold_normalized, app_nil_r in Hin.
  apply (proj2 (in_rev _ _)) in Hin. apply filter_In in Hin as [Hin Hnonzero].
  apply in_map_iff in Hin as [[key p] [Heq Hin]]. cbn [snd] in Heq. subst p.
  exists key. split.
  - apply (proj1 (PTrie.elements_spec _ _ _ _)). exact Hin.
  - apply Bool.negb_true_iff in Hnonzero. now apply Z.eqb_neq.
Qed.

(** Normalization removes every coefficient whose sum is zero. *)
Lemma poly_normal_coef_nonzero : forall A (encode : A -> positive) xs q,
  In q (poly_normal_coef encode xs) -> snd q <> 0%Z.
Proof.
  intros A encode xs q Hin.
  destruct (poly_normal_coef_lookup A encode xs q Hin) as [key [_ Hnonzero]].
  exact Hnonzero.
Qed.

(** Normalization retains only keys occurring in the original coefficient list. *)
Lemma poly_normal_coef_keys : forall A (encode : A -> positive) xs q,
  In q (poly_normal_coef encode xs) -> In (fst q) (map fst xs).
Proof.
  intros A encode xs q Hin.
  destruct (poly_normal_coef_lookup A encode xs q Hin) as [key [Hget _]].
  destruct (poly_fold_keys A encode xs PTrieCode.empty key q Hget)
    as [Hkey|[old [Hold _]]]; [exact Hkey|].
  rewrite PTrie.get_empty in Hold. discriminate.
Qed.

(** Initializing tracked rows normalizes each input row without changing its position. *)
Lemma poly_initial_constraints : forall A (encode : A -> positive) P,
  map poly_constraint (poly_initial encode P) =
    map (fun p => poly_normal_row encode (fst p)) P.
Proof.
  intros A encode P. induction P as [|p ps IH]; cbn [poly_initial map poly_constraint].
  - reflexivity.
  - f_equal. rewrite map_map. exact IH.
Qed.

(** Initializing tracked rows preserves the input row count. *)
Lemma poly_initial_length : forall A (encode : A -> positive) P,
  length (poly_initial encode P) = length P.
Proof.
  intros A encode P. induction P as [|p ps IH]; cbn [poly_initial length].
  - reflexivity.
  - rewrite length_map, IH. reflexivity.
Qed.

(** Disjoint filters select at most one occurrence from each input position. *)
Lemma poly_disjoint_filters : forall A (f g : A -> bool) xs,
  (forall x, f x = true -> g x = false) ->
  length (filter f xs) + length (filter g xs) <= length xs.
Proof.
  intros A f g xs Hdisjoint. induction xs as [|x xs IH]; cbn [filter length].
  - lia.
  - destruct (f x) eqn:Hf, (g x) eqn:Hg; cbn [length]; try lia.
    rewrite (Hdisjoint x Hf) in Hg. discriminate.
Qed.

(** Two disjoint row classes form at most a quarter of the square many pairs. *)
Lemma poly_pair_count : forall a b n,
  a + b <= n -> a * b <= n ^ 2 / 4.
Proof.
  intros a b n Htotal. apply Nat.div_le_lower_bound; [lia|].
  assert (Hsquare : (a + b) ^ 2 <= n ^ 2) by (apply Nat.pow_le_mono_l; lia).
  destruct (Nat.le_ge_cases a b) as [Hab|Hba].
  - pose proof (Nat.sub_add a b Hab). cbn [Nat.pow] in *. nia.
  - pose proof (Nat.sub_add b a Hba). cbn [Nat.pow] in *. nia.
Qed.

(** One elimination keeps zero rows and forms every opposite-sign pair at most once. *)
Lemma poly_step_rows : forall A (encode : A -> positive) eqb x P,
  length (poly_step encode eqb x P) <= (length P) ^ 2 / 4 + length P.
Proof.
  intros A encode eqb x P. unfold poly_step.
  destruct (find (poly_pivot eqb x) P) as [pivot|] eqn:Hpivot.
  - rewrite length_map. lia.
  - set (pos := filter (fun r =>
      (0 <? poly_coefficient eqb x (poly_constraint r))%Z) P).
    set (neg := filter (fun r =>
      (poly_coefficient eqb x (poly_constraint r) <? 0)%Z) P).
    assert (Hclasses : length pos + length neg <= length P).
    { unfold pos, neg. apply poly_disjoint_filters. intros r Hpositive.
      apply Z.ltb_lt in Hpositive. apply Z.ltb_ge. lia. }
    pose proof (poly_pair_count _ _ _ Hclasses) as Hpairs.
    pose proof (filter_length_le
      (fun r => Z.eqb (poly_coefficient eqb x (poly_constraint r)) 0) P) as Hzero.
    rewrite length_app.
    rewrite flat_map_constant_length with (c := length neg)
      by (intros; apply length_map). lia.
Qed.


(** The row-count recurrence is monotone. *)
Lemma poly_rows_recurrence_mono : forall rows more, rows <= more ->
  rows ^ 2 / 4 + rows <= more ^ 2 / 4 + more.
Proof.
  intros rows more Hle. apply Nat.add_le_mono; [|exact Hle].
  apply Nat.Div0.div_le_mono. now apply Nat.pow_le_mono_l.
Qed.

(** At fixed fuel, every size input to the Fourier-Motzkin envelope is monotone. *)
Lemma poly_fmcost_params_mono : forall fuel dim dim' mlen mlen' rows rows' bits bits',
  dim <= dim' -> mlen <= mlen' -> rows <= rows' -> bits <= bits' ->
  fmcost dim mlen fuel rows bits <= fmcost dim' mlen' fuel rows' bits'.
Proof.
  intro fuel. induction fuel as [|fuel IH];
    intros dim dim' mlen mlen' rows rows' bits bits' Hdim Hmlen Hrows Hbits.
  - cbn [fmcost]. apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|lia].
  - change ((rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2 +
      fmcost dim mlen fuel (rows^2 / 4 + rows) (2 * bits + 1) <=
      (rows' + 1)^2 * (dim' + mlen' + 1) * (bits' + 1)^2 +
      fmcost dim' mlen' fuel (rows'^2 / 4 + rows') (2 * bits' + 1)).
    apply Nat.add_le_mono.
    + apply Nat.mul_le_mono.
      * apply Nat.mul_le_mono; [apply Nat.pow_le_mono_l; lia|lia].
      * apply Nat.pow_le_mono_l. lia.
    + apply IH; try assumption; [now apply poly_rows_recurrence_mono|lia].
Qed.

(** One extra elimination round only increases the declared envelope. *)
Lemma poly_fmcost_fuel_step : forall fuel dim mlen rows bits,
  fmcost dim mlen fuel rows bits <= fmcost dim mlen (S fuel) rows bits.
Proof.
  intro fuel. induction fuel as [|fuel IH]; intros dim mlen rows bits.
  - change ((rows + 1) * (dim + mlen + 1) * (bits + 1) <=
      (rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2 +
      fmcost dim mlen 0 (rows^2 / 4 + rows) (2 * bits + 1)).
    eapply Nat.le_trans with (m := (rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2).
    + apply Nat.mul_le_mono.
      * apply Nat.mul_le_mono; [cbn [Nat.pow]; nia|lia].
      * cbn [Nat.pow]. nia.
    + lia.
  - change ((rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2 +
      fmcost dim mlen fuel (rows^2 / 4 + rows) (2 * bits + 1) <=
      (rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2 +
      fmcost dim mlen (S fuel) (rows^2 / 4 + rows) (2 * bits + 1)).
    apply Nat.add_le_mono_l. apply IH.
Qed.

Lemma poly_fmcost_fuel_mono : forall fuel fuel', fuel <= fuel' ->
  forall dim mlen rows bits,
  fmcost dim mlen fuel rows bits <= fmcost dim mlen fuel' rows bits.
Proof.
  intros fuel fuel' Hle. induction Hle; intros dim mlen rows bits; [reflexivity|].
  eapply Nat.le_trans; [apply IHHle|apply poly_fmcost_fuel_step].
Qed.

(** The whole declared envelope is monotone in all five arguments. *)
Lemma poly_fmcost_mono : forall dim dim' mlen mlen' fuel fuel' rows rows' bits bits',
  dim <= dim' -> mlen <= mlen' -> fuel <= fuel' -> rows <= rows' -> bits <= bits' ->
  fmcost dim mlen fuel rows bits <= fmcost dim' mlen' fuel' rows' bits'.
Proof.
  intros dim dim' mlen mlen' fuel fuel' rows rows' bits bits' Hd Hm Hf Hr Hb.
  eapply Nat.le_trans; [eapply poly_fmcost_params_mono; eassumption|].
  now apply poly_fmcost_fuel_mono.
Qed.


(** A tracked row has no repeated stored key. *)
Definition poly_row_unique {A} (r : poly_row A) : Prop :=
  NoDup (map fst (lhs (poly_constraint r))).

Lemma poly_add_rows_unique : forall A (encode : A -> positive) a (p : poly_row A) b q,
  poly_row_unique (poly_add_rows encode a p b q).
Proof.
  intros A encode a p b q. unfold poly_row_unique.
  cbn [poly_add_rows poly_constraint lhs]. apply poly_normal_coef_nodup.
Qed.

Lemma poly_initial_unique : forall A (encode : A -> positive) rows,
  Forall poly_row_unique (poly_initial encode rows).
Proof.
  intros A encode rows. induction rows as [|[r flag] rows IH]; [constructor|].
  cbn [poly_initial fst snd]. constructor.
  - unfold poly_row_unique. cbn [poly_constraint poly_normal_row lhs].
    apply poly_normal_coef_nodup.
  - apply Forall_map. exact IH.
Qed.

Lemma poly_cancel_unique : forall A (encode : A -> positive) eqb x p r,
  poly_row_unique r -> poly_row_unique (poly_cancel encode eqb x p r).
Proof.
  intros A encode eqb x p r Hunique. unfold poly_cancel.
  destruct (Z.eqb (poly_coefficient eqb x (poly_constraint r)) 0); [exact Hunique|].
  apply poly_add_rows_unique.
Qed.

Lemma poly_step_unique : forall A (encode : A -> positive) eqb x rows,
  Forall poly_row_unique rows -> Forall poly_row_unique (poly_step encode eqb x rows).
Proof.
  intros A encode eqb x rows Hunique. unfold poly_step.
  destruct (find (poly_pivot eqb x) rows) as [p|].
  - apply Forall_map. apply Forall_forall. intros r Hin. apply poly_cancel_unique.
    exact (proj1 (Forall_forall _ _) Hunique r Hin).
  - apply Forall_app. split; apply Forall_forall; intros r Hin.
    + apply filter_In in Hin as [Hin _].
      exact (proj1 (Forall_forall _ _) Hunique r Hin).
    + apply in_flat_map in Hin as [p [Hp Hin]].
      apply in_map_iff in Hin as [q [Hsame Hq]]. subst r. apply poly_add_rows_unique.
Qed.

(** The original key accompanies its two nonnegative coefficient sums. *)
Definition poly_signed_add_term {A} (encode : A -> positive)
    (tr : ptrie (A * (Z * Z))) (p : A * Z) : ptrie (A * (Z * Z)) :=
  let key := encode (fst p) in
  let previous := match PTrieCode.get key tr with
    | Some q => snd q | None => (0%Z, 0%Z) end in
  PTrieCode.set key (fst p, lc_add_signed (snd p) previous) tr.

TimeFun poly_signed_add_term.

(** Finishing a stored coefficient performs its only signed subtraction. *)
Definition poly_signed_value {A} (p : A * (Z * Z)) : A * Z :=
  let sums := snd p in (fst p, (fst sums - snd sums)%Z).

TimeFun poly_signed_value.

Definition poly_signed_keep {A} (acc : list (A * Z)) (p : A * (Z * Z))
    : list (A * Z) :=
  let q := poly_signed_value p in
  if Z.eqb (snd q) 0 then acc else q :: acc.

TimeFun poly_signed_keep.

(** Affine preparation emits one nonzero coefficient at each occupied key. *)
Definition poly_signed_normal_coef {A} (encode : A -> positive) (xs : list (A * Z))
    : list (A * Z) :=
  PTrieCode.fold_values poly_signed_keep
    (fold_left (poly_signed_add_term encode) xs PTrieCode.empty) nil.

TimeFun poly_signed_normal_coef.

Definition poly_prepare_form {A} (encode : A -> positive) (f : lin A) : lin A :=
  Lin A (poly_signed_normal_coef encode (coef f)) (cst f).

TimeFun poly_prepare_form.

(** Value projection commutes with a single trie update. *)
Lemma poly_signed_map_set : forall A B (f : A -> B) key value tr,
  PTrieCode.map f (PTrieCode.set key value tr) =
    PTrieCode.set key (f value) (PTrieCode.map f tr).
Proof.
  intros A B f key value tr. apply PTrie.ext. intro q. rewrite PTrie.get_map.
  destruct (Pos.eq_dec q key) as [Heq|Hneq].
  - subst q. rewrite !PTrie.get_set_same. reflexivity.
  - rewrite !PTrie.get_set_other by exact Hneq. rewrite PTrie.get_map. reflexivity.
Qed.

(** A signed pair denotes ordinary addition after projection. *)
Lemma poly_signed_value_add : forall A (x : A) a sums,
  poly_signed_value (x, lc_add_signed a sums) =
    (x, (fst sums - snd sums + a)%Z).
Proof.
  intros A x a [p n]. unfold poly_signed_value, lc_add_signed.
  destruct (0 <=? a)%Z; cbn [fst snd]; f_equal; ring.
Qed.

(** Erasing the signed representation gives the existing coefficient insertion. *)
Lemma poly_signed_add_erases : forall A (encode : A -> positive) tr p,
  PTrieCode.map poly_signed_value (poly_signed_add_term encode tr p) =
    poly_add_term encode (PTrieCode.map poly_signed_value tr) p.
Proof.
  intros A encode tr [x a]. unfold poly_signed_add_term, poly_add_term.
  cbn [fst snd]. rewrite poly_signed_map_set, PTrie.get_map.
  destruct (PTrieCode.get (encode x) tr) as [[y sums]|];
    cbn [option_map fst snd]; rewrite poly_signed_value_add;
    unfold poly_signed_value; cbn [fst snd]; reflexivity.
Qed.

(** Erasing after accumulation agrees exactly with ordinary normalization. *)
Lemma poly_signed_fold_erases : forall A (encode : A -> positive) xs tr,
  PTrieCode.map poly_signed_value (fold_left (poly_signed_add_term encode) xs tr) =
    fold_left (poly_add_term encode) xs (PTrieCode.map poly_signed_value tr).
Proof.
  intros A encode xs. induction xs as [|p xs IH]; intro tr; cbn [fold_left].
  - reflexivity.
  - rewrite IH, poly_signed_add_erases. reflexivity.
Qed.

(** A trie node folds its left values, optional value, and right values in order. *)
Lemma poly_signed_fold_node : forall A B (step : B -> A -> B) l o r b,
  PTrieCode.fold_values step (PTrieCode.node l o r) b =
    PTrieCode.fold_values step r
      (match o with Some a => step (PTrieCode.fold_values step l b) a
       | None => PTrieCode.fold_values step l b end).
Proof.
  intros A B step l o r b. destruct l, o, r; reflexivity.
Qed.

Lemma poly_signed_fold_empty : forall A B (step : B -> A -> B) b,
  PTrieCode.fold_values step PTrieCode.empty b = b.
Proof.
  reflexivity.
Qed.

(** Mapping trie values before a fold composes the folding callback. *)
Lemma poly_signed_fold_map : forall A B D (f : A -> B) (step : D -> B -> D) tr b,
  PTrieCode.fold_values step (PTrieCode.map f tr) b =
    PTrieCode.fold_values (fun acc p => step acc (f p)) tr b.
Proof.
  intros A B D f step [|tr] b; [reflexivity|].
  change (PTrieCode.fold_values step
    (PTrieCode.filter_ne (fun a => Some (f a)) tr) b =
      PTrieCode.fold_values_ne (fun acc p => step acc (f p)) tr b).
  revert b. induction tr as [r IHr|a|a r IHr|l IHl|l IHl r IHr|
    l IHl a|l IHl a r IHr]; intro b;
    cbn [PTrieCode.filter_ne PTrieCode.filter_value PTrieCode.fold_values_ne];
    rewrite poly_signed_fold_node;
    rewrite ?poly_signed_fold_empty, ?IHl, ?IHr; reflexivity.
Qed.

(** The faster preparer returns exactly the existing canonical coefficient list. *)
Lemma poly_signed_normal_eq : forall A (encode : A -> positive) xs,
  poly_signed_normal_coef encode xs = poly_normal_coef encode xs.
Proof.
  intros A encode xs. unfold poly_signed_normal_coef, poly_normal_coef.
  pose proof (poly_signed_fold_erases A encode xs PTrieCode.empty) as Hfold.
  change (PTrieCode.map poly_signed_value
    (fold_left (poly_signed_add_term encode) xs PTrieCode.empty) =
      fold_left (poly_add_term encode) xs PTrieCode.empty) in Hfold.
  rewrite <- Hfold.
  rewrite poly_signed_fold_map. reflexivity.
Qed.

(** Preparation preserves the affine constant. *)
Lemma poly_prepare_form_constant : forall A (encode : A -> positive) f,
  cst (poly_prepare_form encode f) = cst f.
Proof.
  reflexivity.
Qed.

(** Prepared forms have no repeated coefficient key. *)
Lemma poly_prepare_form_nodup : forall A (encode : A -> positive) f,
  NoDup (map fst (coef (poly_prepare_form encode f))).
Proof.
  intros A encode f. cbn [poly_prepare_form coef].
  rewrite poly_signed_normal_eq. apply poly_normal_coef_nodup.
Qed.

(** Prepared forms contain no explicit zero coefficient. *)
Lemma poly_prepare_form_nonzero : forall A (encode : A -> positive) f,
  Forall (fun p => snd p <> 0%Z) (coef (poly_prepare_form encode f)).
Proof.
  intros A encode f. cbn [poly_prepare_form coef].
  rewrite poly_signed_normal_eq. apply Forall_forall. intros p Hp.
  exact (poly_normal_coef_nonzero A encode (coef f) p Hp).
Qed.

(** Preparation retains only keys occurring in the original affine form. *)
Lemma poly_prepare_form_support : forall A (encode : A -> positive) f p,
  In p (coef (poly_prepare_form encode f)) -> In (fst p) (map fst (coef f)).
Proof.
  intros A encode f p Hp. cbn [poly_prepare_form coef] in Hp.
  rewrite poly_signed_normal_eq in Hp. now apply poly_normal_coef_keys in Hp.
Qed.


Module PolySignedAffineClock (X : KEY_T).
  Module SignedCert := LinCertT X.

  Definition poly_signed_pairs (tr : ptrie (X.t * (Z * Z))) : ptrie (Z * Z) :=
    PTrieCode.map (@snd X.t (Z * Z)) tr.

  (** Discarding stored keys gives the checked linear-certificate accumulator. *)
  Lemma poly_signed_add_pairs : forall tr p,
    poly_signed_pairs (poly_signed_add_term X.encode tr p) =
      SignedCert.insert_term (poly_signed_pairs tr) p.
  Proof.
    intros tr [x a]. unfold poly_signed_pairs, poly_signed_add_term,
      SignedCert.insert_term. cbn [fst snd].
    rewrite poly_signed_map_set, PTrie.get_map.
    destruct (PTrieCode.get (X.encode x) tr); reflexivity.
  Qed.

  Lemma poly_signed_fold_pairs : forall xs tr,
    poly_signed_pairs (fold_left (poly_signed_add_term X.encode) xs tr) =
      fold_left SignedCert.insert_term xs (poly_signed_pairs tr).
  Proof.
    intro xs. induction xs as [|p xs IH]; intro tr; cbn [fold_left]; [reflexivity|].
    rewrite IH, poly_signed_add_pairs. reflexivity.
  Qed.

  Lemma poly_signed_gather_pairs : forall xs,
    poly_signed_pairs (fold_left (poly_signed_add_term X.encode) xs PTrieCode.empty) =
      SignedCert.gather xs.
  Proof.
    intro xs. rewrite poly_signed_fold_pairs. reflexivity.
  Qed.

  Definition poly_signed_good (tr : ptrie (X.t * (Z * Z))) : Prop :=
    SignedCert.lc_trie_good (poly_signed_pairs tr).

  Definition poly_signed_potential (tr : ptrie (X.t * (Z * Z))) : N :=
    SignedCert.lc_trie_sum SignedCert.lc_pair_ones (poly_signed_pairs tr).

  Definition poly_signed_insert_factor : N :=
    (2 * X.c_key + 4 * PTrieT.c_trie + 64)%N.

  Lemma poly_signed_add_good : forall tr p,
    poly_signed_good tr -> poly_signed_good (poly_signed_add_term X.encode tr p).
  Proof.
    intros tr p Hgood. unfold poly_signed_good in *.
    rewrite poly_signed_add_pairs. now apply SignedCert.insert_term_good.
  Qed.

  (** The signed insertion clock telescopes the same set-bit potential as LinCert. *)
  Lemma T_poly_signed_add_potential : forall tr x a, poly_signed_good tr ->
    (T_poly_signed_add_term X.encode X.T_encode tr (x, a) +
      poly_signed_potential (poly_signed_add_term X.encode tr (x, a)) <=
      poly_signed_insert_factor * N.of_nat (X.bits x + Z.size_nat a + 1) +
        poly_signed_potential tr)%N.
  Proof.
    intros tr x a Hgood. unfold poly_signed_good in Hgood.
    set (previous := match PTrieCode.get (X.encode x) tr with
      | Some q => snd q | None => (0%Z, 0%Z) end).
    assert (Hprevious_value :
      (match PTrieCode.get (X.encode x) (poly_signed_pairs tr) with
       | Some z => z | None => (0%Z, 0%Z) end) = previous).
    { unfold poly_signed_pairs. rewrite PTrie.get_map.
      destruct (PTrieCode.get (X.encode x) tr); reflexivity. }
    pose proof (SignedCert.lc_previous_nonnegative _ (X.encode x) Hgood) as Hsigns.
    rewrite Hprevious_value in Hsigns. destruct Hsigns as [Hp Hn].
    pose proof (SignedCert.lc_previous_ones (poly_signed_pairs tr) (X.encode x)) as Hprevious.
    rewrite Hprevious_value in Hprevious.
    pose proof (SignedCert.lc_trie_sum_set SignedCert.lc_pair_ones (X.encode x)
      (lc_add_signed a previous) (poly_signed_pairs tr)) as Hset.
    assert (Hinsert_value : SignedCert.insert_term (poly_signed_pairs tr) (x, a) =
      PTrieCode.set (X.encode x) (lc_add_signed a previous) (poly_signed_pairs tr)).
    { unfold SignedCert.insert_term. cbn [fst snd]. rewrite Hprevious_value. reflexivity. }
    rewrite <- Hinsert_value in Hset.
    unfold poly_signed_potential. rewrite poly_signed_add_pairs.
    pose proof (X.T_encode_le x) as Hencode.
    pose proof (PTrieT.T_get_le (X.t * (Z * Z)) (X.encode x) tr) as Hget.
    pose proof (PTrieT.T_set_le (X.t * (Z * Z)) (X.encode x)
      (x, lc_add_signed a previous) tr) as Hput.
    pose proof (SignedCert.T_lc_add_signed_pair a previous Hp Hn) as Hadd.
    time_unfold (@T_poly_signed_add_term). cbn [fst snd]. fold previous.
    unfold poly_signed_insert_factor, X.bits in *. time_simpl.
    destruct (PTrieCode.get (X.encode x) tr); time_simpl; nia.
  Qed.

  (** Folding insertion charges only the raw incoming bit mass. *)
  Lemma T_poly_signed_accum_weighted : forall xs tr, poly_signed_good tr ->
    (List.T_fold_left (poly_signed_add_term X.encode)
      (T_poly_signed_add_term X.encode X.T_encode) xs tr +
      poly_signed_potential (fold_left (poly_signed_add_term X.encode) xs tr) <=
      (poly_signed_insert_factor + 2) * SignedCert.lc_terms_weight xs +
        poly_signed_potential tr + 1)%N.
  Proof.
    induction xs as [|[x a] xs IH]; intros tr Hgood;
      time_unfold List.T_fold_left; cbn [fold_left SignedCert.lc_terms_weight].
    - lia.
    - specialize (IH (poly_signed_add_term X.encode tr (x, a))
        (poly_signed_add_good tr (x, a) Hgood)).
      pose proof (T_poly_signed_add_potential tr x a Hgood) as Hinsert.
      unfold X.bits in Hinsert. nia.
  Qed.

  (** Trie skeleton growth is bounded by the encodings of the incoming keys. *)
  Lemma poly_signed_accum_nodes : forall xs tr,
    (N.of_nat (PTrie.nodes (fold_left (poly_signed_add_term X.encode) xs tr)) <=
      N.of_nat (PTrie.nodes tr) + SignedCert.lc_terms_weight xs)%N.
  Proof.
    induction xs as [|[x a] xs IH]; intro tr;
      cbn [fold_left SignedCert.lc_terms_weight]; [lia|].
    specialize (IH (poly_signed_add_term X.encode tr (x, a))).
    pose proof (PTrie.nodes_set (X.t * (Z * Z)) (X.encode x)
      (x, lc_add_signed a (match PTrieCode.get (X.encode x) tr with
        | Some q => snd q | None => (0%Z, 0%Z) end)) tr) as Hnodes.
    change (PTrie.nodes (poly_signed_add_term X.encode tr (x, a)) <=
      PTrie.nodes tr + Pos.size_nat (X.encode x)) in Hnodes. lia.
  Qed.

  Fixpoint poly_signed_sum_ne (f : Z * Z -> N) (tr : trie_ne (X.t * (Z * Z))) : N :=
    match tr with
    | N001 r => poly_signed_sum_ne f r
    | N010 p => f (snd p)
    | N011 p r => f (snd p) + poly_signed_sum_ne f r
    | N100 l => poly_signed_sum_ne f l
    | N101 l r => poly_signed_sum_ne f l + poly_signed_sum_ne f r
    | N110 l p => poly_signed_sum_ne f l + f (snd p)
    | N111 l p r => poly_signed_sum_ne f l + f (snd p) + poly_signed_sum_ne f r
    end%N.

  Definition poly_signed_sum (f : Z * Z -> N) (tr : ptrie (X.t * (Z * Z))) : N :=
    match tr with Empty => 0 | Nodes n => poly_signed_sum_ne f n end%N.

  (** Projecting stored keys does not change the signed-pair mass. *)
  Lemma poly_signed_sum_pairs : forall f tr,
    SignedCert.lc_trie_sum f (poly_signed_pairs tr) = poly_signed_sum f tr.
  Proof.
    intros f [|tr]; [reflexivity|]. unfold poly_signed_pairs, PTrieCode.map,
      PTrieCode.filter_map, poly_signed_sum.
    induction tr as [r IHr|p|p r IHr|l IHl|l IHl r IHr|l IHl p|l IHl p r IHr];
      cbn [PTrieCode.filter_ne PTrieCode.filter_value poly_signed_sum_ne];
      rewrite SignedCert.lc_trie_sum_node; rewrite ?IHl, ?IHr;
      cbn [SignedCert.lc_trie_sum SignedCert.lc_option_sum]; lia.
  Qed.

  (** Final subtraction and zero testing charge the two stored widths once. *)
  Lemma T_poly_signed_keep_bounded : forall (acc : list (X.t * Z)) (p : X.t * (Z * Z)),
    (T_poly_signed_keep acc p <= 16 * SignedCert.lc_pair_bits (snd p))%N.
  Proof.
    intros acc [x [a b]]. pose proof (Z.T_sub_le a b) as Hsub.
    pose proof (Z.T_eqb_le (a - b) 0) as Heq.
    pose proof (poly_size_add a (-b)) as Hbits. rewrite poly_size_opp in Hbits.
    change (Z.size_nat (a - b) <= Nat.max (Z.size_nat a) (Z.size_nat b) + 1) in Hbits.
    time_unfold (@T_poly_signed_keep). time_unfold (@T_poly_signed_value).
    unfold SignedCert.lc_pair_bits. cbn [poly_signed_value fst snd]. time_simpl. lia.
  Qed.

  (** Finishing a nonempty trie traverses every node and stored pair once. *)
  Lemma T_poly_signed_finish_ne : forall tr acc,
    (PTrieT.T_fold_values_ne (@poly_signed_keep X.t) (@T_poly_signed_keep X.t) tr acc <=
      32 * (N.of_nat (PTrie.nodes_ne tr) +
        poly_signed_sum_ne SignedCert.lc_pair_bits tr))%N.
  Proof.
    induction tr as [r IHr|p|p r IHr|l IHl|l IHl r IHr|l IHl p|l IHl p r IHr];
      intro acc.
    - specialize (IHr acc).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
    - pose proof (T_poly_signed_keep_bounded acc p).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
    - pose proof (T_poly_signed_keep_bounded acc p).
      specialize (IHr (poly_signed_keep acc p)).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
    - specialize (IHl acc).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
    - specialize (IHl acc).
      specialize (IHr (PTrieCode.fold_values_ne poly_signed_keep l acc)).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
    - specialize (IHl acc).
      pose proof (T_poly_signed_keep_bounded
        (PTrieCode.fold_values_ne poly_signed_keep l acc) p).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
    - specialize (IHl acc).
      pose proof (T_poly_signed_keep_bounded
        (PTrieCode.fold_values_ne poly_signed_keep l acc) p).
      specialize (IHr (poly_signed_keep (PTrieCode.fold_values_ne poly_signed_keep l acc) p)).
      time_unfold (@PTrieT.T_fold_values_ne). cbn [PTrie.nodes_ne poly_signed_sum_ne]. lia.
  Qed.

  Lemma T_poly_signed_finish : forall tr acc,
    (PTrieT.T_fold_values (@poly_signed_keep X.t) (@T_poly_signed_keep X.t) tr acc <=
      32 * (N.of_nat (PTrie.nodes tr) + poly_signed_sum SignedCert.lc_pair_bits tr + 1))%N.
  Proof.
    intros [|tr] acc.
    - time_unfold (@PTrieT.T_fold_values). cbn [PTrie.nodes poly_signed_sum]. lia.
    - pose proof (T_poly_signed_finish_ne tr acc).
      time_unfold (@PTrieT.T_fold_values). cbn [PTrie.nodes poly_signed_sum]. lia.
  Qed.

  Definition poly_signed_normal_factor : N := (poly_signed_insert_factor + 72)%N.

  (** The signed preparer is linear in raw occurrence bit mass, including cancellation. *)
  Lemma T_poly_signed_normal_weighted : forall xs,
    (T_poly_signed_normal_coef X.encode X.T_encode xs <=
      poly_signed_normal_factor * (SignedCert.lc_terms_weight xs + 1))%N.
  Proof.
    intro xs. set (tr := fold_left (poly_signed_add_term X.encode) xs PTrieCode.empty).
    assert (Hempty : poly_signed_good PTrieCode.empty).
    { exact SignedCert.lc_empty_good. }
    pose proof (T_poly_signed_accum_weighted xs PTrieCode.empty Hempty) as Haccum.
    change (List.T_fold_left (poly_signed_add_term X.encode)
      (T_poly_signed_add_term X.encode X.T_encode) xs PTrieCode.empty +
      poly_signed_potential tr <=
      (poly_signed_insert_factor + 2) * SignedCert.lc_terms_weight xs + 0 + 1)%N in Haccum.
    pose proof (poly_signed_accum_nodes xs PTrieCode.empty) as Hnodes.
    change (N.of_nat (PTrie.nodes tr) <= 0 + SignedCert.lc_terms_weight xs)%N in Hnodes.
    pose proof (SignedCert.gather_storage xs) as Hstorage.
    rewrite <- poly_signed_gather_pairs, poly_signed_sum_pairs in Hstorage.
    fold tr in Hstorage. pose proof (T_poly_signed_finish tr nil) as Hfinish.
    time_unfold (@T_poly_signed_normal_coef).
    change (fun acc p => T_poly_signed_add_term X.encode X.T_encode acc p)
      with (T_poly_signed_add_term X.encode X.T_encode).
    change (fun acc p => T_poly_signed_keep acc p) with (@T_poly_signed_keep X.t).
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    fold tr. unfold poly_signed_normal_factor. time_simpl. nia.
  Qed.

  Lemma poly_signed_terms_uniform : forall xs bits,
    Forall (fun p => X.bits (fst p) + Z.size_nat (snd p) <= bits) xs ->
    (SignedCert.lc_terms_weight xs <= N.of_nat (length xs) * N.of_nat (bits + 1))%N.
  Proof.
    intro xs. induction xs as [|[x a] xs IH]; intros bits Hwidth.
    - cbn [SignedCert.lc_terms_weight length]. lia.
    - inversion Hwidth as [|p ps Hhead Htail]; subst p ps.
      specialize (IH bits Htail). unfold X.bits in Hhead.
      cbn [fst snd SignedCert.lc_terms_weight length] in *. rewrite Nat2N.inj_succ. nia.
  Qed.

  Definition poly_prepare_factor : N := (poly_signed_normal_factor + 8)%N.

  (** Preparing an affine form fits its original list length and coefficient/key widths. *)
  Lemma T_poly_prepare_form_bounded : forall f bits,
    Forall (fun p => X.bits (fst p) + Z.size_nat (snd p) <= bits) (coef f) ->
    (T_poly_prepare_form X.encode X.T_encode f <=
      poly_prepare_factor * N.of_nat (length (coef f) + 1) * N.of_nat (bits + 1))%N.
  Proof.
    intros f bits Hwidth.
    pose proof (T_poly_signed_normal_weighted (coef f)) as Hnormal.
    pose proof (poly_signed_terms_uniform (coef f) bits Hwidth) as Hmass.
    assert (Hwidth_positive : (1 <= N.of_nat (bits + 1))%N) by lia.
    time_unfold (@T_poly_prepare_form). time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    unfold poly_prepare_factor. rewrite Nat2N.inj_add.
    change (N.of_nat 1) with 1%N. nia.
  Qed.
End PolySignedAffineClock.

Module PolySignedAffineLinearize (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N).
  Module Clock := PolySignedAffineClock X.

  Lemma poly_signed_max_forall : forall (A : Type) (measure : A -> nat) base xs,
    Forall (fun p => measure p <= fold_right Nat.max base (map measure xs)) xs.
  Proof.
    intros A measure base xs. induction xs as [|p xs IH]; cbn [map fold_right].
    - constructor.
    - constructor; [apply Nat.le_max_l|].
      eapply Forall_impl; [|exact IH]. intros q Hq.
      eapply Nat.le_trans; [exact Hq|apply Nat.le_max_r].
  Qed.

  (** The linearizer's raw width contract pays the signed preparation pass directly. *)
  Lemma T_poly_prepare_lin_of : forall e f wrapping,
    F.lin_of e = Some (f, wrapping) ->
    (T_poly_prepare_form X.encode X.T_encode f <=
      Clock.poly_prepare_factor * N.of_nat (tsize e + 1) *
        N.of_nat (F.bits_e e + 1))%N.
  Proof.
    intros e f wrapping Hlinear.
    destruct (F.lin_of_size e f wrapping Hlinear) as [Hlength Hwidth].
    pose proof (poly_signed_max_forall (X.t * Z)
      (fun p => X.bits (fst p) + Z.size_nat (snd p)) (Z.size_nat (cst f)) (coef f))
      as Hentries.
    change (Forall (fun p => X.bits (fst p) + Z.size_nat (snd p) <=
      F.form_bits f) (coef f)) in Hentries.
    assert (Hbits : Forall (fun p => X.bits (fst p) + Z.size_nat (snd p) <=
      F.bits_e e) (coef f)).
    { eapply Forall_impl; [|exact Hentries]. intros p Hp.
      change (X.bits (fst p) + Z.size_nat (snd p) <= F.form_bits f) in Hp.
      change (X.bits (fst p) + Z.size_nat (snd p) <= F.bits_e e). lia. }
    eapply N.le_trans; [apply Clock.T_poly_prepare_form_bounded; exact Hbits|].
    apply N.mul_le_mono_r, N.mul_le_mono_l. lia.
  Qed.
End PolySignedAffineLinearize.

Module PolyCode (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X) <: POLY_OPS X L F C.
  Definition t := reach (list (lcons X.t)).
  Definition wparam := unit.
  Definition subst (x : X.t) (f : lin X.t) (r : lcons X.t) : lcons X.t :=
    poly_substitute X.encode X.eqb x f r.

  Definition fm_elim (x : X.t) (P : list (lcons X.t)) : list (tracked X.t) :=
    map (fun r => Tracked X.t (poly_constraint r) (poly_multipliers r))
      (poly_step X.encode X.eqb x
        (poly_initial X.encode (map (fun r => (r, false)) P))).

  (** Normalize each source once while preserving its certificate index. *)
  Definition poly_normal_rows (P : list (lcons X.t)) : list (lcons X.t) :=
    map (poly_normal_row X.encode) P.

  (** Equality targets require zero weights on inequality sources. *)
  Definition poly_source_equal (P : list (lcons X.t)) (ms : list Z) : bool :=
    forallb (fun pm => match lrel (fst pm) with
      | REq => true | RLe => Z.eqb (snd pm) 0 end) (List.combine P ms).

  (** Source contradictions use scale one; other rows retain their target scale. *)
  Definition poly_canonical_scale (sc : Z) : Z :=
    if Z.eqb sc 0 then 1%Z else sc.

  (** The equality branch demands exact right-hand-side and equality-weight data. *)
  Definition poly_canonical_guard (P : list (lcons X.t)) (c : lcons X.t)
      (r : poly_row X.t) (sc : Z) (ms : list Z) : bool :=
    Z.eqb sc 0 || ((0 <? sc)%Z &&
      match lrel c with
      | RLe => true
      | REq => Z.eqb (rhs (poly_constraint r)) 0 && poly_source_equal P ms
      end).

  Definition candidate (P : list (lcons X.t)) (c : lcons X.t)
      (r : poly_row X.t) : option cert :=
    if poly_contradiction r then
      match poly_multipliers r with
      | [] => None
      | sc :: ms =>
        if poly_canonical_guard P c r sc ms then
          let k := Cert ms (poly_canonical_scale sc) false in
          if C.check_entails P c k then Some k else None
        else None
      end
    else None.

  Fixpoint find_certificate (P : list (lcons X.t)) (c : lcons X.t)
      (rs : list (poly_row X.t)) : option cert :=
    match rs with
    | nil => None
    | r :: rs =>
      match candidate P c r with
      | Some k => Some k
      | None => find_certificate P c rs
      end
    end.

  (** The complement is strict over Q; subtracting one would lose rational countermodels. *)
  Definition entail_engine (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    find_certificate P c
      (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
        (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))).

  (** The private engine checks normalized rows; proofs transport acceptance to raw inputs. *)
  Definition entail_cert (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    entail_engine (poly_normal_rows P) (poly_normal_row X.encode c).

  Definition entails_row (P : list (lcons X.t)) (c : lcons X.t) : bool :=
    match entail_cert P c with Some _ => true | None => false end.

  Definition keep_row (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match lrel r with
    | RLe => entails_row P r
    | REq => entails_row P (LCons X.t (lhs r) RLe (rhs r)) &&
        entails_row P (poly_negate r)
    end.

  Definition bot : t := Unreached.
  Definition is_bot (s : t) : bool :=
    match s with
    | Unreached => true
    | Reached P => entails_row P (LCons X.t nil RLe (-1)%Z)
    end.

  Definition leb (a b : t) : bool :=
    match a, b with
    | Unreached, _ => true
    | _, Unreached => is_bot a
    | Reached P, Reached Q => forallb (keep_row P) Q
    end.

  Definition join (a b : t) : t :=
    match a, b with
    | Unreached, _ => b
    | _, Unreached => a
    | Reached P, Reached Q => Reached (filter (keep_row Q) P ++ filter (keep_row P) Q)
    end.

  Definition top : t := Reached nil.
  Definition meet (a b : t) : t :=
    match a, b with
    | Reached P, Reached Q => Reached (P ++ Q)
    | _, _ => Unreached
    end.

  Definition widen (_ : wparam) (a b : t) : t :=
    match a, b with
    | Unreached, _ => if is_bot b then Unreached else b
    | _, Unreached => a
    | Reached P, Reached Q => Reached (filter (keep_row Q) P)
    end.

  Definition narrow (_ : t) (b : t) : t := b.

  Definition checked_projection (P : list (lcons X.t)) (x : X.t) (r : tracked X.t)
      : bool :=
    forallb (fun p => negb (X.eqb (fst p) x)) (lhs (row_of r)) &&
      C.check_entails P (row_of r) (Cert (mults_of r) 1 false).

  Definition havoc (x : X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P => Reached (map row_of (filter (checked_projection P x) (fm_elim x P)))
    end.

  Definition tmp_encode (x : option X.t) : positive :=
    match x with None => xH | Some y => xO (X.encode y) end.

  Definition tmp_eqb (x y : option X.t) : bool :=
    match x, y with
    | None, None => true
    | Some a, Some b => X.eqb a b
    | _, _ => false
    end.

  Definition rename_old (x y : X.t) : option X.t :=
    if X.eqb y x then None else Some y.

  Definition rename_row (f : X.t -> option X.t) (r : lcons X.t) : lcons (option X.t) :=
    LCons (option X.t) (map (fun p => (f (fst p), snd p)) (lhs r)) (lrel r) (rhs r).

  Fixpoint untag (xs : list (option X.t * Z)) : option (list (X.t * Z)) :=
    match xs with
    | nil => Some nil
    | (None, _) :: _ => None
    | (Some x, z) :: xs =>
      match untag xs with Some ys => Some ((x, z) :: ys) | None => None end
    end.

  Definition assignment_row (x : X.t) (f : lin X.t) : lcons (option X.t) :=
    LCons (option X.t)
      ((Some x, 1%Z) :: map (fun p => (rename_old x (fst p), (- snd p)%Z)) (coef f))
      REq (cst f).

  Definition assigned_candidate (P : list (lcons X.t)) (x : X.t) (f : lin X.t)
      (r : poly_row (option X.t)) : option (lcons X.t) :=
    match untag (lhs (poly_constraint r)), poly_multipliers r with
    | Some xs, _ :: ms =>
      let c := LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r)) in
      if C.check_entails P (subst x f c) (Cert ms 1 false) then Some c else None
    | _, _ => None
    end.

  Definition assign_linear (x : X.t) (f : lin X.t) (P : list (lcons X.t))
      : list (lcons X.t) :=
    flat_map (fun r => match assigned_candidate P x f r with
      | Some c => c :: nil | None => nil end)
      (poly_step tmp_encode tmp_eqb None
        (poly_initial tmp_encode
          ((assignment_row x f, false) ::
           map (fun r => (rename_row (rename_old x) r, false)) P))).

  Definition assign (x : X.t) (e : term L.op X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P =>
      match F.lin_of e with
      | Some (f, NoWrap) =>
        Reached (assign_linear x (poly_prepare_form X.encode f) P)
      | _ => havoc x s
      end
    end.

  Definition atom_row (a : atom X.t) : option (lcons X.t) :=
    match alw a, arw a with
    | NoWrap, NoWrap =>
      let cs := poly_normal_coef X.encode
        (coef (al a) ++ poly_scale_coef (-1)%Z (coef (ar a))) in
      let b := (cst (ar a) - cst (al a))%Z in
      Some (match acmp a with
        | CEq => LCons X.t cs REq b
        | CLe => LCons X.t cs RLe b
        | CLt => LCons X.t cs RLe (b - 1)%Z
        end)
    | _, _ => None
    end.

  Definition assume (g : L.guard) (es : list (term L.op X.t)) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P => Reached
        (flat_map (fun a => match atom_row a with Some r => r :: nil | None => nil end)
          (F.atoms_of g es) ++ P)
    end.

  Definition range_row (f : lin X.t) : lcons (option X.t) :=
    LCons (option X.t)
      ((None, 1%Z) :: map (fun p => (Some (fst p), (- snd p)%Z)) (coef f))
      REq (cst f).

  Definition range_update (a b : Z) (is_eq : bool) (bounds : bnd * bnd) : bnd * bnd :=
    if (0 <? a)%Z then
      (if is_eq then poly_lower (- ((- b) / a))%Z (fst bounds) else fst bounds,
       poly_upper (b / a)%Z (snd bounds))
    else if (a <? 0)%Z then
      (poly_lower (- (b / (- a)))%Z (fst bounds),
       if is_eq then poly_upper ((- b) / (- a))%Z (snd bounds) else snd bounds)
    else bounds.

  Definition range_candidate (P : list (lcons X.t)) (f : lin X.t)
      (bounds : bnd * bnd) (r : poly_row (option X.t)) : bnd * bnd :=
    let c := poly_constraint r in
    if forallb (fun p => match fst p with None => true | Some _ => false end) (lhs c) then
      let a := poly_coefficient tmp_eqb None c in
      let conclusion := LCons X.t (poly_scale_coef a (coef f)) (lrel c)
        (rhs c - a * cst f)%Z in
      match poly_multipliers r with
      | _ :: ms =>
        if C.check_entails P conclusion (Cert ms 1 false) then
          range_update a (rhs c)
            (match lrel c with REq => true | RLe => false end) bounds
        else bounds
      | nil => bounds
      end
    else bounds.

  Definition range_linear (P : list (lcons X.t)) (f : lin X.t) : bnd * bnd :=
    let rows := map (poly_normal_row X.encode) P in
    let input := range_row f :: map (rename_row (@Some X.t)) rows in
    let vars := poly_variables X.encode (LCons X.t (coef f) REq (cst f) :: rows) in
    fold_left (range_candidate rows f)
      (poly_run tmp_encode tmp_eqb (map (@Some X.t) vars)
        (poly_initial tmp_encode (map (fun r => (r, false)) input))) (NegInf, PosInf).

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s with
    | Unreached => (NegInf, PosInf)
    | Reached P =>
      match F.lin_of e with
      | Some (f, NoWrap) => range_linear P f
      | Some (_, WrapTo lo hi) => if (lo <=? hi)%Z then (Fin lo, Fin hi) else (NegInf, PosInf)
      | None => (NegInf, PosInf)
      end
    end.
End PolyCode.

Module Poly (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) <: POLY X L N F C.
  Include PolyCode X L F C.
  Definition wrank (_ : wparam) (s : t) : nat :=
    match s with Unreached => 0 | Reached P => length P end.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached P => Forall (sat v) P end.

  (** A strict flag changes an inequality to its open rational interpretation. *)
  Definition poly_satQ (v : X.t -> Q) (r : poly_row X.t) : Prop :=
    match lrel (poly_constraint r) with
    | REq => (poly_eval_coef_Q v (lhs (poly_constraint r)) ==
        inject_Z (rhs (poly_constraint r)))%Q
    | RLe => if poly_strict r
      then (poly_eval_coef_Q v (lhs (poly_constraint r)) <
        inject_Z (rhs (poly_constraint r)))%Q
      else (poly_eval_coef_Q v (lhs (poly_constraint r)) <=
        inject_Z (rhs (poly_constraint r)))%Q
    end.

  Definition poly_eq_nonstrict (r : poly_row X.t) : Prop :=
    lrel (poly_constraint r) = REq -> poly_strict r = false.


  (** Scaling every stored occurrence scales its integer evaluation. *)
  Lemma eval_coef_scale : forall (v : X.t -> Z) a xs,
    eval_coef v (poly_scale_coef a xs) = (a * eval_coef v xs)%Z.
  Proof.
    intros v a xs. unfold eval_coef, poly_scale_coef.
    induction xs as [|[x b] xs IH]; cbn [map fold_right fst snd].
    - ring.
    - rewrite IH. ring.
  Qed.

  (** A returned candidate passes the checker and never requests an integer cut. *)
  Lemma candidate_returned : forall P c r k, candidate P c r = Some k ->
    C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c r k Hresult. unfold candidate in Hresult.
    destruct (poly_contradiction r); [|discriminate].
    destruct (poly_multipliers r) as [|sc ms]; [discriminate|].
    destruct (poly_canonical_guard P c r sc ms); [|discriminate].
    destruct (C.check_entails P c (Cert ms (poly_canonical_scale sc) false)) eqn:Hcheck;
      [|discriminate].
    injection Hresult as Hsame. subst k. split; [exact Hcheck|reflexivity].
  Qed.

  (** Searching candidates preserves their checker result and cut flag. *)
  Lemma find_certificate_returned : forall P c rs k, find_certificate P c rs = Some k ->
    C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c rs. induction rs as [|r rs IH]; intros k Hresult;
      cbn [find_certificate] in Hresult; [discriminate |].
    destruct (candidate P c r) as [j|] eqn:Hcandidate.
    - injection Hresult as Hsame. subst j. now apply candidate_returned with (r := r).
    - now apply IH.
  Qed.

  (** A coefficient list that omits the updated key keeps its evaluation. *)
  Lemma eval_coef_havoc : forall x st c xs,
    forallb (fun p => negb (X.eqb (fst p) x)) xs = true ->
    eval_coef (fun y => N.num (upd X.eqb st x c y)) xs =
      eval_coef (fun y => N.num (st y)) xs.
  Proof.
    intros x st c xs. unfold eval_coef.
    induction xs as [|[y a] xs IH]; intro Hfree; [reflexivity |].
    cbn [forallb fst] in Hfree. apply andb_true_iff in Hfree as [Hhead Htail].
    apply negb_true_iff in Hhead.
    change (a * N.num (if X.eqb y x then c else st y) +
      eval_coef (fun z => N.num (upd X.eqb st x c z)) xs =
      a * N.num (st y) + eval_coef (fun z => N.num (st z)) xs)%Z.
    rewrite Hhead. f_equal. exact (IH Htail).
  Qed.

  (** Checked projection rows hold after any replacement of the omitted variable. *)
  Lemma checked_projection_sound : forall P x r st c,
    checked_projection P x r = true -> Forall (sat (fun y => N.num (st y))) P ->
    sat (fun y => N.num (upd X.eqb st x c y)) (row_of r).
  Proof.
    intros P x r st c Hchecked Hmodels. unfold checked_projection in Hchecked.
    apply andb_true_iff in Hchecked as [Hfree Hcheck].
    pose proof (C.check_entails_sound P (row_of r) (Cert (mults_of r) 1 false)
      Hcheck (fun y => N.num (st y)) Hmodels) as Hsat.
    unfold sat in *. rewrite (eval_coef_havoc x st c (lhs (row_of r)) Hfree).
    exact Hsat.
  Qed.
  (** The trie mass sums every stored contribution under a numeric valuation. *)
  Fixpoint normalization_mass_ne (v : X.t -> Z) (n : trie_ne (X.t * Z)) : Z :=
    match n with
    | N001 r => normalization_mass_ne v r
    | N010 p => (snd p * v (fst p))%Z
    | N011 p r => (snd p * v (fst p) + normalization_mass_ne v r)%Z
    | N100 l => normalization_mass_ne v l
    | N101 l r => (normalization_mass_ne v l + normalization_mass_ne v r)%Z
    | N110 l p => (normalization_mass_ne v l + snd p * v (fst p))%Z
    | N111 l p r =>
      (normalization_mass_ne v l + snd p * v (fst p) + normalization_mass_ne v r)%Z
    end.

  (** An empty trie has zero mass. *)
  Definition normalization_mass (v : X.t -> Z) (tr : ptrie (X.t * Z)) : Z :=
    match tr with Empty => 0%Z | Nodes n => normalization_mass_ne v n end.

  (** An absent binding contributes zero to the trie mass. *)
  Definition normalization_value (v : X.t -> Z) (o : option (X.t * Z)) : Z :=
    match o with None => 0%Z | Some p => (snd p * v (fst p))%Z end.

  (** Canonical rebuilding adds the left, current and right contributions. *)
  Lemma normalization_mass_node : forall v l o r,
    normalization_mass v (PTrieCode.node l o r) =
      (normalization_mass v l + normalization_value v o + normalization_mass v r)%Z.
  Proof.
    intros v [|l] [p|] [|r];
      cbn [PTrieCode.node normalization_mass normalization_value normalization_mass_ne]; ring.
  Qed.

  (** The observable children account for the full trie mass. *)
  Lemma normalization_mass_view : forall v tr,
    normalization_mass v tr =
      (normalization_mass v (PTrieCode.left tr) +
       normalization_value v (PTrieCode.value tr) +
       normalization_mass v (PTrieCode.right tr))%Z.
  Proof.
    intros v tr.
    assert (Hnode : PTrieCode.node (PTrieCode.left tr) (PTrieCode.value tr)
      (PTrieCode.right tr) = tr).
    { destruct tr as [|n]; [reflexivity | destruct n; reflexivity]. }
    rewrite <- Hnode at 1. apply normalization_mass_node.
  Qed.

  (** Replacing one binding subtracts its old contribution and adds its new one. *)
  Lemma normalization_mass_set : forall v p a tr,
    normalization_mass v (PTrieCode.set p a tr) =
      (normalization_mass v tr + snd a * v (fst a) -
       normalization_value v (PTrieCode.get p tr))%Z.
  Proof.
    intros v p a. unfold PTrieCode.set.
    induction p as [p IH|p IH|]; intro tr; cbn [PTrieCode.replace].
    - rewrite normalization_mass_node, IH, (normalization_mass_view v tr).
      unfold PTrieCode.get, PTrieCode.left, PTrieCode.right, PTrieCode.value.
      cbn [trie_get]. ring.
    - rewrite normalization_mass_node, IH, (normalization_mass_view v tr).
      unfold PTrieCode.get, PTrieCode.left, PTrieCode.right, PTrieCode.value.
      cbn [trie_get]. ring.
    - rewrite normalization_mass_node, (normalization_mass_view v tr).
      unfold PTrieCode.get, PTrieCode.left, PTrieCode.right, PTrieCode.value.
      cbn [trie_get normalization_value]. ring.
  Qed.

  (** A fold whose step adds one contribution accumulates the nonempty trie mass. *)
  Lemma normalization_fold_ne : forall v B (step : B -> X.t * Z -> B) eval,
    (forall b p, eval (step b p) = (eval b + snd p * v (fst p))%Z) ->
    forall n b, eval (PTrieCode.fold_values_ne step n b) =
      (eval b + normalization_mass_ne v n)%Z.
  Proof.
    intros v B step eval Hstep n.
    induction n as [r IHr|p|p r IHr|l IHl|l IHl r IHr|l IHl p|l IHl p r IHr]; intro b;
      cbn [PTrieCode.fold_values_ne normalization_mass_ne].
    - apply IHr.
    - apply Hstep.
    - rewrite IHr, Hstep. ring.
    - apply IHl.
    - rewrite IHr, IHl. ring.
    - rewrite Hstep, IHl. ring.
    - rewrite IHr, Hstep, IHl. ring.
  Qed.

  (** A fold whose step adds one contribution accumulates the whole trie mass. *)
  Lemma normalization_fold : forall v B (step : B -> X.t * Z -> B) eval,
    (forall b p, eval (step b p) = (eval b + snd p * v (fst p))%Z) ->
    forall tr b, eval (PTrieCode.fold_values step tr b) =
      (eval b + normalization_mass v tr)%Z.
  Proof.
    intros v B step eval Hstep [|n] b; cbn [PTrieCode.fold_values normalization_mass].
    - ring.
    - now apply normalization_fold_ne.
  Qed.

  (** Every stored source key agrees with its encoded trie address. *)
  Definition normalization_wf (m : ptrie (X.t * Z)) : Prop :=
    forall p q, PTrieCode.get p m = Some q -> X.encode (fst q) = p.

  (** The empty coefficient accumulator satisfies key agreement. *)
  Lemma normalization_empty : normalization_wf PTrieCode.empty.
  Proof.
    intros p q Hget. rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  (** Accumulating a coefficient preserves agreement between keys and addresses. *)
  Lemma add_term_wf : forall m p, normalization_wf m ->
    normalization_wf (poly_add_term X.encode m p).
  Proof.
    intros m p Hwf key value Hvalue. unfold poly_add_term in Hvalue.
    destruct (Pos.eq_dec key (X.encode (fst p))) as [Heq|Hneq].
    - subst key. rewrite PTrie.get_set_same in Hvalue.
      injection Hvalue as Hsame. subst value. reflexivity.
    - rewrite PTrie.get_set_other in Hvalue by exact Hneq. exact (Hwf _ _ Hvalue).
  Qed.

  (** Accumulation adds the input occurrence to the trie mass. *)
  Lemma add_term_mass : forall v m p, normalization_wf m ->
    normalization_mass v (poly_add_term X.encode m p) =
      (normalization_mass v m + snd p * v (fst p))%Z.
  Proof.
    intros v m p Hwf. unfold poly_add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [q|] eqn:Hq;
      rewrite normalization_mass_set, Hq; cbn [normalization_value fst snd].
    - assert (Hkey : fst q = fst p).
      { apply X.encode_inj. exact (Hwf _ _ Hq). }
      rewrite Hkey. ring.
    - ring.
  Qed.

  (** Accumulating a raw coefficient list preserves the sum of all occurrences. *)
  Lemma normalize_fold_mass : forall v xs m, normalization_wf m ->
    normalization_mass v (fold_left (poly_add_term X.encode) xs m) =
      (normalization_mass v m + eval_coef v xs)%Z.
  Proof.
    intros v xs. induction xs as [|p xs IH]; intros m Hwf; cbn [fold_left].
    - unfold eval_coef. cbn [fold_right]. ring.
    - rewrite (IH _ (add_term_wf _ _ Hwf)), (add_term_mass v m p Hwf).
      unfold eval_coef. cbn [fold_right]. ring.
  Qed.

  (** Filtering zero bindings from the accumulator preserves integer evaluation. *)
  Lemma normalize_coef_eval : forall (v : X.t -> Z) xs,
    eval_coef v (poly_normal_coef X.encode xs) = eval_coef v xs.
  Proof.
    intros v xs. unfold poly_normal_coef.
    rewrite (normalization_fold v _ _ (eval_coef v)).
    - rewrite (normalize_fold_mass v xs PTrieCode.empty normalization_empty). reflexivity.
    - intros acc [x a]. cbn [snd]. destruct (Z.eqb a 0) eqn:Hzero.
      + apply Z.eqb_eq in Hzero. subst a. cbn [fst snd]. ring.
      + change (a * v x + eval_coef v acc = eval_coef v acc + a * v x)%Z. ring.
  Qed.

  (** Every valuation gives the same value to the original and prepared form. *)
  Lemma poly_prepare_form_eval : forall (v : X.t -> Z) f,
    eval_lin v (poly_prepare_form X.encode f) = eval_lin v f.
  Proof.
    intros v f. unfold eval_lin. cbn [poly_prepare_form coef cst].
    rewrite poly_signed_normal_eq, normalize_coef_eval. reflexivity.
  Qed.

  (** Concatenation adds the evaluations of both coefficient lists. *)
  Lemma eval_coef_app : forall (v : X.t -> Z) xs ys,
    eval_coef v (xs ++ ys) = (eval_coef v xs + eval_coef v ys)%Z.
  Proof.
    intros v xs. unfold eval_coef. induction xs as [|[x a] xs IH]; intro ys;
      cbn [app fold_right fst snd]; [reflexivity |].
    rewrite IH. ring.
  Qed.

  (** Updating one variable changes a form by its summed coefficient. *)
  Lemma eval_coef_update : forall (v : X.t -> Z) x z r,
    eval_coef (upd X.eqb v x z) (lhs r) =
      (eval_coef v (lhs r) + poly_coefficient X.eqb x r * (z - v x))%Z.
  Proof.
    intros v x z [xs relation b]. unfold eval_coef, poly_coefficient. cbn [lhs].
    induction xs as [|[y a] xs IH]; cbn [fold_right fst snd]; [ring |].
    rewrite IH. unfold upd. destruct (X.eqb_spec y x) as [Hsame|Hother].
    - subst y. ring.
    - ring.
  Qed.

  (** Removing all occurrences of a key subtracts its full contribution. *)
  Lemma eval_coef_without : forall (v : X.t -> Z) x r,
    eval_coef v (filter (fun p => negb (X.eqb (fst p) x)) (lhs r)) =
      (eval_coef v (lhs r) - poly_coefficient X.eqb x r * v x)%Z.
  Proof.
    intros v x [xs relation b]. unfold eval_coef, poly_coefficient. cbn [lhs].
    induction xs as [|[y a] xs IH]; cbn [filter fold_right fst snd]; [ring |].
    destruct (X.eqb_spec y x) as [Hsame|Hother]; cbn [negb fold_right fst snd].
    - subst y. rewrite IH. ring.
    - rewrite IH. ring.
  Qed.

  (** Substitution adjusts the constant separately from the updated coefficient sum. *)
  Lemma eval_coef_subst : forall (v : X.t -> Z) x f r,
    eval_coef v (lhs (subst x f r)) =
      (eval_coef (upd X.eqb v x (eval_lin v f)) (lhs r) -
       poly_coefficient X.eqb x r * cst f)%Z.
  Proof.
    intros v x f r. unfold subst, poly_substitute. cbn [lhs].
    rewrite normalize_coef_eval, eval_coef_app, eval_coef_scale,
      eval_coef_without, eval_coef_update. unfold eval_lin. ring.
  Qed.

  (** Syntactic substitution denotes the concrete update for arbitrary raw rows. *)
  Lemma subst_sat_checked : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof.
    intros v x f r. unfold sat. rewrite eval_coef_subst.
    unfold subst, poly_substitute. cbn [lrel rhs]. destruct (lrel r); lia.
  Qed.

  (** Returned assignment rows are justified by their checked substitutions. *)
  Lemma assigned_candidate_sound : forall P x f r c v,
    assigned_candidate P x f r = Some c -> Forall (sat v) P ->
    sat (upd X.eqb v x (eval_lin v f)) c.
  Proof.
    intros P x f r c v Hresult Hmodels. unfold assigned_candidate in Hresult.
    destruct (untag (lhs (poly_constraint r))) as [xs|]; [| discriminate].
    destruct (poly_multipliers r) as [|m ms]; [discriminate |].
    destruct (C.check_entails P
      (subst x f (LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r))))
      (Cert ms 1 false)) eqn:Hcheck; [| discriminate].
    injection Hresult as Hsame. subst c. apply subst_sat_checked.
    exact (C.check_entails_sound P _ (Cert ms 1 false) Hcheck v Hmodels).
  Qed.

  (** Every emitted assignment row holds after evaluating its affine right-hand side. *)
  Lemma assign_linear_sound : forall x f P v, Forall (sat v) P ->
    Forall (sat (upd X.eqb v x (eval_lin v f))) (assign_linear x f P).
  Proof.
    intros x f P v Hmodels. unfold assign_linear. apply Forall_forall. intros c Hin.
    apply in_flat_map in Hin as [r [_ Hin]].
    destruct (assigned_candidate P x f r) as [q|] eqn:Hresult; [| contradiction].
    destruct Hin as [Hsame|Hfalse]; [subst q | contradiction].
    exact (assigned_candidate_sound P x f r c v Hresult Hmodels).
  Qed.

  (** Pointwise equal numeric stores have equal coefficient evaluations. *)
  Lemma eval_coef_pointwise : forall (v w : X.t -> Z) xs,
    (forall x, v x = w x) -> eval_coef v xs = eval_coef w xs.
  Proof.
    intros v w xs Hsame. unfold eval_coef.
    induction xs as [|[x a] xs IH]; cbn [fold_right fst snd]; [reflexivity |].
    now rewrite Hsame, IH.
  Qed.

  (** Pointwise equal numeric stores satisfy the same row. *)
  Lemma sat_pointwise : forall (v w : X.t -> Z) r,
    (forall x, v x = w x) -> sat v r -> sat w r.
  Proof.
    intros v w r Hsame Hsat. unfold sat in *.
    rewrite <- (eval_coef_pointwise v w (lhs r) Hsame). exact Hsat.
  Qed.

  (** An accepted atom row is the integer interpretation of its unwrapped comparison. *)
  Lemma atom_row_sound : forall v a r,
    atom_row a = Some r -> atom_holds v a -> sat v r.
  Proof.
    intros v [fl wl comparison fr wr] r Hrow Hatom.
    destruct wl, wr; cbn [atom_row al alw ar arw acmp] in Hrow; try discriminate.
    destruct comparison; injection Hrow as Hsame; subst r;
      unfold sat; cbn [lhs lrel rhs];
      rewrite normalize_coef_eval, eval_coef_app, eval_coef_scale;
      cbn [atom_holds al alw ar arw acmp wrap_into] in Hatom;
      unfold eval_lin in Hatom; lia.
  Qed.

  (** Normalizing a row preserves its integer models. *)
  Lemma normalize_row_sat : forall v r,
    sat v (poly_normal_row X.encode r) <-> sat v r.
  Proof.
    intros v r. unfold sat, poly_normal_row. cbn [lrel lhs rhs].
    rewrite normalize_coef_eval. reflexivity.
  Qed.

  Lemma poly_key_eqb_refl : forall x, X.eqb x x = true.
  Proof.
    intro x. destruct (X.eqb_spec x x); [reflexivity|contradiction].
  Qed.

  Lemma poly_key_eqb_sym : forall x y, X.eqb x y = X.eqb y x.
  Proof.
    intros x y. destruct (X.eqb_spec x y), (X.eqb_spec y x); congruence.
  Qed.

  Lemma coef_of_cons : forall x y a xs,
    C.coef_of x ((y, a) :: xs) =
      if X.eqb x y then (a + C.coef_of x xs)%Z else C.coef_of x xs.
  Proof.
    reflexivity.
  Qed.

  (** A coefficient is the evaluation at its single-key indicator store. *)
  Lemma coef_of_eval : forall x xs,
    C.coef_of x xs = eval_coef (fun y => if X.eqb x y then 1%Z else 0%Z) xs.
  Proof.
    intros x xs. unfold C.coef_of, eval_coef.
    induction xs as [|[y a] xs IH]; cbn [fold_right fst snd]; [reflexivity|].
    rewrite <- IH. destruct (X.eqb x y); ring.
  Qed.

  Lemma coef_of_app : forall x xs ys,
    C.coef_of x (xs ++ ys) = (C.coef_of x xs + C.coef_of x ys)%Z.
  Proof.
    intros x xs ys. rewrite !coef_of_eval. apply eval_coef_app.
  Qed.

  Lemma coef_of_scale : forall x a xs,
    C.coef_of x (poly_scale_coef a xs) = (a * C.coef_of x xs)%Z.
  Proof.
    intros x a xs. rewrite !coef_of_eval. apply eval_coef_scale.
  Qed.

  (** Normalization preserves the total coefficient at every key. *)
  Lemma coef_of_normal : forall x xs,
    C.coef_of x (poly_normal_coef X.encode xs) = C.coef_of x xs.
  Proof.
    intros x xs. rewrite !coef_of_eval. apply normalize_coef_eval.
  Qed.

  Lemma coef_of_poly_coefficient : forall x r,
    C.coef_of x (lhs r) = poly_coefficient X.eqb x r.
  Proof.
    intros x r. unfold C.coef_of, poly_coefficient.
    induction (lhs r) as [|[y a] xs IH]; cbn [fold_right fst snd]; [reflexivity|].
    rewrite poly_key_eqb_sym, IH. reflexivity.
  Qed.

  Lemma poly_coefficient_normal : forall x r,
    poly_coefficient X.eqb x (poly_normal_row X.encode r) =
      poly_coefficient X.eqb x r.
  Proof.
    intros x r. rewrite <- !coef_of_poly_coefficient.
    cbn [poly_normal_row lhs]. apply coef_of_normal.
  Qed.

  Lemma coef_of_filter : forall x y xs,
    C.coef_of y (filter (fun p => negb (X.eqb x (fst p))) xs) =
      if X.eqb y x then 0%Z else C.coef_of y xs.
  Proof.
    intros x y xs. induction xs as [|[z a] xs IH].
    - cbn [filter C.coef_of]. destruct (X.eqb y x); reflexivity.
    - destruct (X.eqb_spec y x) as [Hyx|Hyx].
      + subst y. cbn [filter fst].
        destruct (X.eqb x z) eqn:Hxz; cbn [negb].
        * exact IH.
        * rewrite coef_of_cons, Hxz. exact IH.
      + cbn [filter fst]. destruct (X.eqb_spec x z) as [Hxz|Hxz].
        * subst z. cbn [negb]. rewrite IH, coef_of_cons.
          destruct (X.eqb_spec y x) as [Heq|Hneq]; [contradiction|reflexivity].
        * cbn [negb]. rewrite !coef_of_cons, IH. reflexivity.
  Qed.

  Lemma eval_coef_split : forall x xs (v : X.t -> Z),
    eval_coef v xs = (C.coef_of x xs * v x +
      eval_coef v (filter (fun p => negb (X.eqb x (fst p))) xs))%Z.
  Proof.
    intros x xs v. induction xs as [|[y a] xs IH]; [reflexivity|].
    rewrite coef_of_cons. cbn [filter fst].
    destruct (X.eqb_spec x y) as [Hxy|Hxy].
    - subst y.
      change (a * v x + eval_coef v xs = (a + C.coef_of x xs) * v x +
        eval_coef v (filter (fun p => negb (X.eqb x (fst p))) xs))%Z.
      rewrite IH. ring.
    - change (a * v y + eval_coef v xs = C.coef_of x xs * v x +
        (a * v y + eval_coef v (filter (fun p => negb (X.eqb x (fst p))) xs)))%Z.
      rewrite IH. ring.
  Qed.

  Lemma eval_coef_zero : forall xs (v : X.t -> Z),
    (forall x, C.coef_of x xs = 0%Z) -> eval_coef v xs = 0%Z.
  Proof.
    refine (well_founded_induction
      (well_founded_ltof _ (@length (X.t * Z))) _ _).
    intros xs IH v Hzero. destruct xs as [|[x a] xs]; [reflexivity|].
    rewrite (eval_coef_split x ((x, a) :: xs) v), Hzero.
    rewrite Z.mul_0_l, Z.add_0_l. apply IH.
    - unfold ltof. cbn [filter fst length]. rewrite poly_key_eqb_refl. cbn [negb].
      pose proof (filter_length_le (fun p => negb (X.eqb x (fst p))) xs). lia.
    - intro y. rewrite coef_of_filter.
      destruct (X.eqb y x); [reflexivity|apply Hzero].
  Qed.

  Lemma eval_coef_ext : forall xs ys (v : X.t -> Z),
    (forall x, C.coef_of x xs = C.coef_of x ys) ->
    eval_coef v xs = eval_coef v ys.
  Proof.
    intros xs ys v Heq.
    assert (Hzero : forall x, C.coef_of x (xs ++ poly_scale_coef (-1)%Z ys) = 0%Z).
    { intro x. rewrite coef_of_app, coef_of_scale, Heq. ring. }
    pose proof (eval_coef_zero _ v Hzero) as Heval.
    rewrite eval_coef_app, eval_coef_scale in Heval. lia.
  Qed.

  Lemma eval_coef_app_Q : forall (v : X.t -> Q) xs ys,
    (poly_eval_coef_Q v (xs ++ ys) ==
      poly_eval_coef_Q v xs + poly_eval_coef_Q v ys)%Q.
  Proof.
    intros v xs ys. induction xs as [|[x a] xs IH].
    - change (poly_eval_coef_Q v ys == 0 + poly_eval_coef_Q v ys)%Q. ring.
    - change (inject_Z a * v x + poly_eval_coef_Q v (xs ++ ys) ==
        (inject_Z a * v x + poly_eval_coef_Q v xs) + poly_eval_coef_Q v ys)%Q.
      setoid_rewrite IH. ring.
  Qed.

  Lemma eval_coef_scale_Q : forall a xs (v : X.t -> Q),
    (poly_eval_coef_Q v (poly_scale_coef a xs) == inject_Z a * poly_eval_coef_Q v xs)%Q.
  Proof.
    intros a xs v. induction xs as [|[x z] xs IH].
    - change (0 == inject_Z a * 0)%Q. ring.
    - change (inject_Z (a * z) * v x + poly_eval_coef_Q v (poly_scale_coef a xs) ==
        inject_Z a * (inject_Z z * v x + poly_eval_coef_Q v xs))%Q.
      rewrite inject_Z_mult. setoid_rewrite IH. ring.
  Qed.

  Lemma eval_coef_split_Q : forall x xs (v : X.t -> Q),
    (poly_eval_coef_Q v xs == inject_Z (C.coef_of x xs) * v x +
      poly_eval_coef_Q v (filter (fun p => negb (X.eqb x (fst p))) xs))%Q.
  Proof.
    intros x xs v. induction xs as [|[y a] xs IH].
    - change (0 == 0 * v x + 0)%Q. ring.
    - rewrite coef_of_cons. cbn [filter fst].
      destruct (X.eqb_spec x y) as [Hxy|Hxy].
      + subst y.
        change (inject_Z a * v x + poly_eval_coef_Q v xs ==
          inject_Z (a + C.coef_of x xs) * v x +
          poly_eval_coef_Q v (filter (fun p => negb (X.eqb x (fst p))) xs))%Q.
        rewrite inject_Z_plus. setoid_rewrite IH. ring.
      + change (inject_Z a * v y + poly_eval_coef_Q v xs ==
          inject_Z (C.coef_of x xs) * v x + (inject_Z a * v y +
          poly_eval_coef_Q v (filter (fun p => negb (X.eqb x (fst p))) xs)))%Q.
        setoid_rewrite IH. ring.
  Qed.

  Lemma eval_coef_zero_Q : forall xs (v : X.t -> Q),
    (forall x, C.coef_of x xs = 0%Z) -> (poly_eval_coef_Q v xs == 0)%Q.
  Proof.
    refine (well_founded_induction
      (well_founded_ltof _ (@length (X.t * Z))) _ _).
    intros xs IH v Hzero. destruct xs as [|[x a] xs]; [reflexivity|].
    setoid_rewrite (eval_coef_split_Q x ((x, a) :: xs) v). rewrite Hzero.
    setoid_rewrite Qmult_0_l. setoid_rewrite Qplus_0_l. apply IH.
    - unfold ltof. cbn [filter fst length]. rewrite poly_key_eqb_refl. cbn [negb].
      pose proof (filter_length_le (fun p => negb (X.eqb x (fst p))) xs). lia.
    - intro y. rewrite coef_of_filter.
      destruct (X.eqb y x); [reflexivity|apply Hzero].
  Qed.

  Lemma eval_coef_ext_Q : forall xs ys (v : X.t -> Q),
    (forall x, C.coef_of x xs = C.coef_of x ys) ->
    (poly_eval_coef_Q v xs == poly_eval_coef_Q v ys)%Q.
  Proof.
    intros xs ys v Heq.
    assert (Hzero : forall x, C.coef_of x (xs ++ poly_scale_coef (-1)%Z ys) = 0%Z).
    { intro x. rewrite coef_of_app, coef_of_scale, Heq. ring. }
    pose proof (eval_coef_zero_Q _ v Hzero) as Heval.
    setoid_rewrite eval_coef_app_Q in Heval. setoid_rewrite eval_coef_scale_Q in Heval.
    change (poly_eval_coef_Q v xs + (-1) * poly_eval_coef_Q v ys == 0)%Q in Heval.
    apply (proj1 (Qplus_inj_r (poly_eval_coef_Q v xs) (poly_eval_coef_Q v ys)
      (- poly_eval_coef_Q v ys)%Q)).
    setoid_replace (poly_eval_coef_Q v ys + - poly_eval_coef_Q v ys)%Q with 0%Q by ring.
    setoid_replace (poly_eval_coef_Q v xs + - poly_eval_coef_Q v ys)%Q
      with (poly_eval_coef_Q v xs + (-1) * poly_eval_coef_Q v ys)%Q by ring.
    exact Heval.
  Qed.

  (** The integer normalization algorithm also preserves rational evaluations. *)
  Lemma normalize_coef_eval_Q : forall (v : X.t -> Q) xs,
    (poly_eval_coef_Q v (poly_normal_coef X.encode xs) == poly_eval_coef_Q v xs)%Q.
  Proof.
    intros v xs. apply eval_coef_ext_Q. intro x. apply coef_of_normal.
  Qed.

  (** Source sums use the same truncated pairing as the public certificate specification. *)
  Definition poly_sum (P : list (lcons X.t)) (ms : list Z)
      (entry : lcons X.t -> Z) : Z :=
    fold_right Z.add 0%Z
      (map (fun pm => (snd pm * entry (fst pm))%Z) (List.combine P ms)).

  (** Tracked rows retain exact coefficients, right side, and equality status. *)
  Definition poly_tracks (P : list (lcons X.t)) (r : poly_row X.t) : Prop :=
    C.admissible P (poly_multipliers r) /\
    (forall x, C.coef_of x (lhs (poly_constraint r)) =
      C.comb_coef P (poly_multipliers r) x) /\
    rhs (poly_constraint r) = C.comb_rhs P (poly_multipliers r) /\
    lrel (poly_constraint r) =
      (if C.comb_eq P (poly_multipliers r) then REq else RLe).

  Lemma poly_admissible_cons : forall p P m ms,
    C.admissible (p :: P) (m :: ms) <->
      (lrel p = RLe -> (0 <= m)%Z) /\ C.admissible P ms.
  Proof.
    intros p P m ms. unfold C.admissible. split.
    - intros [Hlength Hweights]. inversion Hweights as [|p' m' P' ms' Hhead Htail];
        subst p' m' P' ms'. split; [exact Hhead|]. split; [cbn [length] in Hlength; lia|].
      exact Htail.
    - intros [Hhead [Hlength Htail]]. split; [cbn [length]; lia|].
      constructor; assumption.
  Qed.

  Lemma poly_comb_coef_cons : forall p P m ms x,
    C.comb_coef (p :: P) (m :: ms) x =
      (m * C.coef_of x (lhs p) + C.comb_coef P ms x)%Z.
  Proof.
    reflexivity.
  Qed.

  Lemma poly_comb_rhs_cons : forall p P m ms,
    C.comb_rhs (p :: P) (m :: ms) = (m * rhs p + C.comb_rhs P ms)%Z.
  Proof.
    reflexivity.
  Qed.

  Lemma poly_comb_eq_cons : forall p P m ms,
    C.comb_eq (p :: P) (m :: ms) =
      (match lrel p with REq => true | RLe => Z.eqb m 0 end) && C.comb_eq P ms.
  Proof.
    reflexivity.
  Qed.

  Lemma poly_sum_weighted : forall P ms ns a b entry,
    length P = length ms -> length P = length ns ->
    poly_sum P (poly_weighted a ms b ns) entry =
      (a * poly_sum P ms entry + b * poly_sum P ns entry)%Z.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] [|n ns] a b entry Hms Hns;
      cbn [length] in Hms, Hns; try discriminate.
    - change (0 = a * 0 + b * 0)%Z. ring.
    - change ((a * m + b * n) * entry p +
        poly_sum P (poly_weighted a ms b ns) entry =
        a * (m * entry p + poly_sum P ms entry) +
        b * (n * entry p + poly_sum P ns entry))%Z.
      rewrite (IH ms ns a b entry) by lia. ring.
  Qed.

  Lemma poly_comb_coef_weighted : forall P ms ns a b x,
    length P = length ms -> length P = length ns ->
    C.comb_coef P (poly_weighted a ms b ns) x =
      (a * C.comb_coef P ms x + b * C.comb_coef P ns x)%Z.
  Proof.
    intros P ms ns a b x Hms Hns.
    change (poly_sum P (poly_weighted a ms b ns) (fun r => C.coef_of x (lhs r)) =
      (a * poly_sum P ms (fun r => C.coef_of x (lhs r)) +
       b * poly_sum P ns (fun r => C.coef_of x (lhs r)))%Z).
    now apply poly_sum_weighted.
  Qed.

  Lemma poly_comb_rhs_weighted : forall P ms ns a b,
    length P = length ms -> length P = length ns ->
    C.comb_rhs P (poly_weighted a ms b ns) =
      (a * C.comb_rhs P ms + b * C.comb_rhs P ns)%Z.
  Proof.
    intros P ms ns a b Hms Hns.
    change (poly_sum P (poly_weighted a ms b ns) rhs =
      (a * poly_sum P ms rhs + b * poly_sum P ns rhs)%Z).
    now apply poly_sum_weighted.
  Qed.

  Lemma poly_mul_eqb_zero : forall a m,
    Z.eqb (a * m) 0 = (Z.eqb a 0 || Z.eqb m 0).
  Proof.
    intros a m. destruct (Z.eqb_spec a 0) as [Ha|Ha].
    - subst a. reflexivity.
    - destruct (Z.eqb_spec m 0) as [Hm|Hm].
      + subst m. now rewrite Z.mul_0_r.
      + apply Z.eqb_neq. intro Hzero. apply Z.mul_eq_0 in Hzero. tauto.
  Qed.

  Lemma poly_add_eqb_zero : forall m n, (0 <= m)%Z -> (0 <= n)%Z ->
    Z.eqb (m + n) 0 = (Z.eqb m 0 && Z.eqb n 0).
  Proof.
    intros m n Hm Hn. destruct (Z.eqb_spec m 0) as [Hm0|Hm0].
    - subst m. reflexivity.
    - destruct (Z.eqb_spec n 0) as [Hn0|Hn0].
      + subst n. apply Z.eqb_neq. lia.
      + apply Z.eqb_neq. lia.
  Qed.

  Lemma poly_comb_eq_scale : forall P ms a,
    C.comb_eq P (map (fun m => (a * m)%Z) ms) =
      (Z.eqb a 0 || C.comb_eq P ms).
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] a.
    - cbn [map C.comb_eq List.combine forallb]. now rewrite orb_true_r.
    - cbn [map C.comb_eq List.combine forallb]. now rewrite orb_true_r.
    - cbn [map C.comb_eq List.combine forallb]. now rewrite orb_true_r.
    - cbn [map]. rewrite !poly_comb_eq_cons, IH.
      destruct (lrel p); cbn [andb]; [reflexivity|].
      rewrite poly_mul_eqb_zero.
      destruct (Z.eqb a 0), (Z.eqb m 0), (C.comb_eq P ms); reflexivity.
  Qed.

  (** Signed scaling is admissible when the source combination is an equality. *)
  Lemma poly_admissible_scale : forall P ms a,
    C.admissible P ms -> (C.comb_eq P ms = true \/ (0 <= a)%Z) ->
    C.admissible P (map (fun m => (a * m)%Z) ms).
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] a Hadmissible Hsign;
      try (destruct Hadmissible as [Hlength _]; cbn [length] in Hlength; discriminate).
    - split; [reflexivity|constructor].
    - apply poly_admissible_cons in Hadmissible as [Hhead Htail].
      cbn [map]. apply poly_admissible_cons. split.
      + intro Hrel. destruct Hsign as [Hequality|Hpositive].
        * rewrite poly_comb_eq_cons, Hrel in Hequality.
          apply andb_true_iff in Hequality as [Hzero _]. apply Z.eqb_eq in Hzero.
          subst m. lia.
        * pose proof (Hhead Hrel). nia.
      + apply IH; [exact Htail|]. destruct Hsign as [Hequality|Hpositive];
          [left|now right].
        rewrite poly_comb_eq_cons in Hequality.
        apply andb_true_iff in Hequality as [_ Htail_eq]. exact Htail_eq.
  Qed.

  Lemma poly_admissible_add : forall P ms ns,
    C.admissible P ms -> C.admissible P ns ->
    C.admissible P (poly_weighted 1%Z ms 1%Z ns).
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] [|n ns] Hms Hns;
      try (destruct Hms as [Hlength _]; cbn [length] in Hlength; discriminate);
      try (destruct Hns as [Hlength _]; cbn [length] in Hlength; discriminate).
    - split; [reflexivity|constructor].
    - apply poly_admissible_cons in Hms as [Hm Hms].
      apply poly_admissible_cons in Hns as [Hn Hns].
      cbn [poly_weighted]. apply poly_admissible_cons. split.
      + intro Hrel. specialize (Hm Hrel). specialize (Hn Hrel). lia.
      + now apply IH.
  Qed.

  Lemma poly_comb_eq_add : forall P ms ns,
    C.admissible P ms -> C.admissible P ns ->
    C.comb_eq P (poly_weighted 1%Z ms 1%Z ns) =
      (C.comb_eq P ms && C.comb_eq P ns).
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] [|n ns] Hms Hns;
      try (destruct Hms as [Hlength _]; cbn [length] in Hlength; discriminate);
      try (destruct Hns as [Hlength _]; cbn [length] in Hlength; discriminate).
    - reflexivity.
    - apply poly_admissible_cons in Hms as [Hm Hms].
      apply poly_admissible_cons in Hns as [Hn Hns].
      cbn [poly_weighted]. rewrite !poly_comb_eq_cons, (IH ms ns Hms Hns).
      destruct (lrel p) eqn:Hrel; [reflexivity|].
      replace (1 * m + 1 * n)%Z with (m + n)%Z by ring.
      rewrite poly_add_eqb_zero by auto.
      destruct (Z.eqb m 0), (Z.eqb n 0), (C.comb_eq P ms), (C.comb_eq P ns);
        reflexivity.
  Qed.

  Lemma poly_weighted_as_add : forall ms ns a b,
    poly_weighted a ms b ns =
      poly_weighted 1%Z (map (fun m => (a * m)%Z) ms)
        1%Z (map (fun n => (b * n)%Z) ns).
  Proof.
    intro ms. induction ms as [|m ms IH]; intros [|n ns] a b;
      cbn [poly_weighted map]; try reflexivity.
    f_equal; [ring|apply IH].
  Qed.

  Lemma poly_weighted_admissible_eq : forall P ms ns a b,
    C.admissible P ms -> C.admissible P ns ->
    (C.comb_eq P ms = true \/ (0 <= a)%Z) ->
    (C.comb_eq P ns = true \/ (0 <= b)%Z) ->
    C.admissible P (poly_weighted a ms b ns) /\
      C.comb_eq P (poly_weighted a ms b ns) =
        ((Z.eqb a 0 || C.comb_eq P ms) && (Z.eqb b 0 || C.comb_eq P ns)).
  Proof.
    intros P ms ns a b Hms Hns Hsigna Hsignb.
    pose proof (poly_admissible_scale P ms a Hms Hsigna) as Ha.
    pose proof (poly_admissible_scale P ns b Hns Hsignb) as Hb.
    rewrite poly_weighted_as_add. split.
    - now apply poly_admissible_add.
    - rewrite poly_comb_eq_add by assumption. now rewrite !poly_comb_eq_scale.
  Qed.

  (** Combining tracked rows preserves their exact source certificate. *)
  Lemma poly_add_rows_tracks : forall P p q a b,
    poly_tracks P p -> poly_tracks P q ->
    (lrel (poly_constraint p) = RLe -> (0 <= a)%Z) ->
    (lrel (poly_constraint q) = RLe -> (0 <= b)%Z) ->
    poly_tracks P (poly_add_rows X.encode a p b q).
  Proof.
    intros P p q a b [Hmp [Hcp [Hrp Hep]]] [Hmq [Hcq [Hrq Heq]]] Hpa Hqb.
    assert (Hsigna : C.comb_eq P (poly_multipliers p) = true \/ (0 <= a)%Z).
    { destruct (C.comb_eq P (poly_multipliers p)) eqn:Hused; [now left|right].
      apply Hpa. rewrite Hep. now rewrite ?Hused. }
    assert (Hsignb : C.comb_eq P (poly_multipliers q) = true \/ (0 <= b)%Z).
    { destruct (C.comb_eq P (poly_multipliers q)) eqn:Hused; [now left|right].
      apply Hqb. rewrite Heq. now rewrite ?Hused. }
    destruct (poly_weighted_admissible_eq P (poly_multipliers p)
      (poly_multipliers q) a b Hmp Hmq Hsigna Hsignb) as [Hweights Hequality].
    unfold poly_tracks, poly_add_rows. cbn [poly_constraint poly_multipliers lhs rhs lrel].
    split; [exact Hweights|]. split.
    - intro x. rewrite coef_of_normal, coef_of_app, !coef_of_scale, Hcp, Hcq.
      symmetry. apply poly_comb_coef_weighted; [exact (proj1 Hmp)|exact (proj1 Hmq)].
    - split.
      + rewrite Hrp, Hrq. symmetry. apply poly_comb_rhs_weighted;
          [exact (proj1 Hmp)|exact (proj1 Hmq)].
      + rewrite Hequality. unfold poly_eq_used. rewrite Hep, Heq.
        destruct (C.comb_eq P (poly_multipliers p)),
          (C.comb_eq P (poly_multipliers q)), (Z.eqb a 0), (Z.eqb b 0); reflexivity.
  Qed.

  Lemma poly_zero_admissible : forall P,
    C.admissible P (repeat 0%Z (length P)).
  Proof.
    intro P. induction P as [|p P IH].
    - split; [reflexivity|constructor].
    - cbn [length repeat]. apply poly_admissible_cons. split; [lia|exact IH].
  Qed.

  Lemma poly_sum_zero : forall P entry,
    poly_sum P (repeat 0%Z (length P)) entry = 0%Z.
  Proof.
    intro P. induction P as [|p P IH]; intro entry; [reflexivity|].
    change (0 * entry p + poly_sum P (repeat 0%Z (length P)) entry = 0)%Z.
    rewrite IH. ring.
  Qed.

  Lemma poly_comb_eq_zero : forall P,
    C.comb_eq P (repeat 0%Z (length P)) = true.
  Proof.
    intro P. induction P as [|p P IH]; [reflexivity|].
    cbn [length repeat]. rewrite poly_comb_eq_cons, IH. destruct (lrel p); reflexivity.
  Qed.

  Lemma poly_map_zero : forall A (xs : list A),
    map (fun _ => 0%Z) xs = repeat 0%Z (length xs).
  Proof.
    intros A xs. induction xs as [|x xs IH]; cbn [map length repeat]; congruence.
  Qed.

  Lemma poly_initial_head_tracks : forall p P flag,
    poly_tracks (p :: P)
      (PolyRow X.t (poly_normal_row X.encode p) (1%Z :: repeat 0%Z (length P)) flag).
  Proof.
    intros p P flag. unfold poly_tracks.
    cbn [poly_multipliers poly_constraint poly_normal_row lhs rhs lrel].
    split.
    - apply poly_admissible_cons. split; [lia|apply poly_zero_admissible].
    - split.
      + intro x. rewrite coef_of_normal, poly_comb_coef_cons.
        change (C.coef_of x (lhs p) = 1 * C.coef_of x (lhs p) +
          poly_sum P (repeat 0%Z (length P)) (fun r => C.coef_of x (lhs r)))%Z.
        rewrite poly_sum_zero. ring.
      + split.
        * rewrite poly_comb_rhs_cons.
          change (rhs p = 1 * rhs p + poly_sum P (repeat 0%Z (length P)) rhs)%Z.
          rewrite poly_sum_zero. ring.
        * rewrite poly_comb_eq_cons, poly_comb_eq_zero. destruct (lrel p); reflexivity.
  Qed.

  Lemma poly_pad_tracks : forall p P r, poly_tracks P r ->
    poly_tracks (p :: P) (poly_pad_row r).
  Proof.
    intros p P r [Hweights [Hcoef [Hrhs Hrel]]].
    unfold poly_tracks, poly_pad_row. cbn [poly_constraint poly_multipliers].
    split.
    - apply poly_admissible_cons. split; [lia|exact Hweights].
    - split.
      + intro x. rewrite poly_comb_coef_cons, Hcoef. ring.
      + split.
        * rewrite poly_comb_rhs_cons, Hrhs. ring.
        * rewrite poly_comb_eq_cons. destruct (lrel p); cbn; exact Hrel.
  Qed.

  Lemma poly_initial_tracks : forall rows,
    Forall (poly_tracks (map fst rows)) (poly_initial X.encode rows).
  Proof.
    intro rows. induction rows as [|[p flag] rows IH]; [constructor|].
    cbn [poly_initial map fst snd]. constructor.
    - replace (map (fun _ : lcons X.t * bool => 0%Z) rows)
        with (repeat 0%Z (length (map fst rows))).
      + apply poly_initial_head_tracks.
      + rewrite length_map, poly_map_zero. reflexivity.
    - apply Forall_map. apply Forall_forall. intros r Hin. apply poly_pad_tracks.
      exact (proj1 (Forall_forall _ _) IH r Hin).
  Qed.

  Lemma poly_cancel_tracks : forall P x p r,
    poly_tracks P p -> poly_tracks P r -> lrel (poly_constraint p) = REq ->
    poly_tracks P (poly_cancel X.encode X.eqb x p r).
  Proof.
    intros P x p r Hp Hr Heq. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0); [exact Hr|].
    apply poly_add_rows_tracks; [exact Hp|exact Hr| |].
    - intro Hfalse. congruence.
    - intros _. apply Z.abs_nonneg.
  Qed.

  Lemma poly_step_tracks : forall P x rows,
    Forall (poly_tracks P) rows ->
    Forall (poly_tracks P) (poly_step X.encode X.eqb x rows).
  Proof.
    intros P x rows Htracks. unfold poly_step.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - apply find_some in Hfind as [Hmember Hpivot].
      assert (Hp : poly_tracks P p) by
        exact (proj1 (Forall_forall _ _) Htracks p Hmember).
      assert (Heq : lrel (poly_constraint p) = REq).
      { unfold poly_pivot in Hpivot. destruct (lrel (poly_constraint p));
          [reflexivity|discriminate]. }
      apply Forall_map. apply Forall_forall. intros r Hin.
      apply poly_cancel_tracks; [exact Hp| |exact Heq].
      exact (proj1 (Forall_forall _ _) Htracks r Hin).
    - apply Forall_app. split; apply Forall_forall; intros r Hin.
      + apply filter_In in Hin as [Hin _].
        exact (proj1 (Forall_forall _ _) Htracks r Hin).
      + apply in_flat_map in Hin as [p [Hp Hin]].
        apply in_map_iff in Hin as [q [Hsame Hq]]. subst r.
        apply filter_In in Hp as [Hp Hpositive]. apply Z.ltb_lt in Hpositive.
        apply filter_In in Hq as [Hq Hnegative]. apply Z.ltb_lt in Hnegative.
        apply poly_add_rows_tracks.
        * exact (proj1 (Forall_forall _ _) Htracks p Hp).
        * exact (proj1 (Forall_forall _ _) Htracks q Hq).
        * intros _. lia.
        * intros _. lia.
  Qed.

  Lemma poly_run_tracks : forall xs P rows,
    Forall (poly_tracks P) rows ->
    Forall (poly_tracks P) (poly_run X.encode X.eqb xs rows).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros P rows Htracks; [exact Htracks|].
    cbn [poly_run]. apply IH. now apply poly_step_tracks.
  Qed.

  (** Every tracked row has the exact public combination promised by its weights. *)
  Lemma poly_tracks_combine : forall P r, poly_tracks P r ->
    exists s, C.combine P (poly_multipliers r) = Some s /\
      lrel s = lrel (poly_constraint r) /\ rhs s = rhs (poly_constraint r) /\
      forall v : X.t -> Z, eval_coef v (lhs s) = eval_coef v (lhs (poly_constraint r)).
  Proof.
    intros P r [Hweights [Hcoef [Hrhs Hrel]]].
    destruct (C.combine_spec P (poly_multipliers r) Hweights)
      as [s [Hcombine [Hscoef [Hsrhs Hsrel]]]].
    exists s. split; [exact Hcombine|]. split; [congruence|].
    split; [congruence|]. intro v. apply eval_coef_ext. intro x.
    rewrite Hscoef, Hcoef. reflexivity.
  Qed.

  Lemma fm_step_mults_checked : forall P x r, In r (fm_elim x P) ->
    exists s, C.combine P (mults_of r) = Some s /\ lrel s = lrel (row_of r) /\
      rhs s = rhs (row_of r) /\
      forall v : X.t -> Z, eval_coef v (lhs s) = eval_coef v (lhs (row_of r)).
  Proof.
    intros P x r Hin. unfold fm_elim in Hin.
    apply in_map_iff in Hin as [s [Hsame Hmember]]. subst r.
    cbn [row_of mults_of]. apply poly_tracks_combine.
    assert (Hsource : map fst (map (fun p => (p, false)) P) = P).
    { rewrite map_map. change (map (fun p => p) P = P). apply map_id. }
    pose proof (poly_initial_tracks (map (fun p => (p, false)) P)) as Hinitial.
    rewrite Hsource in Hinitial.
    exact (proj1 (Forall_forall _ _) (poly_step_tracks P x _ Hinitial) s Hmember).
  Qed.

  (** The strict flag records exactly a positive weight of the strict target complement. *)
  Definition poly_target_strict (r : poly_row X.t) : Prop :=
    forall sc ms, poly_multipliers r = sc :: ms -> poly_strict r = (0 <? sc)%Z.

  Lemma poly_tracks_scale_admissible : forall P r a,
    poly_tracks P r ->
    (lrel (poly_constraint r) = RLe -> (0 <= a)%Z) ->
    C.admissible P (map (fun m => (a * m)%Z) (poly_multipliers r)).
  Proof.
    intros P r a [Hweights [_ [_ Hrel]]] Hpositive. apply poly_admissible_scale;
      [exact Hweights|].
    destruct (C.comb_eq P (poly_multipliers r)) eqn:Hused; [now left|right].
    apply Hpositive. rewrite Hrel. now rewrite ?Hused.
  Qed.

  Lemma poly_positive_product : forall a m, (0 <= m)%Z ->
    (0 <? a * m)%Z = ((0 <? a)%Z && (0 <? m)%Z).
  Proof.
    intros a m Hm. destruct (Z.ltb_spec 0 a), (Z.ltb_spec 0 m); cbn [andb].
    - apply Z.ltb_lt. nia.
    - apply Z.ltb_ge. nia.
    - apply Z.ltb_ge. nia.
    - apply Z.ltb_ge. nia.
  Qed.

  Lemma poly_positive_sum : forall m n, (0 <= m)%Z -> (0 <= n)%Z ->
    (0 <? m + n)%Z = ((0 <? m)%Z || (0 <? n)%Z).
  Proof.
    intros m n Hm Hn. destruct (Z.ltb_spec 0 m), (Z.ltb_spec 0 n); cbn [orb].
    - apply Z.ltb_lt. lia.
    - apply Z.ltb_lt. lia.
    - apply Z.ltb_lt. lia.
    - apply Z.ltb_ge. lia.
  Qed.

  Lemma poly_add_rows_target_strict : forall target P p q a b,
    lrel target = RLe -> poly_tracks (target :: P) p -> poly_tracks (target :: P) q ->
    poly_target_strict p -> poly_target_strict q ->
    (lrel (poly_constraint p) = RLe -> (0 <= a)%Z) ->
    (lrel (poly_constraint q) = RLe -> (0 <= b)%Z) ->
    poly_target_strict (poly_add_rows X.encode a p b q).
  Proof.
    intros target P [pr [|m ms] ps] [qr [|n ns] qs] a b Htarget Hp Hq Hps Hqs Ha Hb;
      unfold poly_target_strict; intros sc weights Hweights;
      cbn [poly_add_rows poly_multipliers poly_weighted] in Hweights;
      try discriminate.
    injection Hweights as Hsc Htail. subst sc weights.
    pose proof (proj1 Hp) as Hm. pose proof (proj1 Hq) as Hn.
    apply poly_admissible_cons in Hm as [Hm _].
    apply poly_admissible_cons in Hn as [Hn _].
    specialize (Hm Htarget). specialize (Hn Htarget).
    pose proof (poly_tracks_scale_admissible _ _ a Hp Ha) as Ham.
    pose proof (poly_tracks_scale_admissible _ _ b Hq Hb) as Hbn.
    cbn [poly_multipliers map] in Ham, Hbn.
    apply poly_admissible_cons in Ham as [Ham _].
    apply poly_admissible_cons in Hbn as [Hbn _].
    specialize (Ham Htarget). specialize (Hbn Htarget).
    cbn [poly_add_rows poly_strict].
    specialize (Hps m ms eq_refl). specialize (Hqs n ns eq_refl).
    cbn [poly_strict] in Hps, Hqs. rewrite Hps, Hqs.
    rewrite poly_positive_sum by assumption.
    rewrite !poly_positive_product by assumption. reflexivity.
  Qed.

  Lemma poly_initial_false_strict : forall rows,
    Forall (fun r => poly_strict r = false)
      (poly_initial X.encode (map (fun r => (r, false)) rows)).
  Proof.
    intro rows. induction rows as [|r rows IH]; [constructor|].
    cbn [map poly_initial fst snd]. constructor; [reflexivity|].
    apply Forall_map. exact IH.
  Qed.

  Lemma poly_pad_target_strict : forall r, poly_strict r = false ->
    poly_target_strict (poly_pad_row r).
  Proof.
    intros r Hfalse sc ms Hweights. cbn [poly_pad_row poly_multipliers] in Hweights.
    injection Hweights as Hsc Htail. subst sc ms.
    cbn [poly_pad_row poly_strict]. exact Hfalse.
  Qed.

  Lemma poly_initial_target_strict : forall target P,
    Forall poly_target_strict
      (poly_initial X.encode ((target, true) :: map (fun r => (r, false)) P)).
  Proof.
    intros target P. cbn [poly_initial fst snd]. constructor.
    - intros sc ms Hweights. cbn [poly_multipliers] in Hweights.
      injection Hweights as Hsc Htail. subst sc ms. reflexivity.
    - apply Forall_map. apply Forall_forall. intros r Hin. apply poly_pad_target_strict.
      exact (proj1 (Forall_forall _ _) (poly_initial_false_strict P) r Hin).
  Qed.

  Lemma poly_cancel_target_strict : forall target P x p r,
    lrel target = RLe -> poly_tracks (target :: P) p -> poly_tracks (target :: P) r ->
    poly_target_strict p -> poly_target_strict r -> lrel (poly_constraint p) = REq ->
    poly_target_strict (poly_cancel X.encode X.eqb x p r).
  Proof.
    intros target P x p r Htarget Hp Hr Hps Hrs Heq. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0); [exact Hrs|].
    apply poly_add_rows_target_strict with (target := target) (P := P);
      try assumption.
    - intro Hfalse. congruence.
    - intros _. apply Z.abs_nonneg.
  Qed.

  Lemma poly_step_target_strict : forall target P x rows,
    lrel target = RLe -> Forall (poly_tracks (target :: P)) rows ->
    Forall poly_target_strict rows ->
    Forall poly_target_strict (poly_step X.encode X.eqb x rows).
  Proof.
    intros target P x rows Htarget Htracks Hstrict. unfold poly_step.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - apply find_some in Hfind as [Hmember Hpivot].
      assert (Heq : lrel (poly_constraint p) = REq).
      { unfold poly_pivot in Hpivot. destruct (lrel (poly_constraint p));
          [reflexivity|discriminate]. }
      apply Forall_map. apply Forall_forall. intros r Hin.
      apply poly_cancel_target_strict with (target := target) (P := P);
        try assumption.
      + exact (proj1 (Forall_forall _ _) Htracks p Hmember).
      + exact (proj1 (Forall_forall _ _) Htracks r Hin).
      + exact (proj1 (Forall_forall _ _) Hstrict p Hmember).
      + exact (proj1 (Forall_forall _ _) Hstrict r Hin).
    - apply Forall_app. split; apply Forall_forall; intros r Hin.
      + apply filter_In in Hin as [Hin _].
        exact (proj1 (Forall_forall _ _) Hstrict r Hin).
      + apply in_flat_map in Hin as [p [Hp Hin]].
        apply in_map_iff in Hin as [q [Hsame Hq]]. subst r.
        apply filter_In in Hp as [Hp Hpositive]. apply Z.ltb_lt in Hpositive.
        apply filter_In in Hq as [Hq Hnegative]. apply Z.ltb_lt in Hnegative.
        apply poly_add_rows_target_strict with (target := target) (P := P);
          [exact Htarget| | | | | |].
        * exact (proj1 (Forall_forall _ _) Htracks p Hp).
        * exact (proj1 (Forall_forall _ _) Htracks q Hq).
        * exact (proj1 (Forall_forall _ _) Hstrict p Hp).
        * exact (proj1 (Forall_forall _ _) Hstrict q Hq).
        * intros _. lia.
        * intros _. lia.
  Qed.

  Lemma poly_run_target_strict : forall xs target P rows,
    lrel target = RLe -> Forall (poly_tracks (target :: P)) rows ->
    Forall poly_target_strict rows ->
    Forall poly_target_strict (poly_run X.encode X.eqb xs rows).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros target P rows Htarget Htracks Hstrict;
      [exact Hstrict|].
    cbn [poly_run]. apply IH with (target := target) (P := P); [exact Htarget| |].
    - now apply poly_step_tracks.
    - now apply poly_step_target_strict with (target := target) (P := P).
  Qed.

  Lemma poly_entailment_initial_tracks : forall c P,
    Forall (poly_tracks (poly_negate c :: P))
      (poly_initial X.encode
        ((poly_negate c, true) :: map (fun r => (r, false)) P)).
  Proof.
    intros c P. pose proof (poly_initial_tracks
      ((poly_negate c, true) :: map (fun r => (r, false)) P)) as Htracks.
    cbn [map fst] in Htracks. rewrite map_map in Htracks.
    change (Forall (poly_tracks (poly_negate c :: map (fun r => r) P))
      (poly_initial X.encode
        ((poly_negate c, true) :: map (fun r => (r, false)) P))) in Htracks.
    now rewrite map_id in Htracks.
  Qed.

  Lemma poly_entailment_tracks : forall xs c P,
    Forall (poly_tracks (poly_negate c :: P))
      (poly_run X.encode X.eqb xs (poly_initial X.encode
        ((poly_negate c, true) :: map (fun r => (r, false)) P))).
  Proof.
    intros xs c P. apply poly_run_tracks. apply poly_entailment_initial_tracks.
  Qed.

  Lemma poly_entailment_target_strict : forall xs c P,
    Forall poly_target_strict
      (poly_run X.encode X.eqb xs (poly_initial X.encode
        ((poly_negate c, true) :: map (fun r => (r, false)) P))).
  Proof.
    intros xs c P. apply poly_run_target_strict with (target := poly_negate c) (P := P).
    - reflexivity.
    - apply poly_entailment_initial_tracks.
    - apply poly_initial_target_strict.
  Qed.

  Lemma poly_contradiction_empty : forall (r : poly_row X.t), poly_contradiction r = true ->
    lhs (poly_constraint r) = nil.
  Proof.
    intros r Hcontra. unfold poly_contradiction in Hcontra.
    destruct (lhs (poly_constraint r)); [reflexivity|discriminate].
  Qed.

  Lemma poly_contradiction_eq_rhs : forall (r : poly_row X.t),
    lrel (poly_constraint r) = REq -> poly_contradiction r = true ->
    rhs (poly_constraint r) <> 0%Z.
  Proof.
    intros r Hrel Hcontra. unfold poly_contradiction in Hcontra. rewrite Hrel in Hcontra.
    destruct (lhs (poly_constraint r)); [|discriminate].
    now apply negb_true_iff, Z.eqb_neq in Hcontra.
  Qed.

  Lemma poly_contradiction_le_rhs : forall (r : poly_row X.t),
    lrel (poly_constraint r) = RLe -> poly_contradiction r = true ->
    (rhs (poly_constraint r) <= 0)%Z.
  Proof.
    intros r Hrel Hcontra. unfold poly_contradiction in Hcontra. rewrite Hrel in Hcontra.
    destruct (lhs (poly_constraint r)); [|discriminate].
    apply orb_true_iff in Hcontra as [Hnegative|Hstrict].
    - apply Z.ltb_lt in Hnegative. lia.
    - apply andb_true_iff in Hstrict as [_ Hnonpositive]. now apply Z.leb_le.
  Qed.

  Lemma poly_contradiction_nonstrict_rhs : forall (r : poly_row X.t),
    lrel (poly_constraint r) = RLe -> poly_strict r = false ->
    poly_contradiction r = true -> (rhs (poly_constraint r) < 0)%Z.
  Proof.
    intros r Hrel Hflag Hcontra. unfold poly_contradiction in Hcontra.
    rewrite Hrel, Hflag in Hcontra.
    destruct (lhs (poly_constraint r)); [|discriminate].
    cbn [andb] in Hcontra. rewrite orb_false_r in Hcontra. now apply Z.ltb_lt.
  Qed.

  (** A zero target residual gives the exact source certificate equations. *)
  Lemma poly_target_data : forall P c r sc ms,
    poly_tracks (poly_negate c :: P) r -> poly_multipliers r = sc :: ms ->
    lhs (poly_constraint r) = nil ->
    C.admissible P ms /\ (0 <= sc)%Z /\
    (forall x, C.comb_coef P ms x = (sc * C.coef_of x (lhs c))%Z) /\
    C.comb_rhs P ms = (rhs (poly_constraint r) + sc * rhs c)%Z /\
    (lrel (poly_constraint r) = REq -> sc = 0%Z /\ C.comb_eq P ms = true).
  Proof.
    intros P c r sc ms [Hweights [Hcoef [Hrhs Hrel]]] Hms Hlhs.
    rewrite Hms in Hweights, Hcoef, Hrhs, Hrel.
    apply poly_admissible_cons in Hweights as [Hnonnegative Htail].
    split; [exact Htail|]. split; [apply Hnonnegative; reflexivity|]. split.
    - intro x. pose proof (Hcoef x) as Heq. rewrite Hlhs in Heq.
      change (0%Z = C.comb_coef (poly_negate c :: P) (sc :: ms) x) in Heq.
      rewrite poly_comb_coef_cons in Heq. cbn [poly_negate lhs] in Heq.
      rewrite coef_of_scale in Heq. nia.
    - split.
      + rewrite poly_comb_rhs_cons in Hrhs. cbn [poly_negate rhs] in Hrhs. nia.
      + intro Hrowrel.
        assert (Hused : C.comb_eq (poly_negate c :: P) (sc :: ms) = true).
        { destruct (C.comb_eq (poly_negate c :: P) (sc :: ms));
            [reflexivity|congruence]. }
        rewrite poly_comb_eq_cons in Hused. cbn [poly_negate lrel] in Hused.
        apply andb_true_iff in Hused as [Hzero Hequality].
        apply Z.eqb_eq in Hzero. auto.
  Qed.

  (** A contradictory residual with zero target weight is a source contradiction. *)
  Lemma poly_zero_target_empty : forall P c r ms,
    poly_tracks (poly_negate c :: P) r -> poly_target_strict r ->
    poly_multipliers r = 0%Z :: ms -> poly_contradiction r = true ->
    C.check_empty P ms = true.
  Proof.
    intros P c r ms Htracks Hstrict Hweights Hcontra.
    destruct (poly_target_data P c r 0%Z ms Htracks Hweights
      (poly_contradiction_empty r Hcontra)) as [Hadmissible [_ [Hcoef [Hrhs Heq]]]].
    apply C.check_empty_complete; [exact Hadmissible| |].
    - intro x. specialize (Hcoef x). lia.
    - destruct (lrel (poly_constraint r)) eqn:Hrel.
      + right. destruct (Heq eq_refl) as [_ Hequality]. split; [exact Hequality|].
        pose proof (poly_contradiction_eq_rhs r Hrel Hcontra). lia.
      + left. assert (Hflag : poly_strict r = false) by exact (Hstrict 0%Z ms Hweights).
        pose proof (poly_contradiction_nonstrict_rhs r Hrel Hflag Hcontra). lia.
  Qed.

  (** Positive target weight turns a contradictory residual into a cut-free certificate. *)
  Lemma poly_positive_target_checked : forall P c r sc ms,
    lrel c = RLe -> poly_tracks (poly_negate c :: P) r ->
    poly_multipliers r = sc :: ms -> (0 < sc)%Z -> poly_contradiction r = true ->
    C.check_entails P c (Cert ms sc false) = true.
  Proof.
    intros P c r sc ms Htarget Htracks Hweights Hpositive Hcontra.
    destruct (poly_target_data P c r sc ms Htracks Hweights
      (poly_contradiction_empty r Hcontra)) as [Hadmissible [_ [Hcoef [Hrhs Heq]]]].
    assert (Hrel : lrel (poly_constraint r) = RLe).
    { destruct (lrel (poly_constraint r)); [|reflexivity].
      destruct (Heq eq_refl) as [Hzero _]. lia. }
    pose proof (poly_contradiction_le_rhs r Hrel Hcontra) as Hnonpositive.
    apply C.check_entails_complete; try assumption. rewrite Htarget. nia.
  Qed.

  (** Exact combination premises survive row normalization in both directions. *)
  Definition poly_exact_entail (P : list (lcons X.t)) (c : lcons X.t)
      (ms : list Z) (sc : Z) : Prop :=
    C.admissible P ms /\ (0 < sc)%Z /\
    (forall x, C.comb_coef P ms x = (sc * C.coef_of x (lhs c))%Z) /\
    match lrel c with
    | REq => C.comb_eq P ms = true /\ C.comb_rhs P ms = (sc * rhs c)%Z
    | RLe => (C.comb_rhs P ms <= sc * rhs c)%Z
    end.

  Definition poly_exact_empty (P : list (lcons X.t)) (ms : list Z) : Prop :=
    C.admissible P ms /\ (forall x, C.comb_coef P ms x = 0%Z) /\
    ((C.comb_rhs P ms < 0)%Z \/
      (C.comb_eq P ms = true /\ C.comb_rhs P ms <> 0%Z)).

  Definition poly_certificate_valid (P : list (lcons X.t)) (c : lcons X.t)
      (k : cert) : Prop :=
    cut k = false /\ (poly_exact_empty P (mults k) \/
      poly_exact_entail P c (mults k) (scale k)).

  Lemma poly_source_equal_spec : forall P ms,
    poly_source_equal P ms = C.comb_eq P ms.
  Proof. reflexivity. Qed.

  Lemma poly_normal_rows_admissible : forall P ms,
    C.admissible (poly_normal_rows P) ms <-> C.admissible P ms.
  Proof.
    intro P. induction P as [|p P IH]; intro ms; [reflexivity|].
    destruct ms as [|m ms].
    - split; intros [Hlength _]; cbn [poly_normal_rows map length] in Hlength; discriminate.
    - change (C.admissible (poly_normal_row X.encode p :: poly_normal_rows P) (m :: ms) <->
        C.admissible (p :: P) (m :: ms)).
      rewrite !poly_admissible_cons, IH. reflexivity.
  Qed.

  Lemma poly_normal_rows_coef : forall P ms x,
    C.comb_coef (poly_normal_rows P) ms x = C.comb_coef P ms x.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] x; try reflexivity.
    change (C.comb_coef (poly_normal_row X.encode p :: poly_normal_rows P) (m :: ms) x =
      C.comb_coef (p :: P) (m :: ms) x).
    rewrite !poly_comb_coef_cons. cbn [poly_normal_row lhs].
    rewrite coef_of_normal, IH. reflexivity.
  Qed.

  Lemma poly_normal_rows_rhs : forall P ms,
    C.comb_rhs (poly_normal_rows P) ms = C.comb_rhs P ms.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms]; try reflexivity.
    change (C.comb_rhs (poly_normal_row X.encode p :: poly_normal_rows P) (m :: ms) =
      C.comb_rhs (p :: P) (m :: ms)).
    rewrite !poly_comb_rhs_cons. cbn [poly_normal_row rhs]. now rewrite IH.
  Qed.

  Lemma poly_normal_rows_eq : forall P ms,
    C.comb_eq (poly_normal_rows P) ms = C.comb_eq P ms.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms]; try reflexivity.
    change (C.comb_eq (poly_normal_row X.encode p :: poly_normal_rows P) (m :: ms) =
      C.comb_eq (p :: P) (m :: ms)).
    rewrite !poly_comb_eq_cons. cbn [poly_normal_row lrel]. now rewrite IH.
  Qed.

  Lemma poly_exact_empty_normalized : forall P ms,
    poly_exact_empty (poly_normal_rows P) ms <-> poly_exact_empty P ms.
  Proof.
    intros P ms. unfold poly_exact_empty.
    rewrite poly_normal_rows_admissible, poly_normal_rows_rhs, poly_normal_rows_eq.
    split; intros [Ha [Hcoef Hrhs]]; split; [exact Ha| |exact Ha|];
      split; [|exact Hrhs| |exact Hrhs].
    - intro x. specialize (Hcoef x). now rewrite poly_normal_rows_coef in Hcoef.
    - intro x. rewrite poly_normal_rows_coef. apply Hcoef.
  Qed.

  Lemma poly_exact_entail_normalized : forall P c ms sc,
    poly_exact_entail (poly_normal_rows P) (poly_normal_row X.encode c) ms sc <->
      poly_exact_entail P c ms sc.
  Proof.
    intros P c ms sc. split; intros [Ha [Hs [Hcoef Hrhs]]].
    - split; [exact (proj1 (poly_normal_rows_admissible P ms) Ha)|].
      split; [exact Hs|]. split.
      + intro x. specialize (Hcoef x). cbn [poly_normal_row lhs] in Hcoef.
        now rewrite poly_normal_rows_coef, coef_of_normal in Hcoef.
      + cbn [poly_normal_row lrel rhs] in Hrhs.
        now rewrite poly_normal_rows_eq, poly_normal_rows_rhs in Hrhs.
    - split; [exact (proj2 (poly_normal_rows_admissible P ms) Ha)|].
      split; [exact Hs|]. split.
      + intro x. cbn [poly_normal_row lhs].
        rewrite poly_normal_rows_coef, coef_of_normal. apply Hcoef.
      + cbn [poly_normal_row lrel rhs].
        now rewrite poly_normal_rows_eq, poly_normal_rows_rhs.
  Qed.

  Lemma poly_certificate_valid_normalized : forall P c k,
    poly_certificate_valid (poly_normal_rows P) (poly_normal_row X.encode c) k <->
      poly_certificate_valid P c k.
  Proof.
    intros P c k. unfold poly_certificate_valid.
    rewrite poly_exact_empty_normalized, poly_exact_entail_normalized. reflexivity.
  Qed.

  Lemma poly_certificate_valid_checked : forall P c k,
    poly_certificate_valid P c k -> C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c [ms sc cutflag] [Hcut [Hempty|Hentail]];
      cbn [cut mults scale] in *; subst cutflag; split; try reflexivity.
    - apply C.check_entails_empty. destruct Hempty as [Ha [Hcoef Hrhs]].
      now apply C.check_empty_complete.
    - destruct Hentail as [Ha [Hs [Hcoef Hrhs]]].
      now apply C.check_entails_complete.
  Qed.

  Lemma poly_canonical_certificate_data : forall P c r sc ms,
    poly_tracks (poly_negate c :: P) r -> poly_target_strict r ->
    poly_multipliers r = sc :: ms -> poly_contradiction r = true ->
    poly_canonical_guard P c r sc ms = true ->
    poly_certificate_valid P c (Cert ms (poly_canonical_scale sc) false).
  Proof.
    intros P c r sc ms Htracks Hstrict Hweights Hcontra Hguard.
    destruct (poly_target_data P c r sc ms Htracks Hweights
      (poly_contradiction_empty r Hcontra)) as [Ha [Hnonnegative [Hcoef [Hrhs Heq]]]].
    split; [reflexivity|]. cbn [mults scale].
    unfold poly_canonical_guard in Hguard.
    destruct (Z.eqb sc 0) eqn:Hzero.
    - apply Z.eqb_eq in Hzero. subst sc. left. split; [exact Ha|]. split.
      + intro x. specialize (Hcoef x). lia.
      + destruct (lrel (poly_constraint r)) eqn:Hrel.
        * right. destruct (Heq eq_refl) as [_ Hused]. split; [exact Hused|].
          pose proof (poly_contradiction_eq_rhs r Hrel Hcontra). lia.
        * left. assert (Hflag : poly_strict r = false) by exact (Hstrict 0%Z ms Hweights).
          pose proof (poly_contradiction_nonstrict_rhs r Hrel Hflag Hcontra). lia.
    - cbn [orb] in Hguard. apply andb_true_iff in Hguard as [Hpositive Hrelation].
      apply Z.ltb_lt in Hpositive. right. unfold poly_exact_entail, poly_canonical_scale.
      rewrite Hzero. split; [exact Ha|]. split; [exact Hpositive|]. split; [exact Hcoef|].
      assert (Hrowrel : lrel (poly_constraint r) = RLe).
      { destruct (lrel (poly_constraint r)); [|reflexivity].
        destruct (Heq eq_refl) as [Hz _]. lia. }
      destruct (lrel c) eqn:Htarget.
      + apply andb_true_iff in Hrelation as [Hrhszero Hused]. apply Z.eqb_eq in Hrhszero.
        rewrite poly_source_equal_spec in Hused. split; [exact Hused|]. lia.
      + pose proof (poly_contradiction_le_rhs r Hrowrel Hcontra). lia.
  Qed.

  Lemma poly_candidate_valid : forall P c r k,
    poly_tracks (poly_negate c :: P) r -> poly_target_strict r ->
    candidate P c r = Some k -> poly_certificate_valid P c k.
  Proof.
    intros P c r k Htracks Hstrict Hresult. unfold candidate in Hresult.
    destruct (poly_contradiction r) eqn:Hcontra; [|discriminate].
    destruct (poly_multipliers r) as [|sc ms] eqn:Hweights; [discriminate|].
    destruct (poly_canonical_guard P c r sc ms) eqn:Hguard; [|discriminate].
    destruct (C.check_entails P c (Cert ms (poly_canonical_scale sc) false)); [|discriminate].
    injection Hresult as Hsame. subst k.
    now apply poly_canonical_certificate_data with (r := r).
  Qed.

  Lemma poly_find_certificate_valid : forall P c rows k,
    Forall (poly_tracks (poly_negate c :: P)) rows -> Forall poly_target_strict rows ->
    find_certificate P c rows = Some k -> poly_certificate_valid P c k.
  Proof.
    intros P c rows. induction rows as [|r rows IH]; intros k Htracks Hstrict Hresult;
      cbn [find_certificate] in Hresult; [discriminate|].
    inversion Htracks as [|? ? Hr Hrs]; subst.
    inversion Hstrict as [|? ? Hflag Hflags]; subst.
    destruct (candidate P c r) as [found|] eqn:Hhead.
    - injection Hresult as Hsame. subst found. now apply poly_candidate_valid with (r := r).
    - now apply IH.
  Qed.

  Lemma poly_entail_engine_valid : forall P c k,
    entail_engine P c = Some k -> poly_certificate_valid P c k.
  Proof.
    intros P c k Hresult. unfold entail_engine in Hresult.
    eapply poly_find_certificate_valid; [apply poly_entailment_tracks|apply poly_entailment_target_strict|].
    exact Hresult.
  Qed.

  Lemma entail_cert_returned : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c k Hresult. unfold entail_cert in Hresult.
    apply poly_entail_engine_valid in Hresult.
    exact (poly_certificate_valid_checked P c k
      (proj1 (poly_certificate_valid_normalized P c k) Hresult)).
  Qed.

  (** Successful row inclusion retains every integer model of its input. *)
  Lemma entails_row_sound : forall P r v,
    entails_row P r = true -> Forall (sat v) P -> sat v r.
  Proof.
    intros P r v Hresult Hmodels. unfold entails_row in Hresult.
    destruct (entail_cert P r) as [k|] eqn:Hcertificate; [|discriminate].
    exact (C.check_entails_sound P r k
      (proj1 (entail_cert_returned P r k Hcertificate)) v Hmodels).
  Qed.

  (** Splitting an equality into two inequalities preserves its meaning. *)
  Lemma keep_row_sound : forall P r v,
    keep_row P r = true -> Forall (sat v) P -> sat v r.
  Proof.
    intros P r v Hkeep Hmodels. unfold keep_row in Hkeep.
    destruct (lrel r) eqn:Hrel.
    - apply andb_true_iff in Hkeep as [Hupper Hlower].
      pose proof (entails_row_sound P _ v Hupper Hmodels) as Hle.
      pose proof (entails_row_sound P _ v Hlower Hmodels) as Hge.
      unfold sat, poly_negate in Hle, Hge. cbn [lhs lrel rhs] in Hle, Hge.
      rewrite eval_coef_scale in Hge. unfold sat. rewrite Hrel. lia.
    - exact (entails_row_sound P r v Hkeep Hmodels).
  Qed.

  (** A state recognized as bottom has no integer model. *)
  Lemma is_bot_sound : forall s v, is_bot s = true -> ~ ngamma s v.
  Proof.
    intros [|P] v Hbot Hmodels; [exact Hmodels |].
    pose proof (entails_row_sound P _ v Hbot Hmodels) as Hfalse.
    cbn [sat lrel lhs rhs eval_coef fold_right] in Hfalse. lia.
  Qed.

  (** Every contradictory producer row is accepted by the certificate search. *)
  Lemma poly_candidate_complete : forall P c r,
    lrel c = RLe -> poly_tracks (poly_negate c :: P) r -> poly_target_strict r ->
    poly_contradiction r = true -> exists k, candidate P c r = Some k.
  Proof.
    intros P c r Htarget Htracks Hstrict Hcontra.
    destruct (poly_multipliers r) as [|sc ms] eqn:Hweights.
    { destruct (proj1 Htracks) as [Hlength _]. rewrite Hweights in Hlength.
      cbn [length] in Hlength. discriminate. }
    assert (Hnonnegative : (0 <= sc)%Z).
    { pose proof (proj1 Htracks) as Ha. rewrite Hweights in Ha.
      apply poly_admissible_cons in Ha as [Hhead _]. apply Hhead. reflexivity. }
    assert (Hguard : poly_canonical_guard P c r sc ms = true).
    { unfold poly_canonical_guard. rewrite Htarget.
      destruct (Z.eqb sc 0) eqn:Hzero; [reflexivity|].
      apply Z.eqb_neq in Hzero. cbn [orb]. rewrite andb_true_r.
      apply Z.ltb_lt. lia. }
    pose proof (poly_canonical_certificate_data P c r sc ms
      Htracks Hstrict Hweights Hcontra Hguard) as Hvalid.
    pose proof (proj1 (poly_certificate_valid_checked _ _ _ Hvalid)) as Hcheck.
    exists (Cert ms (poly_canonical_scale sc) false). unfold candidate.
    now rewrite Hcontra, Hweights, Hguard, Hcheck.
  Qed.

  Lemma poly_find_certificate_complete : forall P c rows r k,
    In r rows -> candidate P c r = Some k -> exists found, find_certificate P c rows = Some found.
  Proof.
    intros P c rows. induction rows as [|p rows IH]; intros r k Hin Hcandidate;
      [contradiction|].
    cbn [find_certificate]. destruct (candidate P c p) as [found|] eqn:Hhead.
    - exists found. reflexivity.
    - destruct Hin as [Hsame|Hin].
      + subst p. congruence.
      + now apply IH with (r := r) (k := k).
  Qed.

  (** Search failure means the final projected system contains no contradictory row. *)
  Lemma poly_entailment_no_contradiction : forall P c,
    lrel c = RLe -> entail_engine P c = None ->
    Forall (fun r => poly_contradiction r = false)
      (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
        (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))).
  Proof.
    intros P c Htarget Hnone. apply Forall_forall. intros r Hin.
    destruct (poly_contradiction r) eqn:Hcontra; [|reflexivity].
    pose proof (proj1 (Forall_forall _ _)
      (poly_entailment_tracks (poly_variables X.encode (c :: P)) c P) r Hin) as Htracks.
    pose proof (proj1 (Forall_forall _ _)
      (poly_entailment_target_strict (poly_variables X.encode (c :: P)) c P) r Hin)
      as Hstrict.
    destruct (poly_candidate_complete P c r Htarget Htracks Hstrict Hcontra)
      as [k Hcandidate].
    destruct (poly_find_certificate_complete P c _ r k Hin Hcandidate) as [found Hfound].
    unfold entail_engine in Hnone. rewrite Hnone in Hfound. discriminate.
  Qed.

  (** A valid lower endpoint can be intersected with the existing interval. *)
  Lemma lower_sound : forall lo hi b z, (b <= z)%Z -> in_bnd lo hi z ->
    in_bnd (poly_lower b lo) hi z.
  Proof.
    intros lo hi b z Hbound [Hlo Hhi]. split; [| exact Hhi].
    destruct lo; cbn [poly_lower] in *; [exact Hbound | | contradiction].
    apply Z.max_lub; assumption.
  Qed.

  (** A valid upper endpoint can be intersected with the existing interval. *)
  Lemma upper_sound : forall lo hi b z, (z <= b)%Z -> in_bnd lo hi z ->
    in_bnd lo (poly_upper b hi) z.
  Proof.
    intros lo hi b z Hbound [Hlo Hhi]. split; [exact Hlo |].
    destruct hi; cbn [poly_upper] in *; [contradiction | | exact Hbound].
    apply Z.min_glb; assumption.
  Qed.

  (** Floor division by a positive coefficient gives a valid integer upper bound. *)
  Lemma positive_division_upper : forall a b z,
    (0 < a)%Z -> (a * z <= b)%Z -> (z <= b / a)%Z.
  Proof.
    intros a b z Hpos Hbound.
    pose proof (Z.div_mod b a ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound b a Hpos) as Hmod. nia.
  Qed.

  (** Endpoint rounding retains every integer satisfying the projected row. *)
  Lemma range_update_sound : forall a b (is_eq : bool) bounds z,
    (if is_eq then (a * z = b)%Z else (a * z <= b)%Z) ->
    in_bnd (fst bounds) (snd bounds) z ->
    in_bnd (fst (range_update a b is_eq bounds))
      (snd (range_update a b is_eq bounds)) z.
  Proof.
    intros a b is_eq [lo hi] z Hrow Hbounds. unfold range_update.
    destruct (0 <? a)%Z eqn:Hpos.
    - apply Z.ltb_lt in Hpos. destruct is_eq; cbn [fst snd] in *.
      + apply lower_sound.
        * assert (Hdiv : (-z <= (-b) / a)%Z).
          { apply positive_division_upper; [exact Hpos | nia]. }
          lia.
        * apply upper_sound; [apply positive_division_upper; [exact Hpos | lia] |].
          exact Hbounds.
      + apply upper_sound; [now apply positive_division_upper | exact Hbounds].
    - destruct (a <? 0)%Z eqn:Hneg; [| exact Hbounds].
      apply Z.ltb_lt in Hneg. destruct is_eq; cbn [fst snd] in *.
      + apply lower_sound.
        * assert (Hdiv : (-z <= b / (-a))%Z).
          { apply positive_division_upper; nia. }
          lia.
        * apply upper_sound; [apply positive_division_upper; nia | exact Hbounds].
      + apply lower_sound; [| exact Hbounds].
        assert (Hdiv : (-z <= b / (-a))%Z).
        { apply positive_division_upper; nia. }
        lia.
  Qed.

  (** A checked projected constraint gives a valid bound on the queried form. *)
  Lemma range_candidate_sound : forall P f bounds r v,
    Forall (sat v) P -> in_bnd (fst bounds) (snd bounds) (eval_lin v f) ->
    in_bnd (fst (range_candidate P f bounds r))
      (snd (range_candidate P f bounds r)) (eval_lin v f).
  Proof.
    intros P f bounds r v Hmodels Hbounds. unfold range_candidate.
    destruct (forallb (fun p => match fst p with None => true | Some _ => false end)
      (lhs (poly_constraint r))); [| exact Hbounds].
    destruct (poly_multipliers r) as [|m ms]; [exact Hbounds |].
    set (a := poly_coefficient tmp_eqb None (poly_constraint r)).
    destruct (C.check_entails P
      (LCons X.t (poly_scale_coef a (coef f)) (lrel (poly_constraint r))
        (rhs (poly_constraint r) - a * cst f)%Z) (Cert ms 1 false)) eqn:Hcheck;
      [| exact Hbounds].
    pose proof (C.check_entails_sound P _ (Cert ms 1 false) Hcheck v Hmodels) as Hrow.
    apply range_update_sound; [| exact Hbounds]. unfold sat in Hrow.
    cbn [lhs lrel rhs] in Hrow. rewrite eval_coef_scale in Hrow.
    unfold eval_lin. destruct (lrel (poly_constraint r)); nia.
  Qed.

  (** Repeated checked bound updates retain the value of the queried form. *)
  Lemma range_fold_sound : forall P f rs bounds v,
    Forall (sat v) P -> in_bnd (fst bounds) (snd bounds) (eval_lin v f) ->
    in_bnd (fst (fold_left (range_candidate P f) rs bounds))
      (snd (fold_left (range_candidate P f) rs bounds)) (eval_lin v f).
  Proof.
    intros P f rs. induction rs as [|r rs IH]; intros bounds v Hmodels Hbounds;
      cbn [fold_left]; [exact Hbounds |].
    apply IH; [exact Hmodels |]. now apply range_candidate_sound.
  Qed.

  (** The interval for an affine form contains its value in every input model. *)
  Lemma range_linear_sound : forall P f v, Forall (sat v) P ->
    in_bnd (fst (range_linear P f)) (snd (range_linear P f)) (eval_lin v f).
  Proof.
    intros P f v Hmodels. unfold range_linear.
    apply range_fold_sound; [| split; exact I].
    apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
    apply normalize_row_sat. exact (proj1 (Forall_forall _ _) Hmodels s Hin).
  Qed.


  (** A normalized row sum has the same sum of coefficients at every key. *)
  Lemma poly_add_rows_coefficient : forall x a p b q,
    poly_coefficient X.eqb x (poly_constraint (poly_add_rows X.encode a p b q)) =
      (a * poly_coefficient X.eqb x (poly_constraint p) +
       b * poly_coefficient X.eqb x (poly_constraint q))%Z.
  Proof.
    intros x a p b q. rewrite <- !coef_of_poly_coefficient.
    cbn [poly_add_rows poly_constraint lhs].
    rewrite coef_of_normal, coef_of_app, !coef_of_scale. reflexivity.
  Qed.

  (** Multiplying by a sign yields the nonnegative absolute value. *)
  Lemma poly_sgn_abs : forall a, (Z.sgn a * a = Z.abs a)%Z.
  Proof.
    intros [|a|a]; cbn; ring.
  Qed.

  (** The cancellation formula always removes its selected coefficient. *)
  Lemma poly_cancel_zero : forall x p r,
    poly_coefficient X.eqb x
      (poly_constraint (poly_cancel X.encode X.eqb x p r)) = 0%Z.
  Proof.
    intros x p r. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0) eqn:Hzero.
    - now apply Z.eqb_eq in Hzero.
    - rewrite poly_add_rows_coefficient, <- poly_sgn_abs. ring.
  Qed.

  (** A coordinate zero in both inputs stays zero after cancellation. *)
  Lemma poly_cancel_preserves_zero : forall x y p r,
    poly_coefficient X.eqb y (poly_constraint p) = 0%Z ->
    poly_coefficient X.eqb y (poly_constraint r) = 0%Z ->
    poly_coefficient X.eqb y
      (poly_constraint (poly_cancel X.encode X.eqb x p r)) = 0%Z.
  Proof.
    intros x y p r Hp Hr. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0); [exact Hr|].
    rewrite poly_add_rows_coefficient, Hp, Hr. ring.
  Qed.

  (** Equality pivots and opposite-sign pairing both eliminate the selected variable. *)
  Lemma poly_step_zero : forall x rows,
    Forall (fun r => poly_coefficient X.eqb x (poly_constraint r) = 0%Z)
      (poly_step X.encode X.eqb x rows).
  Proof.
    intros x rows. unfold poly_step.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - apply Forall_map. apply Forall_forall. intros r _. apply poly_cancel_zero.
    - apply Forall_app. split; apply Forall_forall; intros r Hin.
      + apply filter_In in Hin as [_ Hzero]. now apply Z.eqb_eq in Hzero.
      + apply in_flat_map in Hin as [p [_ Hin]].
        apply in_map_iff in Hin as [q [Hsame _]]. subst r.
        rewrite poly_add_rows_coefficient. ring.
  Qed.

  (** Elimination preserves every coefficient already zero in all input rows. *)
  Lemma poly_step_preserves_zero : forall x y rows,
    Forall (fun r => poly_coefficient X.eqb y (poly_constraint r) = 0%Z) rows ->
    Forall (fun r => poly_coefficient X.eqb y (poly_constraint r) = 0%Z)
      (poly_step X.encode X.eqb x rows).
  Proof.
    intros x y rows Hzero. unfold poly_step.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - apply find_some in Hfind as [Hp _].
      apply Forall_map. apply Forall_forall. intros r Hr.
      apply poly_cancel_preserves_zero.
      + exact (proj1 (Forall_forall _ _) Hzero p Hp).
      + exact (proj1 (Forall_forall _ _) Hzero r Hr).
    - apply Forall_app. split; apply Forall_forall; intros r Hin.
      + apply filter_In in Hin as [Hin _].
        exact (proj1 (Forall_forall _ _) Hzero r Hin).
      + apply in_flat_map in Hin as [p [Hp Hin]].
        apply in_map_iff in Hin as [q [Hsame Hq]]. subst r.
        apply filter_In in Hp as [Hp _]. apply filter_In in Hq as [Hq _].
        rewrite poly_add_rows_coefficient,
          (proj1 (Forall_forall _ _) Hzero p Hp),
          (proj1 (Forall_forall _ _) Hzero q Hq). ring.
  Qed.

  (** Repeated elimination preserves every initially zero coefficient. *)
  Lemma poly_run_preserves_zero : forall xs x rows,
    Forall (fun r => poly_coefficient X.eqb x (poly_constraint r) = 0%Z) rows ->
    Forall (fun r => poly_coefficient X.eqb x (poly_constraint r) = 0%Z)
      (poly_run X.encode X.eqb xs rows).
  Proof.
    intro xs. induction xs as [|y xs IH]; intros x rows Hzero; [exact Hzero|].
    cbn [poly_run]. apply IH. now apply poly_step_preserves_zero.
  Qed.

  (** Every variable listed for elimination has zero coefficient in the final rows. *)
  Lemma poly_run_zero : forall xs rows x, In x xs ->
    Forall (fun r => poly_coefficient X.eqb x (poly_constraint r) = 0%Z)
      (poly_run X.encode X.eqb xs rows).
  Proof.
    intro xs. induction xs as [|y xs IH]; intros rows x Hin; [contradiction|].
    cbn [poly_run]. destruct Hin as [Hsame|Hin].
    - subst y. apply poly_run_preserves_zero. apply poly_step_zero.
    - now apply IH.
  Qed.

  (** Every final row simultaneously has zero coefficients at all eliminated keys. *)
  Lemma poly_run_zero_all : forall xs rows,
    Forall (fun r => forall x, In x xs ->
      poly_coefficient X.eqb x (poly_constraint r) = 0%Z)
      (poly_run X.encode X.eqb xs rows).
  Proof.
    intros xs rows. apply Forall_forall. intros r Hr x Hx.
    exact (proj1 (Forall_forall _ _) (poly_run_zero xs rows x Hx) r Hr).
  Qed.

  (** Inserting a stored key preserves every existing key's own value. *)
  Lemma poly_variable_set_preserves : forall acc x y,
    PTrieCode.get (X.encode x) acc = Some x ->
    PTrieCode.get (X.encode x) (PTrieCode.set (X.encode y) y acc) = Some x.
  Proof.
    intros acc x y Hget. destruct (Pos.eq_dec (X.encode x) (X.encode y))
      as [Hsame|Hother].
    - apply X.encode_inj in Hsame. subst y. apply PTrie.get_set_same.
    - rewrite PTrie.get_set_other by exact Hother. exact Hget.
  Qed.

  (** Scanning a row records all its raw keys and preserves the prior key set. *)
  Lemma poly_variables_terms_present : forall (ps : list (X.t * Z)) acc x,
    In x (map fst ps) \/ PTrieCode.get (X.encode x) acc = Some x ->
    PTrieCode.get (X.encode x)
      (fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc)
        ps acc) = Some x.
  Proof.
    intro ps. induction ps as [|[y a] ps IH]; intros acc x Hpresent.
    - cbn [map In] in Hpresent. destruct Hpresent as [Hfalse|Hget];
        [contradiction|exact Hget].
    - cbn [fold_left fst]. apply IH. cbn [map fst In] in Hpresent.
      destruct Hpresent as [[Hsame|Hin]|Hget].
      + subst y. right. apply PTrie.get_set_same.
      + now left.
      + right. now apply poly_variable_set_preserves.
  Qed.

  (** Scanning source rows records every raw occurrence, including cancelled keys. *)
  Lemma poly_variables_rows_present : forall rows acc x,
    (exists r, In r rows /\ In x (map fst (lhs r))) \/
      PTrieCode.get (X.encode x) acc = Some x ->
    PTrieCode.get (X.encode x)
      (fold_left (fun acc r =>
        fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc)
          (lhs r) acc) rows acc) = Some x.
  Proof.
    intro rows. induction rows as [|r rows IH]; intros acc x Hpresent.
    - destruct Hpresent as [[s [Hin _]]|Hget]; [contradiction|exact Hget].
    - cbn [fold_left]. apply IH.
      destruct Hpresent as [[s [[Hsame|Hin] Hterm]]|Hget].
      + subst s. right. apply poly_variables_terms_present. now left.
      + left. exists s. auto.
      + right. apply poly_variables_terms_present. now right.
  Qed.

  (** Accumulating trie values into a list retains every stored value. *)
  Lemma poly_variables_fold_present : forall (entries : list (positive * X.t)) acc x,
    In x (map snd entries) \/ In x acc ->
    In x (fold_left (fun acc p => snd p :: acc) entries acc).
  Proof.
    intro entries. induction entries as [|[key value] entries IH];
      intros acc x Hpresent.
    - cbn [map In] in Hpresent. destruct Hpresent as [Hfalse|Hin];
        [contradiction|exact Hin].
    - cbn [fold_left snd]. apply IH. cbn [map snd In] in Hpresent.
      destruct Hpresent as [[Hsame|Hin]|Hin].
      + subst value. right. now left.
      + now left.
      + right. now right.
  Qed.

  (** The elimination coordinate list contains every key occurring in any raw source row. *)
  Lemma poly_variables_contains : forall rows r x a,
    In r rows -> In (x, a) (lhs r) -> In x (poly_variables X.encode rows).
  Proof.
    intros rows r x a Hrow Hterm. unfold poly_variables.
    rewrite PTrieT.F9_fold_values. apply poly_variables_fold_present. left.
    apply in_map_iff. exists (X.encode x, x). split; [reflexivity|].
    apply (proj2 (PTrie.elements_spec _ _ _ _)).
    apply poly_variables_rows_present. left. exists r. split; [exact Hrow|].
    apply in_map_iff. exists (x, a). split; [reflexivity|exact Hterm].
  Qed.

  (** A prepared row has distinct nonzero coefficients supported by its source keys. *)
  Definition poly_reduced_row (xs : list X.t) (r : poly_row X.t) : Prop :=
    NoDup (map fst (lhs (poly_constraint r))) /\
      Forall (fun p => snd p <> 0%Z /\ In (fst p) xs) (lhs (poly_constraint r)).

  (** Scaling a coefficient list does not change its list of keys. *)
  Lemma poly_scale_coef_keys : forall a (terms : list (X.t * Z)),
    map fst (poly_scale_coef a terms) = map fst terms.
  Proof.
    intros a terms. unfold poly_scale_coef. rewrite map_map. reflexivity.
  Qed.

  (** Every raw key retained by normalization remains in the supplied source list. *)
  Lemma poly_normal_coef_reduced : forall xs terms,
    (forall p, In p terms -> In (fst p) xs) ->
    Forall (fun p => snd p <> 0%Z /\ In (fst p) xs)
      (poly_normal_coef X.encode terms).
  Proof.
    intros xs terms Hsupport. apply Forall_forall. intros p Hp. split.
    - eapply poly_normal_coef_nonzero. exact Hp.
    - apply poly_normal_coef_keys in Hp.
      apply in_map_iff in Hp as [q [Hsame Hq]]. rewrite <- Hsame. now apply Hsupport.
  Qed.

  (** Normalizing a source row establishes distinct nonzero supported coefficients. *)
  Lemma poly_normal_row_reduced : forall xs r ms flag,
    (forall p, In p (lhs r) -> In (fst p) xs) ->
    poly_reduced_row xs (PolyRow X.t (poly_normal_row X.encode r) ms flag).
  Proof.
    intros xs r ms flag Hsupport. unfold poly_reduced_row.
    cbn [poly_constraint poly_normal_row lhs]. split.
    - apply poly_normal_coef_nodup.
    - now apply poly_normal_coef_reduced.
  Qed.

  (** Every initialized source row has distinct nonzero supported coefficients. *)
  Lemma poly_initial_reduced : forall xs rows,
    Forall (fun r => forall p, In p (lhs (fst r)) -> In (fst p) xs) rows ->
    Forall (poly_reduced_row xs) (poly_initial X.encode rows).
  Proof.
    intros xs rows. induction rows as [|[r flag] rows IH]; intro Hsupport;
      [constructor|].
    inversion Hsupport as [|source rest Hhead Htail]; subst source rest.
    cbn [poly_initial fst snd]. constructor.
    - apply poly_normal_row_reduced. exact Hhead.
    - apply Forall_map. eapply Forall_impl; [|exact (IH Htail)].
      intros q Hq. exact Hq.
  Qed.

  (** Combining prepared rows preserves distinct nonzero coefficients and source support. *)
  Lemma poly_add_rows_reduced : forall xs a p b q,
    poly_reduced_row xs p -> poly_reduced_row xs q ->
    poly_reduced_row xs (poly_add_rows X.encode a p b q).
  Proof.
    intros xs a p b q [_ Hp] [_ Hq]. unfold poly_reduced_row.
    cbn [poly_add_rows poly_constraint lhs]. split.
    - apply poly_normal_coef_nodup.
    - apply poly_normal_coef_reduced. intros term Hterm.
      assert (Hkey : In (fst term)
        (map fst (poly_scale_coef a (lhs (poly_constraint p)) ++
          poly_scale_coef b (lhs (poly_constraint q))))).
      { apply in_map. exact Hterm. }
      rewrite map_app, !poly_scale_coef_keys in Hkey.
      apply in_app_or in Hkey as [Hkey|Hkey].
      + apply in_map_iff in Hkey as [s [Hsame Hs]]. rewrite <- Hsame.
        exact (proj2 (proj1 (Forall_forall _ _) Hp s Hs)).
      + apply in_map_iff in Hkey as [s [Hsame Hs]]. rewrite <- Hsame.
        exact (proj2 (proj1 (Forall_forall _ _) Hq s Hs)).
  Qed.

  (** Cancelling against a prepared pivot preserves the prepared-row invariant. *)
  Lemma poly_cancel_reduced : forall xs x p r,
    poly_reduced_row xs p -> poly_reduced_row xs r ->
    poly_reduced_row xs (poly_cancel X.encode X.eqb x p r).
  Proof.
    intros xs x p r Hp Hr. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0); [exact Hr|].
    now apply poly_add_rows_reduced.
  Qed.

  (** A complete elimination step preserves the prepared-row invariant. *)
  Lemma poly_step_reduced : forall xs x rows,
    Forall (poly_reduced_row xs) rows ->
    Forall (poly_reduced_row xs) (poly_step X.encode X.eqb x rows).
  Proof.
    intros xs x rows Hrows. unfold poly_step.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - apply find_some in Hfind as [Hp _].
      apply Forall_map. apply Forall_forall. intros r Hr.
      apply poly_cancel_reduced.
      + exact (proj1 (Forall_forall _ _) Hrows p Hp).
      + exact (proj1 (Forall_forall _ _) Hrows r Hr).
    - apply Forall_app. split; apply Forall_forall; intros r Hin.
      + apply filter_In in Hin as [Hin _].
        exact (proj1 (Forall_forall _ _) Hrows r Hin).
      + apply in_flat_map in Hin as [p [Hp Hin]].
        apply in_map_iff in Hin as [q [Hsame Hq]]. subst r.
        apply filter_In in Hp as [Hp _]. apply filter_In in Hq as [Hq _].
        apply poly_add_rows_reduced.
        * exact (proj1 (Forall_forall _ _) Hrows p Hp).
        * exact (proj1 (Forall_forall _ _) Hrows q Hq).
  Qed.

  (** Repeated elimination preserves the prepared-row invariant. *)
  Lemma poly_run_reduced : forall xs keys rows,
    Forall (poly_reduced_row xs) rows ->
    Forall (poly_reduced_row xs) (poly_run X.encode X.eqb keys rows).
  Proof.
    intros xs keys. induction keys as [|x keys IH]; intros rows Hrows; [exact Hrows|].
    cbn [poly_run]. apply IH. now apply poly_step_reduced.
  Qed.

  (** A key absent from the stored terms has zero summed coefficient. *)
  Lemma poly_coefficient_absent : forall x r,
    ~ In x (map fst (lhs r)) -> poly_coefficient X.eqb x r = 0%Z.
  Proof.
    intros x [terms relation bound]. unfold poly_coefficient. cbn [lhs].
    induction terms as [|[y a] terms IH]; intro Habsent; [reflexivity|].
    cbn [map fst In] in Habsent. cbn [fold_right fst snd].
    destruct (X.eqb_spec y x) as [Hsame|Hother].
    - subst y. exfalso. apply Habsent. now left.
    - apply IH. intro Hin. apply Habsent. now right.
  Qed.

  (** A prepared row whose supported coefficients all vanish has an empty left-hand side. *)
  Lemma poly_reduced_zero_empty : forall xs r,
    poly_reduced_row xs r ->
    (forall x, In x xs -> poly_coefficient X.eqb x (poly_constraint r) = 0%Z) ->
    lhs (poly_constraint r) = nil.
  Proof.
    intros xs r [Hunique Hterms] Hzero.
    destruct (poly_constraint r) as [terms relation bound].
    destruct terms as [|[x a] terms]; [reflexivity|].
    cbn [lhs map fst] in Hunique, Hterms.
    inversion Hunique as [|key keys Habsent Htail]; subst key keys.
    inversion Hterms as [|term rest [Hnonzero Hsupport] Hrest]; subst term rest.
    cbn [fst snd] in Hnonzero, Hsupport.
    specialize (Hzero x Hsupport).
    assert (Hcoefficient : poly_coefficient X.eqb x (LCons X.t terms relation bound) = 0%Z).
    { apply poly_coefficient_absent. exact Habsent. }
    unfold poly_coefficient in Hzero, Hcoefficient. cbn [lhs] in Hcoefficient.
    cbn [lhs fold_right fst snd] in Hzero.
    rewrite poly_key_eqb_refl, Hcoefficient in Hzero. exfalso. apply Hnonzero. lia.
  Qed.

  (** Eliminating every source key leaves only constant rows. *)
  Lemma poly_terminal_rows : forall xs rows,
    Forall (fun r => forall p, In p (lhs (fst r)) -> In (fst p) xs) rows ->
    Forall (fun r => lhs (poly_constraint r) = nil)
      (poly_run X.encode X.eqb xs (poly_initial X.encode rows)).
  Proof.
    intros xs rows Hsupport.
    pose proof (poly_run_reduced xs xs _ (poly_initial_reduced xs rows Hsupport)) as Hreduced.
    pose proof (poly_run_zero_all xs (poly_initial X.encode rows)) as Hzero.
    apply Forall_forall. intros r Hr. apply poly_reduced_zero_empty with (xs := xs).
    - exact (proj1 (Forall_forall _ _) Hreduced r Hr).
    - exact (proj1 (Forall_forall _ _) Hzero r Hr).
  Qed.

  (** A constant row not recognized as a contradiction holds under every rational store. *)
  Lemma poly_constant_model_Q : forall r v,
    lhs (poly_constraint r) = nil -> poly_contradiction r = false -> poly_satQ v r.
  Proof.
    intros r v Hempty Hconsistent. unfold poly_contradiction in Hconsistent.
    rewrite Hempty in Hconsistent. unfold poly_satQ. rewrite Hempty.
    cbn [poly_eval_coef_Q fold_right]. destruct (lrel (poly_constraint r)).
    - apply negb_false_iff in Hconsistent. apply Z.eqb_eq in Hconsistent.
      rewrite Hconsistent. reflexivity.
    - apply orb_false_iff in Hconsistent as [Hnonnegative Hstrict].
      apply Z.ltb_ge in Hnonnegative. destruct (poly_strict r) eqn:Hflag.
      + cbn [andb] in Hstrict. apply Z.leb_gt in Hstrict.
        change (inject_Z 0 < inject_Z (rhs (poly_constraint r)))%Q.
        now rewrite <- Zlt_Qlt.
      + change (inject_Z 0 <= inject_Z (rhs (poly_constraint r)))%Q.
        now rewrite <- Zle_Qle.
  Qed.

  (** The zero store models a terminal system when none of its rows is contradictory. *)
  Lemma poly_terminal_model_Q : forall rows,
    Forall (fun r => lhs (poly_constraint r) = nil) rows ->
    Forall (fun r => poly_contradiction r = false) rows ->
    Forall (poly_satQ (fun _ => 0%Q)) rows.
  Proof.
    intros rows Hempty Hconsistent. apply Forall_forall. intros r Hr.
    apply poly_constant_model_Q.
    - exact (proj1 (Forall_forall _ _) Hempty r Hr).
    - exact (proj1 (Forall_forall _ _) Hconsistent r Hr).
  Qed.

  (** The source and negated target are supported by the same original coordinate list. *)
  Lemma poly_entail_source_support : forall P c,
    Forall (fun r => forall p, In p (lhs (fst r)) ->
      In (fst p) (poly_variables X.encode (c :: P)))
      ((poly_negate c, true) :: map (fun r => (r, false)) P).
  Proof.
    intros P c. constructor.
    - intros p Hp. cbn [fst poly_negate lhs] in Hp. unfold poly_scale_coef in Hp.
      apply in_map_iff in Hp as [q [Hsame Hq]]. subst p. cbn [fst].
      destruct q as [x a]. apply poly_variables_contains with (r := c) (a := a).
      + now left.
      + exact Hq.
    - apply Forall_map. apply Forall_forall. intros r Hr [x a] Hterm.
      apply poly_variables_contains with (r := r) (a := a); [now right|exact Hterm].
  Qed.

  (** The actual entailment run eliminates every stored coefficient of its final rows. *)
  Lemma poly_entail_terminal_rows : forall P c,
    Forall (fun r => lhs (poly_constraint r) = nil)
      (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
        (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))).
  Proof.
    intros P c. apply poly_terminal_rows. apply poly_entail_source_support.
  Qed.

  (** A failed entailment search leaves a terminal system modeled by the zero store. *)
  Lemma poly_entail_terminal_model_Q : forall P c,
    lrel c = RLe -> entail_engine P c = None ->
    Forall (poly_satQ (fun _ => 0%Q))
      (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
        (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))).
  Proof.
    intros P c Hrelation Hnone. apply poly_terminal_model_Q.
    - apply poly_entail_terminal_rows.
    - now apply poly_entailment_no_contradiction.
  Qed.

  (** The residual puts both sides of a rational row on the same scale. *)
  Definition poly_residual_Q (v : X.t -> Q) (c : lcons X.t) : Q :=
    (poly_eval_coef_Q v (lhs c) - inject_Z (rhs c))%Q.

  Lemma poly_inject_nonzero : forall z, z <> 0%Z -> ~ (inject_Z z == 0)%Q.
  Proof.
    intros z Hnonzero Hzero. apply Hnonzero.
    apply (proj1 (inject_Z_injective z 0)). exact Hzero.
  Qed.

  Lemma poly_inject_positive : forall z, (0 < z)%Z -> (0 < inject_Z z)%Q.
  Proof.
    intros z Hpositive. rewrite Zlt_Qlt in Hpositive. exact Hpositive.
  Qed.

  Lemma poly_Q_scale_eq_zero : forall a x : Q, (0 < a)%Q ->
    ((a * x == 0)%Q <-> (x == 0)%Q).
  Proof.
    intros a x Hpositive. assert (Hnonzero : ~ (a == 0)%Q) by lra.
    pose proof (Qmult_inj_l x 0 a Hnonzero) as Hiff.
    now setoid_rewrite Qmult_0_r in Hiff.
  Qed.

  Lemma poly_Q_scale_lt_zero : forall a x : Q, (0 < a)%Q ->
    ((a * x < 0)%Q <-> (x < 0)%Q).
  Proof.
    intros a x Hpositive. pose proof (Qmult_lt_l x 0 a Hpositive) as Hiff.
    now setoid_rewrite Qmult_0_r in Hiff.
  Qed.

  Lemma poly_Q_scale_le_zero : forall a x : Q, (0 < a)%Q ->
    ((a * x <= 0)%Q <-> (x <= 0)%Q).
  Proof.
    intros a x Hpositive. pose proof (Qmult_le_l x 0 a Hpositive) as Hiff.
    now setoid_rewrite Qmult_0_r in Hiff.
  Qed.

  Lemma poly_satQ_residual : forall v r,
    poly_satQ v r <->
      match lrel (poly_constraint r) with
      | REq => (poly_residual_Q v (poly_constraint r) == 0)%Q
      | RLe => if poly_strict r then (poly_residual_Q v (poly_constraint r) < 0)%Q
          else (poly_residual_Q v (poly_constraint r) <= 0)%Q
      end.
  Proof.
    intros v r. unfold poly_satQ, poly_residual_Q.
    destruct (lrel (poly_constraint r)); [|destruct (poly_strict r)]; split; intro H; lra.
  Qed.

  (** Updating one rational coordinate changes evaluation by its total raw coefficient. *)
  Lemma poly_eval_update_Q : forall v x q xs,
    (poly_eval_coef_Q (upd X.eqb v x q) xs == poly_eval_coef_Q v xs +
      inject_Z (C.coef_of x xs) * (q - v x))%Q.
  Proof.
    intros v x q xs. induction xs as [|[y a] xs IH].
    - change (0 == 0 + 0 * (q - v x))%Q. ring.
    - change (inject_Z a * upd X.eqb v x q y + poly_eval_coef_Q (upd X.eqb v x q) xs ==
        (inject_Z a * v y + poly_eval_coef_Q v xs) +
          inject_Z (C.coef_of x ((y, a) :: xs)) * (q - v x))%Q.
      setoid_rewrite IH. rewrite coef_of_cons. unfold upd.
      rewrite (poly_key_eqb_sym y x). destruct (X.eqb_spec x y) as [Heq|Hneq].
      + subst y. rewrite inject_Z_plus. ring.
      + ring.
  Qed.

  Lemma poly_residual_update_Q : forall v x q c,
    (poly_residual_Q (upd X.eqb v x q) c == poly_residual_Q v c +
      inject_Z (poly_coefficient X.eqb x c) * (q - v x))%Q.
  Proof.
    intros v x q c. unfold poly_residual_Q.
    setoid_rewrite poly_eval_update_Q. rewrite coef_of_poly_coefficient. ring.
  Qed.

  Lemma poly_satQ_update_zero : forall v x q r,
    poly_coefficient X.eqb x (poly_constraint r) = 0%Z ->
    (poly_satQ (upd X.eqb v x q) r <-> poly_satQ v r).
  Proof.
    intros v x q r Hzero.
    assert (Heval : (poly_residual_Q (upd X.eqb v x q) (poly_constraint r) ==
      poly_residual_Q v (poly_constraint r))%Q).
    { setoid_rewrite poly_residual_update_Q. rewrite Hzero.
      change (poly_residual_Q v (poly_constraint r) + 0 * (q - v x) ==
        poly_residual_Q v (poly_constraint r))%Q. ring. }
    rewrite !poly_satQ_residual.
    destruct (lrel (poly_constraint r)); [|destruct (poly_strict r)];
      now setoid_rewrite Heval.
  Qed.

  (** Row combination acts linearly on rational residuals. *)
  Lemma poly_residual_add_Q : forall v a p b q,
    (poly_residual_Q v (poly_constraint (poly_add_rows X.encode a p b q)) ==
      inject_Z a * poly_residual_Q v (poly_constraint p) +
      inject_Z b * poly_residual_Q v (poly_constraint q))%Q.
  Proof.
    intros v a p b q. unfold poly_residual_Q, poly_add_rows.
    cbn [poly_constraint lhs rhs].
    setoid_rewrite normalize_coef_eval_Q. setoid_rewrite eval_coef_app_Q.
    setoid_rewrite eval_coef_scale_Q. rewrite inject_Z_plus, !inject_Z_mult. ring.
  Qed.

  (** Adding a satisfied equality and scaling positively preserves every row interpretation. *)
  Lemma poly_add_equality_positive_satQ : forall v a p b r,
    lrel (poly_constraint p) = REq -> poly_eq_nonstrict p -> poly_satQ v p ->
    (0 < b)%Z ->
    (poly_satQ v (poly_add_rows X.encode a p b r) <-> poly_satQ v r).
  Proof.
    intros v a p b r Hpeq Hstrict Hp Hb.
    pose proof (Hstrict Hpeq) as Hpflag.
    assert (Hbzero : Z.eqb b 0 = false) by (apply Z.eqb_neq; lia).
    assert (Hbpositive : Z.ltb 0 b = true) by now apply Z.ltb_lt.
    assert (Hrel : lrel (poly_constraint (poly_add_rows X.encode a p b r)) =
      lrel (poly_constraint r)).
    { unfold poly_add_rows. cbn [poly_constraint lrel].
      unfold poly_eq_used. rewrite Hpeq.
      destruct (lrel (poly_constraint r)); cbn [andb]; [reflexivity|now rewrite Hbzero]. }
    assert (Hflag : poly_strict (poly_add_rows X.encode a p b r) = poly_strict r).
    { unfold poly_add_rows. cbn [poly_strict]. rewrite Hpflag, Hbpositive.
      now rewrite andb_false_r. }
    pose proof (proj1 (poly_satQ_residual v p) Hp) as Hpzero. rewrite Hpeq in Hpzero.
    assert (Hres : (poly_residual_Q v (poly_constraint (poly_add_rows X.encode a p b r)) ==
      inject_Z b * poly_residual_Q v (poly_constraint r))%Q).
    { eapply Qeq_trans; [apply poly_residual_add_Q|]. setoid_rewrite Hpzero. ring. }
    rewrite !poly_satQ_residual, Hrel, Hflag.
    pose proof (poly_inject_positive b Hb) as HbQ.
    destruct (lrel (poly_constraint r)); [|destruct (poly_strict r)];
      setoid_rewrite Hres.
    - now apply poly_Q_scale_eq_zero.
    - now apply poly_Q_scale_lt_zero.
    - now apply poly_Q_scale_le_zero.
  Qed.

  Lemma poly_pivot_info : forall x p, poly_pivot X.eqb x p = true ->
    lrel (poly_constraint p) = REq /\ poly_coefficient X.eqb x (poly_constraint p) <> 0%Z.
  Proof.
    intros x p Hpivot. unfold poly_pivot in Hpivot.
    destruct (lrel (poly_constraint p)) eqn:Hrel; [|discriminate].
    split; [reflexivity|]. now apply negb_true_iff, Z.eqb_neq in Hpivot.
  Qed.

  Lemma poly_cancel_satQ : forall v x p r,
    poly_pivot X.eqb x p = true -> poly_eq_nonstrict p -> poly_satQ v p ->
    (poly_satQ v (poly_cancel X.encode X.eqb x p r) <-> poly_satQ v r).
  Proof.
    intros v x p r Hpivot Hstrict Hp.
    destruct (poly_pivot_info x p Hpivot) as [Hpeq Hnonzero].
    unfold poly_cancel. destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0);
      [reflexivity|].
    apply poly_add_equality_positive_satQ; try assumption. now apply Z.abs_pos.
  Qed.

  (** A bound records the coordinate value where the row becomes an equality. *)
  Definition poly_endpoint_Q (v : X.t -> Q) (x : X.t) (r : poly_row X.t) : Q :=
    (v x - poly_residual_Q v (poly_constraint r) /
      inject_Z (poly_coefficient X.eqb x (poly_constraint r)))%Q.
  Definition poly_bound_Q (v : X.t -> Q) (x : X.t) (r : poly_row X.t) : Q * bool :=
    (poly_endpoint_Q v x r, poly_strict r).

  Lemma poly_endpoint_residual_Q : forall v x r,
    poly_coefficient X.eqb x (poly_constraint r) <> 0%Z ->
    (poly_residual_Q v (poly_constraint r) ==
      inject_Z (poly_coefficient X.eqb x (poly_constraint r)) *
        (v x - poly_endpoint_Q v x r))%Q.
  Proof.
    intros v x r Hnonzero. unfold poly_endpoint_Q. field. now apply poly_inject_nonzero.
  Qed.

  Lemma poly_endpoint_update_Q : forall v x q r,
    poly_coefficient X.eqb x (poly_constraint r) <> 0%Z ->
    (poly_residual_Q (upd X.eqb v x q) (poly_constraint r) ==
      inject_Z (poly_coefficient X.eqb x (poly_constraint r)) *
        (q - poly_endpoint_Q v x r))%Q.
  Proof.
    intros v x q r Hnonzero. eapply Qeq_trans; [apply poly_residual_update_Q|].
    setoid_rewrite (poly_endpoint_residual_Q v x r Hnonzero). ring.
  Qed.

  Lemma poly_upper_satQ : forall v x q r,
    lrel (poly_constraint r) = RLe ->
    (0 < poly_coefficient X.eqb x (poly_constraint r))%Z ->
    (poly_satQ (upd X.eqb v x q) r <-> poly_upper_at q (poly_bound_Q v x r)).
  Proof.
    intros v x q r Hrel Hpositive.
    pose proof (poly_inject_positive _ Hpositive) as HpositiveQ.
    rewrite poly_satQ_residual, Hrel. unfold poly_upper_at, poly_bound_Q. cbn [fst snd].
    destruct (poly_strict r); setoid_rewrite (poly_endpoint_update_Q v x q r ltac:(lia)).
    - rewrite (poly_Q_scale_lt_zero _ _ HpositiveQ). lra.
    - rewrite (poly_Q_scale_le_zero _ _ HpositiveQ). lra.
  Qed.

  Lemma poly_lower_satQ : forall v x q r,
    lrel (poly_constraint r) = RLe ->
    (poly_coefficient X.eqb x (poly_constraint r) < 0)%Z ->
    (poly_satQ (upd X.eqb v x q) r <-> poly_lower_at q (poly_bound_Q v x r)).
  Proof.
    intros v x q r Hrel Hnegative.
    assert (HpositiveQ : (0 < inject_Z (- poly_coefficient X.eqb x (poly_constraint r)))%Q).
    { apply poly_inject_positive. lia. }
    assert (Hres : (poly_residual_Q (upd X.eqb v x q) (poly_constraint r) ==
      inject_Z (- poly_coefficient X.eqb x (poly_constraint r)) *
        (poly_endpoint_Q v x r - q))%Q).
    { eapply Qeq_trans; [apply poly_endpoint_update_Q; lia|]. rewrite inject_Z_opp. ring. }
    rewrite poly_satQ_residual, Hrel. unfold poly_lower_at, poly_bound_Q. cbn [fst snd].
    destruct (poly_strict r); setoid_rewrite Hres.
    - rewrite (poly_Q_scale_lt_zero _ _ HpositiveQ). lra.
    - rewrite (poly_Q_scale_le_zero _ _ HpositiveQ). lra.
  Qed.

  (** An equality contribution never supplies a positive strict summand. *)
  Lemma poly_eq_used_nonstrict : forall a r,
    poly_eq_nonstrict r -> poly_eq_used a (poly_constraint r) = true ->
    ((0 <? a)%Z && poly_strict r) = false.
  Proof.
    intros a r Hnonstrict Hused. unfold poly_eq_nonstrict in Hnonstrict.
    unfold poly_eq_used in Hused. destruct (lrel (poly_constraint r)).
    - rewrite (Hnonstrict eq_refl). apply andb_false_r.
    - apply Z.eqb_eq in Hused. subst a. reflexivity.
  Qed.

  Lemma poly_add_rows_eq_nonstrict : forall a p b q,
    poly_eq_nonstrict p -> poly_eq_nonstrict q ->
    poly_eq_nonstrict (poly_add_rows X.encode a p b q).
  Proof.
    intros a p b q Hp Hq Hrel.
    cbn [poly_add_rows poly_constraint lrel] in Hrel.
    destruct (poly_eq_used a (poly_constraint p) && poly_eq_used b (poly_constraint q))
      eqn:Hused; [|discriminate].
    apply andb_true_iff in Hused as [Ha Hb]. cbn [poly_add_rows poly_strict].
    rewrite (poly_eq_used_nonstrict a p Hp Ha), (poly_eq_used_nonstrict b q Hq Hb).
    reflexivity.
  Qed.

  Lemma poly_cancel_eq_nonstrict : forall x p r,
    poly_eq_nonstrict p -> poly_eq_nonstrict r ->
    poly_eq_nonstrict (poly_cancel X.encode X.eqb x p r).
  Proof.
    intros x p r Hp Hr. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0); [exact Hr|].
    now apply poly_add_rows_eq_nonstrict.
  Qed.

  (** Elimination preserves the convention that equality rows are not strict. *)
  Lemma poly_step_eq_nonstrict : forall x rows,
    Forall poly_eq_nonstrict rows ->
    Forall poly_eq_nonstrict (poly_step X.encode X.eqb x rows).
  Proof.
    intros x rows Hflags. unfold poly_step.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - apply find_some in Hfind as [Hp _]. apply Forall_map.
      apply Forall_forall. intros r Hr. apply poly_cancel_eq_nonstrict.
      + exact (proj1 (Forall_forall _ _) Hflags p Hp).
      + exact (proj1 (Forall_forall _ _) Hflags r Hr).
    - apply Forall_app. split; apply Forall_forall; intros r Hin.
      + apply filter_In in Hin as [Hin _].
        exact (proj1 (Forall_forall _ _) Hflags r Hin).
      + apply in_flat_map in Hin as [p [Hp Hin]].
        apply in_map_iff in Hin as [q [Hsame Hq]]. subst r.
        apply filter_In in Hp as [Hp _]. apply filter_In in Hq as [Hq _].
        apply poly_add_rows_eq_nonstrict.
        * exact (proj1 (Forall_forall _ _) Hflags p Hp).
        * exact (proj1 (Forall_forall _ _) Hflags q Hq).
  Qed.

  Lemma poly_run_eq_nonstrict : forall xs rows,
    Forall poly_eq_nonstrict rows ->
    Forall poly_eq_nonstrict (poly_run X.encode X.eqb xs rows).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros rows Hflags; [exact Hflags|].
    cbn [poly_run]. apply IH. now apply poly_step_eq_nonstrict.
  Qed.

  Lemma poly_initial_eq_nonstrict : forall rows,
    Forall (fun p => lrel (fst p) = REq -> snd p = false) rows ->
    Forall poly_eq_nonstrict (poly_initial X.encode rows).
  Proof.
    intro rows. induction rows as [|[r flag] rows IH]; intro Hflags; [constructor|].
    inversion Hflags as [|p rows' Hhead Htail]; subst p rows'.
    cbn [poly_initial fst snd]. constructor.
    - intros Hrel. cbn [poly_constraint poly_normal_row lrel] in Hrel.
      cbn [poly_strict]. apply Hhead. exact Hrel.
    - apply Forall_map. change (Forall poly_eq_nonstrict (poly_initial X.encode rows)).
      now apply IH.
  Qed.

  Lemma poly_entailment_initial_nonstrict : forall P c,
    Forall poly_eq_nonstrict
      (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P)).
  Proof.
    intros P c. apply poly_initial_eq_nonstrict. constructor.
    - cbn [fst poly_negate lrel]. discriminate.
    - apply Forall_map. apply Forall_forall. intros r Hin Hrel. reflexivity.
  Qed.

  (** Normalization changes neither equality nor strict/non-strict rational models. *)
  Lemma poly_normalize_satQ : forall v c ms flag,
    poly_satQ v (PolyRow X.t (poly_normal_row X.encode c) ms flag) <->
      poly_satQ v (PolyRow X.t c ms flag).
  Proof.
    intros v c ms flag. unfold poly_satQ.
    cbn [poly_constraint poly_strict poly_normal_row lhs lrel rhs].
    destruct (lrel c); [|destruct flag]; now setoid_rewrite normalize_coef_eval_Q.
  Qed.

  (** Initial multiplier vectors do not change the models of their flagged source rows. *)
  Lemma poly_initial_models_Q : forall v rows,
    Forall (poly_satQ v) (poly_initial X.encode rows) <->
      Forall (fun p => poly_satQ v (PolyRow X.t (fst p) nil (snd p))) rows.
  Proof.
    intros v rows. induction rows as [|[r flag] rows IH].
    - split; intro H; constructor.
    - cbn [poly_initial fst snd]. rewrite !Forall_cons_iff, Forall_map.
      change ((poly_satQ v (PolyRow X.t (poly_normal_row X.encode r) nil flag) /\
        Forall (poly_satQ v) (poly_initial X.encode rows)) <->
        (poly_satQ v (PolyRow X.t r nil flag) /\
        Forall (fun p => poly_satQ v (PolyRow X.t (fst p) nil (snd p))) rows)).
      rewrite poly_normalize_satQ, IH. reflexivity.
  Qed.

  (** A model of the strict-complement input satisfies the source and falsifies its target. *)
  Lemma poly_entailment_initial_models_Q : forall P c v,
    lrel c = RLe ->
    Forall (poly_satQ v)
      (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P)) ->
    Forall (satQ v) P /\ ~ satQ v c.
  Proof.
    intros P c v Htarget Hmodels. apply poly_initial_models_Q in Hmodels.
    inversion Hmodels as [|p rows Hhead Htail]; subst p rows. split.
    - rewrite Forall_map in Htail. exact Htail.
    - unfold poly_satQ in Hhead.
      cbn [fst snd poly_constraint poly_strict poly_negate lhs lrel rhs] in Hhead.
      setoid_rewrite eval_coef_scale_Q in Hhead. rewrite inject_Z_opp in Hhead.
      change ((-1) * poly_eval_coef_Q v (lhs c) < - inject_Z (rhs c))%Q in Hhead.
      intro Hmodel. unfold satQ in Hmodel. rewrite Htarget in Hmodel.
      change (poly_eval_coef_Q v (lhs c) <= inject_Z (rhs c))%Q in Hmodel. lra.
  Qed.

  (** With no equality pivot, every row involving the eliminated variable is an inequality. *)
  Lemma poly_no_pivot_inequality : forall x rows r,
    find (poly_pivot X.eqb x) rows = None -> In r rows ->
    poly_coefficient X.eqb x (poly_constraint r) <> 0%Z ->
    lrel (poly_constraint r) = RLe.
  Proof.
    intros x rows r Hnone Hin Hnonzero.
    pose proof (find_none (poly_pivot X.eqb x) rows Hnone r Hin) as Hp.
    unfold poly_pivot in Hp. destruct (lrel (poly_constraint r)) eqn:Hrel; [|reflexivity].
    apply negb_false_iff, Z.eqb_eq in Hp. contradiction.
  Qed.

  (** Positive combinations of inequalities retain the disjunction of their strict flags. *)
  Lemma poly_positive_pair_shape : forall a p b r,
    lrel (poly_constraint p) = RLe -> lrel (poly_constraint r) = RLe ->
    (0 < a)%Z -> (0 < b)%Z ->
    lrel (poly_constraint (poly_add_rows X.encode a p b r)) = RLe /\
      poly_strict (poly_add_rows X.encode a p b r) = (poly_strict p || poly_strict r).
  Proof.
    intros a p b r Hp Hr Ha Hb.
    assert (Hazero : Z.eqb a 0 = false) by (apply Z.eqb_neq; lia).
    assert (Hapos : Z.ltb 0 a = true) by now apply Z.ltb_lt.
    assert (Hbpos : Z.ltb 0 b = true) by now apply Z.ltb_lt.
    split.
    - unfold poly_add_rows. cbn [poly_constraint lrel]. unfold poly_eq_used.
      now rewrite Hp, Hr, Hazero.
    - unfold poly_add_rows. cbn [poly_strict]. now rewrite Hapos, Hbpos.
  Qed.

  (** An opposite-sign pair is exactly the compatibility constraint between its endpoints. *)
  Lemma poly_pair_bounds_compatible : forall v x p r,
    lrel (poly_constraint p) = RLe -> lrel (poly_constraint r) = RLe ->
    (0 < poly_coefficient X.eqb x (poly_constraint p))%Z ->
    (poly_coefficient X.eqb x (poly_constraint r) < 0)%Z ->
    poly_satQ v (poly_add_rows X.encode
      (- poly_coefficient X.eqb x (poly_constraint r)) p
      (poly_coefficient X.eqb x (poly_constraint p)) r) ->
    poly_bounds_compatible (poly_bound_Q v x r) (poly_bound_Q v x p).
  Proof.
    intros v x p r Hprel Hrrel Hpositive Hnegative Hsat.
    set (a := poly_coefficient X.eqb x (poly_constraint p)) in *.
    set (b := poly_coefficient X.eqb x (poly_constraint r)) in *.
    assert (Hfactor : (0 < inject_Z (-b) * inject_Z a)%Q).
    { apply Qmult_lt_0_compat; apply poly_inject_positive; lia. }
    destruct (poly_positive_pair_shape (-b)%Z p a r Hprel Hrrel ltac:(lia) Hpositive)
      as [Hrel Hflag].
    assert (Hres : (poly_residual_Q v
      (poly_constraint (poly_add_rows X.encode (-b) p a r)) ==
      (inject_Z (-b) * inject_Z a) * (poly_endpoint_Q v x r - poly_endpoint_Q v x p))%Q).
    { eapply Qeq_trans; [apply poly_residual_add_Q|].
      setoid_rewrite (poly_endpoint_residual_Q v x p ltac:(unfold a in Hpositive; lia)).
      setoid_rewrite (poly_endpoint_residual_Q v x r ltac:(unfold b in Hnegative; lia)).
      fold a b. rewrite !inject_Z_opp. ring. }
    apply (proj1 (poly_satQ_residual _ _)) in Hsat. rewrite Hrel, Hflag in Hsat.
    unfold poly_bounds_compatible, poly_bound_Q. cbn [fst snd].
    rewrite orb_comm in Hsat.
    destruct (poly_strict r || poly_strict p); setoid_rewrite Hres in Hsat.
    - apply (proj1 (poly_Q_scale_lt_zero _ _ Hfactor)) in Hsat. lra.
    - apply (proj1 (poly_Q_scale_le_zero _ _ Hfactor)) in Hsat. lra.
  Qed.

  (** A model after eliminating one coordinate extends to a model before elimination. *)
  Lemma poly_step_model_lift : forall x rows v,
    Forall poly_eq_nonstrict rows ->
    Forall (poly_satQ v) (poly_step X.encode X.eqb x rows) ->
    exists q : Q, Forall (poly_satQ (upd X.eqb v x q)) rows.
  Proof.
    intros x rows v Hnonstrict Hmodels.
    unfold poly_step in Hmodels.
    destruct (find (poly_pivot X.eqb x) rows) as [p|] eqn:Hfind.
    - destruct (find_some (poly_pivot X.eqb x) rows Hfind) as [Hin Hpivot].
      destruct (poly_pivot_info x p Hpivot) as [Hrel Hnonzero].
      pose proof (proj1 (Forall_forall _ _) Hnonstrict p Hin) as Hpstrict.
      set (q := poly_endpoint_Q v x p).
      assert (Hpmodel : poly_satQ (upd X.eqb v x q) p).
      { apply (proj2 (poly_satQ_residual _ _)). rewrite Hrel.
        setoid_rewrite (poly_endpoint_update_Q v x q p Hnonzero). unfold q. ring. }
      exists q. rewrite Forall_map in Hmodels. apply Forall_forall. intros r Hr.
      apply (proj1 (poly_cancel_satQ _ x p r Hpivot Hpstrict Hpmodel)).
      apply (proj2 (poly_satQ_update_zero v x q _ (poly_cancel_zero x p r))).
      now apply (proj1 (Forall_forall _ _) Hmodels).
    - set (pos := filter (fun r => (0 <? poly_coefficient X.eqb x (poly_constraint r))%Z) rows)
        in *.
      set (neg := filter (fun r => (poly_coefficient X.eqb x (poly_constraint r) <? 0)%Z) rows)
        in *.
      assert (Hcompatible : forall lo hi,
        In lo (map (poly_bound_Q v x) neg) -> In hi (map (poly_bound_Q v x) pos) ->
        poly_bounds_compatible lo hi).
      { intros lo hi Hlo Hhi.
        apply in_map_iff in Hlo as [lower [Hsame Hlower]]. subst lo.
        apply in_map_iff in Hhi as [upper [Hsame Hupper]]. subst hi.
        unfold neg in Hlower. apply filter_In in Hlower as [Hlower Hnegative].
        unfold pos in Hupper. apply filter_In in Hupper as [Hupper Hpositive].
        apply Z.ltb_lt in Hnegative, Hpositive.
        apply poly_pair_bounds_compatible.
        - apply poly_no_pivot_inequality with (x := x) (rows := rows); try assumption; lia.
        - apply poly_no_pivot_inequality with (x := x) (rows := rows); try assumption; lia.
        - exact Hpositive.
        - exact Hnegative.
        - apply (proj1 (Forall_forall _ _) Hmodels).
          apply in_or_app. right. apply in_flat_map. exists upper. split.
          + unfold pos. apply filter_In. split; [exact Hupper|now apply Z.ltb_lt].
          + apply in_map_iff. exists lower. split; [reflexivity|].
            unfold neg. apply filter_In. split;
              [exact Hlower|now apply Z.ltb_lt]. }
      destruct (poly_Q_interval_model (map (poly_bound_Q v x) neg)
        (map (poly_bound_Q v x) pos) Hcompatible) as [q [Hlower Hupper]].
      exists q. apply Forall_forall. intros r Hin.
      destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0) eqn:Hzero.
      + apply Z.eqb_eq in Hzero.
        apply (proj2 (poly_satQ_update_zero v x q r Hzero)).
        apply (proj1 (Forall_forall _ _) Hmodels). apply in_or_app. left.
        apply filter_In. split; [exact Hin|now apply Z.eqb_eq].
      + apply Z.eqb_neq in Hzero.
        assert (Hrel : lrel (poly_constraint r) = RLe).
        { now apply poly_no_pivot_inequality with (x := x) (rows := rows). }
        destruct (Z.ltb 0 (poly_coefficient X.eqb x (poly_constraint r))) eqn:Hpositive.
        * apply Z.ltb_lt in Hpositive.
          apply (proj2 (poly_upper_satQ v x q r Hrel Hpositive)).
          apply (proj1 (Forall_forall _ _) Hupper). apply in_map.
          unfold pos. apply filter_In. split; [exact Hin|now apply Z.ltb_lt].
        * apply Z.ltb_ge in Hpositive.
          assert (Hnegative : (poly_coefficient X.eqb x (poly_constraint r) < 0)%Z) by lia.
          apply (proj2 (poly_lower_satQ v x q r Hrel Hnegative)).
          apply (proj1 (Forall_forall _ _) Hlower). apply in_map.
          unfold neg. apply filter_In. split; [exact Hin|now apply Z.ltb_lt].
  Qed.

  (** Reversing the finite elimination sequence reconstructs a rational source model. *)
  Lemma poly_run_model_lift : forall xs rows v,
    Forall poly_eq_nonstrict rows ->
    Forall (poly_satQ v) (poly_run X.encode X.eqb xs rows) ->
    exists w : X.t -> Q, Forall (poly_satQ w) rows.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros rows v Hnonstrict Hmodels.
    - exists v. exact Hmodels.
    - cbn [poly_run] in Hmodels.
      destruct (IH (poly_step X.encode X.eqb x rows) v
        (poly_step_eq_nonstrict x rows Hnonstrict) Hmodels) as [w Hstep].
      destruct (poly_step_model_lift x rows w Hnonstrict Hstep) as [q Hsource].
      exists (upd X.eqb w x q). exact Hsource.
  Qed.

  (** Failure of the checked producer reconstructs a rational counterexample to its target. *)
  Lemma poly_engine_failed_model_Q : forall P c,
    lrel c = RLe -> entail_engine P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  Proof.
    intros P c Hrel Hnone.
    destruct (poly_run_model_lift (poly_variables X.encode (c :: P))
      (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))
      (fun _ => 0%Q) (poly_entailment_initial_nonstrict P c)
      (poly_entail_terminal_model_Q P c Hrel Hnone)) as [v Hmodels].
    exists v. now apply poly_entailment_initial_models_Q.
  Qed.

  Lemma poly_normal_row_models_Q : forall v c,
    satQ v (poly_normal_row X.encode c) <-> satQ v c.
  Proof.
    intros v c. change (poly_satQ v (PolyRow X.t (poly_normal_row X.encode c) [] false) <->
      poly_satQ v (PolyRow X.t c [] false)). apply poly_normalize_satQ.
  Qed.

  Lemma poly_normal_rows_models_Q : forall v P,
    Forall (satQ v) (poly_normal_rows P) <-> Forall (satQ v) P.
  Proof.
    intros v P. unfold poly_normal_rows. rewrite Forall_map.
    split; intro Hmodels; eapply Forall_impl; [|exact Hmodels| |exact Hmodels].
    - intros c Hc. exact (proj1 (poly_normal_row_models_Q v c) Hc).
    - intros c Hc. exact (proj2 (poly_normal_row_models_Q v c) Hc).
  Qed.

  Lemma poly_failed_certificate_model_Q : forall P c,
    lrel c = RLe -> entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  Proof.
    intros P c Hrel Hnone. unfold entail_cert in Hnone.
    destruct (poly_engine_failed_model_Q (poly_normal_rows P)
      (poly_normal_row X.encode c) Hrel Hnone) as [v [Hmodels Hfalse]].
    exists v. split; [exact (proj1 (poly_normal_rows_models_Q v P) Hmodels)|].
    intro Hc. apply Hfalse. exact (proj2 (poly_normal_row_models_Q v c) Hc).
  Qed.


  (** A complete successful untagging maps each original key through Some. *)
  Lemma untag_keys : forall xs ys, untag xs = Some ys ->
    map fst xs = map (@Some X.t) (map fst ys).
  Proof.
    intro xs. induction xs as [|[x a] xs IH]; intros ys Hresult.
    - cbn [untag] in Hresult. injection Hresult as Hsame. subst ys. reflexivity.
    - destruct x as [x|]; cbn [untag] in Hresult; [|discriminate].
      destruct (untag xs) as [zs|] eqn:Htail; [|discriminate].
      injection Hresult as Hsame. subst ys. cbn [map fst]. f_equal.
      now apply IH.
  Qed.

  Lemma untag_nodup : forall xs ys, untag xs = Some ys ->
    NoDup (map fst xs) -> NoDup (map fst ys).
  Proof.
    intros xs ys Hresult Hunique. apply NoDup_map_inv with (f := @Some X.t).
    rewrite <- (untag_keys xs ys Hresult). exact Hunique.
  Qed.

  (** Every raw one-step elimination emits normalized coefficient lists. *)
  Lemma fm_elim_nodup : forall x P,
    Forall (fun r => NoDup (map fst (lhs (row_of r)))) (fm_elim x P).
  Proof.
    intros x P. unfold fm_elim. apply Forall_map.
    change (Forall poly_row_unique
      (poly_step X.encode X.eqb x
        (poly_initial X.encode (map (fun r => (r, false)) P)))).
    apply poly_step_unique, poly_initial_unique.
  Qed.

  Lemma havoc_rows_nodup : forall x P,
    Forall (fun r => NoDup (map fst (lhs r)))
      (map row_of (filter (checked_projection P x) (fm_elim x P))).
  Proof.
    intros x P. apply Forall_map. apply Forall_forall. intros r Hin.
    apply filter_In in Hin as [Hin _].
    exact (proj1 (Forall_forall _ _) (fm_elim_nodup x P) r Hin).
  Qed.

  Lemma assigned_candidate_nodup : forall P x f r c,
    poly_row_unique r -> assigned_candidate P x f r = Some c -> NoDup (map fst (lhs c)).
  Proof.
    intros P x f r c Hunique Hresult. unfold assigned_candidate in Hresult.
    destruct (untag (lhs (poly_constraint r))) as [xs|] eqn:Huntag; [|discriminate].
    destruct (poly_multipliers r) as [|m ms]; [discriminate|].
    destruct (C.check_entails P
      (subst x f (LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r))))
      (Cert ms 1 false)); [|discriminate].
    injection Hresult as Hsame. subst c. cbn [lhs].
    apply untag_nodup with (xs := lhs (poly_constraint r)); assumption.
  Qed.

  Lemma assign_linear_nodup : forall x f P,
    Forall (fun r => NoDup (map fst (lhs r))) (assign_linear x f P).
  Proof.
    intros x f P. unfold assign_linear. apply Forall_forall. intros c Hin.
    apply in_flat_map in Hin as [r [Hmember Hin]].
    destruct (assigned_candidate P x f r) as [s|] eqn:Hcandidate; [|contradiction].
    destruct Hin as [Hsame|Hfalse]; [subst s|contradiction].
    apply assigned_candidate_nodup with (P := P) (x := x) (f := f) (r := r);
      [|exact Hcandidate].
    exact (proj1 (Forall_forall _ _)
      (poly_step_unique _ tmp_encode tmp_eqb None _
        (poly_initial_unique _ tmp_encode _)) r Hmember).
  Qed.

  Lemma atom_row_nodup : forall a r, atom_row a = Some r -> NoDup (map fst (lhs r)).
  Proof.
    intros a r Hresult. unfold atom_row in Hresult.
    destruct (alw a), (arw a); try discriminate.
    destruct (acmp a); injection Hresult as Hsame; subst r;
      cbn [lhs]; apply poly_normal_coef_nodup.
  Qed.

  Lemma assume_rows_nodup : forall g es,
    Forall (fun r => NoDup (map fst (lhs r)))
      (flat_map (fun a => match atom_row a with Some r => r :: nil | None => nil end)
        (F.atoms_of g es)).
  Proof.
    intros g es. apply Forall_forall. intros r Hin.
    apply in_flat_map in Hin as [a [Ha Hin]].
    destruct (atom_row a) as [s|] eqn:Hatom; [|contradiction].
    destruct Hin as [Hsame|Hfalse]; [subst s|contradiction].
    now apply atom_row_nodup with (a := a).
  Qed.

  (** Keeping every list member leaves the list unchanged. *)
  Lemma filter_all_true : forall A (f : A -> bool) xs,
    forallb f xs = true -> filter f xs = xs.
  Proof.
    intros A f xs. induction xs as [|x xs IH]; intro Hall; [reflexivity|].
    cbn [forallb] in Hall. apply andb_true_iff in Hall as [Hhead Htail].
    cbn [filter]. rewrite Hhead, (IH Htail). reflexivity.
  Qed.

  (** Rejecting at least one member strictly reduces the filtered list length. *)
  Lemma filter_some_false : forall A (f : A -> bool) xs,
    forallb f xs = false -> length (filter f xs) < length xs.
  Proof.
    intros A f xs. induction xs as [|x xs IH]; intro Hsome; [discriminate|].
    cbn [forallb] in Hsome. cbn [filter].
    destruct (f x); cbn [length] in *.
    - specialize (IH Hsome). lia.
    - pose proof (filter_length_le f xs). lia.
  Qed.

  (** Reached states denote their simultaneous rational solutions. *)
  Definition poly_models_Q (s : t) (v : X.t -> Q) : Prop :=
    match s with Unreached => False | Reached P => Forall (satQ v) P end.

  Lemma entails_row_sound_Q : forall P c v,
    entails_row P c = true -> Forall (satQ v) P -> satQ v c.
  Proof.
    intros P c v Hresult Hmodels. unfold entails_row in Hresult.
    destruct (entail_cert P c) as [k|] eqn:Hcertificate; [|discriminate].
    destruct (entail_cert_returned P c k Hcertificate) as [Hcheck Hcut].
    now apply C.check_entails_sound_Q with (P := P) (k := k).
  Qed.

  Lemma entails_row_complete_Q : forall P c,
    lrel c = RLe -> (forall v : X.t -> Q, Forall (satQ v) P -> satQ v c) ->
    entails_row P c = true.
  Proof.
    intros P c Hrel Hsemantic. unfold entails_row.
    destruct (entail_cert P c) as [k|] eqn:Hcertificate; [reflexivity|].
    destruct (poly_failed_certificate_model_Q P c Hrel Hcertificate)
      as [v [Hmodels Hfalse]]. exfalso. exact (Hfalse (Hsemantic v Hmodels)).
  Qed.

  (** Equality is equivalent to its two non-strict inequality directions over Q. *)
  Lemma poly_row_eq_split_Q : forall v r, lrel r = REq ->
    (satQ v r <-> satQ v (LCons X.t (lhs r) RLe (rhs r)) /\ satQ v (poly_negate r)).
  Proof.
    intros v r Hrel. unfold satQ. cbn [lhs lrel rhs poly_negate]. rewrite Hrel.
    change ((poly_eval_coef_Q v (lhs r) == inject_Z (rhs r))%Q <->
      (poly_eval_coef_Q v (lhs r) <= inject_Z (rhs r))%Q /\
      (poly_eval_coef_Q v (poly_scale_coef (-1)%Z (lhs r)) <= inject_Z (- rhs r))%Q).
    setoid_rewrite eval_coef_scale_Q. rewrite inject_Z_opp.
    change ((poly_eval_coef_Q v (lhs r) == inject_Z (rhs r))%Q <->
      (poly_eval_coef_Q v (lhs r) <= inject_Z (rhs r))%Q /\
      ((-1) * poly_eval_coef_Q v (lhs r) <= - inject_Z (rhs r))%Q).
    split; [intro H; split; lra|intros [Hleft Hright]; lra].
  Qed.

  Lemma keep_row_sound_Q : forall P r v,
    keep_row P r = true -> Forall (satQ v) P -> satQ v r.
  Proof.
    intros P r v Hkeep Hmodels. unfold keep_row in Hkeep.
    destruct (lrel r) eqn:Hrel.
    - apply andb_true_iff in Hkeep as [Hleft Hright].
      apply (proj2 (poly_row_eq_split_Q v r Hrel)). split.
      + now apply entails_row_sound_Q with (P := P).
      + now apply entails_row_sound_Q with (P := P).
    - now apply entails_row_sound_Q with (P := P).
  Qed.

  Lemma keep_row_complete_Q : forall P r,
    (forall v : X.t -> Q, Forall (satQ v) P -> satQ v r) -> keep_row P r = true.
  Proof.
    intros P r Hsemantic. unfold keep_row. destruct (lrel r) eqn:Hrel.
    - apply andb_true_iff. split; apply entails_row_complete_Q; [reflexivity| |reflexivity|].
      + intros v Hmodels. exact (proj1 (proj1 (poly_row_eq_split_Q v r Hrel)
          (Hsemantic v Hmodels))).
      + intros v Hmodels. exact (proj2 (proj1 (poly_row_eq_split_Q v r Hrel)
          (Hsemantic v Hmodels))).
    - apply entails_row_complete_Q; [exact Hrel|exact Hsemantic].
  Qed.

  Lemma keep_row_iff_Q : forall P r,
    keep_row P r = true <-> forall v : X.t -> Q, Forall (satQ v) P -> satQ v r.
  Proof.
    intros P r. split.
    - intros Hkeep v Hmodels. now apply keep_row_sound_Q with (P := P).
    - apply keep_row_complete_Q.
  Qed.

  Lemma is_bot_sound_Q : forall s v, is_bot s = true -> ~ poly_models_Q s v.
  Proof.
    intros [|P] v Hbot Hmodels; [exact Hmodels|].
    pose proof (entails_row_sound_Q P (LCons X.t nil RLe (-1)%Z) v Hbot Hmodels) as Hfalse.
    change (0 <= -1)%Q in Hfalse. lra.
  Qed.

  Lemma is_bot_complete_Q : forall s,
    (forall v : X.t -> Q, ~ poly_models_Q s v) -> is_bot s = true.
  Proof.
    intros [|P] Hempty; [reflexivity|].
    apply entails_row_complete_Q; [reflexivity|].
    intros v Hmodels. exfalso. exact (Hempty v Hmodels).
  Qed.

  (** Boolean inclusion preserves every rational model. *)
  Lemma leb_sound_Q : forall a b, leb a b = true ->
    forall v : X.t -> Q, poly_models_Q a v -> poly_models_Q b v.
  Proof.
    intros [|P] [|Q] Hle v Hmodels; cbn [poly_models_Q] in *; try contradiction.
    - exact (is_bot_sound_Q (Reached P) v Hle Hmodels).
    - apply Forall_forall. intros r Hin. apply keep_row_sound_Q with (P := P).
      + exact (proj1 (forallb_forall _ _) Hle r Hin).
      + exact Hmodels.
  Qed.

  (** Every rational semantic inclusion is recognized by Boolean inclusion. *)
  Lemma leb_complete_Q : forall a b,
    (forall v : X.t -> Q, poly_models_Q a v -> poly_models_Q b v) -> leb a b = true.
  Proof.
    intros [|P] [|Q] Hsemantic; [reflexivity|reflexivity| |].
    - apply is_bot_complete_Q. intros v Hmodels. exact (Hsemantic v Hmodels).
    - apply forallb_forall. intros r Hin. apply keep_row_complete_Q.
      intros v Hmodels. exact (proj1 (Forall_forall _ _) (Hsemantic v Hmodels) r Hin).
  Qed.

  Lemma leb_iff_Q : forall a b,
    leb a b = true <-> forall v : X.t -> Q, poly_models_Q a v -> poly_models_Q b v.
  Proof.
    intros a b. split; [apply leb_sound_Q|apply leb_complete_Q].
  Qed.

  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intro a. apply leb_complete_Q. intros v Hmodels. exact Hmodels.
  Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc. apply leb_complete_Q. intros v Hmodels.
    apply leb_sound_Q with (a := b); [exact Hbc|].
    now apply leb_sound_Q with (a := a).
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    destruct a; reflexivity.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Hbot. apply leb_complete_Q. intros v Hmodels.
    exfalso. exact (is_bot_sound_Q a v Hbot Hmodels).
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|P] [|Q]; apply leb_complete_Q; intros v Hmodels;
      cbn [poly_models_Q join] in *; try contradiction; try exact Hmodels.
    apply Forall_app. split; apply Forall_forall; intros r Hin;
      apply filter_In in Hin as [Hin Hkeep].
    - exact (proj1 (Forall_forall _ _) Hmodels r Hin).
    - now apply keep_row_sound_Q with (P := P).
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|P] [|Q]; apply leb_complete_Q; intros v Hmodels;
      cbn [poly_models_Q join] in *; try contradiction; try exact Hmodels.
    apply Forall_app. split; apply Forall_forall; intros r Hin;
      apply filter_In in Hin as [Hin Hkeep].
    - now apply keep_row_sound_Q with (P := Q).
    - exact (proj1 (Forall_forall _ _) Hmodels r Hin).
  Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    destruct a; reflexivity.
  Qed.
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p [|P] [|Q]; apply leb_complete_Q; intros v Hmodels;
      cbn [poly_models_Q widen] in *; try contradiction; try exact Hmodels.
    apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
    exact (proj1 (Forall_forall _ _) Hmodels r Hin).
  Qed.
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p [|P] [|Q]; apply leb_complete_Q; intros v Hmodels;
      cbn [poly_models_Q widen] in *; try contradiction.
    - destruct (is_bot (Reached Q)) eqn:Hbot.
      + exfalso. exact (is_bot_sound_Q (Reached Q) v Hbot Hmodels).
      + exact Hmodels.
    - apply Forall_forall. intros r Hin. apply filter_In in Hin as [_ Hkeep].
      now apply keep_row_sound_Q with (P := Q).
  Qed.
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p [|P] [|Q] Hle; cbn [widen]; try reflexivity.
    - change (is_bot (Reached Q) = true) in Hle. now rewrite Hle.
    - f_equal. apply filter_all_true. exact Hle.
  Qed.
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|P] [|Q] Hbot Hle; cbn [is_bot leb] in Hbot, Hle; try discriminate.
    change (length (filter (keep_row Q) P) < length P). now apply filter_some_false.
  Qed.
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p [|P] [|Q] Hbot; cbn [is_bot] in Hbot; try discriminate.
    - apply Nat.le_refl.
    - apply filter_length_le.
  Qed.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle. split; [|exact Hle]. apply leb_complete_Q. intros v Hmodels. exact Hmodels.
  Qed.
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof.
    intros [|P] [|Q] v Hle Hmodels; cbn [ngamma] in *; try contradiction.
    - exact (is_bot_sound (Reached P) v Hle Hmodels).
    - apply Forall_forall. intros r Hin. apply keep_row_sound with (P := P).
      + exact (proj1 (forallb_forall _ _) Hle r Hin).
      + exact Hmodels.
  Qed.
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof.
    intros v Hfalse. exact Hfalse.
  Qed.
  Lemma ngamma_top : forall v, ngamma top v.
  Proof.
    intro v. constructor.
  Qed.
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x [|P] st c Hmodels; [contradiction |].
    change (Forall (sat (fun y => N.num (upd X.eqb st x c y)))
      (map row_of (filter (checked_projection P x) (fm_elim x P)))).
    apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [q [Hsame Hin]]. subst r.
    apply filter_In in Hin as [_ Hchecked].
    exact (checked_projection_sound P x q st c Hchecked Hmodels).
  Qed.
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x e [|P] st c Hmodels Heval; [contradiction |]. unfold assign.
    destruct (F.lin_of e) as [[f wrapping]|] eqn:Hform.
    - destruct wrapping.
      + pose proof (F.lin_sound st e c f NoWrap Heval Hform) as Hvalue.
        cbn [wrap_into] in Hvalue.
        pose proof (assign_linear_sound x (poly_prepare_form X.encode f) P
          (fun y => N.num (st y)) Hmodels) as Hpost.
        rewrite poly_prepare_form_eval in Hpost.
        apply Forall_forall. intros r Hin.
        apply sat_pointwise with
          (v := upd X.eqb (fun y => N.num (st y)) x
            (eval_lin (fun y => N.num (st y)) f)).
        * intro y. unfold upd. destruct (X.eqb y x); [symmetry; exact Hvalue | reflexivity].
        * exact (proj1 (Forall_forall _ _) Hpost r Hin).
      + exact (havoc_sound x (Reached P) st c Hmodels).
    - exact (havoc_sound x (Reached P) st c Hmodels).
  Qed.

  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof.
    intros g es [|P] st cs Hmodels Heval Hguard; [contradiction |].
    change (Forall (sat (fun y => N.num (st y)))
      (flat_map (fun a => match atom_row a with Some r => r :: nil | None => nil end)
        (F.atoms_of g es) ++ P)).
    pose proof (F.atoms_sound g es st cs Heval Hguard) as Hatoms.
    apply Forall_app. split; [| exact Hmodels]. apply Forall_forall. intros r Hin.
    apply in_flat_map in Hin as [a [Hin Hrow]].
    destruct (atom_row a) as [q|] eqn:Hresult; [| contradiction].
    destruct Hrow as [Hsame|Hfalse]; [subst q | contradiction].
    apply atom_row_sound with (a := a); [exact Hresult |].
    exact (proj1 (Forall_forall _ _) Hatoms a Hin).
  Qed.
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof.
    intros e [|P] st c Hmodels Heval; [contradiction |]. unfold range.
    destruct (F.lin_of e) as [[f wrapping]|] eqn:Hform; [destruct wrapping |].
    - pose proof (F.lin_sound st e c f NoWrap Heval Hform) as Hvalue.
      cbn [wrap_into] in Hvalue. rewrite Hvalue. now apply range_linear_sound.
    - destruct (lo <=? hi)%Z eqn:Hvalid; [| split; exact I].
      apply Z.leb_le in Hvalid.
      pose proof (F.lin_sound st e c f (WrapTo lo hi) Heval Hform) as Hvalue.
      cbn [wrap_into] in Hvalue.
      pose proof (Z.mod_pos_bound (eval_lin (fun y => N.num (st y)) f - lo)
        (hi - lo + 1) ltac:(lia)) as Hmod.
      change (lo <= N.num c <= hi)%Z. lia.
    - split; exact I.
  Qed.
  Lemma ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  Proof.
    intros P v. reflexivity.
  Qed.
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof.
    intros v Hfalse. exact Hfalse.
  Qed.
End Poly.

(** The temporary coordinate uses the runtime encoding and its derived clocks. *)
Module PolyClockKey (X : KEY_T) <: KEY_T.
  Definition t := option X.t.
  Definition encode (x : t) : positive :=
    match x with None => xH | Some y => xO (X.encode y) end.
  Definition eqb (x y : t) : bool :=
    match x, y with
    | None, None => true
    | Some a, Some b => X.eqb a b
    | _, _ => false
    end.
  Include KEY_SPEC.
  (** The tag bit separates the temporary coordinate from every source key. *)
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [a|] [b|] H; cbn [encode] in H; try discriminate; [|reflexivity].
    f_equal. apply X.encode_inj. now injection H.
  Qed.
  (** Temporary-key equality reflects the source key equality. *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [a|] [b|]; cbn [eqb]; try (constructor; congruence).
    destruct (X.eqb_spec a b); constructor; congruence.
  Qed.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := (2 * X.c_key + 8)%N.
  (** Encoding pays the source clock and the option tag. *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof.
    intros [x|]; time_unfold T_encode; unfold c_key, bits, encode;
      cbn [Pos.size_nat]; time_simpl.
    - pose proof (X.T_encode_le x). unfold X.bits in *.
      rewrite !Nat2N.inj_add, Nat2N.inj_succ. cbn [N.of_nat]. nia.
    - cbn [N.of_nat]. nia.
  Qed.
  (** Equality pays at most one source-key comparison. *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof.
    intros [a|] [b|]; time_unfold T_eqb; unfold c_key, bits, encode;
      cbn [Pos.size_nat]; time_simpl.
    - pose proof (X.T_eqb_le a b). unfold X.bits in *.
      rewrite !Nat2N.inj_add, Nat2N.inj_succ. cbn [N.of_nat]. nia.
    - rewrite !Nat2N.inj_add, Nat2N.inj_succ. cbn [N.of_nat]. nia.
    - cbn [N.of_nat]. nia.
    - cbn [N.of_nat]. nia.
  Qed.
End PolyClockKey.

(** This context supplies unused language fields to key-parametric clock lemmas. *)
Module PolyClockLinearize (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    <: LINEARIZE_T X L N.
  Definition lin_of (_ : term L.op X.t) : option (lin X.t * wrapr) := None.
  Definition atoms_of (_ : L.guard) (_ : list (term L.op X.t)) : list (atom X.t) := nil.
  (** The unused context recognizes no expression and therefore makes no value claim. *)
  Lemma lin_sound : forall st e c f r,
    eval_term L.eval st e = Some c -> lin_of e = Some (f, r) ->
    N.num c = wrap_into r (eval_lin (fun x => N.num (st x)) f).
  Proof.
    intros st e c f r Heval Hlinear. discriminate.
  Qed.
  (** The unused context emits no guard obligations. *)
  Lemma atoms_sound : forall g es st cs,
    eval_terms L.eval st es = Some cs -> L.holds g cs ->
    Forall (atom_holds (fun x => N.num (st x))) (atoms_of g es).
  Proof.
    intros. constructor.
  Qed.
  Definition bits_e (_ : term L.op X.t) : nat := 0.
  Definition bits_es (_ : L.guard) (_ : list (term L.op X.t)) : nat := 0.
  TimeFun lin_of.
  TimeFun atoms_of.
  Definition form_bits (f : lin X.t) : nat :=
    fold_right Nat.max (Z.size_nat (cst f))
      (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) (coef f)).
  Definition wrap_bits (r : wrapr) : nat :=
    match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end.
  (** No recognized form needs a size allowance in this proof-only context. *)
  Lemma lin_of_size : forall e f r, lin_of e = Some (f, r) ->
    length (coef f) <= tsize e /\ form_bits f + wrap_bits r <= bits_e e.
  Proof.
    intros e f r Hlinear. discriminate.
  Qed.
  (** The empty emitted atom list fits every operand-size allowance. *)
  Lemma atoms_of_size : forall g es,
    length (atoms_of g es) <= 2 * fold_right Nat.add 1 (map tsize es) /\
    Forall (fun a =>
      length (coef (al a)) + length (coef (ar a)) <= fold_right Nat.add 0 (map tsize es) /\
      form_bits (al a) + wrap_bits (alw a) + form_bits (ar a) + wrap_bits (arw a) <=
        bits_es g es) (atoms_of g es).
  Proof.
    intros. split; [cbn [atoms_of length]; lia|constructor].
  Qed.
  Definition c_linearize : N := 1%N.
  (** Rejecting an expression takes one unit, paid by its nonzero term size. *)
  Lemma T_lin_of_le : forall e,
    (T_lin_of e <= c_linearize * N.of_nat (tsize e) * N.of_nat (bits_e e + 1))%N.
  Proof.
    intro e. assert (Hsize : 1 <= tsize e) by (destruct e; cbn [tsize]; lia).
    time_unfold T_lin_of. unfold c_linearize, bits_e. cbn [N.of_nat]. nia.
  Qed.
  (** Emitting the empty list takes one unit of work. *)
  Lemma T_atoms_of_le : forall g es,
    (T_atoms_of g es <= c_linearize *
      N.of_nat (fold_right Nat.add 0%nat (map tsize es) + 1) *
      N.of_nat (bits_es g es + 1))%N.
  Proof.
    intros g es. time_unfold T_atoms_of. unfold c_linearize, bits_es.
    rewrite Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.
End PolyClockLinearize.


(** Checked arithmetic and elimination helpers can also be applied to temporary keys. *)
Module PolyClockCore (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X).
  Include Poly X L N F C.
  Definition wsize (_ : wparam) : nat := 0.
  Definition normal (P : list (lcons X.t)) : Prop :=
    Forall (fun r => NoDup (map fst (lhs r))) P.
  Definition normal_s (s : t) : Prop :=
    match s with Unreached => True | Reached P => normal P end.
  Definition vars_of (P : list (lcons X.t)) : list X.t :=
    fold_left (fun acc x => if existsb (X.eqb x) acc then acc else x :: acc)
      (flat_map (fun r => map fst (lhs r)) P) nil.
  Definition n (P : list (lcons X.t)) : nat := length P + length (vars_of P).
  Definition ell (P : list (lcons X.t)) : nat :=
    fold_right Nat.max 0 (map C.row_bits P) +
    fold_right Nat.max 0 (map C.row_key_bits P).
  (** An absent key has coefficient zero. *)
  Lemma poly_coef_absent : forall x xs,
    ~ In x (map fst xs) -> C.coef_of x xs = 0%Z.
  Proof.
    intros x xs. induction xs as [|[y a] xs IH]; intro Habsent; [reflexivity|].
    rewrite coef_of_cons. destruct (X.eqb_spec x y) as [Heq|Hneq].
    - subst y. exfalso. apply Habsent. left. reflexivity.
    - apply IH. intro Hin. apply Habsent. right. exact Hin.
  Qed.

  (** A unique stored coefficient equals its row's total coefficient at that key. *)
  Lemma poly_coef_member : forall x a xs,
    NoDup (map fst xs) -> In (x, a) xs -> C.coef_of x xs = a.
  Proof.
    intros x a xs. induction xs as [|[y b] xs IH]; intros Hunique Hin;
      [contradiction|].
    inversion Hunique as [|key keys Hnot Htail]; subst key keys.
    destruct Hin as [Heq|Hin].
    - injection Heq as Hkey Hcoef. subst y b.
      rewrite coef_of_cons, poly_key_eqb_refl, (poly_coef_absent x xs Hnot).
      ring.
    - rewrite coef_of_cons. destruct (X.eqb_spec x y) as [Heq|Hneq].
      + subst y. exfalso. apply Hnot. apply in_map with (f := fst) in Hin. exact Hin.
      + apply IH; assumption.
  Qed.

  (** A maximum fold bounds each contributing entry. *)
  Lemma poly_max_member : forall A (f : A -> nat) base xs x,
    In x xs -> f x <= fold_right Nat.max base (map f xs).
  Proof.
    intros A f base xs. induction xs as [|a xs IH]; intros x Hin; [contradiction|].
    cbn [map fold_right]. destruct Hin as [->|Hin].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  Qed.

  (** A maximum fold also bounds its initial value. *)
  Lemma poly_max_base : forall A (f : A -> nat) base xs,
    base <= fold_right Nat.max base (map f xs).
  Proof.
    intros A f base xs. induction xs as [|a xs IH]; cbn [map fold_right]; lia.
  Qed.

  (** Bounding the initial value and every entry bounds a maximum fold. *)
  Lemma poly_max_bound : forall A (f : A -> nat) base xs bound,
    base <= bound -> Forall (fun x => f x <= bound) xs ->
    fold_right Nat.max base (map f xs) <= bound.
  Proof.
    intros A f base xs bound Hbase Hentries. induction Hentries as [|a xs Ha Htail IH];
      cbn [map fold_right]; lia.
  Qed.

  (** Uniqueness prevents coefficient lookup from summing separate occurrences. *)
  Lemma poly_coef_bits : forall x xs bits,
    NoDup (map fst xs) -> Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Z.size_nat (C.coef_of x xs) <= bits.
  Proof.
    intros x xs. induction xs as [|[y a] xs IH]; intros bits Hunique Hbits.
    - change (0 <= bits). lia.
    - inversion Hunique as [|key keys Hnot Htail]; subst key keys.
      inversion Hbits as [|p ps Ha Htailbits]; subst p ps. rewrite coef_of_cons.
      destruct (X.eqb_spec x y) as [Heq|Hneq].
      + subst y. rewrite (poly_coef_absent x xs Hnot), Z.add_0_r. exact Ha.
      + apply IH; assumption.
  Qed.

  (** A coefficient in a normal row fits the row's declared width. *)
  Lemma poly_row_coefficient_bits : forall x r,
    NoDup (map fst (lhs r)) ->
    Z.size_nat (poly_coefficient X.eqb x r) <= C.row_bits r.
  Proof.
    intros x r Hunique. rewrite <- coef_of_poly_coefficient.
    apply poly_coef_bits; [exact Hunique|]. apply Forall_forall. intros p Hin.
    unfold C.row_bits.
    exact (poly_max_member _ (fun p => Z.size_nat (snd p))
      (Z.size_nat (rhs r)) (lhs r) p Hin).
  Qed.

  (** Every initialized constraint is the normalization of one original constraint. *)
  Lemma poly_initial_source : forall P r,
    In r (poly_initial X.encode (map (fun p => (p, false)) P)) ->
    exists p, In p P /\ poly_constraint r = poly_normal_row X.encode p.
  Proof.
    intros P r Hin. apply in_map with (f := poly_constraint) in Hin.
    rewrite poly_initial_constraints, map_map in Hin.
    apply in_map_iff in Hin as [p [Heq Hin]]. exists p. split; [exact Hin|].
    symmetry. exact Heq.
  Qed.

  (** Each initial coefficient is bounded by the maximum original row width. *)
  Lemma poly_initial_coefficient_bits : forall P x r,
    normal P -> In r (poly_initial X.encode (map (fun p => (p, false)) P)) ->
    Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <=
      fold_right Nat.max 0 (map C.row_bits P).
  Proof.
    intros P x r Hnormal Hin.
    destruct (poly_initial_source P r Hin) as [p [Hp Hrow]].
    rewrite Hrow, poly_coefficient_normal.
    eapply Nat.le_trans; [apply poly_row_coefficient_bits|].
    - unfold normal in Hnormal. exact (proj1 (Forall_forall _ _) Hnormal p Hp).
    - exact (poly_max_member _ C.row_bits 0 P p Hp).
  Qed.

  (** An unchanged initial vector fits every width increased by one. *)
  Lemma poly_unit_row_bits : forall (r : poly_row X.t) count bits,
    length (poly_multipliers r) = count ->
    Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers r) ->
    length (poly_multipliers r) = count /\
      Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers r).
  Proof.
    intros r count bits Hlength Hunit. split; [exact Hlength|].
    apply Forall_forall. intros m Hin.
    destruct (proj1 (Forall_forall _ _) Hunit m Hin) as [Hm|Hm]; subst m;
      cbn [Z.size_nat Pos.size_nat]; lia.
  Qed.

  (** Adding two initial vectors preserves their common length and bounds their entries. *)
  Lemma poly_add_rows_multiplier_bits : forall a p b q count bits,
    length (poly_multipliers p) = count ->
    length (poly_multipliers q) = count ->
    Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers p) ->
    Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers q) ->
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    length (poly_multipliers (poly_add_rows X.encode a p b q)) = count /\
      Forall (fun m => Z.size_nat m <= bits + 1)
        (poly_multipliers (poly_add_rows X.encode a p b q)).
  Proof.
    intros a p b q count bits Hlp Hlq Hup Huq Ha Hb.
    cbn [poly_add_rows poly_multipliers]. split.
    - rewrite poly_weighted_length by lia. exact Hlp.
    - apply poly_weighted_units; assumption.
  Qed.

  (** Equality cancellation uses only the pivot coefficient and the target coefficient. *)
  Lemma poly_cancel_multiplier_bits : forall x p r count bits,
    length (poly_multipliers p) = count ->
    length (poly_multipliers r) = count ->
    Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers p) ->
    Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers r) ->
    Z.size_nat (poly_coefficient X.eqb x (poly_constraint p)) <= bits ->
    Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <= bits ->
    length (poly_multipliers (poly_cancel X.encode X.eqb x p r)) = count /\
      Forall (fun m => Z.size_nat m <= bits + 1)
        (poly_multipliers (poly_cancel X.encode X.eqb x p r)).
  Proof.
    intros x p r count bits Hlp Hlr Hup Hur Hp Hr. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0).
    - apply poly_unit_row_bits; assumption.
    - apply poly_add_rows_multiplier_bits; try assumption.
      + eapply Nat.le_trans; [apply poly_size_sign_mul|exact Hr].
      + now rewrite poly_size_abs.
  Qed.

  (** A single step combines unit vectors with coefficients bounded by the input width. *)
  Lemma poly_step_multiplier_bits : forall x rows count bits,
    Forall (fun r => length (poly_multipliers r) = count /\
      Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers r) /\
      Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <= bits) rows ->
    Forall (fun r => length (poly_multipliers r) = count /\
      Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers r))
      (poly_step X.encode X.eqb x rows).
  Proof.
    intros x rows count bits Hrows. rewrite Forall_forall in Hrows.
    unfold poly_step. destruct (find (poly_pivot X.eqb x) rows) as [pivot|] eqn:Hpivot.
    - apply find_some in Hpivot as [Hpivot _].
      destruct (Hrows pivot Hpivot) as [Hlp [Hup Hp]].
      apply Forall_map, Forall_forall. intros r Hin.
      destruct (Hrows r Hin) as [Hlr [Hur Hr]].
      apply poly_cancel_multiplier_bits; assumption.
    - apply Forall_app. split.
      + apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
        destruct (Hrows r Hin) as [Hlength [Hunit _]].
        apply poly_unit_row_bits; assumption.
      + apply Forall_forall. intros r Hin. apply in_flat_map in Hin as [p [Hp Hin]].
        apply filter_In in Hp as [Hp _]. apply in_map_iff in Hin as [q [Heq Hq]].
        apply filter_In in Hq as [Hq _]. subst r.
        destruct (Hrows p Hp) as [Hlp [Hup Hbp]].
        destruct (Hrows q Hq) as [Hlq [Huq Hbq]].
        apply poly_add_rows_multiplier_bits; try assumption. now rewrite poly_size_opp.
  Qed.

  (** The right-hand side fits the declared row width. *)
  Lemma poly_row_rhs_bits : forall r, Z.size_nat (rhs r) <= C.row_bits r.
  Proof.
    intro r. unfold C.row_bits. apply poly_max_base.
  Qed.

  (** Every stored key fits the row's declared key width. *)
  Lemma poly_row_key_member : forall r p, In p (lhs r) ->
    Pos.size_nat (X.encode (fst p)) <= C.row_key_bits r.
  Proof.
    intros r p Hin. unfold C.row_key_bits.
    exact (poly_max_member _ (fun p => Pos.size_nat (X.encode (fst p))) 0 (lhs r) p Hin).
  Qed.

  (** Normalization preserves the width bound of a row with unique keys. *)
  Lemma poly_normal_row_bits : forall r,
    NoDup (map fst (lhs r)) -> C.row_bits (poly_normal_row X.encode r) <= C.row_bits r.
  Proof.
    intros r Hunique. unfold C.row_bits at 1. cbn [poly_normal_row lhs rhs].
    apply poly_max_bound; [apply poly_row_rhs_bits|].
    apply Forall_forall. intros [x a] Hin. cbn [snd].
    pose proof (poly_coef_member x a (poly_normal_coef X.encode (lhs r))
      (poly_normal_coef_nodup _ _ _) Hin) as Hcoef.
    rewrite coef_of_normal in Hcoef. rewrite <- Hcoef, coef_of_poly_coefficient.
    now apply poly_row_coefficient_bits.
  Qed.

  (** Normalization retains only input keys and therefore does not increase key width. *)
  Lemma poly_normal_row_key_bits : forall r,
    C.row_key_bits (poly_normal_row X.encode r) <= C.row_key_bits r.
  Proof.
    intro r. unfold C.row_key_bits at 1. cbn [poly_normal_row lhs].
    apply poly_max_bound; [lia|]. apply Forall_forall. intros p Hin.
    pose proof (poly_normal_coef_keys _ _ _ _ Hin) as Hkey.
    apply in_map_iff in Hkey as [q [Heq Hq]]. rewrite <- Heq.
    now apply poly_row_key_member.
  Qed.

  (** Combining equally bounded coefficients uses at most twice the width and one carry bit. *)
  Lemma poly_weighted_value_bits : forall a b u v bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat u <= bits -> Z.size_nat v <= bits ->
    Z.size_nat (a * u + b * v) <= 2 * bits + 1.
  Proof.
    intros a b u v bits Ha Hb Hu Hv.
    pose proof (poly_size_mul a u) as Hleft.
    pose proof (poly_size_mul b v) as Hright.
    pose proof (poly_size_add (a * u) (b * v)) as Hsum. lia.
  Qed.

  (** A normalized weighted row bounds every coefficient and its right-hand side. *)
  Lemma poly_add_rows_bits : forall a p b q bits,
    NoDup (map fst (lhs (poly_constraint p))) ->
    NoDup (map fst (lhs (poly_constraint q))) ->
    C.row_bits (poly_constraint p) <= bits -> C.row_bits (poly_constraint q) <= bits ->
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    C.row_bits (poly_constraint (poly_add_rows X.encode a p b q)) <= 2 * bits + 1.
  Proof.
    intros a p b q bits Hnp Hnq Hp Hq Ha Hb.
    unfold C.row_bits at 1. cbn [poly_add_rows poly_constraint lhs rhs].
    apply poly_max_bound.
    - apply poly_weighted_value_bits; try assumption.
      + eapply Nat.le_trans; [apply poly_row_rhs_bits|exact Hp].
      + eapply Nat.le_trans; [apply poly_row_rhs_bits|exact Hq].
    - apply Forall_forall. intros [x z] Hin. cbn [snd].
      pose proof (poly_coef_member x z
        (poly_normal_coef X.encode (poly_scale_coef a (lhs (poly_constraint p)) ++
          poly_scale_coef b (lhs (poly_constraint q))))
        (poly_normal_coef_nodup _ _ _) Hin) as Hcoef.
      rewrite coef_of_normal, coef_of_app, !coef_of_scale in Hcoef. rewrite <- Hcoef.
      apply poly_weighted_value_bits; try assumption.
      + rewrite coef_of_poly_coefficient. eapply Nat.le_trans;
          [apply poly_row_coefficient_bits; exact Hnp|exact Hp].
      + rewrite coef_of_poly_coefficient. eapply Nat.le_trans;
          [apply poly_row_coefficient_bits; exact Hnq|exact Hq].
  Qed.

  (** A normalized weighted row introduces no key beyond either input row. *)
  Lemma poly_add_rows_key_bits : forall a p b q keys,
    C.row_key_bits (poly_constraint p) <= keys ->
    C.row_key_bits (poly_constraint q) <= keys ->
    C.row_key_bits (poly_constraint (poly_add_rows X.encode a p b q)) <= keys.
  Proof.
    intros a p b q keys Hp Hq. unfold C.row_key_bits at 1.
    cbn [poly_add_rows poly_constraint lhs]. apply poly_max_bound; [lia|].
    apply Forall_forall. intros r Hin.
    pose proof (poly_normal_coef_keys _ _ _ _ Hin) as Hkey.
    unfold poly_scale_coef in Hkey. rewrite map_app, !map_map in Hkey.
    cbn [fst] in Hkey. apply in_app_or in Hkey as [Hkey|Hkey].
    - apply in_map_iff in Hkey as [s [Heq Hs]]. rewrite <- Heq.
      eapply Nat.le_trans; [apply poly_row_key_member; exact Hs|exact Hp].
    - apply in_map_iff in Hkey as [s [Heq Hs]]. rewrite <- Heq.
      eapply Nat.le_trans; [apply poly_row_key_member; exact Hs|exact Hq].
  Qed.

  (** Equality cancellation respects the same arithmetic and key-width envelopes. *)
  Lemma poly_cancel_sizes : forall x p r bits keys,
    NoDup (map fst (lhs (poly_constraint p))) ->
    NoDup (map fst (lhs (poly_constraint r))) ->
    C.row_bits (poly_constraint p) <= bits -> C.row_bits (poly_constraint r) <= bits ->
    C.row_key_bits (poly_constraint p) <= keys ->
    C.row_key_bits (poly_constraint r) <= keys ->
    C.row_bits (poly_constraint (poly_cancel X.encode X.eqb x p r)) <= 2 * bits + 1 /\
      C.row_key_bits (poly_constraint (poly_cancel X.encode X.eqb x p r)) <= keys.
  Proof.
    intros x p r bits keys Hnp Hnr Hp Hr Hkp Hkr. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0).
    - split; lia.
    - split.
      + apply poly_add_rows_bits; try assumption.
        * eapply Nat.le_trans; [apply poly_size_sign_mul|].
          eapply Nat.le_trans; [apply poly_row_coefficient_bits; exact Hnr|exact Hr].
        * rewrite poly_size_abs. eapply Nat.le_trans;
            [apply poly_row_coefficient_bits; exact Hnp|exact Hp].
      + apply poly_add_rows_key_bits; assumption.
  Qed.

  (** A single elimination step satisfies the coefficient and key-width recurrence. *)
  Lemma poly_step_sizes : forall x rows bits keys,
    Forall (fun r => NoDup (map fst (lhs (poly_constraint r))) /\
      C.row_bits (poly_constraint r) <= bits /\
      C.row_key_bits (poly_constraint r) <= keys) rows ->
    Forall (fun r => C.row_bits (poly_constraint r) <= 2 * bits + 1 /\
      C.row_key_bits (poly_constraint r) <= keys) (poly_step X.encode X.eqb x rows).
  Proof.
    intros x rows bits keys Hrows. rewrite Forall_forall in Hrows.
    unfold poly_step. destruct (find (poly_pivot X.eqb x) rows) as [pivot|] eqn:Hpivot.
    - apply find_some in Hpivot as [Hpivot _].
      destruct (Hrows pivot Hpivot) as [Hnp [Hp Hkp]].
      apply Forall_map, Forall_forall. intros r Hin.
      destruct (Hrows r Hin) as [Hnr [Hr Hkr]]. apply poly_cancel_sizes; assumption.
    - apply Forall_app. split.
      + apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
        destruct (Hrows r Hin) as [Hnr [Hr Hkr]]. split; lia.
      + apply Forall_forall. intros r Hin. apply in_flat_map in Hin as [p [Hp Hin]].
        apply filter_In in Hp as [Hp _]. apply in_map_iff in Hin as [q [Heq Hq]].
        apply filter_In in Hq as [Hq _]. subst r.
        destruct (Hrows p Hp) as [Hnp [Hbp Hkp]].
        destruct (Hrows q Hq) as [Hnq [Hbq Hkq]]. split.
        * apply poly_add_rows_bits; try assumption.
          -- rewrite poly_size_opp. eapply Nat.le_trans;
               [apply poly_row_coefficient_bits; exact Hnq|exact Hbq].
          -- eapply Nat.le_trans; [apply poly_row_coefficient_bits; exact Hnp|exact Hbp].
        * apply poly_add_rows_key_bits; assumption.
  Qed.

  (** Initial normalization fits the maximum widths of normal input rows. *)
  Lemma poly_initial_sizes : forall P, normal P ->
    Forall (fun r => NoDup (map fst (lhs (poly_constraint r))) /\
      C.row_bits (poly_constraint r) <= fold_right Nat.max 0 (map C.row_bits P) /\
      C.row_key_bits (poly_constraint r) <= fold_right Nat.max 0 (map C.row_key_bits P))
      (poly_initial X.encode (map (fun p => (p, false)) P)).
  Proof.
    intros P Hnormal. apply Forall_forall. intros r Hin.
    destruct (poly_initial_source P r Hin) as [p [Hp Hrow]]. rewrite Hrow.
    assert (Hnp : NoDup (map fst (lhs p))).
    { unfold normal in Hnormal. exact (proj1 (Forall_forall _ _) Hnormal p Hp). }
    split; [apply poly_normal_coef_nodup|]. split.
    - eapply Nat.le_trans; [apply poly_normal_row_bits; exact Hnp|].
      exact (poly_max_member _ C.row_bits 0 P p Hp).
    - eapply Nat.le_trans; [apply poly_normal_row_key_bits|].
      exact (poly_max_member _ C.row_key_bits 0 P p Hp).
  Qed.

  (** Normalization cannot retain more coefficients than it receives. *)
  Lemma poly_normal_length : forall xs,
    length (poly_normal_coef X.encode xs) <= length xs.
  Proof.
    intro xs. rewrite <- (length_map fst (poly_normal_coef X.encode xs)),
      <- (length_map fst xs). apply NoDup_incl_length; [apply poly_normal_coef_nodup|].
    intros x Hin. apply in_map_iff in Hin as [p [Heq Hin]]. subst x.
    exact (poly_normal_coef_keys _ X.encode xs p Hin).
  Qed.

  (** Inserting a possibly new variable preserves old members and includes that variable. *)
  Lemma poly_var_insert_contains : forall acc x y,
    In y acc \/ y = x ->
    In y (if existsb (X.eqb x) acc then acc else x :: acc).
  Proof.
    intros acc x y Hin. destruct (existsb (X.eqb x) acc) eqn:Hpresent.
    - destruct Hin as [Hin|Heq]; [exact Hin|]. subst y.
      apply existsb_exists in Hpresent as [z [Hz Heq]].
      destruct (X.eqb_spec x z) as [Hequal|Hneq]; [now subst z|discriminate].
    - destruct Hin as [Hin|Heq]; [right; exact Hin|left; congruence].
  Qed.

  (** The variable collection fold contains its input and its initial accumulator. *)
  Lemma poly_vars_fold_contains : forall xs acc x,
    In x acc \/ In x xs ->
    In x (fold_left (fun acc y => if existsb (X.eqb y) acc then acc else y :: acc) xs acc).
  Proof.
    intro xs. induction xs as [|y xs IH]; intros acc x Hin; cbn [fold_left].
    - destruct Hin as [Hin|Hin]; [exact Hin|contradiction].
    - apply IH. destruct Hin as [Hin|[Heq|Hin]].
      + left. apply poly_var_insert_contains. now left.
      + left. apply poly_var_insert_contains. right. congruence.
      + now right.
  Qed.

  (** The declared variable list contains every variable of every input row. *)
  Lemma poly_vars_of_contains : forall P r x,
    In r P -> In x (map fst (lhs r)) -> In x (vars_of P).
  Proof.
    intros P r x Hr Hx. unfold vars_of. apply poly_vars_fold_contains. right.
    apply in_flat_map. exists r. auto.
  Qed.

  (** A normal row has at most the declared number of distinct input variables. *)
  Lemma poly_row_dimension : forall P r, normal P -> In r P ->
    length (lhs r) <= length (vars_of P).
  Proof.
    intros P r Hnormal Hr. rewrite <- (length_map fst (lhs r)).
    apply NoDup_incl_length.
    - unfold normal in Hnormal. exact (proj1 (Forall_forall _ _) Hnormal r Hr).
    - intros x Hx. now apply poly_vars_of_contains with (r := r).
  Qed.

  (** The normalized initial rows fit the input variable dimension. *)
  Lemma poly_initial_dimension : forall P r, normal P ->
    In r (poly_initial X.encode (map (fun p => (p, false)) P)) ->
    length (lhs (poly_constraint r)) <= length (vars_of P).
  Proof.
    intros P r Hnormal Hin. destruct (poly_initial_source P r Hin) as [p [Hp Hrow]].
    rewrite Hrow. cbn [poly_normal_row lhs].
    eapply Nat.le_trans; [apply poly_normal_length|]. now apply poly_row_dimension.
  Qed.

  (** A missing accumulator binding contributes zero to the next addition. *)
  Definition poly_previous (m : ptrie (X.t * Z)) (x : X.t) : Z :=
    match PTrieCode.get (X.encode x) m with Some p => snd p | None => 0%Z end.

  (** Updating a different source key leaves a future addition's old value unchanged. *)
  Lemma poly_previous_other : forall m p x, x <> fst p ->
    poly_previous (poly_add_term X.encode m p) x = poly_previous m x.
  Proof.
    intros m p x Hneq. unfold poly_previous, poly_add_term.
    rewrite PTrie.get_set_other; [reflexivity|].
    intro Heq. apply Hneq. now apply X.encode_inj.
  Qed.

  (** A nonzero accumulator binding is retained by coefficient normalization. *)
  Lemma poly_normal_lookup_member : forall xs key q,
    PTrieCode.get key (fold_left (poly_add_term X.encode) xs PTrieCode.empty) = Some q ->
    snd q <> 0%Z -> In q (poly_normal_coef X.encode xs).
  Proof.
    intros xs key q Hget Hnonzero. unfold poly_normal_coef.
    rewrite PTrieT.F9_fold_values.
    rewrite (poly_fold_values_list _ _
      (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) _ nil).
    rewrite poly_fold_normalized, app_nil_r. apply (proj1 (in_rev _ _)).
    apply filter_In. split.
    - apply in_map_iff. exists (key, q). split; [reflexivity|].
      apply (proj2 (PTrie.elements_spec _ _ _ _)). exact Hget.
    - apply Bool.negb_true_iff, Z.eqb_neq. exact Hnonzero.
  Qed.

  (** Accumulating a unique coefficient list preserves its uniform coefficient width. *)
  Lemma poly_unique_accum_bits : forall xs bits,
    NoDup (map fst xs) -> Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    forall key q,
      PTrieCode.get key (fold_left (poly_add_term X.encode) xs PTrieCode.empty) = Some q ->
      Z.size_nat (snd q) <= bits.
  Proof.
    intros xs bits Hunique Hbits key [x a] Hget. cbn [snd].
    destruct (Z.eq_dec a 0) as [Hzero|Hnonzero]; [subst a; change (0 <= bits); lia|].
    pose proof (poly_normal_lookup_member xs key (x, a) Hget Hnonzero) as Hin.
    pose proof (poly_coef_member x a _ (poly_normal_coef_nodup _ _ _) Hin) as Hcoef.
    rewrite coef_of_normal in Hcoef. rewrite <- Hcoef. now apply poly_coef_bits.
  Qed.

  (** Allocated trie nodes are charged once to the inserted key lengths. *)
  Lemma poly_accum_nodes : forall xs m keys,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs ->
    PTrie.nodes (fold_left (poly_add_term X.encode) xs m) <=
      PTrie.nodes m + length xs * keys.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys Hkeys; cbn [fold_left length].
    - lia.
    - inversion Hkeys as [|q qs Hp Htail]; subst q qs.
      specialize (IH (poly_add_term X.encode m p) keys Htail).
      pose proof (PTrie.nodes_set _ (X.encode (fst p))
        (fst p, (poly_previous m (fst p) + snd p)%Z) m) as Hset.
      change (PTrie.nodes (poly_add_term X.encode m p) <=
        PTrie.nodes m + Pos.size_nat (X.encode (fst p))) in Hset.
      nia.
  Qed.

  (** The per-term clock charges encoding, two trie paths, and one bounded addition. *)
  Definition poly_add_factor : N := (X.c_key + 2 * PTrieT.c_trie + 24)%N.

  (** Accumulating a term pays for its key and both summand widths. *)
  Lemma T_poly_add_term_bounded : forall m p keys bits old,
    Pos.size_nat (X.encode (fst p)) <= keys -> Z.size_nat (snd p) <= bits ->
    Z.size_nat (poly_previous m (fst p)) <= old ->
    (T_poly_add_term X.encode X.T_encode m p <=
      poly_add_factor * N.of_nat (keys + bits + old + 1))%N.
  Proof.
    intros m p keys bits old Hkey Hbits Hold.
    pose proof (X.T_encode_le (fst p)) as Hencode.
    pose proof (PTrieT.T_get_le (X.t * Z) (X.encode (fst p)) m) as Hget.
    pose proof (PTrieT.T_set_le (X.t * Z) (X.encode (fst p))
      (fst p, (poly_previous m (fst p) + snd p)%Z) m) as Hput.
    pose proof (Z.T_add_le (poly_previous m (fst p)) (snd p)) as Hadd.
    assert (Hbranch : (match PTrieCode.get (X.encode (fst p)) m with
      | Some _ => 1 | None => 0 end <= 1)%N).
    { destruct (PTrieCode.get (X.encode (fst p)) m); lia. }
    time_unfold (@T_poly_add_term). fold (poly_previous m (fst p)).
    unfold poly_add_factor, X.bits in *. time_simpl. nia.
  Qed.

  (** Unique remaining keys keep the same old-value bound throughout accumulation. *)
  Lemma T_poly_accum_unique : forall xs m keys bits old,
    NoDup (map fst xs) ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (forall p, In p xs -> Z.size_nat (poly_previous m (fst p)) <= old) ->
    (List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
      xs m <= (poly_add_factor + 1) * N.of_nat (length xs) *
        N.of_nat (keys + bits + old + 1) + 1)%N.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys bits old Hunique Hsizes Hprevious.
    - time_unfold List.T_fold_left. cbn [length]. nia.
    - inversion Hunique as [|key rest Hnot Hunique_tail]; subst key rest.
      inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      assert (Hfuture : forall q, In q xs ->
        Z.size_nat (poly_previous (poly_add_term X.encode m p) (fst q)) <= old).
      { intros q Hq. rewrite poly_previous_other.
        - apply Hprevious. now right.
        - intro Heq. apply Hnot. rewrite <- Heq. now apply in_map. }
      specialize (IH _ _ _ _ Hunique_tail Htail Hfuture).
      pose proof (T_poly_add_term_bounded m p keys bits old Hkey Hbits
        (Hprevious p (or_introl eq_refl))) as Hhead.
      time_unfold List.T_fold_left. cbn [length]. time_simpl. nia.
  Qed.

  (** Splitting an accumulation list adds only its two traversal clocks. *)
  Lemma T_poly_accum_app : forall xs ys m,
    (List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
      (xs ++ ys) m <=
      List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode) xs m +
      List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode) ys
        (fold_left (poly_add_term X.encode) xs m))%N.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros ys m;
      cbn [app fold_left]; time_unfold List.T_fold_left; [lia|].
    specialize (IH ys (poly_add_term X.encode m p)).
    change (1 + (T_poly_add_term X.encode X.T_encode m p +
      List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
        (xs ++ ys) (poly_add_term X.encode m p)) <=
      1 + (T_poly_add_term X.encode X.T_encode m p +
        List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
          xs (poly_add_term X.encode m p)) +
      List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
        ys (fold_left (poly_add_term X.encode) xs (poly_add_term X.encode m p)))%N.
    rewrite <- !N.add_assoc. apply N.add_le_mono_l, N.add_le_mono_l. exact IH.
  Qed.

  (** The normalization callback only discards an exact zero coefficient. *)
  Definition poly_normal_keep (acc : list (X.t * Z)) (p : X.t * Z) : list (X.t * Z) :=
    if Z.eqb (snd p) 0 then acc else p :: acc.

  TimeFun poly_normal_keep.

  (** Comparing any integer with zero needs no traversal of its magnitude. *)
  Lemma T_poly_zero_test : forall z, (Z.T_eqb z 0 <= 2)%N.
  Proof.
    intros [|p|p]; time_unfold Z.T_eqb; time_simpl; lia.
  Qed.

  (** Filtering a stored zero has constant callback cost. *)
  Lemma T_poly_normal_keep_le : forall acc p, (T_poly_normal_keep acc p <= 5)%N.
  Proof.
    intros acc p. pose proof (T_poly_zero_test (snd p)).
    time_unfold T_poly_normal_keep. time_simpl. nia.
  Qed.

  (** Two unique lists need at most two summand widths at each shared key. *)
  Lemma T_poly_accum_pair : forall xs ys keys bits,
    NoDup (map fst xs) -> NoDup (map fst ys) ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) ys ->
    (List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
      (xs ++ ys) PTrieCode.empty <=
      2 * (poly_add_factor + 1) * N.of_nat (length xs + length ys + 1) *
        N.of_nat (keys + bits + 1))%N.
  Proof.
    intros xs ys keys bits Hnx Hny Hxs Hys.
    assert (Hzero : forall p, In p xs ->
      Z.size_nat (poly_previous PTrieCode.empty (fst p)) <= 0).
    { intros p Hin. unfold poly_previous. rewrite PTrie.get_empty. reflexivity. }
    pose proof (T_poly_accum_unique xs PTrieCode.empty keys bits 0 Hnx Hxs Hzero) as Hleft.
    assert (Hvalues : Forall (fun p => Z.size_nat (snd p) <= bits) xs).
    { eapply Forall_impl; [|exact Hxs]. intros p [_ Hp]. exact Hp. }
    assert (Hprevious : forall p, In p ys -> Z.size_nat
      (poly_previous (fold_left (poly_add_term X.encode) xs PTrieCode.empty) (fst p)) <= bits).
    { intros p Hin. unfold poly_previous.
      destruct (PTrieCode.get (X.encode (fst p))
        (fold_left (poly_add_term X.encode) xs PTrieCode.empty)) as [q|] eqn:Hget.
      - exact (poly_unique_accum_bits xs bits Hnx Hvalues _ q Hget).
      - change (0 <= bits). lia. }
    pose proof (T_poly_accum_unique ys _ keys bits bits Hny Hys Hprevious) as Hright.
    pose proof (T_poly_accum_app xs ys PTrieCode.empty) as Hsplit.
    assert (Hmass : (1 <= N.of_nat (keys + bits + 1))%N) by lia.
    assert (Htwice : (N.of_nat (keys + bits + bits + 1) <=
      2 * N.of_nat (keys + bits + 1))%N) by lia.
    rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Normalization adds a linear value traversal to the two accumulation passes. *)
  Definition poly_normal_factor : N :=
    (2 * (poly_add_factor + 1) + 6 * PTrieT.k_fold + 8)%N.

  (** Normalizing two normal lists is linear in their entries and key/coefficient widths. *)
  Lemma T_poly_normal_pair : forall xs ys keys bits,
    NoDup (map fst xs) -> NoDup (map fst ys) ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) ys ->
    (T_poly_normal_coef X.encode X.T_encode (xs ++ ys) <=
      poly_normal_factor * N.of_nat (length xs + length ys + 1) *
        N.of_nat (keys + bits + 1))%N.
  Proof.
    intros xs ys keys bits Hnx Hny Hxs Hys.
    pose proof (T_poly_accum_pair xs ys keys bits Hnx Hny Hxs Hys) as Haccum.
    set (tr := fold_left (poly_add_term X.encode) (xs ++ ys) PTrieCode.empty).
    assert (Hkeys : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) (xs ++ ys)).
    { apply Forall_app. split.
      - eapply Forall_impl; [|exact Hxs]. intros p [Hp _]. exact Hp.
      - eapply Forall_impl; [|exact Hys]. intros p [Hp _]. exact Hp. }
    pose proof (poly_accum_nodes (xs ++ ys) PTrieCode.empty keys Hkeys) as Hnodes.
    change (PTrie.nodes tr <= length (xs ++ ys) * keys) in Hnodes.
    rewrite length_app in Hnodes.
    pose proof (PTrieT.T9_fold_values (X.t * Z) (list (X.t * Z))
      poly_normal_keep T_poly_normal_keep tr nil 5 T_poly_normal_keep_le) as Hfold.
    time_unfold (@T_poly_normal_coef). fold tr.
    change (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) with poly_normal_keep.
    unfold poly_normal_factor. time_simpl.
    change (fun (acc : PTrieCode.t (X.t * Z)) (p : X.t * Z) =>
      T_poly_add_term X.encode X.T_encode acc p) with
      (T_poly_add_term X.encode X.T_encode).
    change (fun (_ : list (X.t * Z)) (p : X.t * Z) =>
      (1 + (1 + Z.T_eqb (snd p) 0))%N) with T_poly_normal_keep.
    nia.
  Qed.

  (** A single unique list is the empty-right-list instance of the normalization bound. *)
  Lemma T_poly_normal_unique : forall xs keys bits,
    NoDup (map fst xs) ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (T_poly_normal_coef X.encode X.T_encode xs <=
      poly_normal_factor * N.of_nat (length xs + 1) * N.of_nat (keys + bits + 1))%N.
  Proof.
    intros xs keys bits Hunique Hsizes.
    pose proof (T_poly_normal_pair xs nil keys bits Hunique ltac:(constructor) Hsizes
      ltac:(constructor)) as Htime. rewrite app_nil_r in Htime. cbn [length] in Htime.
    now rewrite Nat.add_0_r in Htime.
  Qed.

  Definition prows (s : t) : list (lcons X.t) :=
    match s with Unreached => nil | Reached P => P end.
  Definition wunits (_ : t) : nat := 0.
  Definition terms (s : t) : nat :=
    fold_right Nat.add 0 (map (fun r => length (lhs r)) (prows s)).
  Definition nell (s : t) : nat := ell (prows s) + Nat.log2 (terms s) + 1.
  Definition mu (s : t) : nat := terms s + n (prows s) + nell s.
  Definition lat (m : nat) : nat :=
    2 * (m + 1) * (fmcost m (m + 1) m (m + 1) (m + 1) + m^2 + 1).
  Definition size (s : t) : nat := lat (2 * mu s).
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      (length (prows s) + 3)^2 *
      (n (prows s) + terms s + tsize e + length (prows s) + 3) *
      (nell s + X.bits x + F.bits_e e + 1)^2 + N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      (length (prows s) + 1)^2 * (n (prows s) + terms s + length (prows s) + 1) *
      (nell s + X.bits x + 1)^2.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    (length (prows s) + 1) * (length (F.atoms_of g es) + 1) *
      (fold_right Nat.add 0%nat (map tsize es) + 1) *
      (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1) +
      N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      fmcost (n (prows s) + tsize e) (length (prows s) + 2) (n (prows s) + tsize e)
        (length (prows s) + 2) (nell s + F.bits_e e + 1) + N.to_nat (F.T_lin_of e).
  Definition range_bits (e : term L.op X.t) (s : t) : nat := range_work e s.
  TimeFun subst.
  TimeFun fm_elim.
  TimeFun poly_normal_rows.
  TimeFun poly_source_equal.
  TimeFun poly_canonical_scale.
  TimeFun poly_canonical_guard.
  TimeFun candidate.
  TimeFun find_certificate.
  TimeFun entail_engine.
  TimeFun entail_cert.
  TimeFun entails_row.
  TimeFun keep_row.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun checked_projection.
  TimeFun havoc.
  TimeFun tmp_encode.
  TimeFun tmp_eqb.
  TimeFun rename_old.
  TimeFun rename_row.
  TimeFun untag.
  TimeFun assignment_row.
  TimeFun assigned_candidate.
  TimeFun assign_linear.
  TimeFun assign.
  TimeFun atom_row.
  TimeFun assume.
  TimeFun range_row.
  TimeFun range_update.
  TimeFun range_candidate.
  TimeFun range_linear.
  TimeFun range.
  (** The number of set bits pays for carry chains in nonnegative accumulation. *)
  Fixpoint poly_mul_ones_count (p : positive) : N :=
    match p with
    | xI q => (poly_mul_ones_count q + 1)%N
    | xO q => poly_mul_ones_count q
    | xH => 1%N
    end.

  (** A positive integer has no more set bits than binary digits. *)
  Lemma poly_mul_ones_count_le : forall p, (poly_mul_ones_count p <= N.of_nat (Pos.size_nat p))%N.
  Proof.
    induction p as [p IH|p IH|]; time_cbn; lia.
  Qed.

  (** A successor pays for every carry by removing set bits. *)
  Lemma poly_T_succ_ones : forall p,
    (Pos.T_succ p + poly_mul_ones_count (Pos.succ p) <= poly_mul_ones_count p + 2)%N.
  Proof.
    induction p as [p IH|p IH|]; time_unfold Pos.T_succ; time_cbn; lia.
  Qed.

  (** Addition charges the first operand's digits and the change of set-bit potential. *)
  Lemma poly_T_add_ones_both : forall p q,
    (Pos.T_add p q + poly_mul_ones_count (Pos.add p q) <=
      3 * N.of_nat (Pos.size_nat p) + poly_mul_ones_count q + 3)%N /\
    (Pos.T_add_carry p q + poly_mul_ones_count (Pos.add_carry p q) <=
      3 * N.of_nat (Pos.size_nat p) + poly_mul_ones_count q + 3)%N.
  Proof.
    intro p. induction p as [p IH|p IH|]; intros [q|q|];
      time_unfold Pos.T_add; time_unfold Pos.T_add_carry; time_cbn;
      try specialize (IH q);
      try pose proof (poly_T_succ_ones p); try pose proof (poly_T_succ_ones q);
      try pose proof (poly_mul_ones_count_le p); try pose proof (poly_mul_ones_count_le q); lia.
  Qed.

  (** Shift-and-add multiplication amortizes its internal carry chains. *)
  Lemma poly_T_mul_ones : forall p q,
    (Pos.T_mul p q + poly_mul_ones_count (Pos.mul p q) <=
      6 * N.of_nat (Pos.size_nat p) * (N.of_nat (Pos.size_nat q) + 1) + poly_mul_ones_count q)%N.
  Proof.
    intro p. induction p as [p IH|p IH|]; intro q;
      time_unfold Pos.T_mul; time_cbn; try specialize (IH q).
    - pose proof (proj1 (poly_T_add_ones_both q (xO (Pos.mul p q)))) as Hadd.
      time_cbn_all. nia.
    - nia.
    - nia.
  Qed.

  (** Positive multiplication is bilinear in operand bit lengths. *)
  Lemma poly_T_pos_mul_bilinear : forall p q,
    (Pos.T_mul p q <=
      7 * N.of_nat (Pos.size_nat p) * (N.of_nat (Pos.size_nat q) + 1))%N.
  Proof.
    intros p q. pose proof (poly_T_mul_ones p q) as Hmul.
    pose proof (poly_mul_ones_count_le q) as Hones.
    pose proof (Pos.size_nat_pos p) as Hpositive. nia.
  Qed.

  (** Signed multiplication has the same bilinear bound with its sign dispatch. *)
  Lemma poly_T_Z_mul_bilinear : forall x y,
    (Z.T_mul x y <=
      8 * N.of_nat (Z.size_nat x + 1) * N.of_nat (Z.size_nat y + 1))%N.
  Proof.
    intros [|p|p] [|q|q]; time_unfold Z.T_mul; time_cbn;
      try pose proof (poly_T_pos_mul_bilinear p q); nia.
  Qed.

  (** Every stored accumulator coefficient fits one common bit budget. *)
  Definition poly_accum_values_bits (m : ptrie (X.t * Z)) (bits : nat) : Prop :=
    forall key p, PTrieCode.get key m = Some p -> Z.size_nat (snd p) <= bits.

  (** A lookup in a bounded accumulator has the same coefficient-width bound. *)
  Lemma poly_previous_bits : forall m bits x,
    poly_accum_values_bits m bits -> Z.size_nat (poly_previous m x) <= bits.
  Proof.
    intros m bits x Hbits. unfold poly_previous.
    destruct (PTrieCode.get (X.encode x) m) as [p|] eqn:Hget.
    - exact (Hbits _ p Hget).
    - change (0 <= bits). lia.
  Qed.

  (** One raw insertion needs at most one extra bit beyond a shared input bound. *)
  Lemma poly_add_term_values_bits : forall m p bits,
    poly_accum_values_bits m bits -> Z.size_nat (snd p) <= bits ->
    poly_accum_values_bits (poly_add_term X.encode m p) (bits + 1).
  Proof.
    intros m p bits Hvalues Hp key q Hget.
    change (PTrieCode.get key (PTrieCode.set (X.encode (fst p))
      (fst p, (poly_previous m (fst p) + snd p)%Z) m) = Some q) in Hget.
    destruct (Pos.eq_dec key (X.encode (fst p))) as [Heq|Hneq].
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Hsame. subst q.
      cbn [snd]. pose proof (poly_size_add (poly_previous m (fst p)) (snd p)).
      pose proof (poly_previous_bits m bits (fst p) Hvalues). lia.
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      pose proof (Hvalues key q Hget). lia.
  Qed.

  (** Raw accumulation grows its uniform coefficient budget by at most one per occurrence. *)
  Lemma poly_accum_raw_bits : forall xs m bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    poly_accum_values_bits m bits ->
    poly_accum_values_bits (fold_left (poly_add_term X.encode) xs m) (bits + length xs).
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m bits Hsizes Hvalues;
      cbn [fold_left length].
    - now rewrite Nat.add_0_r.
    - inversion Hsizes as [|q qs Hp Htail]; subst q qs.
      replace (bits + S (length xs)) with (bits + 1 + length xs) by lia.
      apply (IH (poly_add_term X.encode m p) (bits + 1)).
      + eapply Forall_impl; [|exact Htail]. intros q Hq. cbn in Hq. lia.
      + now apply poly_add_term_values_bits.
  Qed.

  (** The remaining traversal length pays for the increasing partial-sum widths. *)
  Lemma T_poly_accum_raw : forall xs m keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs -> poly_accum_values_bits m bits ->
    (List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
      xs m <= (poly_add_factor + 1) * N.of_nat (length xs) *
        N.of_nat (keys + 2 * bits + 2 * length xs + 1) + 1)%N.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys bits Hsizes Hvalues.
    - time_unfold List.T_fold_left. cbn [length]. nia.
    - inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      assert (Hnext : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
        Z.size_nat (snd p) <= bits + 1) xs).
      { eapply Forall_impl; [|exact Htail]. intros q [Hqkey Hqbits]. split; lia. }
      pose proof (poly_add_term_values_bits m p bits Hvalues Hbits) as Hnewvalues.
      specialize (IH (poly_add_term X.encode m p) keys (bits + 1) Hnext Hnewvalues).
      pose proof (T_poly_add_term_bounded m p keys bits bits Hkey Hbits
        (poly_previous_bits m bits (fst p) Hvalues)) as Hhead.
      time_unfold List.T_fold_left. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  Definition poly_raw_normal_factor : N :=
    (4 * (poly_add_factor + 1) + 6 * PTrieT.k_fold + 16)%N.

  (** Raw normalization is quadratic in the input length and linear in its initial widths. *)
  Lemma T_poly_normal_raw : forall xs keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (T_poly_normal_coef X.encode X.T_encode xs <=
      poly_raw_normal_factor * N.of_nat (length xs + 1) *
        N.of_nat (keys + 2 * bits + 2 * length xs + 1))%N.
  Proof.
    intros xs keys bits Hsizes.
    assert (Hempty : poly_accum_values_bits PTrieCode.empty bits).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (T_poly_accum_raw xs PTrieCode.empty keys bits Hsizes Hempty) as Haccum.
    set (tr := fold_left (poly_add_term X.encode) xs PTrieCode.empty).
    assert (Hkeys : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs).
    { eapply Forall_impl; [|exact Hsizes]. intros p [Hp _]. exact Hp. }
    pose proof (poly_accum_nodes xs PTrieCode.empty keys Hkeys) as Hnodes.
    change (PTrie.nodes tr <= length xs * keys) in Hnodes.
    pose proof (PTrieT.T9_fold_values (X.t * Z) (list (X.t * Z))
      poly_normal_keep T_poly_normal_keep tr nil 5 T_poly_normal_keep_le) as Hfold.
    time_unfold (@T_poly_normal_coef). fold tr.
    change (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) with poly_normal_keep.
    unfold poly_raw_normal_factor. time_simpl.
    change (fun (acc : PTrieCode.t (X.t * Z)) (p : X.t * Z) =>
      T_poly_add_term X.encode X.T_encode acc p) with
      (T_poly_add_term X.encode X.T_encode).
    change (fun (_ : list (X.t * Z)) (p : X.t * Z) =>
      (1 + (1 + Z.T_eqb (snd p) 0))%N) with T_poly_normal_keep.
    nia.
  Qed.

  (** A raw repeated-key coefficient gains at most one bit per additional occurrence. *)
  Lemma poly_raw_coefficient_bits : forall x xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Z.size_nat (C.coef_of x xs) <= length xs + bits.
  Proof.
    intros x xs. induction xs as [|[y a] xs IH]; intros bits Hsizes.
    - change (0 <= 0 + bits). lia.
    - inversion Hsizes as [|p ps Ha Htail]; subst p ps.
      rewrite coef_of_cons. cbn [length]. destruct (X.eqb x y).
      + pose proof (poly_size_add a (C.coef_of x xs)).
        specialize (IH bits Htail). cbn [snd] in Ha. lia.
      + specialize (IH bits Htail). lia.
  Qed.

  (** Callback bounds are needed only on list members actually visited by mapping. *)
  Lemma poly_T_map_members : forall (A B : Type) (f : A -> B) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (ListDef.T_map f T_f xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold ListDef.T_map. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)).
      time_unfold ListDef.T_map. time_cbn. nia.
  Qed.

  (** Filtering also needs callback bounds only on its actual input list. *)
  Lemma poly_T_filter_members : forall A (f : A -> bool) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (List.T_filter f T_f xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold List.T_filter. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)).
      time_unfold List.T_filter. destruct (f x); time_cbn; nia.
  Qed.

  (** Scaling has a bilinear multiplication charge for each original occurrence. *)
  Lemma T_poly_scale_coef_bounded : forall a (xs : list (X.t * Z)) bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    (T_poly_scale_coef a xs <=
      16 * N.of_nat ((length xs + 1) * (Z.size_nat a + 1) * (bits + 1)))%N.
  Proof.
    intros a xs bits Hbits. time_unfold (@T_poly_scale_coef).
    lazymatch goal with
    | |- context [ListDef.T_map ?f ?Tf xs] =>
      assert (Hmap : (ListDef.T_map f Tf xs <=
        (12 * N.of_nat ((Z.size_nat a + 1) * (bits + 1)) + 1) *
        N.of_nat (length xs) + 1)%N);
      [ apply poly_T_map_members; intros [x z] Hin;
        pose proof (proj1 (Forall_forall _ _) Hbits (x, z) Hin) as Hz;
        pose proof (poly_T_Z_mul_bilinear a z);
        time_simpl; time_cbn_all; nia
      | nia ]
    end.
  Qed.

  (** Coefficient lookup tests the stored key and adds its matching occurrence. *)
  Definition poly_coefficient_step (x : X.t) (p : X.t * Z) (z : Z) : Z :=
    if X.eqb (fst p) x then (snd p + z)%Z else z.

  TimeFun poly_coefficient_step.

  (** The executable lookup fold agrees with the public summed coefficient. *)
  Lemma poly_coefficient_step_fold : forall x xs,
    fold_right (poly_coefficient_step x) 0%Z xs = C.coef_of x xs.
  Proof.
    intros x xs.
    change (poly_coefficient X.eqb x (LCons X.t xs REq 0%Z) = C.coef_of x xs).
    symmetry. exact (coef_of_poly_coefficient x (LCons X.t xs REq 0%Z)).
  Qed.

  (** Lookup charges a key comparison, projections, and one binary addition. *)
  Definition poly_coefficient_factor : N := (X.c_key + 16)%N.

  (** One coefficient-fold step pays for both summand widths and the stored key. *)
  Lemma T_poly_coefficient_step_bounded : forall x p z keys bits old,
    Pos.size_nat (X.encode (fst p)) <= keys -> Z.size_nat (snd p) <= bits ->
    Z.size_nat z <= old ->
    (T_poly_coefficient_step x p z <=
      poly_coefficient_factor * N.of_nat (keys + bits + old + 1))%N.
  Proof.
    intros x p z keys bits old Hkeys Hbits Hold.
    pose proof (X.T_eqb_le (fst p) x) as Heqb.
    pose proof (Z.T_add_le (snd p) z) as Hadd.
    time_unfold T_poly_coefficient_step. unfold poly_coefficient_factor, X.bits in *.
    destruct (X.eqb (fst p) x); time_simpl; nia.
  Qed.

  (** Raw lookup charges each partial sum at the length of its remaining suffix. *)
  Lemma T_poly_coefficient_fold : forall x xs keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (List.T_fold_right (poly_coefficient_step x) (T_poly_coefficient_step x) 0%Z xs <=
      (poly_coefficient_factor + 1) * N.of_nat (length xs + 1) *
        N.of_nat (keys + 2 * bits + length xs + 1))%N.
  Proof.
    intros x xs. induction xs as [|p xs IH]; intros keys bits Hsizes.
    - time_unfold List.T_fold_right. cbn [length]. unfold poly_coefficient_factor. nia.
    - inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      specialize (IH keys bits Htail).
      assert (Htailbits : Forall (fun q => Z.size_nat (snd q) <= bits) xs).
      { eapply Forall_impl; [|exact Htail]. intros q [_ Hq]. exact Hq. }
      assert (Hsum : Z.size_nat (fold_right (poly_coefficient_step x) 0%Z xs) <=
        length xs + bits).
      { rewrite poly_coefficient_step_fold. now apply poly_raw_coefficient_bits. }
      pose proof (T_poly_coefficient_step_bounded x p
        (fold_right (poly_coefficient_step x) 0%Z xs)
        keys bits (length xs + bits) Hkey Hbits Hsum) as Hhead.
      time_unfold List.T_fold_right. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** A raw row lookup includes the growing partial sums in its traversal bound. *)
  Lemma T_poly_coefficient_bounded : forall x r keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) (lhs r) ->
    (T_poly_coefficient X.eqb X.T_eqb x r <=
      (poly_coefficient_factor + 4) * N.of_nat (length (lhs r) + 1) *
        N.of_nat (keys + 2 * bits + length (lhs r) + 1))%N.
  Proof.
    intros x r keys bits Hsizes.
    pose proof (T_poly_coefficient_fold x (lhs r) keys bits Hsizes) as Hfold.
    time_unfold (@T_poly_coefficient).
    change (fun p z => if X.eqb (fst p) x then (snd p + z)%Z else z)
      with (poly_coefficient_step x).
    time_simpl.
    change (fun (p : X.t * Z) z => (1 + (1 + X.T_eqb (fst p) x +
      (if X.eqb (fst p) x then 1 + Z.T_add (snd p) z else 0)))%N)
      with (T_poly_coefficient_step x).
    assert (Hmass : (1 <= N.of_nat (length (lhs r) + 1) *
      N.of_nat (keys + 2 * bits + length (lhs r) + 1))%N).
    { change (1 * 1 <= N.of_nat (length (lhs r) + 1) *
        N.of_nat (keys + 2 * bits + length (lhs r) + 1))%N.
      apply N.mul_le_mono; lia. }
    replace ((poly_coefficient_factor + 4) * N.of_nat (length (lhs r) + 1) *
      N.of_nat (keys + 2 * bits + length (lhs r) + 1))%N with
      (((poly_coefficient_factor + 1) * N.of_nat (length (lhs r) + 1) *
       N.of_nat (keys + 2 * bits + length (lhs r) + 1)) +
       3 * (N.of_nat (length (lhs r) + 1) *
       N.of_nat (keys + 2 * bits + length (lhs r) + 1)))%N by ring.
    lia.
  Qed.

  (** Every stored coefficient is bounded by its row's maximum coefficient width. *)
  Lemma poly_row_entry_bits : forall r p, In p (lhs r) ->
    Z.size_nat (snd p) <= C.row_bits r.
  Proof.
    intros r p Hin. unfold C.row_bits.
    exact (poly_max_member _ (fun p => Z.size_nat (snd p))
      (Z.size_nat (rhs r)) (lhs r) p Hin).
  Qed.

  (** A raw row supplies uniform key and coefficient bounds for every occurrence. *)
  Lemma poly_row_entry_sizes : forall r,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= C.row_key_bits r /\
      Z.size_nat (snd p) <= C.row_bits r) (lhs r).
  Proof.
    intro r. apply Forall_forall. intros p Hin. split.
    - now apply poly_row_key_member with (r := r).
    - now apply poly_row_entry_bits with (r := r).
  Qed.

  (** Summing all repeated occurrences adds at most the raw row length in bits. *)
  Lemma poly_raw_row_coefficient_bits : forall x r,
    Z.size_nat (poly_coefficient X.eqb x r) <= length (lhs r) + C.row_bits r.
  Proof.
    intros x r. rewrite <- coef_of_poly_coefficient. apply poly_raw_coefficient_bits.
    apply Forall_forall. intros p Hin. now apply poly_row_entry_bits with (r := r).
  Qed.

  (** The row size dominates its length and both initial arithmetic widths. *)
  Lemma poly_lsize_parts : forall r,
    length (lhs r) + C.row_key_bits r + C.row_bits r + 1 <= C.lsize r /\
    (length (lhs r) + 1) * (C.row_bits r + 1) <= C.lsize r /\
    (length (lhs r) + 1) * (C.row_key_bits r + 1) <= C.lsize r.
  Proof.
    intro r. unfold C.lsize. nia.
  Qed.

  (** Substitution retains exactly the source terms with a different key. *)
  Definition poly_without_key (x : X.t) (p : X.t * Z) : bool :=
    negb (X.eqb (fst p) x).

  TimeFun poly_without_key.

  (** The retention test charges only the stored key's comparison bound. *)
  Lemma T_poly_without_key_le : forall x p keys,
    Pos.size_nat (X.encode (fst p)) <= keys ->
    (T_poly_without_key x p <= (X.c_key + 4) * N.of_nat (keys + 1))%N.
  Proof.
    intros x p keys Hkey. pose proof (X.T_eqb_le (fst p) x) as Heqb.
    time_unfold T_poly_without_key. unfold X.bits in *. time_simpl. nia.
  Qed.

  (** Filtering one raw row is linear in the public row size. *)
  Lemma T_poly_without_filter_le : forall x r,
    (List.T_filter (poly_without_key x) (T_poly_without_key x) (lhs r) <=
      (X.c_key + 8) * N.of_nat (C.lsize r))%N.
  Proof.
    intros x r.
    assert (Hfilter : (List.T_filter (poly_without_key x) (T_poly_without_key x)
      (lhs r) <= ((X.c_key + 4) * N.of_nat (C.row_key_bits r + 1) + 1) *
        N.of_nat (length (lhs r)) + 1)%N).
    { apply poly_T_filter_members. intros p Hin. apply T_poly_without_key_le.
      now apply poly_row_key_member with (r := r). }
    pose proof (poly_lsize_parts r) as [Hparts [_ Hkeys]]. nia.
  Qed.

  (** Substitution accumulates the surviving source terms and one scaled affine form. *)
  Definition poly_subst_input (x : X.t) (f : lin X.t) (r : lcons X.t)
      : list (X.t * Z) :=
    filter (poly_without_key x) (lhs r) ++
      poly_scale_coef (poly_coefficient X.eqb x r) (coef f).

  (** Aggregate-first substitution creates at most the two original lists' total length. *)
  Lemma poly_subst_input_length : forall x f r,
    length (poly_subst_input x f r) <= length (lhs r) + length (coef f).
  Proof.
    intros x f r. unfold poly_subst_input, poly_scale_coef.
    rewrite length_app, length_map. apply Nat.add_le_mono_r, filter_length_le.
  Qed.

  (** The accumulated substitution list has bounded source keys and product widths. *)
  Lemma poly_subst_input_sizes : forall x f r,
    Forall (fun p =>
      Pos.size_nat (X.encode (fst p)) <=
        C.row_key_bits r + C.row_key_bits (LCons X.t (coef f) REq (cst f)) /\
      Z.size_nat (snd p) <= length (lhs r) + C.row_bits r +
        C.row_bits (LCons X.t (coef f) REq (cst f))) (poly_subst_input x f r).
  Proof.
    intros x f r. unfold poly_subst_input. apply Forall_app. split.
    - apply Forall_forall. intros p Hin. apply filter_In in Hin as [Hin _].
      pose proof (poly_row_key_member r p Hin).
      pose proof (poly_row_entry_bits r p Hin). split; lia.
    - apply Forall_forall. intros [y z] Hin. unfold poly_scale_coef in Hin.
      apply in_map_iff in Hin as [[u a] [Heq Hin]]. cbn [fst snd] in Heq.
      injection Heq as Heqy Heqz. subst y z.
      pose proof (poly_row_key_member (LCons X.t (coef f) REq (cst f))
        (u, a) Hin) as Hkey.
      pose proof (poly_row_entry_bits (LCons X.t (coef f) REq (cst f))
        (u, a) Hin) as Hbits.
      pose proof (poly_raw_row_coefficient_bits x r) as Hcoefficient.
      pose proof (poly_size_mul (poly_coefficient X.eqb x r) a) as Hmul.
      cbn [fst snd] in *. split; lia.
  Qed.

  (** Each constituent traversal fits one quadratic source-and-form size. *)
  Definition poly_subst_factor : N :=
    (8 * poly_raw_normal_factor + 4 * poly_coefficient_factor + 8 * X.c_key + 192)%N.

  (** Finding a pivot stops early or pays for each tested input occurrence. *)
  Lemma poly_T_find_members : forall A (f : A -> bool) T_f k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (List.T_find f T_f xs <= (k + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold List.T_find. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)).
      time_unfold List.T_find. destruct (f x); time_cbn; nia.
  Qed.

  (** Flattening charges each callback and the length of the row list it returns. *)
  Lemma poly_T_flat_map_members : forall A B (f : A -> list B) T_f k width xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (forall x, In x xs -> length (f x) <= width) ->
    (List.T_flat_map f T_f xs <=
      (k + N.of_nat width + 3) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f k width xs. induction xs as [|x xs IH]; intros Hcallback Hwidth.
    - time_unfold List.T_flat_map. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      pose proof (Hwidth x (or_introl eq_refl)) as Hlength.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)
        ltac:(intros y Hin; apply Hwidth; now right)).
      pose proof (Datatypes.T_app_le (f x) (flat_map f xs)) as Happ.
      time_unfold List.T_flat_map. time_cbn. nia.
  Qed.

  (** Normal lookups use the same primitive step with both summands in one width envelope. *)
  Definition poly_coef_step_factor : N := (2 * poly_coefficient_factor)%N.

  (** A complete lookup also pays its row projection and empty traversal. *)
  Definition poly_coef_factor : N := (poly_coef_step_factor + 4)%N.

  (** A coefficient lookup step charges the stored key and bounded summands. *)
  Lemma T_poly_coeff_step_normal : forall x p z keys bits,
    Pos.size_nat (X.encode (fst p)) <= keys ->
    Z.size_nat (snd p) <= bits -> Z.size_nat z <= bits ->
    (T_poly_coefficient_step x p z <= poly_coef_step_factor * N.of_nat (keys + bits + 1))%N.
  Proof.
    intros x p z keys bits Hkey Hp Hz.
    pose proof (T_poly_coefficient_step_bounded x p z keys bits bits Hkey Hp Hz) as Hstep.
    unfold poly_coef_step_factor. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** A normal coefficient fold keeps its partial result within the input coefficient width. *)
  Lemma T_poly_coeff_fold : forall x xs keys bits,
    NoDup (map fst xs) ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (List.T_fold_right (poly_coefficient_step x) (T_poly_coefficient_step x) 0%Z xs <=
      (poly_coef_step_factor + 1) * N.of_nat (length xs) *
        N.of_nat (keys + bits + 1) + 1)%N.
  Proof.
    intros x xs. induction xs as [|p xs IH]; intros keys bits Hunique Hsizes.
    - time_unfold List.T_fold_right. time_cbn. lia.
    - inversion Hunique as [|key rest Hnot Hunique_tail]; subst key rest.
      inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      assert (Hvalue : Z.size_nat (fold_right (poly_coefficient_step x) 0%Z xs) <= bits).
      { rewrite poly_coefficient_step_fold. apply poly_coef_bits; [exact Hunique_tail|].
        eapply Forall_impl; [|exact Htail]. intros q [_ Hq]. exact Hq. }
      specialize (IH keys bits Hunique_tail Htail).
      pose proof (T_poly_coeff_step_normal x p _ keys bits Hkey Hbits Hvalue) as Hstep.
      time_unfold List.T_fold_right. time_cbn. nia.
  Qed.

  (** Declared row widths bound the fields of every coefficient occurrence. *)
  Lemma poly_row_entry_bounds : forall r keys bits,
    C.row_key_bits r <= keys -> C.row_bits r <= bits ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) (lhs r).
  Proof.
    intros r keys bits Hkeys Hbits. apply Forall_forall. intros p Hin. split.
    - eapply Nat.le_trans; [apply poly_row_key_member; exact Hin|exact Hkeys].
    - eapply Nat.le_trans; [|exact Hbits]. unfold C.row_bits.
      exact (poly_max_member _ (fun p => Z.size_nat (snd p))
        (Z.size_nat (rhs r)) (lhs r) p Hin).
  Qed.

  (** Looking up a coefficient in a normal row is linear in its entries and declared widths. *)
  Lemma T_poly_coefficient_normal : forall x r keys bits,
    NoDup (map fst (lhs r)) -> C.row_key_bits r <= keys -> C.row_bits r <= bits ->
    (T_poly_coefficient X.eqb X.T_eqb x r <=
      poly_coef_factor * N.of_nat (length (lhs r) + 1) * N.of_nat (keys + bits + 1))%N.
  Proof.
    intros x r keys bits Hunique Hkeys Hbits.
    pose proof (T_poly_coeff_fold x (lhs r) keys bits Hunique
      (poly_row_entry_bounds r keys bits Hkeys Hbits)) as Hfold.
    time_unfold (@T_poly_coefficient).
    lazymatch goal with
    | |- context [List.T_fold_right ?f ?Tf 0%Z (lhs r)] =>
      change f with (poly_coefficient_step x); change Tf with (T_poly_coefficient_step x)
    end.
    unfold poly_coef_factor. time_simpl. nia.
  Qed.

  (** Scaling a bounded coefficient list charges a bounded multiplication per occurrence. *)
  Lemma T_poly_scale_bounded : forall a (xs : list (X.t * Z)) bits,
    Z.size_nat a <= bits -> Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    (T_poly_scale_coef a xs <=
      16 * N.of_nat (length xs + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros a xs bits Ha Hxs. pose proof (T_poly_scale_coef_bounded a xs bits Hxs) as Hscale.
    eapply N.le_trans; [exact Hscale|]. rewrite !Nat2N.inj_mul, N.pow_2_r.
    rewrite <- !N.mul_assoc. apply N.mul_le_mono_l, N.mul_le_mono_l, N.mul_le_mono_r.
    lia.
  Qed.

  (** Scaling preserves uniqueness of the source keys. *)
  Lemma poly_scale_nodup : forall a (xs : list (X.t * Z)),
    NoDup (map fst xs) -> NoDup (map fst (poly_scale_coef a xs)).
  Proof.
    intros a xs Hunique. unfold poly_scale_coef. rewrite map_map. exact Hunique.
  Qed.

  (** Scaling preserves key widths and adds the factor width to coefficient widths. *)
  Lemma poly_scale_entry_sizes : forall a xs keys bits,
    Z.size_nat a <= bits ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= 2 * bits) (poly_scale_coef a xs).
  Proof.
    intros a xs keys bits Ha Hxs. unfold poly_scale_coef. apply Forall_map.
    eapply Forall_impl; [|exact Hxs]. intros [x z] [Hkey Hz]. cbn [fst snd].
    split; [exact Hkey|]. cbn [snd] in Hz. pose proof (poly_size_mul a z). lia.
  Qed.

  (** Monotone factor bounds turn a binary product clock into a square envelope. *)
  Lemma poly_clock_product_bound : forall cost factor a b size left right,
    (cost <= factor * a * b)%N -> (a <= left * size)%N ->
    (b <= right * size)%N ->
    (cost <= (factor * left * right) * (size * size))%N.
  Proof.
    intros cost factor a b size left right Hcost Ha Hb.
    eapply N.le_trans; [exact Hcost|].
    replace (factor * a * b)%N with (factor * (a * b))%N by ring.
    replace ((factor * left * right) * (size * size))%N with
      (factor * ((left * size) * (right * size)))%N by ring.
    apply N.mul_le_mono_l. now apply N.mul_le_mono.
  Qed.

  (** Conversion preserves a natural-number square as one binary product. *)
  Lemma poly_nat_square : forall n,
    N.of_nat (n^2) = (N.of_nat n * N.of_nat n)%N.
  Proof.
    intro n. change (N.of_nat (n * (n * 1)) = (N.of_nat n * N.of_nat n)%N).
    rewrite Nat.mul_1_r. apply Nat2N.inj_mul.
  Qed.

  (** A positive extent is bounded by its square. *)
  Lemma poly_nat_square_ge : forall n, 1 <= n ->
    (N.of_nat n <= N.of_nat (n^2))%N.
  Proof.
    intros n Hpositive. rewrite poly_nat_square.
    replace (N.of_nat n) with (N.of_nat n * 1)%N at 1 by ring.
    apply N.mul_le_mono_l. lia.
  Qed.

  (** The two public row sizes pay for the whole aggregate-first substitution. *)
  Definition poly_subst_extent (f : lin X.t) (r : lcons X.t) : nat :=
    C.lsize (LCons X.t (coef f) REq (cst f)) + C.lsize r + 1.

  (** The substitution extent is positive even when both coefficient lists are empty. *)
  Lemma poly_subst_extent_positive : forall f r, 1 <= poly_subst_extent f r.
  Proof.
    intros f r. unfold poly_subst_extent. lia.
  Qed.

  (** The extent bounds all original list lengths and arithmetic widths together. *)
  Lemma poly_subst_extent_inputs : forall f r,
    length (lhs r) + length (coef f) + C.row_key_bits r +
      C.row_key_bits (LCons X.t (coef f) REq (cst f)) + C.row_bits r +
      C.row_bits (LCons X.t (coef f) REq (cst f)) + 3 <= poly_subst_extent f r.
  Proof.
    intros f r. pose proof (poly_lsize_parts r) as [Hr _].
    pose proof (poly_lsize_parts (LCons X.t (coef f) REq (cst f))) as [Hf _].
    change (length (coef f) + C.row_key_bits (LCons X.t (coef f) REq (cst f)) +
      C.row_bits (LCons X.t (coef f) REq (cst f)) + 1 <=
      C.lsize (LCons X.t (coef f) REq (cst f))) in Hf.
    unfold poly_subst_extent. lia.
  Qed.

  (** Looking up the substituted coefficient fits the square of the input extent. *)
  Lemma T_poly_subst_coefficient : forall x f r,
    (T_poly_coefficient X.eqb X.T_eqb x r <=
      2 * (poly_coefficient_factor + 4) * N.of_nat ((poly_subst_extent f r)^2))%N.
  Proof.
    intros x f r. pose proof (poly_subst_extent_inputs f r) as Hinputs.
    pose proof (T_poly_coefficient_bounded x r _ _ (poly_row_entry_sizes r)) as Htime.
    assert (Hlength : (N.of_nat (length (lhs r) + 1) <=
      1 * N.of_nat (poly_subst_extent f r))%N) by lia.
    assert (Hwidth : (N.of_nat (C.row_key_bits r + 2 * C.row_bits r +
      length (lhs r) + 1) <= 2 * N.of_nat (poly_subst_extent f r))%N) by lia.
    pose proof (poly_clock_product_bound _ _ _ _ _ _ _ Htime Hlength Hwidth) as Hbound.
    rewrite <- poly_nat_square in Hbound.
    replace ((poly_coefficient_factor + 4) * 1 * 2)%N with
      (2 * (poly_coefficient_factor + 4))%N in Hbound by ring.
    exact Hbound.
  Qed.

  (** Scaling pays one form-size factor and one source-size factor. *)
  Lemma T_poly_subst_scale : forall x f r,
    (T_poly_scale_coef (poly_coefficient X.eqb x r) (coef f) <=
      16 * N.of_nat ((poly_subst_extent f r)^2))%N.
  Proof.
    intros x f r. set (a := poly_coefficient X.eqb x r).
    set (fr := LCons X.t (coef f) REq (cst f)).
    pose proof (poly_raw_row_coefficient_bits x r) as Ha. fold a in Ha.
    pose proof (poly_lsize_parts r) as [Hr _].
    pose proof (poly_lsize_parts fr) as [_ [Hform _]].
    change ((length (coef f) + 1) * (C.row_bits fr + 1) <= C.lsize fr) in Hform.
    assert (Hbits : Forall (fun p => Z.size_nat (snd p) <= C.row_bits fr) (coef f)).
    { apply Forall_forall. intros p Hin. exact (poly_row_entry_bits fr p Hin). }
    pose proof (T_poly_scale_coef_bounded a (coef f) (C.row_bits fr) Hbits) as Htime.
    replace (16 * N.of_nat ((length (coef f) + 1) * (Z.size_nat a + 1) *
      (C.row_bits fr + 1)))%N with
      (16 * N.of_nat ((length (coef f) + 1) * (C.row_bits fr + 1)) *
        N.of_nat (Z.size_nat a + 1))%N in Htime by (rewrite !Nat2N.inj_mul; ring).
    assert (Hleft : (N.of_nat ((length (coef f) + 1) * (C.row_bits fr + 1)) <=
      1 * N.of_nat (poly_subst_extent f r))%N).
    { unfold poly_subst_extent. fold fr. lia. }
    assert (Hright : (N.of_nat (Z.size_nat a + 1) <=
      1 * N.of_nat (poly_subst_extent f r))%N).
    { unfold poly_subst_extent. fold fr. lia. }
    pose proof (poly_clock_product_bound _ _ _ _ _ _ _ Htime Hleft Hright) as Hbound.
    rewrite <- poly_nat_square in Hbound. exact Hbound.
  Qed.

  (** Raw normalization of the substitution list fits four extent factors. *)
  Lemma T_poly_subst_normal : forall x f r,
    (T_poly_normal_coef X.encode X.T_encode (poly_subst_input x f r) <=
      4 * poly_raw_normal_factor * N.of_nat ((poly_subst_extent f r)^2))%N.
  Proof.
    intros x f r. set (fr := LCons X.t (coef f) REq (cst f)).
    pose proof (poly_subst_extent_inputs f r) as Hinputs. fold fr in Hinputs.
    pose proof (poly_subst_input_length x f r) as Hlength.
    pose proof (T_poly_normal_raw (poly_subst_input x f r)
      (C.row_key_bits r + C.row_key_bits fr)
      (length (lhs r) + C.row_bits r + C.row_bits fr)
      (poly_subst_input_sizes x f r)) as Htime.
    assert (Hleft : (N.of_nat (length (poly_subst_input x f r) + 1) <=
      1 * N.of_nat (poly_subst_extent f r))%N) by lia.
    assert (Hright : (N.of_nat (C.row_key_bits r + C.row_key_bits fr +
      2 * (length (lhs r) + C.row_bits r + C.row_bits fr) +
      2 * length (poly_subst_input x f r) + 1) <=
      4 * N.of_nat (poly_subst_extent f r))%N) by lia.
    pose proof (poly_clock_product_bound _ _ _ _ _ _ _ Htime Hleft Hright) as Hbound.
    rewrite <- poly_nat_square in Hbound.
    replace (poly_raw_normal_factor * 1 * 4)%N with
      (4 * poly_raw_normal_factor)%N in Hbound by ring. exact Hbound.
  Qed.

  (** Filtering the source is also bounded by the shared square envelope. *)
  Lemma T_poly_subst_filter : forall x f r,
    (List.T_filter (poly_without_key x) (T_poly_without_key x) (lhs r) <=
      (X.c_key + 8) * N.of_nat ((poly_subst_extent f r)^2))%N.
  Proof.
    intros x f r. pose proof (T_poly_without_filter_le x r) as Htime.
    pose proof (poly_nat_square_ge _ (poly_subst_extent_positive f r)) as Hsquare.
    eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l.
    unfold poly_subst_extent in *. lia.
  Qed.

  (** Appending the two input pieces pays only for the surviving source list. *)
  Lemma T_poly_subst_app : forall x f r,
    (Datatypes.T_app (filter (poly_without_key x) (lhs r))
      (poly_scale_coef (poly_coefficient X.eqb x r) (coef f)) <=
      N.of_nat ((poly_subst_extent f r)^2))%N.
  Proof.
    intros x f r. pose proof (poly_subst_extent_inputs f r) as Hinputs.
    pose proof (poly_nat_square_ge _ (poly_subst_extent_positive f r)) as Hsquare.
    pose proof (filter_length_le (poly_without_key x) (lhs r)) as Hlength.
    pose proof (Datatypes.T_app_le (filter (poly_without_key x) (lhs r))
      (poly_scale_coef (poly_coefficient X.eqb x r) (coef f))) as Htime. lia.
  Qed.

  (** The right-hand-side product and subtraction fit fixed multiples of the same square. *)
  Lemma T_poly_subst_arithmetic : forall x f r,
    (Z.T_mul (poly_coefficient X.eqb x r) (cst f) <=
      8 * N.of_nat ((poly_subst_extent f r)^2))%N /\
    (Z.T_sub (rhs r) (poly_coefficient X.eqb x r * cst f) <=
      12 * N.of_nat ((poly_subst_extent f r)^2))%N.
  Proof.
    intros x f r. set (a := poly_coefficient X.eqb x r).
    pose proof (poly_subst_extent_inputs f r) as Hinputs.
    pose proof (poly_raw_row_coefficient_bits x r) as Ha. fold a in Ha.
    pose proof (poly_row_rhs_bits r) as Hr.
    pose proof (poly_row_rhs_bits (LCons X.t (coef f) REq (cst f))) as Hf.
    change (Z.size_nat (cst f) <= C.row_bits (LCons X.t (coef f) REq (cst f))) in Hf.
    pose proof (poly_T_Z_mul_bilinear a (cst f)) as Hmul.
    assert (Hleft : (N.of_nat (Z.size_nat a + 1) <=
      1 * N.of_nat (poly_subst_extent f r))%N) by lia.
    assert (Hright : (N.of_nat (Z.size_nat (cst f) + 1) <=
      1 * N.of_nat (poly_subst_extent f r))%N) by lia.
    pose proof (poly_clock_product_bound _ _ _ _ _ _ _ Hmul Hleft Hright) as Hbound.
    rewrite <- poly_nat_square in Hbound. split; [exact Hbound|].
    pose proof (Z.T_sub_le (rhs r) (a * cst f)) as Hsub.
    pose proof (poly_size_mul a (cst f)) as Hproduct.
    pose proof (poly_nat_square_ge _ (poly_subst_extent_positive f r)) as Hsquare.
    assert (Hlinear : (Z.T_sub (rhs r) (a * cst f) <=
      12 * N.of_nat (poly_subst_extent f r))%N) by lia.
    eapply N.le_trans; [exact Hlinear|]. now apply N.mul_le_mono_l.
  Qed.

  (** Substitution fits a quadratic bound even when its raw inputs repeat keys. *)
  Lemma T_poly_subst_bounded : forall x f r,
    (T_subst x f r <= poly_subst_factor * N.of_nat
      ((C.lsize (LCons X.t (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof.
    intros x f r. set (a := poly_coefficient X.eqb x r).
    set (mass := N.of_nat ((poly_subst_extent f r)^2)).
    pose proof (T_poly_subst_coefficient x f r) as Hcoefficient.
    pose proof (T_poly_subst_scale x f r) as Hscale.
    pose proof (T_poly_subst_normal x f r) as Hnormal.
    pose proof (T_poly_subst_filter x f r) as Hfilter.
    pose proof (T_poly_subst_app x f r) as Happ.
    destruct (T_poly_subst_arithmetic x f r) as [Hmul Hsub].
    fold mass in Hcoefficient, Hscale, Hnormal, Hfilter, Happ, Hmul, Hsub.
    fold a in Hscale, Happ, Hmul, Hsub.
    assert (Hmass : (1 <= mass)%N).
    { unfold mass. pose proof (poly_subst_extent_positive f r) as Hpositive.
      pose proof (poly_nat_square_ge _ Hpositive). lia. }
    change (T_subst x f r <= poly_subst_factor * mass)%N.
    time_unfold T_subst. time_unfold (@T_poly_substitute).
    change (fun p => negb (X.eqb (fst p) x)) with (poly_without_key x).
    fold a. fold (poly_subst_input x f r). time_simpl.
    lazymatch goal with
    | |- context [List.T_filter (poly_without_key x) ?Tf (lhs r)] =>
      change Tf with (T_poly_without_key x)
    end.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    change (filter (poly_without_key x) (lhs r) ++ poly_scale_coef a (coef f))
      with (poly_subst_input x f r).
    unfold poly_subst_factor. nia.
  Qed.

  (** A bounded factor times a successor-width multiplier has a quadratic scalar clock. *)
  Lemma poly_T_mul_successor_width : forall a z bits,
    Z.size_nat a <= bits -> Z.size_nat z <= bits + 1 ->
    (Z.T_mul a z <= 16 * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros a z bits Ha Hz. eapply N.le_trans; [apply poly_T_Z_mul_bilinear|].
    assert (Hproduct : (N.of_nat (Z.size_nat a + 1) * N.of_nat (Z.size_nat z + 1) <=
      N.of_nat (bits + 1) * (2 * N.of_nat (bits + 1)))%N).
    { apply N.mul_le_mono; lia. }
    rewrite N.pow_2_r. clear Ha Hz. nia.
  Qed.

  (** Adding two bounded products has a smaller quadratic clock than either multiplication. *)
  Lemma poly_T_add_products_width : forall a m b z bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat m <= bits + 1 -> Z.size_nat z <= bits + 1 ->
    (Z.T_add (a * m) (b * z) <= 8 * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros a m b z bits Ha Hb Hm Hz.
    pose proof (poly_size_mul a m) as Hleft.
    pose proof (poly_size_mul b z) as Hright.
    assert (Hsum : (N.of_nat (Z.size_nat (a * m) + Z.size_nat (b * z)) <=
      4 * N.of_nat bits + 2)%N) by lia.
    eapply N.le_trans; [apply Z.T_add_le|].
    rewrite N.pow_2_r, Nat2N.inj_add. cbn [N.of_nat]. clear -Hsum. nia.
  Qed.

  (** One weighted entry pays two bounded products and their sum. *)
  Lemma T_poly_weighted_entry : forall a m b z bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat m <= bits + 1 -> Z.size_nat z <= bits + 1 ->
    (Z.T_mul a m + Z.T_mul b z + Z.T_add (a * m) (b * z) <=
      48 * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros a m b z bits Ha Hb Hm Hz.
    pose proof (poly_T_mul_successor_width a m bits Ha Hm) as Hleft.
    pose proof (poly_T_mul_successor_width b z bits Hb Hz) as Hright.
    pose proof (poly_T_add_products_width a m b z bits Ha Hb Hm Hz) as Hadd.
    lia.
  Qed.

  (** Weighted multiplier vectors charge one bounded scalar operation per entry. *)
  Lemma T_poly_weighted_bounded : forall a ms b ns bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Forall (fun z => Z.size_nat z <= bits + 1) ms ->
    Forall (fun z => Z.size_nat z <= bits + 1) ns ->
    (T_poly_weighted a ms b ns <=
      64 * N.of_nat (length ms + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros a ms. induction ms as [|m ms IH]; intros b ns bits Ha Hb Hms Hns;
      assert (Hwidth : (1 <= N.of_nat (bits + 1)^2)%N)
      by (rewrite N.pow_2_r; assert (1 <= N.of_nat (bits + 1))%N by lia; nia).
    - time_unfold T_poly_weighted. time_cbn. nia.
    - destruct ns as [|z ns].
      + time_unfold T_poly_weighted. time_cbn. nia.
      + inversion Hms as [|u us Hm Htailm]; subst u us.
        inversion Hns as [|u us Hz Htailn]; subst u us.
        specialize (IH b ns bits Ha Hb Htailm Htailn).
        pose proof (T_poly_weighted_entry a m b z bits Ha Hb Hm Hz) as Hentry.
        time_unfold T_poly_weighted. time_cbn.
        clear Ha Hb Hm Hz Htailm Htailn Hms Hns. nia.
  Qed.

  (** A tracked input row fits fixed dimension, multiplier, and arithmetic-width envelopes. *)
  Definition poly_row_envelope (dim mlen keys bits : nat) (r : poly_row X.t) : Prop :=
    NoDup (map fst (lhs (poly_constraint r))) /\
    length (lhs (poly_constraint r)) <= dim /\
    C.row_key_bits (poly_constraint r) <= keys /\ C.row_bits (poly_constraint r) <= bits /\
    length (poly_multipliers r) <= mlen /\
    Forall (fun z => Z.size_nat z <= bits + 1) (poly_multipliers r).

  (** One row operation charges its coefficients and multiplier entries at the common width. *)
  Definition poly_clock_span (dim mlen keys bits : nat) : N :=
    (N.of_nat (dim + mlen + 1) * N.of_nat (keys + bits + 1)^2)%N.

  (** A smaller occurrence count and width fit the common quadratic row envelope. *)
  Lemma poly_span_product : forall count width dim mlen keys bits,
    count <= dim + mlen -> width <= keys + bits ->
    (N.of_nat (count + 1) * N.of_nat (width + 1)^2 <=
      poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros count width dim mlen keys bits Hcount Hwidth. unfold poly_clock_span.
    apply N.mul_le_mono; [lia|]. apply N.pow_le_mono_l. lia.
  Qed.

  (** The quadratic row envelope also covers a linear-width occurrence traversal. *)
  Lemma poly_span_linear : forall count width dim mlen keys bits,
    count <= dim + mlen -> width <= keys + bits ->
    (N.of_nat (count + 1) * N.of_nat (width + 1) <=
      poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros count width dim mlen keys bits Hcount Hwidth.
    eapply N.le_trans; [|apply poly_span_product; eassumption].
    apply N.mul_le_mono_l. assert (1 <= N.of_nat (width + 1))%N by lia.
    rewrite N.pow_2_r. nia.
  Qed.

  (** Two scaled coefficient lists use at most twice each linear normalization dimension. *)
  Lemma poly_span_normal_pair : forall left right dim mlen keys bits,
    left <= dim -> right <= dim ->
    (N.of_nat (left + right + 1) * N.of_nat (keys + 2 * bits + 1) <=
      4 * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros left right dim mlen keys bits Hleft Hright.
    assert (Hcount : (N.of_nat (left + right + 1) <=
      2 * N.of_nat (dim + mlen + 1))%N) by lia.
    assert (Hwidth : (N.of_nat (keys + 2 * bits + 1) <=
      2 * N.of_nat (keys + bits + 1))%N) by lia.
    pose proof (N.mul_le_mono _ _ _ _ Hcount Hwidth) as Hproduct.
    assert (Hpositive : (1 <= N.of_nat (keys + bits + 1))%N) by lia.
    unfold poly_clock_span. rewrite N.pow_2_r. nia.
  Qed.

  (** Every row envelope has at least one unit of work. *)
  Lemma poly_span_positive : forall dim mlen keys bits,
    (1 <= poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros dim mlen keys bits. unfold poly_clock_span.
    assert (1 <= N.of_nat (dim + mlen + 1))%N by lia.
    assert (1 <= N.of_nat (keys + bits + 1))%N by lia. rewrite N.pow_2_r. nia.
  Qed.

  (** Deciding whether an equality row is used only tests a relation tag or exact zero. *)
  Lemma T_poly_eq_used_le : forall a (r : lcons X.t), (T_poly_eq_used a r <= 4)%N.
  Proof.
    intros a r. pose proof (T_poly_zero_test a) as Hzero.
    time_unfold (@T_poly_eq_used). destruct (lrel r); time_simpl; nia.
  Qed.

  (** Scaling one row fits the common quadratic operation envelope. *)
  Lemma T_poly_scale_row_envelope : forall a r dim mlen keys bits,
    poly_row_envelope dim mlen keys bits r -> Z.size_nat a <= bits ->
    (T_poly_scale_coef a (lhs (poly_constraint r)) <=
      16 * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros a r dim mlen keys bits (Hnormal & Hdim & Hkeys & Hbits & Hmlen & Hmults) Ha.
    assert (Hentries : Forall (fun p => Z.size_nat (snd p) <= bits)
      (lhs (poly_constraint r))).
    { pose proof (poly_row_entry_bounds _ keys bits Hkeys Hbits) as Hsizes.
      eapply Forall_impl; [|exact Hsizes]. intros p [_ Hp]. exact Hp. }
    pose proof (T_poly_scale_bounded a _ bits Ha Hentries) as Hscale.
    pose proof (poly_span_product (length (lhs (poly_constraint r))) bits
      dim mlen keys bits ltac:(lia) ltac:(lia)) as Hspan.
    eapply N.le_trans; [exact Hscale|]. rewrite <- N.mul_assoc.
    now apply N.mul_le_mono_l.
  Qed.

  (** Normalizing two scaled normal rows fits the common row envelope. *)
  Lemma T_poly_normal_rows_envelope : forall a p b q dim mlen keys bits,
    poly_row_envelope dim mlen keys bits p ->
    poly_row_envelope dim mlen keys bits q ->
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    (T_poly_normal_coef X.encode X.T_encode
      (poly_scale_coef a (lhs (poly_constraint p)) ++
       poly_scale_coef b (lhs (poly_constraint q))) <=
      4 * poly_normal_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros a p b q dim mlen keys bits
      (Hnp & Hdp & Hkp & Hbp & Hmp & Hup)
      (Hnq & Hdq & Hkq & Hbq & Hmq & Huq) Ha Hb.
    pose proof (poly_row_entry_bounds _ keys bits Hkp Hbp) as Hep.
    pose proof (poly_row_entry_bounds _ keys bits Hkq Hbq) as Heq.
    pose proof (T_poly_normal_pair (poly_scale_coef a (lhs (poly_constraint p)))
      (poly_scale_coef b (lhs (poly_constraint q))) keys (2 * bits)
      (poly_scale_nodup _ _ Hnp) (poly_scale_nodup _ _ Hnq)
      (poly_scale_entry_sizes _ _ _ _ Ha Hep)
      (poly_scale_entry_sizes _ _ _ _ Hb Heq)) as Hnormal.
    assert (Hlength_p : length (poly_scale_coef a (lhs (poly_constraint p))) =
      length (lhs (poly_constraint p))) by (unfold poly_scale_coef; apply length_map).
    assert (Hlength_q : length (poly_scale_coef b (lhs (poly_constraint q))) =
      length (lhs (poly_constraint q))) by (unfold poly_scale_coef; apply length_map).
    rewrite Hlength_p, Hlength_q in Hnormal.
    pose proof (poly_span_normal_pair _ _ dim mlen keys bits Hdp Hdq) as Hspan.
    apply (N.mul_le_mono_l _ _ poly_normal_factor) in Hspan.
    nia.
  Qed.

  (** Right-hand-side arithmetic uses two products and one bounded sum. *)
  Lemma T_poly_rhs_pair_envelope : forall a b u v dim mlen keys bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat u <= bits -> Z.size_nat v <= bits ->
    (Z.T_mul a u + Z.T_mul b v + Z.T_add (a * u) (b * v) <=
      48 * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros a b u v dim mlen keys bits Ha Hb Hu Hv.
    pose proof (T_poly_weighted_entry a u b v bits Ha Hb ltac:(lia) ltac:(lia)) as Hentry.
    pose proof (poly_span_product 0 bits dim mlen keys bits ltac:(lia) ltac:(lia)) as Hspan.
    change (1 * N.of_nat (bits + 1)^2 <= poly_clock_span dim mlen keys bits)%N in Hspan.
    rewrite N.mul_1_l in Hspan.
    eapply N.le_trans; [exact Hentry|]. now apply N.mul_le_mono_l.
  Qed.

  (** Row addition combines normalization, scaling, multipliers, and bounded scalar arithmetic. *)
  Definition poly_add_rows_factor : N := (8 * poly_normal_factor + 256)%N.

  (** Adding two bounded tracked rows fits the declared quadratic operation envelope. *)
  Lemma T_poly_add_rows_bounded : forall a p b q dim mlen keys bits,
    poly_row_envelope dim mlen keys bits p ->
    poly_row_envelope dim mlen keys bits q ->
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    (T_poly_add_rows X.encode X.T_encode a p b q <=
      poly_add_rows_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros a p b q dim mlen keys bits Hp Hq Ha Hb.
    pose proof (T_poly_scale_row_envelope a p _ _ _ _ Hp Ha) as Hscale_p.
    pose proof (T_poly_scale_row_envelope b q _ _ _ _ Hq Hb) as Hscale_q.
    pose proof (T_poly_normal_rows_envelope a p b q _ _ _ _ Hp Hq Ha Hb) as Hnormal.
    destruct Hp as (Hnp & Hdp & Hkp & Hbp & Hmp & Hup).
    destruct Hq as (Hnq & Hdq & Hkq & Hbq & Hmq & Huq).
    pose proof (T_poly_weighted_bounded a _ b _ bits Ha Hb Hup Huq) as Hweighted.
    pose proof (poly_span_product (length (poly_multipliers p)) bits
      dim mlen keys bits ltac:(lia) ltac:(lia)) as Hweights_span.
    assert (Hweighted_span : (T_poly_weighted a (poly_multipliers p)
      b (poly_multipliers q) <= 64 * poly_clock_span dim mlen keys bits)%N).
    { eapply N.le_trans; [exact Hweighted|]. rewrite <- N.mul_assoc.
      now apply N.mul_le_mono_l. }
    clear Hweighted Hweights_span.
    pose proof (T_poly_rhs_pair_envelope a b (rhs (poly_constraint p))
      (rhs (poly_constraint q)) dim mlen keys bits Ha Hb
      ltac:(pose proof (poly_row_rhs_bits (poly_constraint p)); lia)
      ltac:(pose proof (poly_row_rhs_bits (poly_constraint q)); lia)) as Hrhs.
    pose proof (T_poly_eq_used_le a (poly_constraint p)) as Heqp.
    pose proof (T_poly_eq_used_le b (poly_constraint q)) as Heqq.
    pose proof (Z.T_ltb_le 0 a) as Hapos. pose proof (Z.T_ltb_le 0 b) as Hbpos.
    change (Z.T_ltb 0 a <= 4)%N in Hapos.
    change (Z.T_ltb 0 b <= 4)%N in Hbpos.
    pose proof (Datatypes.T_app_le (poly_scale_coef a (lhs (poly_constraint p)))
      (poly_scale_coef b (lhs (poly_constraint q)))) as Happ.
    assert (Hscale_length : length (poly_scale_coef a (lhs (poly_constraint p))) =
      length (lhs (poly_constraint p))) by (unfold poly_scale_coef; apply length_map).
    rewrite Hscale_length in Happ.
    pose proof (poly_span_linear (length (lhs (poly_constraint p))) 0
      dim mlen keys bits ltac:(lia) ltac:(lia)) as Happend_span.
    change (N.of_nat (length (lhs (poly_constraint p)) + 1) * 1 <=
      poly_clock_span dim mlen keys bits)%N in Happend_span.
    rewrite N.mul_1_r in Happend_span.
    assert (Happend : (Datatypes.T_app (poly_scale_coef a (lhs (poly_constraint p)))
      (poly_scale_coef b (lhs (poly_constraint q))) <=
      2 * poly_clock_span dim mlen keys bits)%N) by lia.
    clear Happ Happend_span.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    time_unfold (@T_poly_add_rows). unfold poly_add_rows_factor. time_simpl.
    change (fun u : X.t => X.T_encode u) with X.T_encode. nia.
  Qed.

  (** Multiplying by a sign needs only a linear pass over the other operand. *)
  Lemma T_poly_sign_mul_bounded : forall a b bits,
    Z.size_nat b <= bits ->
    (Z.T_mul (- Z.sgn a) b <= 6 * N.of_nat (bits + 1))%N.
  Proof.
    intros a b bits Hb. pose proof (Z.T_mul_le (- Z.sgn a) b) as Hmul.
    assert (Hsign_bits : Z.size_nat (- Z.sgn a) <= 1).
    { destruct a; cbn [Z.sgn Z.opp Z.size_nat Pos.size_nat]; lia. }
    nia.
  Qed.

  (** Cancellation adds two coefficient lookups and a bounded factor calculation. *)
  Definition poly_cancel_factor : N :=
    (poly_add_rows_factor + 4 * poly_coef_factor + 96)%N.

  (** Eliminating with an equality pivot fits the same row envelope. *)
  Lemma T_poly_cancel_bounded : forall x p r dim mlen keys bits,
    poly_row_envelope dim mlen keys bits p ->
    poly_row_envelope dim mlen keys bits r ->
    (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x p r <=
      poly_cancel_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x p r dim mlen keys bits Hp Hr.
    destruct Hp as (Hnp & Hdp & Hkp & Hbp & Hmp & Hup).
    destruct Hr as (Hnr & Hdr & Hkr & Hbr & Hmr & Hur).
    set (a := poly_coefficient X.eqb x (poly_constraint p)).
    set (b := poly_coefficient X.eqb x (poly_constraint r)).
    assert (Ha : Z.size_nat a <= bits).
    { unfold a. eapply Nat.le_trans; [apply poly_row_coefficient_bits; exact Hnp|exact Hbp]. }
    assert (Hb : Z.size_nat b <= bits).
    { unfold b. eapply Nat.le_trans; [apply poly_row_coefficient_bits; exact Hnr|exact Hbr]. }
    pose proof (T_poly_coefficient_normal x _ keys bits Hnp Hkp Hbp) as Hlookup_p.
    pose proof (T_poly_coefficient_normal x _ keys bits Hnr Hkr Hbr) as Hlookup_r.
    pose proof (poly_span_linear (length (lhs (poly_constraint p))) (keys + bits)
      dim mlen keys bits ltac:(lia) ltac:(lia)) as Hspan_p.
    pose proof (poly_span_linear (length (lhs (poly_constraint r))) (keys + bits)
      dim mlen keys bits ltac:(lia) ltac:(lia)) as Hspan_r.
    pose proof (N.mul_le_mono_l _ _ poly_coef_factor Hspan_p) as Hlookup_span_p.
    pose proof (N.mul_le_mono_l _ _ poly_coef_factor Hspan_r) as Hlookup_span_r.
    pose proof (T_poly_add_rows_bounded (- Z.sgn a * b)%Z p (Z.abs a) r
      dim mlen keys bits ltac:(repeat split; assumption) ltac:(repeat split; assumption)
      ltac:(pose proof (poly_size_sign_mul a b); lia)
      ltac:(now rewrite poly_size_abs)) as Hadd.
    pose proof (T_poly_sign_mul_bounded a b bits Hb) as Hmultiply.
    pose proof (Z.T_abs_le a) as Habs. pose proof (T_poly_zero_test b) as Hzero.
    assert (Hsign : (Z.T_sgn a <= 1)%N).
    { destruct a; time_unfold Z.T_sgn; time_simpl; lia. }
    assert (Hopp : (Z.T_opp (Z.sgn a) <= 1)%N).
    { destruct a; time_unfold Z.T_opp; time_simpl; lia. }
    pose proof (poly_span_linear 0 bits dim mlen keys bits ltac:(lia) ltac:(lia)) as Hscalar.
    change (1 * N.of_nat (bits + 1) <= poly_clock_span dim mlen keys bits)%N in Hscalar.
    rewrite N.mul_1_l in Hscalar.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    time_unfold (@T_poly_cancel). fold a b. unfold poly_cancel_factor. time_simpl.
    destruct (Z.eqb b 0); time_simpl;
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb;
      try change (fun u : X.t => X.T_encode u) with X.T_encode; nia.
  Qed.

  (** A coefficient lookup in an enveloped row fits one common row charge. *)
  Lemma T_poly_lookup_envelope : forall x r dim mlen keys bits,
    poly_row_envelope dim mlen keys bits r ->
    (T_poly_coefficient X.eqb X.T_eqb x (poly_constraint r) <=
      poly_coef_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x r dim mlen keys bits (Hn & Hd & Hk & Hb & Hm & Hu).
    pose proof (T_poly_coefficient_normal x _ keys bits Hn Hk Hb) as Hlookup.
    pose proof (poly_span_linear (length (lhs (poly_constraint r))) (keys + bits)
      dim mlen keys bits ltac:(lia) ltac:(lia)) as Hspan.
    pose proof (N.mul_le_mono_l _ _ poly_coef_factor Hspan). nia.
  Qed.

  (** The coefficient of an enveloped normal row stays within its coefficient width. *)
  Lemma poly_envelope_coefficient_bits : forall x r dim mlen keys bits,
    poly_row_envelope dim mlen keys bits r ->
    Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <= bits.
  Proof.
    intros x r dim mlen keys bits (Hn & Hd & Hk & Hb & Hm & Hu).
    eapply Nat.le_trans; [apply poly_row_coefficient_bits; exact Hn|exact Hb].
  Qed.

  (** Row selection applies a scalar test to the coefficient of the selected variable. *)
  Definition poly_clock_select (test : Z -> bool) (x : X.t) (r : poly_row X.t) : bool :=
    test (poly_coefficient X.eqb x (poly_constraint r)).

  TimeFun poly_clock_select.

  Definition poly_select_factor : N := (poly_coef_factor + 12)%N.

  (** The three sign-class tests add only a linear scalar test to coefficient lookup. *)
  Lemma T_poly_select_bounded : forall test T_test x r dim mlen keys bits,
    poly_row_envelope dim mlen keys bits r ->
    (forall z, Z.size_nat z <= bits -> (T_test z <= N.of_nat (bits + 1) + 4)%N) ->
    (T_poly_clock_select test T_test x r <=
      poly_select_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros test T_test x r dim mlen keys bits Hr Htest.
    pose proof (T_poly_lookup_envelope x r _ _ _ _ Hr) as Hlookup.
    pose proof (Htest _ (poly_envelope_coefficient_bits x r _ _ _ _ Hr)) as Hscalar.
    pose proof (poly_span_linear 0 bits dim mlen keys bits ltac:(lia) ltac:(lia)) as Hspan.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    time_unfold T_poly_clock_select. unfold poly_select_factor. time_simpl.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb. nia.
  Qed.

  (** A pivot test adds the relation tag and a zero test to coefficient lookup. *)
  Lemma T_poly_pivot_bounded : forall x r dim mlen keys bits,
    poly_row_envelope dim mlen keys bits r ->
    (T_poly_pivot X.eqb X.T_eqb x r <=
      poly_select_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x r dim mlen keys bits Hr.
    pose proof (T_poly_lookup_envelope x r _ _ _ _ Hr) as Hlookup.
    pose proof (T_poly_zero_test (poly_coefficient X.eqb x (poly_constraint r))) as Hzero.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    time_unfold (@T_poly_pivot). destruct (lrel (poly_constraint r));
      unfold poly_select_factor; time_simpl;
      try change (fun u v : X.t => X.T_eqb u v) with X.T_eqb; nia.
  Qed.

  (** The positive selector has a constant first comparison operand. *)
  Lemma poly_positive_test_clock : forall bits z, Z.size_nat z <= bits ->
    (Z.T_ltb 0 z <= N.of_nat (bits + 1) + 4)%N.
  Proof.
    intros bits z Hz. pose proof (Z.T_ltb_le 0 z) as Hcompare.
    change (Z.T_ltb 0 z <= 4)%N in Hcompare.
    lia.
  Qed.

  (** The negative selector charges at most the coefficient's width. *)
  Lemma poly_negative_test_clock : forall bits z, Z.size_nat z <= bits ->
    (Z.T_ltb z 0 <= N.of_nat (bits + 1) + 4)%N.
  Proof.
    intros bits z Hz. pose proof (Z.T_ltb_le z 0) as Hcompare. lia.
  Qed.

  (** The zero selector compares only the outer integer constructor. *)
  Lemma poly_zero_test_clock : forall bits z, Z.size_nat z <= bits ->
    (Z.T_eqb z 0 <= N.of_nat (bits + 1) + 4)%N.
  Proof.
    intros bits z Hz. pose proof (T_poly_zero_test z) as Hcompare. lia.
  Qed.

  (** One pair forms the Fourier-Motzkin combination of its two coefficients. *)
  Definition poly_clock_pair (x : X.t) (p q : poly_row X.t) : poly_row X.t :=
    poly_add_rows X.encode (- poly_coefficient X.eqb x (poly_constraint q))%Z p
      (poly_coefficient X.eqb x (poly_constraint p)) q.

  TimeFun poly_clock_pair.

  Definition poly_pair_factor : N :=
    (poly_add_rows_factor + 2 * poly_coef_factor + 16)%N.

  (** Constructing a pair charges its two coefficient lookups and its normalized row sum. *)
  Lemma T_poly_pair_bounded : forall x p q dim mlen keys bits,
    poly_row_envelope dim mlen keys bits p -> poly_row_envelope dim mlen keys bits q ->
    (T_poly_clock_pair x p q <=
      poly_pair_factor * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x p q dim mlen keys bits Hp Hq.
    pose proof (T_poly_lookup_envelope x p _ _ _ _ Hp) as Hlookup_p.
    pose proof (T_poly_lookup_envelope x q _ _ _ _ Hq) as Hlookup_q.
    pose proof (poly_envelope_coefficient_bits x p _ _ _ _ Hp) as Hbits_p.
    pose proof (poly_envelope_coefficient_bits x q _ _ _ _ Hq) as Hbits_q.
    pose proof (T_poly_add_rows_bounded
      (- poly_coefficient X.eqb x (poly_constraint q))%Z p
      (poly_coefficient X.eqb x (poly_constraint p)) q dim mlen keys bits Hp Hq
      ltac:(now rewrite poly_size_opp) Hbits_p) as Hadd.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    assert (Hopp : (Z.T_opp (poly_coefficient X.eqb x (poly_constraint q)) <= 1)%N).
    { destruct (poly_coefficient X.eqb x (poly_constraint q));
        time_unfold Z.T_opp; time_simpl; lia. }
    time_unfold T_poly_clock_pair. unfold poly_pair_factor. time_simpl.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun u : X.t => X.T_encode u) with X.T_encode. nia.
  Qed.

  (** Mapping one positive row over the negative class builds its pair list. *)
  Definition poly_clock_pair_map (x : X.t) (neg : list (poly_row X.t)) (p : poly_row X.t)
      : list (poly_row X.t) := map (poly_clock_pair x p) neg.

  TimeFun poly_clock_pair_map.

  (** The inner pair traversal pays one bounded row combination for every negative row. *)
  Lemma T_poly_pair_map_bounded : forall x neg p dim mlen keys bits,
    poly_row_envelope dim mlen keys bits p ->
    Forall (poly_row_envelope dim mlen keys bits) neg ->
    (T_poly_clock_pair_map x neg p <=
      (poly_pair_factor * poly_clock_span dim mlen keys bits + 1) *
        N.of_nat (length neg) + 4)%N.
  Proof.
    intros x neg p dim mlen keys bits Hp Hneg.
    pose proof (poly_T_map_members _ _ (poly_clock_pair x p) (T_poly_clock_pair x p)
      (poly_pair_factor * poly_clock_span dim mlen keys bits)%N neg
      ltac:(intros q Hq; apply T_poly_pair_bounded; [exact Hp|];
        exact (proj1 (Forall_forall _ _) Hneg q Hq))) as Hmap.
    time_unfold T_poly_clock_pair_map.
    change (fun q => T_poly_clock_pair x p q) with (T_poly_clock_pair x p).
    time_simpl. nia.
  Qed.

  (** Flattening the inner pair traversals creates the complete opposite-sign cross product. *)
  Definition poly_clock_pairs (x : X.t) (pos neg : list (poly_row X.t)) : list (poly_row X.t) :=
    flat_map (poly_clock_pair_map x neg) pos.

  TimeFun poly_clock_pairs.

  (** All opposite-sign pairs fit the square of the original row count. *)
  Lemma T_poly_pairs_bounded : forall x pos neg count dim mlen keys bits,
    Forall (poly_row_envelope dim mlen keys bits) pos ->
    Forall (poly_row_envelope dim mlen keys bits) neg ->
    length pos <= count -> length neg <= count ->
    (T_poly_clock_pairs x pos neg <=
      (poly_pair_factor + 16) * N.of_nat (count + 1)^2 *
        poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x pos neg count dim mlen keys bits Hpos Hneg Hp Hn.
    pose proof (poly_T_flat_map_members _ _ (poly_clock_pair_map x neg)
      (T_poly_clock_pair_map x neg)
      ((poly_pair_factor * poly_clock_span dim mlen keys bits + 1) *
        N.of_nat (length neg) + 4)%N (length neg) pos
      ltac:(intros p Hin; apply T_poly_pair_map_bounded; [|exact Hneg];
        exact (proj1 (Forall_forall _ _) Hpos p Hin))
      ltac:(intros p Hin; unfold poly_clock_pair_map; rewrite length_map; reflexivity)) as Hflat.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    set (work := poly_clock_span dim mlen keys bits) in *.
    set (count1 := N.of_nat (count + 1)).
    assert (Hcount1 : (1 <= count1)%N) by (unfold count1; lia).
    assert (Hpos_count : (N.of_nat (length pos) <= count1)%N)
      by (unfold count1; lia).
    assert (Hneg_count : (N.of_nat (length neg) <= count1)%N)
      by (unfold count1; lia).
    assert (Hinner :
      (((poly_pair_factor * work + 1) * N.of_nat (length neg) + 4 +
        N.of_nat (length neg) + 3) <=
        (poly_pair_factor + 9) * work * count1)%N).
    { pose proof (N.mul_le_mono_l _ _ (poly_pair_factor * work + 1)%N
        Hneg_count) as Hproducts.
      pose proof (N.mul_le_mono_r _ _ count1 Hpositive) as Hwork_count.
      nia. }
    pose proof (N.mul_le_mono _ _ _ _ Hinner Hpos_count) as Htotal.
    assert (Hmass : (1 <= work * count1 * count1)%N).
    { change (1 * 1 * 1 <= work * count1 * count1)%N.
      apply N.mul_le_mono; [apply N.mul_le_mono; assumption|assumption]. }
    clear Hpos Hneg Hp Hn Hinner Hpos_count Hneg_count.
    time_unfold T_poly_clock_pairs.
    change (fun p => T_poly_clock_pair_map x neg p) with (T_poly_clock_pair_map x neg).
    time_simpl. fold count1. rewrite N.pow_2_r. nia.
  Qed.

  (** Selecting one sign class pays a bounded predicate for every input row. *)
  Lemma T_poly_filter_select : forall test T_test x rows dim mlen keys bits,
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    (forall z, Z.size_nat z <= bits -> (T_test z <= N.of_nat (bits + 1) + 4)%N) ->
    (List.T_filter (poly_clock_select test x) (T_poly_clock_select test T_test x) rows <=
      (poly_select_factor * poly_clock_span dim mlen keys bits + 1) *
        N.of_nat (length rows) + 1)%N.
  Proof.
    intros test T_test x rows dim mlen keys bits Hrows Htest.
    apply poly_T_filter_members. intros r Hin. apply T_poly_select_bounded; [|exact Htest].
    exact (proj1 (Forall_forall _ _) Hrows r Hin).
  Qed.

  (** The inequality branch retains zeros and combines the positive and negative classes. *)
  Definition poly_clock_inequalities (x : X.t) (rows : list (poly_row X.t))
      : list (poly_row X.t) :=
    let pos := filter (fun r => (0 <? poly_coefficient X.eqb x (poly_constraint r))%Z) rows in
    let neg := filter (fun r => (poly_coefficient X.eqb x (poly_constraint r) <? 0)%Z) rows in
    filter (fun r => Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0) rows ++
      poly_clock_pairs x pos neg.

  TimeFun poly_clock_inequalities.

  Definition poly_inequalities_factor : N :=
    (poly_pair_factor + 8 * poly_select_factor + 48)%N.

  (** The complete inequality branch fits the square row-count envelope. *)
  Lemma T_poly_inequalities_bounded : forall x rows dim mlen keys bits,
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    (T_poly_clock_inequalities x rows <=
      poly_inequalities_factor * N.of_nat (length rows + 1)^2 *
        poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x rows dim mlen keys bits Hrows.
    pose proof (T_poly_filter_select (fun z => (0 <? z)%Z) (fun z => Z.T_ltb 0 z)
      x rows _ _ _ _ Hrows (poly_positive_test_clock bits)) as Hpositive_filter.
    pose proof (T_poly_filter_select (fun z => (z <? 0)%Z) (fun z => Z.T_ltb z 0)
      x rows _ _ _ _ Hrows (poly_negative_test_clock bits)) as Hnegative_filter.
    pose proof (T_poly_filter_select (fun z => Z.eqb z 0) (fun z => Z.T_eqb z 0)
      x rows _ _ _ _ Hrows (poly_zero_test_clock bits)) as Hzero_filter.
    set (pos := filter (poly_clock_select (fun z => (0 <? z)%Z) x) rows).
    set (neg := filter (poly_clock_select (fun z => (z <? 0)%Z) x) rows).
    set (zero := filter (poly_clock_select (fun z => Z.eqb z 0) x) rows).
    assert (Hpos : Forall (poly_row_envelope dim mlen keys bits) pos).
    { apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
      exact (proj1 (Forall_forall _ _) Hrows r Hin). }
    assert (Hneg : Forall (poly_row_envelope dim mlen keys bits) neg).
    { apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
      exact (proj1 (Forall_forall _ _) Hrows r Hin). }
    pose proof (filter_length_le (poly_clock_select (fun z => (0 <? z)%Z) x) rows) as Hp.
    pose proof (filter_length_le (poly_clock_select (fun z => (z <? 0)%Z) x) rows) as Hn.
    pose proof (filter_length_le (poly_clock_select (fun z => Z.eqb z 0) x) rows) as Hz.
    fold pos in Hp. fold neg in Hn. fold zero in Hz.
    pose proof (T_poly_pairs_bounded x pos neg (length rows) _ _ _ _ Hpos Hneg Hp Hn) as Hpairs.
    pose proof (Datatypes.T_app_le zero (poly_clock_pairs x pos neg)) as Happ.
    pose proof (poly_span_positive dim mlen keys bits) as Hspan.
    set (work := poly_clock_span dim mlen keys bits) in *.
    set (row_count := (N.of_nat (length rows + 1)^2)%N) in Hpairs |- *.
    assert (Hcount : (N.of_nat (length rows + 1) <= row_count)%N).
    { unfold row_count. rewrite N.pow_2_r.
      assert (1 <= N.of_nat (length rows + 1))%N by lia. nia. }
    assert (Hcount_positive : (1 <= row_count)%N) by lia.
    set (total := (row_count * work)%N).
    assert (Hcount_total : (row_count <= total)%N).
    { unfold total. pose proof (N.mul_le_mono_l _ _ row_count Hspan) as Hproduct.
      rewrite N.mul_1_r in Hproduct. exact Hproduct. }
    assert (Htotal_positive : (1 <= total)%N) by lia.
    assert (Hfilter :
      ((poly_select_factor * work + 1) * N.of_nat (length rows) + 1 <=
        (poly_select_factor + 2) * total)%N).
    { assert (Hfactor : (poly_select_factor * work + 1 <=
        (poly_select_factor + 1) * work)%N) by nia.
      assert (Hlength : (N.of_nat (length rows) <= row_count)%N) by lia.
      pose proof (N.mul_le_mono _ _ _ _ Hfactor Hlength) as Hproducts.
      unfold total in Htotal_positive |- *. nia. }
    pose proof (N.le_trans _ _ _ Hpositive_filter Hfilter) as Hpositive_total.
    pose proof (N.le_trans _ _ _ Hnegative_filter Hfilter) as Hnegative_total.
    pose proof (N.le_trans _ _ _ Hzero_filter Hfilter) as Hzero_total.
    assert (Happend_total : (Datatypes.T_app zero (poly_clock_pairs x pos neg) <=
      2 * total)%N) by lia.
    rewrite <- N.mul_assoc in Hpairs. fold total in Hpairs.
    clear Hpositive_filter Hnegative_filter Hzero_filter Hfilter Happ Hpos Hneg Hp Hn Hz.
    time_unfold T_poly_clock_inequalities.
    change (fun r : poly_row X.t => (0 <? poly_coefficient X.eqb x (poly_constraint r))%Z)
      with (poly_clock_select (fun z => (0 <? z)%Z) x).
    change (fun r : poly_row X.t => (poly_coefficient X.eqb x (poly_constraint r) <? 0)%Z)
      with (poly_clock_select (fun z => (z <? 0)%Z) x).
    change (fun r : poly_row X.t => Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0)
      with (poly_clock_select (fun z => Z.eqb z 0) x).
    fold pos neg zero. time_simpl.
    lazymatch goal with
    | |- context [List.T_filter (poly_clock_select (fun z => (0 <? z)%Z) x) ?Tf rows] =>
        change Tf with (T_poly_clock_select (fun z => (0 <? z)%Z) (fun z => Z.T_ltb 0 z) x)
    end.
    lazymatch goal with
    | |- context [List.T_filter (poly_clock_select (fun z => (z <? 0)%Z) x) ?Tf rows] =>
        change Tf with (T_poly_clock_select (fun z => (z <? 0)%Z) (fun z => Z.T_ltb z 0) x)
    end.
    lazymatch goal with
    | |- context [List.T_filter (poly_clock_select (fun z => Z.eqb z 0) x) ?Tf rows] =>
        change Tf with (T_poly_clock_select (fun z => Z.eqb z 0) (fun z => Z.T_eqb z 0) x)
    end.
    unfold poly_inequalities_factor.
    rewrite <- N.mul_assoc. fold total. nia.
  Qed.

  Definition poly_step_factor : N :=
    (poly_cancel_factor + poly_inequalities_factor + 4 * poly_select_factor + 32)%N.

  (** Finding a pivot and then taking either elimination branch fits the square envelope. *)
  Lemma T_poly_step_bounded : forall x rows dim mlen keys bits,
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows <=
      poly_step_factor * N.of_nat (length rows + 1)^2 *
        poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x rows dim mlen keys bits Hrows.
    pose proof (poly_T_find_members _ (poly_pivot X.eqb x)
      (T_poly_pivot X.eqb X.T_eqb x)
      (poly_select_factor * poly_clock_span dim mlen keys bits)%N rows
      ltac:(intros r Hin; apply T_poly_pivot_bounded;
        exact (proj1 (Forall_forall _ _) Hrows r Hin))) as Hfind.
    pose proof (poly_span_positive dim mlen keys bits) as Hspan.
    time_unfold (@T_poly_step).
    try change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    try change (fun u : X.t => X.T_encode u) with X.T_encode.
    change (fun r => T_poly_pivot X.eqb X.T_eqb x r)
      with (T_poly_pivot X.eqb X.T_eqb x).
    destruct (find (poly_pivot X.eqb x) rows) as [pivot|] eqn:Hpivot.
    - apply find_some in Hpivot as [Hpivot _].
      pose proof (proj1 (Forall_forall _ _) Hrows pivot Hpivot) as Hpivot_row.
      pose proof (poly_T_map_members _ _ (poly_cancel X.encode X.eqb x pivot)
        (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot)
        (poly_cancel_factor * poly_clock_span dim mlen keys bits)%N rows
        ltac:(intros r Hin; apply T_poly_cancel_bounded; [exact Hpivot_row|];
          exact (proj1 (Forall_forall _ _) Hrows r Hin))) as Hmap.
      change (fun r => T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot r)
        with (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot).
      unfold poly_step_factor. time_simpl.
      try change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      try change (fun u : X.t => X.T_encode u) with X.T_encode.
      rewrite N.pow_2_r. nia.
    - pose proof (T_poly_inequalities_bounded x rows _ _ _ _ Hrows) as Hbranch.
      unfold T_poly_clock_inequalities, T_poly_clock_pairs, T_poly_clock_pair_map,
        T_poly_clock_pair, poly_clock_pairs, poly_clock_pair_map, poly_clock_pair in Hbranch.
      cbn beta iota zeta in Hbranch.
      unfold poly_step_factor. revert Hbranch. time_simpl. intro Hbranch.
      try change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      try change (fun u : X.t => X.T_encode u) with X.T_encode.
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb in Hbranch.
      change (fun u : X.t => X.T_encode u) with X.T_encode in Hbranch.
      rewrite N.pow_2_r in Hbranch |- *. nia.
  Qed.
  (** A raw input row fits the fixed dimension and width parameters used during initialization. *)
  Definition poly_input_envelope (dim keys bits : nat) (r : lcons X.t) : Prop :=
    NoDup (map fst (lhs r)) /\ length (lhs r) <= dim /\
      C.row_key_bits r <= keys /\ C.row_bits r <= bits.

  Definition poly_normal_row_factor : N := (poly_normal_factor + 8)%N.

  (** Normalizing one normal source row pays its linear coefficient-list normalization. *)
  Lemma T_poly_normal_row_bounded : forall r dim keys bits,
    poly_input_envelope dim keys bits r ->
    (T_poly_normal_row X.encode X.T_encode r <=
      poly_normal_row_factor * N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N.
  Proof.
    intros r dim keys bits (Hnormal & Hdim & Hkeys & Hbits).
    pose proof (T_poly_normal_unique (lhs r) keys bits Hnormal
      (poly_row_entry_bounds r keys bits Hkeys Hbits)) as Hnormalization.
    assert (Hwidth : (1 <= N.of_nat (keys + bits + 1))%N) by lia.
    time_unfold (@T_poly_normal_row). unfold poly_normal_row_factor. time_simpl.
    change (fun u : X.t => X.T_encode u) with X.T_encode. nia.
  Qed.

  (** Padding an identity-vector row requires only its three record projections. *)
  Lemma T_poly_pad_row_le : forall r : poly_row X.t, (T_poly_pad_row r <= 4)%N.
  Proof.
    intro r. time_unfold (@T_poly_pad_row). time_simpl. lia.
  Qed.

  Definition poly_initial_factor : N := (poly_normal_row_factor + 16)%N.

  (** Building normalized rows and their identity multiplier vectors fits a quadratic row count. *)
  Lemma T_poly_initial_bounded : forall P dim keys bits,
    Forall (fun p => poly_input_envelope dim keys bits (fst p)) P ->
    (T_poly_initial X.encode X.T_encode P <=
      poly_initial_factor * N.of_nat (length P + 1)^2 *
        N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N.
  Proof.
    intro P. induction P as [|[r flag] P IH]; intros dim keys bits Hrows.
    - assert (Hdimension : (1 <= N.of_nat (dim + 1))%N) by lia.
      assert (Hwidth : (1 <= N.of_nat (keys + bits + 1))%N) by lia.
      time_unfold (@T_poly_initial). time_simpl. unfold poly_initial_factor,
        poly_normal_row_factor, poly_normal_factor. nia.
    - inversion Hrows as [|p ps Hr Htail]; subst p ps.
      specialize (IH dim keys bits Htail).
      pose proof (T_poly_normal_row_bounded r dim keys bits Hr) as Hrow.
      pose proof (poly_T_map_members _ _ (fun _ : lcons X.t * bool => 0%Z)
        (fun _ : lcons X.t * bool => 1%N) 1 P
        (fun _ _ => N.le_refl 1%N)) as Hzeros.
      pose proof (poly_T_map_members _ _ (@poly_pad_row X.t) (@T_poly_pad_row X.t) 4
        (poly_initial X.encode P) ltac:(intros; apply T_poly_pad_row_le)) as Hpad.
      rewrite poly_initial_length in Hpad.
      assert (Hdimension : (1 <= N.of_nat (dim + 1))%N) by lia.
      assert (Hwidth : (1 <= N.of_nat (keys + bits + 1))%N) by lia.
      time_unfold (@T_poly_initial). cbn [fst snd length].
      change (fun p => T_poly_pad_row p) with (@T_poly_pad_row X.t).
      unfold poly_initial_factor in *. time_simpl.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      rewrite N.pow_2_r in IH |- *. nia.
  Qed.

  (** Every normal source row fits the common input maxima and variable dimension. *)
  Lemma poly_source_envelopes : forall P, normal P ->
    Forall (fun p => poly_input_envelope (n P)
      (fold_right Nat.max 0 (map C.row_key_bits P))
      (fold_right Nat.max 0 (map C.row_bits P)) (fst p))
      (map (fun r => (r, false)) P).
  Proof.
    intros P Hnormal. apply Forall_map, Forall_forall. intros r Hin.
    unfold poly_input_envelope. cbn [fst]. split.
    - unfold normal in Hnormal. exact (proj1 (Forall_forall _ _) Hnormal r Hin).
    - split.
      + pose proof (poly_row_dimension P r Hnormal Hin). unfold n. lia.
      + split; [exact (poly_max_member _ C.row_key_bits 0 P r Hin)|].
        exact (poly_max_member _ C.row_bits 0 P r Hin).
  Qed.

  (** Initial normalization and unit vectors satisfy every input invariant for one FM step. *)
  Lemma poly_initial_envelopes : forall P, normal P ->
    Forall (poly_row_envelope (n P) (length P)
      (fold_right Nat.max 0 (map C.row_key_bits P))
      (fold_right Nat.max 0 (map C.row_bits P)))
      (poly_initial X.encode (map (fun r => (r, false)) P)).
  Proof.
    intros P Hnormal. apply Forall_forall. intros r Hin.
    pose proof (poly_initial_sizes P Hnormal) as Hsizes.
    destruct (proj1 (Forall_forall _ _) Hsizes r Hin) as [Hunique [Hbits Hkeys]].
    pose proof (poly_initial_dimension P r Hnormal Hin) as Hdim.
    pose proof (poly_initial_units X.t X.encode (map (fun r => (r, false)) P)) as Hunits.
    destruct (proj1 (Forall_forall _ _) Hunits r Hin) as [Hlength Hunit].
    rewrite length_map in Hlength. unfold poly_row_envelope. repeat split; try assumption.
    - unfold n. lia.
    - lia.
    - apply Forall_forall. intros z Hz.
      destruct (proj1 (Forall_forall _ _) Hunit z Hz) as [Heq|Heq]; subst z;
        cbn [Z.size_nat Pos.size_nat]; lia.
  Qed.

  (** The FM row-count recurrence is bounded by the successor square. *)
  Lemma poly_step_length_square : forall x rows,
    length (poly_step X.encode X.eqb x rows) <= (length rows + 1)^2.
  Proof.
    intros x rows. pose proof (poly_step_rows X.t X.encode X.eqb x rows) as Hrows.
    assert (Hdivision : length rows ^ 2 / 4 <= length rows ^ 2).
    { apply Nat.Div0.div_le_upper_bound; nia. }
    cbn [Nat.pow] in *. nia.
  Qed.

  (** Mapping output records charges one closure and two projections per constraint. *)
  Lemma T_poly_track_map : forall rows,
    (ListDef.T_map (fun r => Tracked X.t (poly_constraint r) (poly_multipliers r))
      (fun _ => 3%N) rows <= 4 * N.of_nat (length rows) + 1)%N.
  Proof.
    intro rows. exact (poly_T_map_members _ _
      (fun r => Tracked X.t (poly_constraint r) (poly_multipliers r))
      (fun _ => 3%N) 3 rows (fun _ _ => N.le_refl 3%N)).
  Qed.

  (** The complete FM clock combines initialization, elimination, and record projection. *)
  Definition poly_fm_factor : N := (poly_step_factor + poly_initial_factor + 32)%N.

  (** The actual elimination clock fits the frozen row, dimension, and width envelope. *)
  Lemma T_poly_fm_bounded : forall x P, normal P ->
    (T_fm_elim x P <= poly_fm_factor * N.of_nat (length P + 1)^2 *
      N.of_nat (n P + length P + 1) * N.of_nat (ell P + 1)^2)%N.
  Proof.
    intros x P Hnormal.
    set (input := map (fun r => (r, false)) P).
    set (initial := poly_initial X.encode input).
    set (rows := poly_step X.encode X.eqb x initial).
    set (keys := fold_right Nat.max 0 (map C.row_key_bits P)).
    set (bits := fold_right Nat.max 0 (map C.row_bits P)).
    pose proof (T_poly_initial_bounded input (n P) keys bits
      (poly_source_envelopes P Hnormal)) as Hinitial.
    pose proof (T_poly_step_bounded x initial (n P) (length P) keys bits
      (poly_initial_envelopes P Hnormal)) as Hstep.
    assert (Hinput_length : length input = length P) by (unfold input; apply length_map).
    assert (Hinitial_length : length initial = length P).
    { unfold initial. now rewrite poly_initial_length. }
    rewrite Hinput_length in Hinitial. rewrite Hinitial_length in Hstep.
    pose proof (poly_step_length_square x initial) as Hcount.
    fold rows in Hcount. rewrite Hinitial_length in Hcount.
    pose proof (poly_T_map_members _ _ (fun r => (r, false)) (fun _ => 1%N) 1 P
      (fun _ _ => N.le_refl 1%N)) as Hinput.
    pose proof (T_poly_track_map rows) as Houtput.
    pose proof (poly_span_linear (n P) (keys + bits)
      (n P) (length P) keys bits ltac:(lia) ltac:(lia)) as Hinitial_span.
    pose proof (poly_span_positive (n P) (length P) keys bits) as Hspan.
    set (row_work := poly_clock_span (n P) (length P) keys bits) in *.
    set (row_count := (N.of_nat (length P + 1)^2)%N) in *.
    assert (Hinitial_total : (T_poly_initial X.encode X.T_encode input <=
      poly_initial_factor * row_count * row_work)%N).
    { eapply N.le_trans; [exact Hinitial|]. rewrite <- !N.mul_assoc.
      apply N.mul_le_mono_l, N.mul_le_mono_l. exact Hinitial_span. }
    assert (Hcount_positive : (1 <= row_count)%N).
    { unfold row_count. rewrite N.pow_2_r. assert (1 <= N.of_nat (length P + 1))%N by lia.
      nia. }
    assert (Hinput_total : (ListDef.T_map (fun r => (r, false)) (fun _ => 1%N) P <=
      2 * row_count * row_work)%N).
    { assert (N.of_nat (length P + 1) <= row_count)%N.
      { unfold row_count. rewrite N.pow_2_r. nia. }
      nia. }
    assert (Houtput_total : (ListDef.T_map
      (fun r => Tracked X.t (poly_constraint r) (poly_multipliers r))
      (fun _ => 3%N) rows <= 5 * row_count * row_work)%N).
    { assert (Hrows_N : (N.of_nat (length rows) <= row_count)%N).
      { assert (Hcount_N : (N.of_nat (length rows) <=
          N.of_nat ((length P + 1)^2))%N) by (clear -Hcount; lia).
        rewrite poly_nat_square in Hcount_N.
        unfold row_count. rewrite N.pow_2_r. exact Hcount_N. }
      clear -Houtput Hrows_N Hspan Hcount_positive.
      nia. }
    clear Hinitial Hinitial_span Hinput Houtput Hcount.
    assert (Hshape : row_work =
      (N.of_nat (n P + length P + 1) * N.of_nat (ell P + 1)^2)%N).
    { unfold row_work, poly_clock_span, ell, keys, bits.
      f_equal. f_equal. f_equal. lia. }
    time_unfold T_fm_elim. fold input initial rows.
    rewrite <- N.mul_assoc, <- Hshape. unfold poly_fm_factor.
    time_simpl. fold row_count.
    change (fun _ : poly_row X.t => (1 + (1 + 1))%N)
      with (fun _ : poly_row X.t => 3%N).
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    assert (Htotal_positive : (1 <= row_count * row_work)%N).
    { change (1 * 1 <= row_count * row_work)%N.
      apply N.mul_le_mono; assumption. }
    rewrite <- N.mul_assoc in Hstep, Hinitial_total, Hinput_total, Houtput_total |- *.
    set (total := (row_count * row_work)%N) in *.
    clear -Hstep Hinitial_total Hinput_total Houtput_total Htotal_positive.
    clearbody total. nia.
  Qed.


  (** Distinct coefficients supported by a fixed key list fit its length. *)
  Lemma poly_reduced_dimension : forall vars r,
    poly_reduced_row vars r -> length (lhs (poly_constraint r)) <= length vars.
  Proof.
    intros vars r [Hunique Hsupport]. rewrite <- (length_map fst (lhs (poly_constraint r))).
    apply NoDup_incl_length; [exact Hunique|]. intros x Hx.
    apply in_map_iff in Hx as [p [Hsame Hp]]. rewrite <- Hsame.
    exact (proj2 (proj1 (Forall_forall _ _) Hsupport p Hp)).
  Qed.

  (** Truncating a weighted pair cannot lengthen its left multiplier vector. *)
  Lemma poly_weighted_length_le : forall a ms b ns,
    length (poly_weighted a ms b ns) <= length ms.
  Proof.
    intros a ms. induction ms as [|m ms IH]; intros b [|n ns];
      cbn [poly_weighted length]; try lia. specialize (IH b ns). lia.
  Qed.

  (** A coefficient times a tracked multiplier uses one more bit than a row product. *)
  Lemma poly_weighted_entry_growth : forall a b m n bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat m <= bits + 1 -> Z.size_nat n <= bits + 1 ->
    Z.size_nat (a * m + b * n) <= 2 * bits + 2.
  Proof.
    intros a b m n bits Ha Hb Hm Hn.
    pose proof (poly_size_mul a m) as Hleft.
    pose proof (poly_size_mul b n) as Hright.
    pose proof (poly_size_add (a * m) (b * n)) as Hsum. lia.
  Qed.

  (** Weighted multiplier vectors follow the same doubled-width recurrence. *)
  Lemma poly_weighted_growth : forall a ms b ns bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Forall (fun m => Z.size_nat m <= bits + 1) ms ->
    Forall (fun n => Z.size_nat n <= bits + 1) ns ->
    Forall (fun z => Z.size_nat z <= 2 * bits + 2) (poly_weighted a ms b ns).
  Proof.
    intros a ms. induction ms as [|m ms IH]; intros b ns bits Ha Hb Hms Hns;
      [constructor|].
    destruct ns as [|n ns]; [constructor|].
    inversion Hms as [|m' ms' Hm Htailm]; subst m' ms'.
    inversion Hns as [|n' ns' Hn Htailn]; subst n' ns'.
    cbn [poly_weighted]. constructor.
    - now apply poly_weighted_entry_growth.
    - now apply IH.
  Qed.

  (** A weighted row pair preserves its multiplier length bound and controls all entries. *)
  Lemma poly_add_rows_growth : forall a p b q mlen bits,
    length (poly_multipliers p) <= mlen ->
    Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers p) ->
    Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers q) ->
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    length (poly_multipliers (poly_add_rows X.encode a p b q)) <= mlen /\
      Forall (fun m => Z.size_nat m <= 2 * bits + 2)
        (poly_multipliers (poly_add_rows X.encode a p b q)).
  Proof.
    intros a p b q mlen bits Hlength Hp Hq Ha Hb.
    cbn [poly_add_rows poly_multipliers]. split.
    - eapply Nat.le_trans; [apply poly_weighted_length_le|exact Hlength].
    - now apply poly_weighted_growth.
  Qed.

  (** Cancellation uses only coefficients within the current row width. *)
  Lemma poly_cancel_growth : forall x p r mlen bits,
    length (poly_multipliers p) <= mlen ->
    length (poly_multipliers r) <= mlen ->
    Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers p) ->
    Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers r) ->
    Z.size_nat (poly_coefficient X.eqb x (poly_constraint p)) <= bits ->
    Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <= bits ->
    length (poly_multipliers (poly_cancel X.encode X.eqb x p r)) <= mlen /\
      Forall (fun m => Z.size_nat m <= 2 * bits + 2)
        (poly_multipliers (poly_cancel X.encode X.eqb x p r)).
  Proof.
    intros x p r mlen bits Hlp Hlr Hp Hr Hcp Hcr. unfold poly_cancel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0).
    - split; [exact Hlr|]. eapply Forall_impl; [|exact Hr]. intros m Hm.
      change (Z.size_nat m <= bits + 1) in Hm.
      change (Z.size_nat m <= 2 * bits + 2). lia.
    - apply poly_add_rows_growth; try assumption.
      + eapply Nat.le_trans; [apply poly_size_sign_mul|exact Hcr].
      + now rewrite poly_size_abs.
  Qed.

  (** Every branch of one FM step preserves the multiplier envelope. *)
  Lemma poly_step_multiplier_growth : forall x rows mlen bits,
    Forall (fun r =>
      length (poly_multipliers r) <= mlen /\
      Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers r) /\
      Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <= bits) rows ->
    Forall (fun r => length (poly_multipliers r) <= mlen /\
      Forall (fun m => Z.size_nat m <= 2 * bits + 2) (poly_multipliers r))
      (poly_step X.encode X.eqb x rows).
  Proof.
    intros x rows mlen bits Hrows. rewrite Forall_forall in Hrows.
    unfold poly_step. destruct (find (poly_pivot X.eqb x) rows) as [pivot|] eqn:Hpivot.
    - apply find_some in Hpivot as [Hpivot _].
      destruct (Hrows pivot Hpivot) as [Hlp [Hp Hcp]].
      apply Forall_map, Forall_forall. intros r Hin.
      destruct (Hrows r Hin) as [Hlr [Hr Hcr]]. now apply poly_cancel_growth.
    - apply Forall_app. split.
      + apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
        destruct (Hrows r Hin) as [Hlr [Hr _]]. split; [exact Hlr|].
        eapply Forall_impl; [|exact Hr]. intros m Hm.
        change (Z.size_nat m <= bits + 1) in Hm.
        change (Z.size_nat m <= 2 * bits + 2). lia.
      + apply Forall_forall. intros r Hin. apply in_flat_map in Hin as [p [Hp Hin]].
        apply filter_In in Hp as [Hp _]. apply in_map_iff in Hin as [q [Heq Hq]].
        apply filter_In in Hq as [Hq _]. subst r.
        destruct (Hrows p Hp) as [Hlp [Hmp Hcp]].
        destruct (Hrows q Hq) as [_ [Hmq Hcq]].
        apply poly_add_rows_growth; try assumption. now rewrite poly_size_opp.
  Qed.

  (** One elimination keeps the original variable dimension and doubles only arithmetic width. *)
  Lemma poly_step_envelopes : forall vars x rows dim mlen keys bits,
    length vars <= dim -> Forall (poly_reduced_row vars) rows ->
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    Forall (poly_row_envelope dim mlen keys (2 * bits + 1))
      (poly_step X.encode X.eqb x rows).
  Proof.
    intros vars x rows dim mlen keys bits Hdim Hreduced Henvelopes.
    pose proof (poly_step_reduced vars x rows Hreduced) as Hsupport.
    assert (Hsizes : Forall (fun r =>
      C.row_bits (poly_constraint r) <= 2 * bits + 1 /\
      C.row_key_bits (poly_constraint r) <= keys) (poly_step X.encode X.eqb x rows)).
    { apply poly_step_sizes. eapply Forall_impl; [|exact Henvelopes].
      intros r (Hn & Hd & Hk & Hb & Hm & Hu). auto. }
    assert (Hmults : Forall (fun r => length (poly_multipliers r) <= mlen /\
      Forall (fun m => Z.size_nat m <= 2 * bits + 2) (poly_multipliers r))
      (poly_step X.encode X.eqb x rows)).
    { apply poly_step_multiplier_growth. eapply Forall_impl; [|exact Henvelopes].
      intros r (Hn & Hd & Hk & Hb & Hm & Hu). repeat split; try assumption.
      eapply Nat.le_trans; [apply poly_row_coefficient_bits; exact Hn|exact Hb]. }
    apply Forall_forall. intros r Hr.
    pose proof (proj1 (Forall_forall _ _) Hsupport r Hr) as Hsupported.
    destruct (proj1 (Forall_forall _ _) Hsizes r Hr) as [Hb Hk].
    destruct (proj1 (Forall_forall _ _) Hmults r Hr) as [Hm Hu].
    unfold poly_row_envelope. split; [exact (proj1 Hsupported)|]. split.
    - exact (Nat.le_trans _ _ _ (poly_reduced_dimension vars r Hsupported) Hdim).
    - repeat split; try assumption.
      replace (2 * bits + 1 + 1) with (2 * bits + 2) by lia. exact Hu.
  Qed.

  (** This proof model iterates the public doubled-width recurrence. *)
  Fixpoint poly_width_after (fuel bits : nat) : nat :=
    match fuel with
    | 0 => bits
    | S k => poly_width_after k (2 * bits + 1)
    end.

  (** Larger initial widths give larger widths after the same number of eliminations. *)
  Lemma poly_width_after_mono : forall fuel bits bits', bits <= bits' ->
    poly_width_after fuel bits <= poly_width_after fuel bits'.
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros bits bits' Hbits;
      cbn [poly_width_after]; [exact Hbits|]. apply IH. lia.
  Qed.

  (** Fixed key widths fit inside the public combined-width recurrence. *)
  Lemma poly_width_after_fixed_keys : forall fuel keys bits,
    keys + poly_width_after fuel bits <= poly_width_after fuel (keys + bits).
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros keys bits;
      cbn [poly_width_after]; [lia|].
    eapply Nat.le_trans; [apply IH|]. apply poly_width_after_mono. lia.
  Qed.

  (** A complete run retains the same dimension, key width, and multiplier length bounds. *)
  Lemma poly_run_envelopes : forall xs vars rows dim mlen keys bits,
    length vars <= dim -> Forall (poly_reduced_row vars) rows ->
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    Forall (poly_row_envelope dim mlen keys (poly_width_after (length xs) bits))
      (poly_run X.encode X.eqb xs rows).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros vars rows dim mlen keys bits
      Hdim Hreduced Henvelopes; [exact Henvelopes|].
    cbn [poly_run length poly_width_after]. apply IH with (vars := vars).
    - exact Hdim.
    - now apply poly_step_reduced.
    - now apply poly_step_envelopes with (vars := vars).
  Qed.

  (** Initialization supports every row on the declared variables of the original inputs. *)
  Lemma poly_initial_reduced_vars : forall inputs,
    Forall (poly_reduced_row (vars_of (map fst inputs))) (poly_initial X.encode inputs).
  Proof.
    intro inputs. apply poly_initial_reduced. apply Forall_forall. intros p Hp term Hterm.
    apply poly_vars_of_contains with (r := fst p).
    - now apply in_map.
    - now apply in_map.
  Qed.

  (** Source bounds establish every part of the initial tracked-row envelope. *)
  Lemma poly_initial_envelopes_from_sources : forall inputs dim keys bits,
    Forall (fun p =>
      NoDup (map fst (lhs (fst p))) /\ length (lhs (fst p)) <= dim /\
      C.row_key_bits (fst p) <= keys /\ C.row_bits (fst p) <= bits) inputs ->
    Forall (poly_row_envelope dim (length inputs) keys bits) (poly_initial X.encode inputs).
  Proof.
    intros inputs dim keys bits Hsources. apply Forall_forall. intros r Hr.
    pose proof (poly_initial_units X.t X.encode inputs) as Hunits.
    destruct (proj1 (Forall_forall _ _) Hunits r Hr) as [Hlength Hunit].
    apply in_map with (f := poly_constraint) in Hr.
    rewrite poly_initial_constraints in Hr.
    apply in_map_iff in Hr as [p [Hsame Hp]].
    destruct (proj1 (Forall_forall _ _) Hsources p Hp) as [Hn [Hd [Hk Hb]]].
    unfold poly_row_envelope. rewrite <- Hsame. split.
    - cbn [poly_normal_row lhs]. apply poly_normal_coef_nodup.
    - split.
      + cbn [poly_normal_row lhs]. eapply Nat.le_trans; [apply poly_normal_length|exact Hd].
      + split.
        * eapply Nat.le_trans; [apply poly_normal_row_key_bits|exact Hk].
        * split.
          -- eapply Nat.le_trans; [now apply poly_normal_row_bits|exact Hb].
          -- split; [lia|]. apply Forall_forall. intros z Hz.
             destruct (proj1 (Forall_forall _ _) Hunit z Hz) as [Heq|Heq]; subst z;
               cbn [Z.size_nat Pos.size_nat]; lia.
  Qed.

  (** Entailment elimination uses the target keys together with the original source variables. *)
  Definition poly_entail_vars (P : list (lcons X.t)) (c : lcons X.t) : list X.t :=
    map fst (lhs c) ++ vars_of P.

  (** The fixed entailment support fits its frozen input dimension. *)
  Lemma poly_entail_vars_length : forall P c,
    length (poly_entail_vars P c) <= n P + length (lhs c).
  Proof.
    intros P c. unfold poly_entail_vars, n. rewrite length_app, length_map. lia.
  Qed.

  (** Negating the target preserves its keys, and all source keys lie in the fixed support. *)
  Lemma poly_entail_initial_reduced : forall P c,
    Forall (poly_reduced_row (poly_entail_vars P c))
      (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P)).
  Proof.
    intros P c. apply poly_initial_reduced. constructor.
    - intros p Hp. cbn [fst poly_negate poly_scale_coef lhs] in Hp.
      apply in_map_iff in Hp as [q [Hsame Hq]]. subst p.
      unfold poly_entail_vars. apply in_or_app. left. cbn [fst]. now apply in_map.
    - apply Forall_map, Forall_forall. intros r Hr p Hp. cbn [fst] in Hp.
      unfold poly_entail_vars. apply in_or_app. right.
      apply poly_vars_of_contains with (r := r); [exact Hr|]. now apply in_map.
  Qed.
  (** Every Fourier-Motzkin envelope pays at least one unit of work. *)
  Lemma poly_fmcost_positive : forall dim mlen fuel rows bits,
    0 < fmcost dim mlen fuel rows bits.
  Proof.
    intros dim mlen [|fuel] rows bits; cbn [fmcost Nat.pow]; nia.
  Qed.

  (** The recursive traversal adds a fixed charge to each bounded elimination. *)
  Definition poly_run_factor : N := (poly_step_factor + 8)%N.

  (** Running elimination on a fixed support follows the frozen cost recurrence. *)
  Lemma T_poly_run_bounded : forall xs vars rows dim mlen keys bits,
    length vars <= dim -> Forall (poly_reduced_row vars) rows ->
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs rows <=
      poly_run_factor * N.of_nat
        (fmcost dim mlen (length xs) (length rows) (keys + bits)))%N.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros vars rows dim mlen keys bits
      Hdim Hsupport Henvelopes.
    - pose proof (poly_fmcost_positive dim mlen 0 (length rows) (keys + bits)) as Hwork.
      time_unfold (@T_poly_run). time_cbn. unfold poly_run_factor. nia.
    - set (next := poly_step X.encode X.eqb x rows).
      assert (Hnext_support : Forall (poly_reduced_row vars) next).
      { unfold next. now apply poly_step_reduced. }
      assert (Hnext_envelopes :
        Forall (poly_row_envelope dim mlen keys (2 * bits + 1)) next).
      { unfold next. now apply poly_step_envelopes with (vars := vars). }
      pose proof (IH vars next dim mlen keys (2 * bits + 1)
        Hdim Hnext_support Hnext_envelopes) as Hrun.
      assert (Hnext_rows : length next <= (length rows)^2 / 4 + length rows).
      { unfold next. apply poly_step_rows. }
      pose proof (poly_fmcost_params_mono (length xs)
        dim dim mlen mlen (length next) ((length rows)^2 / 4 + length rows)
        (keys + (2 * bits + 1)) (2 * (keys + bits) + 1)
        (Nat.le_refl _) (Nat.le_refl _) Hnext_rows ltac:(lia)) as Hfuture.
      assert (Hrecursive :
        (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs next <=
          poly_run_factor * N.of_nat
            (fmcost dim mlen (length xs) ((length rows)^2 / 4 + length rows)
              (2 * (keys + bits) + 1)))%N).
      { eapply N.le_trans; [exact Hrun|]. apply N.mul_le_mono_l. lia. }
      pose proof (T_poly_step_bounded x rows dim mlen keys bits Henvelopes) as Hstep.
      pose proof (poly_span_positive dim mlen keys bits) as Hspan.
      assert (Hlength : (1 <= N.of_nat (length rows + 1))%N) by lia.
      remember (N.of_nat (length rows + 1)^2 * poly_clock_span dim mlen keys bits)%N
        as work eqn:Hwork.
      assert (Hcharge : (1 <= work)%N).
      { rewrite Hwork, N.pow_2_r. nia. }
      assert (Hhead :
        (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows <=
          poly_step_factor * work)%N).
      { rewrite Hwork, N.mul_assoc. exact Hstep. }
      change (T_poly_run X.encode X.T_encode X.eqb X.T_eqb (x :: xs) rows <=
        poly_run_factor * N.of_nat
          ((length rows + 1)^2 * (dim + mlen + 1) * (keys + bits + 1)^2 +
            fmcost dim mlen (length xs) ((length rows)^2 / 4 + length rows)
              (2 * (keys + bits) + 1)))%N.
      rewrite Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_pow.
      change (N.of_nat 2) with 2%N.
      replace (N.of_nat (length rows + 1)^2 * N.of_nat (dim + mlen + 1) *
        N.of_nat (keys + bits + 1)^2)%N with work.
      2: { rewrite Hwork. unfold poly_clock_span. ring. }
      time_unfold (@T_poly_run). time_simpl.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      fold next. clear Hwork Hstep Hrun Hfuture Hspan Hlength Hnext_rows.
      change (1 + (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows +
        T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs next) <=
        poly_run_factor * (work + N.of_nat
          (fmcost dim mlen (length xs) ((length rows)^2 / 4 + length rows)
            (2 * (keys + bits) + 1))))%N.
      clear -Hrecursive Hhead Hcharge.
      unfold poly_run_factor in Hrecursive |- *.
      nia.
  Qed.


  (** Every stored variable agrees with the trie address where it is stored. *)
  Definition poly_variable_addressed (m : ptrie X.t) : Prop :=
    forall key x, PTrieCode.get key m = Some x -> X.encode x = key.

  (** An empty variable table satisfies address agreement. *)
  Lemma poly_variable_addressed_empty : poly_variable_addressed PTrieCode.empty.
  Proof.
    intros key x Hget. rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  (** Storing a variable at its own address preserves address agreement. *)
  Lemma poly_variable_addressed_set : forall m x,
    poly_variable_addressed m ->
    poly_variable_addressed (PTrieCode.set (X.encode x) x m).
  Proof.
    intros m x Haddressed key y Hget.
    destruct (Pos.eq_dec key (X.encode x)) as [Hsame|Hother].
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Heq. now subst y.
    - rewrite PTrie.get_set_other in Hget by exact Hother. now apply Haddressed in Hget.
  Qed.

  (** Scanning a coefficient list preserves address agreement. *)
  Lemma poly_variable_terms_addressed : forall (terms : list (X.t * Z)) m,
    poly_variable_addressed m ->
    poly_variable_addressed
      (fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc) terms m).
  Proof.
    intro terms. induction terms as [|p terms IH]; intros m Haddressed; cbn [fold_left].
    - exact Haddressed.
    - apply IH. now apply poly_variable_addressed_set.
  Qed.

  (** Scanning complete rows preserves address agreement. *)
  Lemma poly_variable_rows_addressed : forall rows m,
    poly_variable_addressed m ->
    poly_variable_addressed (fold_left (fun acc r =>
      fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc)
        (lhs r) acc) rows m).
  Proof.
    intro rows. induction rows as [|r rows IH]; intros m Haddressed; cbn [fold_left].
    - exact Haddressed.
    - apply IH. now apply poly_variable_terms_addressed.
  Qed.

  (** Distinct addresses imply distinct stored variables. *)
  Lemma poly_variable_values_nodup : forall m,
    poly_variable_addressed m -> NoDup (map snd (PTrieCode.elements m)).
  Proof.
    intros m Haddressed. apply NoDup_map_inv with (f := X.encode). rewrite map_map.
    assert (Hkeys : map (fun p => X.encode (snd p)) (PTrieCode.elements m) =
      map fst (PTrieCode.elements m)).
    { apply map_ext_in. intros [key x] Hin. cbn [fst snd]. apply Haddressed.
      exact (proj1 (PTrie.elements_spec _ m key x) Hin). }
    rewrite Hkeys. apply PTrie.elements_nodup.
  Qed.

  (** A cons fold reverses its input in front of its initial accumulator. *)
  Lemma poly_variable_cons_fold : forall (xs acc : list X.t),
    fold_left (fun acc x => x :: acc) xs acc = rev xs ++ acc.
  Proof.
    intro xs. induction xs as [|x xs IH]; intro acc; cbn [fold_left rev].
    - reflexivity.
    - rewrite IH, <- app_assoc. reflexivity.
  Qed.

  (** This proof model names the actual table built by the variable collector. *)
  Definition poly_variable_table (rows : list (lcons X.t)) : ptrie X.t :=
    fold_left (fun acc r =>
      fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc)
        (lhs r) acc) rows PTrieCode.empty.

  (** The executable variable list is the reverse enumeration of the constructed table. *)
  Lemma poly_variables_shape : forall rows,
    poly_variables X.encode rows = rev (map snd (PTrieCode.elements (poly_variable_table rows))).
  Proof.
    intro rows. unfold poly_variables, poly_variable_table. rewrite PTrieT.F9_fold_values.
    rewrite (poly_fold_values_list _ _ (fun acc x => x :: acc) _ nil).
    now rewrite poly_variable_cons_fold, app_nil_r.
  Qed.

  (** Each executable elimination coordinate occurs only once. *)
  Lemma poly_variables_nodup : forall rows, NoDup (poly_variables X.encode rows).
  Proof.
    intro rows. rewrite poly_variables_shape. apply NoDup_rev.
    apply poly_variable_values_nodup. unfold poly_variable_table.
    apply poly_variable_rows_addressed. apply poly_variable_addressed_empty.
  Qed.

  (** Reading an updated variable table yields the new variable or a previous binding. *)
  Lemma poly_variable_set_origin : forall m x key y,
    PTrieCode.get key (PTrieCode.set (X.encode x) x m) = Some y ->
    y = x \/ PTrieCode.get key m = Some y.
  Proof.
    intros m x key y Hget. destruct (Pos.eq_dec key (X.encode x)) as [Hsame|Hother].
    - subst key. rewrite PTrie.get_set_same in Hget. left. injection Hget as Heq. symmetry. exact Heq.
    - rewrite PTrie.get_set_other in Hget by exact Hother. now right.
  Qed.

  (** Every variable retained after scanning terms came from those terms or the input table. *)
  Lemma poly_variable_terms_origin : forall (terms : list (X.t * Z)) m key x,
    PTrieCode.get key
      (fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc) terms m) =
      Some x -> In x (map fst terms) \/ PTrieCode.get key m = Some x.
  Proof.
    intro terms. induction terms as [|p terms IH]; intros m key x Hget;
      cbn [fold_left] in Hget.
    - now right.
    - destruct (IH _ _ _ Hget) as [Hin|Hprior].
      + left. now right.
      + destruct (poly_variable_set_origin m (fst p) key x Hprior) as [Hsame|Hbefore].
        * left. left. symmetry. exact Hsame.
        * now right.
  Qed.

  (** Every variable retained after scanning rows came from a source row or the input table. *)
  Lemma poly_variable_rows_origin : forall rows m key x,
    PTrieCode.get key (fold_left (fun acc r =>
      fold_left (fun acc p => PTrieCode.set (X.encode (fst p)) (fst p) acc)
        (lhs r) acc) rows m) = Some x ->
    (exists r, In r rows /\ In x (map fst (lhs r))) \/ PTrieCode.get key m = Some x.
  Proof.
    intro rows. induction rows as [|r rows IH]; intros m key x Hget;
      cbn [fold_left] in Hget.
    - now right.
    - destruct (IH _ _ _ Hget) as [[s [Hs Hterm]]|Hprior].
      + left. exists s. split; [now right|exact Hterm].
      + destruct (poly_variable_terms_origin (lhs r) m key x Hprior) as [Hterm|Hbefore].
        * left. exists r. split; [now left|exact Hterm].
        * now right.
  Qed.

  (** The executable variable list introduces no variable outside the raw source rows. *)
  Lemma poly_variables_support : forall rows x,
    In x (poly_variables X.encode rows) -> exists r, In r rows /\ In x (map fst (lhs r)).
  Proof.
    intros rows x Hin. rewrite poly_variables_shape in Hin.
    apply (proj2 (in_rev _ _)) in Hin.
    apply in_map_iff in Hin as [[key y] [Hsame Hin]]. cbn [snd] in Hsame. subst y.
    apply (proj1 (PTrie.elements_spec _ _ _ _)) in Hin.
    unfold poly_variable_table in Hin.
    destruct (poly_variable_rows_origin rows PTrieCode.empty key x Hin) as [Hsource|Hempty].
    - exact Hsource.
    - rewrite PTrie.get_empty in Hempty. discriminate.
  Qed.

  (** Every executable coordinate belongs to the declared source variable collection. *)
  Lemma poly_variables_in_vars_of : forall rows,
    incl (poly_variables X.encode rows) (vars_of rows).
  Proof.
    intros rows x Hx. destruct (poly_variables_support rows x Hx) as [r [Hr Hterm]].
    now apply poly_vars_of_contains with (r := r).
  Qed.

  (** The executable coordinate count fits the declared source dimension. *)
  Lemma poly_variables_count : forall rows,
    length (poly_variables X.encode rows) <= length (vars_of rows).
  Proof.
    intro rows. apply NoDup_incl_length; [apply poly_variables_nodup|].
    apply poly_variables_in_vars_of.
  Qed.

  (** Entailment coordinates use only target occurrences and declared source variables. *)
  Lemma poly_entail_variables_incl : forall P c,
    incl (poly_variables X.encode (c :: P)) (map fst (lhs c) ++ vars_of P).
  Proof.
    intros P c x Hx. destruct (poly_variables_support (c :: P) x Hx)
      as [r [[Hsame|Hr] Hterm]].
    - subst r. apply in_or_app. now left.
    - apply in_or_app. right. now apply poly_vars_of_contains with (r := r).
  Qed.

  (** The actual entailment fuel excludes the extra source-row count in the public budget. *)
  Lemma poly_entail_variables_count : forall P c,
    length (poly_variables X.encode (c :: P)) <= length (vars_of P) + length (lhs c).
  Proof.
    intros P c. assert (Hcount : length (poly_variables X.encode (c :: P)) <=
      length (map fst (lhs c) ++ vars_of P)).
    { apply NoDup_incl_length; [apply poly_variables_nodup|].
      apply poly_entail_variables_incl. }
    rewrite length_app, length_map in Hcount. lia.
  Qed.

  (** The actual number of eliminations fits the frozen public fuel. *)
  Lemma poly_entail_fuel : forall P c,
    length (poly_variables X.encode (c :: P)) <= n P + length (lhs c).
  Proof.
    intros P c. pose proof (poly_entail_variables_count P c). unfold n. lia.
  Qed.

  (** A nonempty source list leaves one extra cost stage for checking terminal candidates. *)
  Lemma poly_entail_spare_fuel : forall P c, P <> [] ->
    S (length (poly_variables X.encode (c :: P))) <= n P + length (lhs c).
  Proof.
    intros P c Hnonempty. pose proof (poly_entail_variables_count P c) as Hcount.
    unfold n. destruct P; [contradiction|]. cbn [length]. lia.
  Qed.

  (** Source rows use the fixed input dimension and a shared bit envelope. *)
  Definition poly_source_envelope (dim bits : nat) (r : lcons X.t) : Prop :=
    length (lhs r) <= dim /\ C.row_key_bits r + C.row_bits r <= bits.

  Lemma poly_source_envelope_mono : forall r dim bits dim' bits',
    poly_source_envelope dim bits r -> dim <= dim' -> bits <= bits' ->
    poly_source_envelope dim' bits' r.
  Proof.
    unfold poly_source_envelope. intros r dim bits dim' bits' [Hl Hb] HD HB. split; lia.
  Qed.

  Lemma poly_entail_source_envelopes : forall P c, normal P ->
    Forall (poly_source_envelope (n P + length (lhs c))
      (ell P + C.row_bits c + C.row_key_bits c)) (c :: P).
  Proof.
    intros P c Hnormal. constructor.
    - unfold poly_source_envelope. split; lia.
    - apply Forall_forall. intros p Hp. unfold poly_source_envelope.
      pose proof (poly_row_dimension P p Hnormal Hp) as Hlength.
      pose proof (poly_max_member _ C.row_bits 0 P p Hp) as Hbits.
      pose proof (poly_max_member _ C.row_key_bits 0 P p Hp) as Hkeys.
      unfold n, ell. split; lia.
  Qed.

  Lemma poly_lsize_envelope : forall r dim bits,
    poly_source_envelope dim bits r ->
    C.lsize r <= (dim + 1) * (bits + 1).
  Proof.
    intros r dim bits [Hlength Hbits]. unfold C.lsize.
    apply Nat.mul_le_mono; lia.
  Qed.

  Lemma poly_csize_entry_envelope : forall r m dim bits,
    poly_source_envelope dim bits r -> Z.size_nat m <= bits + 1 ->
    (length (lhs r) + 1) *
      (C.row_key_bits r + (Z.size_nat m + 1) * (C.row_bits r + 1)) <=
      3 * (dim + 1) * (bits + 1)^2.
  Proof.
    intros r m dim bits [Hlength Hbits] Hm.
    assert (Hinner : C.row_key_bits r +
      (Z.size_nat m + 1) * (C.row_bits r + 1) <= 3 * (bits + 1)^2).
    { assert (Hproduct : (Z.size_nat m + 1) * (C.row_bits r + 1) <=
        (bits + 2) * (bits + 1)) by (apply Nat.mul_le_mono; lia).
      cbn [Nat.pow]. nia. }
    eapply Nat.le_trans with (m := (dim + 1) * (3 * (bits + 1)^2)).
    - apply Nat.mul_le_mono; [lia|exact Hinner].
    - nia.
  Qed.

  Lemma poly_csize_envelope : forall P ms dim bits,
    Forall (poly_source_envelope dim bits) P ->
    Forall (fun m => Z.size_nat m <= bits + 1) ms ->
    C.csize P ms <= (length P + length ms) *
      (3 * (dim + 1) * (bits + 1)^2).
  Proof.
    intros P. induction P as [|p P IH]; intros ms dim bits HP Hms;
      destruct ms as [|m ms]; cbn [C.csize length].
    - lia.
    - assert (1 <= 3 * (dim + 1) * (bits + 1)^2) by (cbn [Nat.pow]; nia).
      nia.
    - assert (1 <= 3 * (dim + 1) * (bits + 1)^2) by (cbn [Nat.pow]; nia).
      nia.
    - inversion HP as [|? ? Hp HP']; subst.
      inversion Hms as [|? ? Hm Hms']; subst.
      pose proof (IH ms dim bits HP' Hms') as Htail.
      pose proof (poly_csize_entry_envelope p m dim bits Hp Hm) as Hhead.
      nia.
  Qed.

  Lemma poly_cbits_envelope : forall P ms dim bits,
    Forall (poly_source_envelope dim bits) P ->
    Forall (fun m => Z.size_nat m <= bits + 1) ms ->
    C.cbits P ms <= 2 * bits + length P + 2.
  Proof.
    intros P ms dim bits HP Hms. unfold C.cbits.
    assert (Hmax : fold_right Nat.max 0
      (map (fun pm => Z.size_nat (snd pm) + C.row_bits (fst pm))
        (combine P ms)) <= 2 * bits + 1).
    { apply poly_max_bound; [lia|]. apply Forall_forall.
      intros [p m] Hin. cbn [fst snd].
      pose proof (in_combine_l _ _ _ _ Hin) as Hp.
      pose proof (in_combine_r _ _ _ _ Hin) as Hm.
      destruct (proj1 (Forall_forall _ _) HP p Hp) as [_ Hrow].
      pose proof (proj1 (Forall_forall _ _) Hms m Hm) as Hwidth.
      change (Z.size_nat m <= bits + 1) in Hwidth. lia. }
    assert (Hlog : Nat.log2 (length P) <= length P).
    { apply Nat.log2_le_lin. lia. }
    lia.
  Qed.

  Lemma poly_checker_measure_envelope : forall P c ms sc dim mlen bits,
    Forall (poly_source_envelope dim bits) (c :: P) ->
    length P <= mlen -> length ms <= mlen ->
    Forall (fun m => Z.size_nat m <= bits + 1) ms ->
    Z.size_nat sc <= bits + 1 ->
    C.csize P ms + (Z.size_nat sc + 1) *
      (C.lsize c + C.cbits P ms + 1) <=
      8 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2.
  Proof.
    intros P c ms sc dim mlen bits Hsource HP Hms Hmult Hscale.
    inversion Hsource as [|? ? Hc Hrows]; subst.
    pose proof (poly_csize_envelope P ms dim bits Hrows Hmult) as Hsize.
    pose proof (poly_cbits_envelope P ms dim bits Hrows Hmult) as Hwidth.
    pose proof (poly_lsize_envelope c dim bits Hc) as Hconclusion.
    assert (Hsmall : C.lsize c + C.cbits P ms + 1 <=
      4 * (dim + mlen + 1) * (bits + 1)) by nia.
    assert (Hscaled : (Z.size_nat sc + 1) *
      (C.lsize c + C.cbits P ms + 1) <=
      8 * (dim + mlen + 1) * (bits + 1)^2).
    { eapply Nat.le_trans with (m :=
        2 * (bits + 1) * (4 * (dim + mlen + 1) * (bits + 1))).
      - apply Nat.mul_le_mono; [lia|exact Hsmall].
      - cbn [Nat.pow]. nia. }
    assert (Hcert : C.csize P ms <=
      6 * mlen * (dim + mlen + 1) * (bits + 1)^2).
    { eapply Nat.le_trans; [exact Hsize|].
      eapply Nat.le_trans with (m := 2 * mlen * (3 * (dim + 1) * (bits + 1)^2)).
      - apply Nat.mul_le_mono; [lia|reflexivity].
      - assert (Hdim : dim + 1 <= dim + mlen + 1) by lia.
        apply (Nat.mul_le_mono_r _ _ (6 * mlen * (bits + 1)^2)) in Hdim. nia. }
    clear Hsize Hwidth Hconclusion Hsmall Hscale.
    set (mass := (dim + mlen + 1) * (bits + 1)^2) in *.
    assert (Hcert' : C.csize P ms <= 6 * mlen * mass) by (unfold mass; nia).
    assert (Hscaled' : (Z.size_nat sc + 1) *
      (C.lsize c + C.cbits P ms + 1) <= 8 * mass) by (unfold mass; nia).
    replace (8 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2)
      with (8 * (mlen + 1) * mass) by (unfold mass; nia).
    clear -Hcert' Hscaled'. nia.
  Qed.

  Lemma poly_empty_measure_envelope : forall P ms dim mlen bits,
    Forall (poly_source_envelope dim bits) P ->
    length P <= mlen -> length ms <= mlen ->
    Forall (fun m => Z.size_nat m <= bits + 1) ms ->
    C.csize P ms + 1 <=
      8 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2.
  Proof.
    intros P ms dim mlen bits Hsource HP Hms Hmult.
    pose proof (poly_csize_envelope P ms dim bits Hsource Hmult) as Hsize.
    assert (Hcert : C.csize P ms <=
      6 * mlen * (dim + mlen + 1) * (bits + 1)^2).
    { eapply Nat.le_trans; [exact Hsize|].
      eapply Nat.le_trans with (m := 2 * mlen * (3 * (dim + 1) * (bits + 1)^2)).
      - apply Nat.mul_le_mono; [lia|reflexivity].
      - assert (Hdim : dim + 1 <= dim + mlen + 1) by lia.
        apply (Nat.mul_le_mono_r _ _ (6 * mlen * (bits + 1)^2)) in Hdim. nia. }
    set (mass := (dim + mlen + 1) * (bits + 1)^2).
    assert (Hmass : 1 <= mass) by (unfold mass; cbn [Nat.pow]; nia).
    assert (Hcert' : C.csize P ms <= 6 * mlen * mass) by (unfold mass; nia).
    replace (8 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2)
      with (8 * (mlen + 1) * mass) by (unfold mass; nia).
    clear -Hcert' Hmass. nia.
  Qed.

  Lemma T_poly_contradiction_bounded : forall r bits,
    C.row_bits (poly_constraint r) <= bits ->
    (T_poly_contradiction r <= 24 * N.of_nat (bits + 1))%N.
  Proof.
    intros r bits Hbits.
    pose proof (poly_row_rhs_bits (poly_constraint r)) as Hrhs.
    pose proof (T_poly_zero_test (rhs (poly_constraint r))) as Heq.
    pose proof (Z.T_ltb_le (rhs (poly_constraint r)) 0) as Hlt.
    pose proof (Z.T_leb_le (rhs (poly_constraint r)) 0) as Hle.
    time_unfold (@T_poly_contradiction).
    destruct (lhs (poly_constraint r)); [destruct (lrel (poly_constraint r))|];
      time_simpl; nia.
  Qed.

  Definition poly_canonical_eq_entry (pm : lcons X.t * Z) : bool :=
    match lrel (fst pm) with REq => true | RLe => Z.eqb (snd pm) 0 end.
  TimeFun poly_canonical_eq_entry.

  Lemma T_poly_canonical_eq_entry_bounded : forall pm,
    (T_poly_canonical_eq_entry pm <= 6)%N.
  Proof.
    intro pm. pose proof (T_poly_zero_test (snd pm)) as Hzero.
    time_unfold T_poly_canonical_eq_entry. destruct (lrel (fst pm)); time_simpl; lia.
  Qed.

  Lemma T_poly_source_equal_bounded : forall P ms,
    (T_poly_source_equal P ms <= 12 * N.of_nat (length P + 1))%N.
  Proof.
    intros P ms. pose proof (List.T_combine_le P ms) as Hcombine.
    pose proof (List.T_forallb_le poly_canonical_eq_entry T_poly_canonical_eq_entry 6
      (List.combine P ms) T_poly_canonical_eq_entry_bounded) as Hscan.
    assert (Hlength : length (List.combine P ms) <= length P).
    { rewrite length_combine. apply Nat.le_min_l. }
    time_unfold T_poly_source_equal. time_simpl.
    lazymatch goal with
    | |- context [List.T_forallb ?f ?Tf (List.combine P ms)] =>
        change f with poly_canonical_eq_entry;
        change Tf with T_poly_canonical_eq_entry
    end.
    lia.
  Qed.

  Lemma T_poly_canonical_scale_bounded : forall sc,
    (T_poly_canonical_scale sc <= 3)%N.
  Proof.
    intro sc. pose proof (T_poly_zero_test sc).
    time_unfold T_poly_canonical_scale. time_simpl. lia.
  Qed.

  Lemma poly_positive_zero_clock : forall sc, (Z.T_ltb 0 sc <= 4)%N.
  Proof.
    intro sc. pose proof (Z.T_ltb_le 0 sc) as Hcompare.
    exact Hcompare.
  Qed.

  Lemma T_poly_canonical_guard_bounded : forall P c r sc ms,
    (T_poly_canonical_guard P c r sc ms <= 32 * N.of_nat (length P + 1))%N.
  Proof.
    intros P c r sc ms.
    pose proof (T_poly_zero_test sc) as Hzero.
    pose proof (poly_positive_zero_clock sc) as Hpositive.
    pose proof (T_poly_zero_test (rhs (poly_constraint r))) as Hrhs.
    pose proof (T_poly_source_equal_bounded P ms) as Hequalities.
    time_unfold T_poly_canonical_guard. destruct (lrel c); time_simpl; lia.
  Qed.

  Definition poly_candidate_factor : N := (8 * C.c_lc + 80)%N.

  Lemma T_candidate_bounded : forall P c r dim mlen bits,
    Forall (poly_source_envelope dim bits) (c :: P) ->
    length P <= mlen -> C.row_bits (poly_constraint r) <= bits ->
    length (poly_multipliers r) <= mlen ->
    Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers r) ->
    (T_candidate P c r <= poly_candidate_factor * N.of_nat (mlen + 1) *
      N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros P c r dim mlen bits Hsource HP Hrow Hlength Hmult.
    pose proof (T_poly_contradiction_bounded r bits Hrow) as Hcontradiction.
    set (work := (N.of_nat (mlen + 1) * N.of_nat (dim + mlen + 1) *
      N.of_nat (bits + 1)^2)%N).
    assert (Hwork : (N.of_nat (bits + 1) <= work)%N).
    { assert (Hsquare : (N.of_nat (bits + 1) <= N.of_nat (bits + 1)^2)%N)
        by (rewrite N.pow_2_r; nia).
      eapply N.le_trans; [exact Hsquare|]. unfold work.
      rewrite <- (N.mul_1_l (N.of_nat (bits + 1)^2)) at 1.
      apply N.mul_le_mono_r. nia. }
    assert (Hcount_work : (N.of_nat (mlen + 1) <= work)%N).
    { replace work with (N.of_nat (mlen + 1) *
        (N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2))%N by (unfold work; ring).
      rewrite <- (N.mul_1_r (N.of_nat (mlen + 1))) at 1.
      apply N.mul_le_mono_l.
      change (1 * 1 <= N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N.
      apply N.mul_le_mono; [lia|rewrite N.pow_2_r; nia]. }
    replace (poly_candidate_factor * N.of_nat (mlen + 1) *
      N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N
      with (poly_candidate_factor * work)%N by (unfold work; ring).
    time_unfold T_candidate.
    destruct (poly_contradiction r);
      [|unfold poly_candidate_factor; time_simpl; clearbody work; nia].
    destruct (poly_multipliers r) as [|sc ms] eqn:Hvalues;
      [unfold poly_candidate_factor; time_simpl; clearbody work; nia|].
    cbn [length] in Hlength. inversion Hmult as [|? ? Hsc Hms]; subst.
    assert (Htail : length ms <= mlen) by lia.
    pose proof (T_poly_canonical_guard_bounded P c r sc ms) as Hguard.
    assert (Hguard_total : (T_poly_canonical_guard P c r sc ms <= 32 * work)%N).
    { eapply N.le_trans; [exact Hguard|]. apply N.mul_le_mono_l.
      eapply N.le_trans; [|exact Hcount_work]. lia. }
    pose proof (T_poly_canonical_scale_bounded sc) as Hscale_clock.
    set (sc' := poly_canonical_scale sc).
    assert (Hscale : Z.size_nat sc' <= bits + 1).
    { unfold sc', poly_canonical_scale. destruct (Z.eqb sc 0);
        [change (1 <= bits + 1); lia|exact Hsc]. }
    pose proof (poly_checker_measure_envelope P c ms sc' dim mlen bits
      Hsource HP Htail Hms Hscale) as Hcheck_size.
    pose proof (C.T_check_entails_le P c (Cert ms sc' false)) as Hcheck.
    cbn [mults scale] in Hcheck.
    assert (Hcheck_clock : (C.T_check_entails P c (Cert ms sc' false) <=
      8 * C.c_lc * work)%N).
    { eapply N.le_trans; [exact Hcheck|]. unfold work.
      assert (Htransport : (N.of_nat (C.csize P ms + (Z.size_nat sc' + 1) *
        (C.lsize c + C.cbits P ms + 1)) <=
        N.of_nat (8 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2))%N) by lia.
      rewrite !Nat2N.inj_mul, Nat2N.inj_pow in Htransport.
      change (N.of_nat 2) with 2%N in Htransport.
      change (N.of_nat 8) with 8%N in Htransport.
      apply N.mul_le_mono_l with (p := C.c_lc) in Htransport. nia. }
    fold sc'. destruct (poly_canonical_guard P c r sc ms);
      unfold poly_candidate_factor; time_simpl.
    all: clear -Hcontradiction Hguard_total Hscale_clock Hcheck_clock Hwork;
      clearbody work; nia.
  Qed.

  Lemma T_find_certificate_members : forall P c rows k,
    (forall r, In r rows -> (T_candidate P c r <= k)%N) ->
    (T_find_certificate P c rows <= (k + 1) * N.of_nat (length rows) + 1)%N.
  Proof.
    intros P c rows. induction rows as [|r rows IH]; intros k Hrows.
    - time_unfold T_find_certificate. cbn [length]. lia.
    - pose proof (Hrows r (or_introl eq_refl)) as Hhead.
      specialize (IH k (fun q Hq => Hrows q (or_intror Hq))).
      time_unfold T_find_certificate. destruct (candidate P c r);
        cbn [length]; rewrite Nat2N.inj_succ; time_simpl; nia.
  Qed.

  Definition poly_terminal_factor : N := (8 * C.c_lc + 88)%N.

  Lemma T_find_certificate_bounded : forall P c rows count dim mlen bits,
    Forall (poly_source_envelope dim bits) (c :: P) ->
    length P <= mlen -> mlen <= count -> length rows <= count ->
    Forall (fun r => C.row_bits (poly_constraint r) <= bits /\
      length (poly_multipliers r) <= mlen /\
      Forall (fun m => Z.size_nat m <= bits + 1) (poly_multipliers r)) rows ->
    (T_find_certificate P c rows <= poly_terminal_factor * N.of_nat (count + 1)^2 *
      N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros P c rows count dim mlen bits Hsource HP HM HR Hrows.
    pose proof (T_find_certificate_members P c rows
      (poly_candidate_factor * N.of_nat (mlen + 1) *
        N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N) as Hscan.
    specialize (Hscan ltac:(intros r Hr;
      destruct (proj1 (Forall_forall _ _) Hrows r Hr) as [Hb [Hl Hm]];
      exact (T_candidate_bounded P c r dim mlen bits Hsource HP Hb Hl Hm))).
    set (span := (N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N).
    assert (Hspan : (1 <= span)%N) by (unfold span; rewrite N.pow_2_r; nia).
    assert (Hwork : (N.of_nat (mlen + 1) * span <=
      N.of_nat (count + 1) * span)%N) by (apply N.mul_le_mono_r; lia).
    assert (Hcount : (N.of_nat (length rows) <= N.of_nat (count + 1))%N) by lia.
    assert (Hscaled : ((poly_candidate_factor * N.of_nat (mlen + 1) * span + 1) *
      N.of_nat (length rows) <=
      (poly_candidate_factor + 1) * N.of_nat (count + 1)^2 * span)%N).
    { eapply N.le_trans with (m :=
        ((poly_candidate_factor + 1) * N.of_nat (count + 1) * span *
          N.of_nat (count + 1))%N).
      - apply N.mul_le_mono; [|exact Hcount].
        assert (1 <= N.of_nat (count + 1) * span)%N by nia.
        pose proof (N.mul_le_mono_l _ _ poly_candidate_factor Hwork). nia.
      - rewrite N.pow_2_r. ring_simplify. lia. }
    unfold poly_terminal_factor, poly_candidate_factor in *.
    replace ((8 * C.c_lc + 88) * N.of_nat (count + 1)^2 *
      N.of_nat (dim + mlen + 1) * N.of_nat (bits + 1)^2)%N
      with ((8 * C.c_lc + 88) * N.of_nat (count + 1)^2 * span)%N
      by (unfold span; ring).
    assert (Hscan' : (T_find_certificate P c rows <=
      ((8 * C.c_lc + 80) * N.of_nat (mlen + 1) * span + 1) *
        N.of_nat (length rows) + 1)%N) by (unfold span; nia).
    assert (Hpositive : (1 <= N.of_nat (count + 1)^2 * span)%N)
      by (clear -Hspan; change (1 * 1 <= N.of_nat (count + 1)^2 * span)%N;
        apply N.mul_le_mono; [rewrite N.pow_2_r; nia|exact Hspan]).
    repeat rewrite <- N.mul_assoc in Hscan'.
    repeat rewrite <- N.mul_assoc in Hscaled.
    repeat rewrite <- N.mul_assoc.
    set (total := (N.of_nat (count + 1)^2 * span)%N) in *.
    clear -Hscan' Hscaled Hpositive. clearbody total.
    eapply N.le_trans; [exact Hscan'|].
    eapply N.le_trans; [apply N.add_le_mono_r; exact Hscaled|].
    clear -Hpositive. rewrite !N.mul_add_distr_r. lia.
  Qed.

  (** A lone inequality cannot form an opposite-sign pair with itself. *)
  Lemma poly_step_single_inequality : forall x r,
    lrel (poly_constraint r) = RLe ->
    poly_step X.encode X.eqb x [r] = [r] \/
    poly_step X.encode X.eqb x [r] = [].
  Proof.
    intros x r Hrel. unfold poly_step.
    assert (Hfind : find (poly_pivot X.eqb x) [r] = None).
    { cbn [find]. unfold poly_pivot. rewrite Hrel. reflexivity. }
    rewrite Hfind. cbn [filter].
    set (a := poly_coefficient X.eqb x (poly_constraint r)).
    destruct (0 <? a)%Z eqn:Hpos; destruct (a <? 0)%Z eqn:Hneg;
      destruct (Z.eqb a 0) eqn:Hzero; cbn [flat_map map app];
      try (left; reflexivity); try (right; reflexivity);
      try apply Z.ltb_lt in Hpos; try apply Z.ltb_ge in Hpos;
      try apply Z.ltb_lt in Hneg; try apply Z.ltb_ge in Hneg;
      try apply Z.eqb_eq in Hzero; try apply Z.eqb_neq in Hzero;
      exfalso; lia.
  Qed.

  Lemma poly_run_empty_rows : forall xs,
    poly_run X.encode X.eqb xs [] = [].
  Proof.
    induction xs as [|x xs IH]; cbn [poly_run]; [reflexivity|].
    change (poly_run X.encode X.eqb xs [] = []). exact IH.
  Qed.

  Lemma poly_run_single_inequality : forall xs r,
    lrel (poly_constraint r) = RLe ->
    poly_run X.encode X.eqb xs [r] = [r] \/
    poly_run X.encode X.eqb xs [r] = [].
  Proof.
    intros xs. induction xs as [|x xs IH]; intros r Hrel.
    - left. reflexivity.
    - cbn [poly_run]. destruct (poly_step_single_inequality x r Hrel) as [Hkeep | Hdrop].
      + rewrite Hkeep. exact (IH r Hrel).
      + rewrite Hdrop. right. apply poly_run_empty_rows.
  Qed.

  Lemma poly_entail_empty_units : forall xs c,
    Forall (fun r => poly_multipliers r = [1%Z])
      (poly_run X.encode X.eqb xs (poly_initial X.encode [(poly_negate c, true)])).
  Proof.
    intros xs c.
    change (Forall (fun r => poly_multipliers r = [1%Z])
      (poly_run X.encode X.eqb xs
        [PolyRow X.t (poly_normal_row X.encode (poly_negate c)) [1%Z] true])).
    destruct (poly_run_single_inequality xs
      (PolyRow X.t (poly_normal_row X.encode (poly_negate c)) [1%Z] true)
      eq_refl) as [Hkeep | Hdrop]; rewrite ?Hkeep, ?Hdrop; repeat constructor.
  Qed.

  Lemma T_candidate_empty_bounded : forall c r dim bits,
    poly_source_envelope dim bits c -> C.row_bits (poly_constraint r) <= bits ->
    poly_multipliers r = [1%Z] ->
    (T_candidate [] c r <= poly_candidate_factor *
      N.of_nat (dim + 2) * N.of_nat (bits + 1))%N.
  Proof.
    intros c r dim bits Hsource Hrow Hmult.
    pose proof (poly_lsize_envelope c dim bits Hsource) as Hconclusion.
    pose proof (T_poly_contradiction_bounded r bits Hrow) as Hcontradiction.
    pose proof (T_poly_canonical_guard_bounded [] c r 1 []) as Hguard.
    change (T_poly_canonical_guard [] c r 1 [] <= 32)%N in Hguard.
    pose proof (T_poly_canonical_scale_bounded 1) as Hscale.
    set (work := (N.of_nat (dim + 2) * N.of_nat (bits + 1))%N).
    assert (Hwork : (N.of_nat (bits + 1) <= work)%N) by (unfold work; nia).
    pose proof (C.T_check_entails_le [] c (Cert [] 1 false)) as Hcheck.
    change (C.T_check_entails [] c (Cert [] 1 false) <=
      C.c_lc * N.of_nat (2 * (C.lsize c + 1 + 1)))%N in Hcheck.
    replace (C.lsize c + 1 + 1) with (C.lsize c + 2) in Hcheck by lia.
    assert (Hcheck_clock : (C.T_check_entails [] c (Cert [] 1 false) <=
      4 * C.c_lc * work)%N).
    { eapply N.le_trans; [exact Hcheck|].
      assert (Hsize : 2 * (C.lsize c + 2) <= 4 * (dim + 2) * (bits + 1)) by nia.
      assert (Htransport : (N.of_nat (2 * (C.lsize c + 2)) <=
        N.of_nat (4 * (dim + 2) * (bits + 1)))%N) by lia.
      rewrite !Nat2N.inj_mul in Htransport. unfold work.
      apply N.mul_le_mono_l with (p := C.c_lc) in Htransport. nia. }
    time_unfold T_candidate. destruct (poly_contradiction r); [rewrite Hmult|];
      unfold poly_candidate_factor; time_simpl.
    all: replace ((8 * C.c_lc + 80) * N.of_nat (dim + 2) * N.of_nat (bits + 1))%N
      with ((8 * C.c_lc + 80) * work)%N by (unfold work; ring).
    all: try change (poly_canonical_scale 1) with 1%Z.
    all: try (destruct (poly_canonical_guard [] c r 1 []); time_simpl).
    all: clear -Hcontradiction Hguard Hscale Hcheck_clock Hwork; clearbody work; nia.
  Qed.

  Lemma T_find_certificate_empty_bounded : forall c rows count dim bits,
    poly_source_envelope dim bits c -> length rows <= count ->
    Forall (fun r => C.row_bits (poly_constraint r) <= bits /\
      poly_multipliers r = [1%Z]) rows ->
    (T_find_certificate [] c rows <= poly_terminal_factor * N.of_nat (count + 1) *
      N.of_nat (dim + 2) * N.of_nat (bits + 1))%N.
  Proof.
    intros c rows count dim bits Hsource Hlength Hrows.
    pose proof (T_find_certificate_members [] c rows
      (poly_candidate_factor * N.of_nat (dim + 2) * N.of_nat (bits + 1))%N) as Hscan.
    specialize (Hscan ltac:(intros r Hr;
      destruct (proj1 (Forall_forall _ _) Hrows r Hr) as [Hb Hm];
      exact (T_candidate_empty_bounded c r dim bits Hsource Hb Hm))).
    set (span := (N.of_nat (dim + 2) * N.of_nat (bits + 1))%N).
    assert (Hspan : (1 <= span)%N) by (unfold span; nia).
    assert (Hcount : (N.of_nat (length rows) <= N.of_nat (count + 1))%N) by lia.
    assert (Hscaled : ((poly_candidate_factor * span + 1) * N.of_nat (length rows) <=
      (poly_candidate_factor + 1) * N.of_nat (count + 1) * span)%N).
    { eapply N.le_trans with (m := ((poly_candidate_factor + 1) * span *
        N.of_nat (count + 1))%N).
      - apply N.mul_le_mono; [nia|exact Hcount].
      - nia. }
    unfold poly_terminal_factor, poly_candidate_factor in *.
    replace ((8 * C.c_lc + 88) * N.of_nat (count + 1) *
      N.of_nat (dim + 2) * N.of_nat (bits + 1))%N
      with ((8 * C.c_lc + 88) * N.of_nat (count + 1) * span)%N by (unfold span; ring).
    assert (Hscan' : (T_find_certificate [] c rows <=
      ((8 * C.c_lc + 80) * span + 1) * N.of_nat (length rows) + 1)%N)
      by (unfold span; nia).
    assert (Hpositive : (1 <= N.of_nat (count + 1) * span)%N)
      by (clear -Hspan; change (1 * 1 <= N.of_nat (count + 1) * span)%N;
        apply N.mul_le_mono; [lia|exact Hspan]).
    repeat rewrite <- N.mul_assoc in Hscan'.
    repeat rewrite <- N.mul_assoc in Hscaled.
    repeat rewrite <- N.mul_assoc.
    set (total := (N.of_nat (count + 1) * span)%N) in *.
    clear -Hscan' Hscaled Hpositive. clearbody total.
    eapply N.le_trans; [exact Hscan'|].
    eapply N.le_trans; [apply N.add_le_mono_r; exact Hscaled|].
    clear -Hpositive. rewrite !N.mul_add_distr_r. lia.
  Qed.

  (** A linear traversal fits a larger count and positive per-entry work charge. *)
  Lemma poly_clock_linear_count_bound : forall factor delta rows count work,
    (rows + 1 <= count)%N -> (1 <= work)%N ->
    ((factor * work + delta) * rows + 1 <=
      (factor + delta + 1) * count * work)%N.
  Proof.
    intros factor delta rows count work Hcount Hwork.
    assert (Hfactor : (factor * work + delta <= (factor + delta) * work)%N).
    { rewrite N.mul_add_distr_r. apply N.add_le_mono_l.
      rewrite <- (N.mul_1_r delta) at 1. now apply N.mul_le_mono_l. }
    assert (Hrows : (rows <= count)%N) by lia.
    pose proof (N.mul_le_mono _ _ _ _ Hfactor Hrows) as Hproduct.
    assert (Hmass : (1 <= count * work)%N).
    { change (1 * 1 <= count * work)%N. apply N.mul_le_mono; [lia|exact Hwork]. }
    replace ((factor + delta + 1) * count * work)%N with
      (((factor + delta) * work) * count + count * work)%N by ring.
    now apply N.add_le_mono.
  Qed.

  (** A fold charges only the callback on elements it actually visits. *)
  Lemma poly_T_fold_left_members : forall (A B : Type) (f : B -> A -> B)
      (T_f : B -> A -> N) k xs b,
    (forall acc x, In x xs -> (T_f acc x <= k)%N) ->
    (List.T_fold_left f T_f xs b <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f k xs. induction xs as [|x xs IH]; intros b Hcallback.
    - time_unfold List.T_fold_left. cbn [length]. lia.
    - pose proof (Hcallback b x (or_introl eq_refl)) as Hhead.
      specialize (IH (f b x) (fun acc y Hy => Hcallback acc y (or_intror Hy))).
      time_unfold List.T_fold_left. cbn [length]. time_simpl. nia.
  Qed.

  (** This named body matches the native variable collector's inner closure. *)
  Definition poly_variable_insert (m : ptrie X.t) (p : X.t * Z) : ptrie X.t :=
    PTrieCode.set (X.encode (fst p)) (fst p) m.

  TimeFun poly_variable_insert.

  (** This named body matches the native variable collector's row closure. *)
  Definition poly_variable_scan (m : ptrie X.t) (r : lcons X.t) : ptrie X.t :=
    fold_left poly_variable_insert (lhs r) m.

  TimeFun poly_variable_scan.

  Definition poly_variable_insert_factor : N := (X.c_key + PTrieT.c_trie + 8)%N.

  (** Variable insertion pays for one encoding and one trie path. *)
  Lemma T_poly_variable_insert_bounded : forall m p keys,
    Pos.size_nat (X.encode (fst p)) <= keys ->
    (T_poly_variable_insert m p <=
      poly_variable_insert_factor * N.of_nat (keys + 1))%N.
  Proof.
    intros m p keys Hkeys.
    pose proof (X.T_encode_le (fst p)) as Hencode.
    pose proof (PTrieT.T_set_le X.t (X.encode (fst p)) (fst p) m) as Hset.
    time_unfold T_poly_variable_insert.
    unfold poly_variable_insert_factor, X.bits in *. time_simpl. nia.
  Qed.

  (** A row key maximum bounds every key visited during variable collection. *)
  Lemma poly_variable_row_keys : forall r keys,
    C.row_key_bits r <= keys ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) (lhs r).
  Proof.
    intros r keys Hkeys. apply Forall_forall. intros p Hp.
    pose proof (poly_row_key_member r p Hp). lia.
  Qed.

  (** Each insertion allocates at most its key length in trie nodes. *)
  Lemma poly_variable_terms_nodes : forall xs m keys,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs ->
    PTrie.nodes (fold_left poly_variable_insert xs m) <=
      PTrie.nodes m + length xs * keys.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys Hkeys; cbn [fold_left length].
    - lia.
    - inversion Hkeys as [|q qs Hp Htail]; subst q qs.
      specialize (IH (poly_variable_insert m p) keys Htail).
      pose proof (PTrie.nodes_set X.t (X.encode (fst p)) (fst p) m) as Hset.
      change (PTrie.nodes (poly_variable_insert m p) <=
        PTrie.nodes m + Pos.size_nat (X.encode (fst p))) in Hset. nia.
  Qed.

  (** All source rows allocate at most their entry count times the key width. *)
  Lemma poly_variable_rows_nodes : forall rows m dim keys,
    Forall (fun r => length (lhs r) <= dim /\ C.row_key_bits r <= keys) rows ->
    PTrie.nodes (fold_left poly_variable_scan rows m) <=
      PTrie.nodes m + length rows * dim * keys.
  Proof.
    intro rows. induction rows as [|r rows IH]; intros m dim keys Hrows;
      cbn [fold_left length].
    - lia.
    - inversion Hrows as [|p ps [Hd Hk] Htail]; subst p ps.
      specialize (IH (poly_variable_scan m r) dim keys Htail).
      pose proof (poly_variable_terms_nodes (lhs r) m keys
        (poly_variable_row_keys r keys Hk)) as Hrow.
      change (PTrie.nodes (poly_variable_scan m r) <=
        PTrie.nodes m + length (lhs r) * keys) in Hrow. nia.
  Qed.

  Definition poly_variable_scan_factor : N := (poly_variable_insert_factor + 8)%N.

  (** Scanning one row is linear in its coefficient count and key width. *)
  Lemma T_poly_variable_scan_bounded : forall m r dim keys,
    length (lhs r) <= dim -> C.row_key_bits r <= keys ->
    (T_poly_variable_scan m r <=
      poly_variable_scan_factor * N.of_nat (dim + 1) * N.of_nat (keys + 1))%N.
  Proof.
    intros m r dim keys Hdim Hkeys.
    pose proof (poly_T_fold_left_members _ _ poly_variable_insert T_poly_variable_insert
      (poly_variable_insert_factor * N.of_nat (keys + 1))%N (lhs r) m
      ltac:(intros acc p Hp; apply T_poly_variable_insert_bounded;
        pose proof (poly_row_key_member r p Hp); lia)) as Hfold.
    assert (Hwidth : (1 <= N.of_nat (keys + 1))%N) by lia.
    time_unfold T_poly_variable_scan.
    change (fun acc p => T_poly_variable_insert acc p) with T_poly_variable_insert.
    unfold poly_variable_scan_factor. time_simpl. nia.
  Qed.

  Definition poly_variables_factor : N :=
    (poly_variable_scan_factor + 4 * PTrieT.k_fold + 16)%N.

  (** The actual variable collector charges its source scan and trie enumeration. *)
  Lemma T_poly_variables_bounded : forall rows dim keys,
    Forall (fun r => length (lhs r) <= dim /\ C.row_key_bits r <= keys) rows ->
    (T_poly_variables X.encode X.T_encode rows <=
      poly_variables_factor * N.of_nat (length rows + 1) *
        N.of_nat (dim + 1) * N.of_nat (keys + 1))%N.
  Proof.
    intros rows dim keys Hrows.
    set (tr := fold_left poly_variable_scan rows PTrieCode.empty).
    set (entry_work := (N.of_nat (dim + 1) * N.of_nat (keys + 1))%N).
    set (work := (N.of_nat (length rows + 1) * entry_work)%N).
    assert (Hentry : (1 <= entry_work)%N).
    { unfold entry_work. change (1 * 1 <= N.of_nat (dim + 1) * N.of_nat (keys + 1))%N.
      apply N.mul_le_mono; lia. }
    assert (Hwork : (1 <= work)%N).
    { unfold work. change (1 * 1 <= N.of_nat (length rows + 1) * entry_work)%N.
      apply N.mul_le_mono; [lia|exact Hentry]. }
    pose proof (poly_T_fold_left_members _ _ poly_variable_scan T_poly_variable_scan
      (poly_variable_scan_factor * entry_work)%N rows PTrieCode.empty
      ltac:(intros m r Hr; destruct (proj1 (Forall_forall _ _) Hrows r Hr) as [Hd Hk];
        unfold entry_work; rewrite N.mul_assoc; now apply T_poly_variable_scan_bounded)) as Hscan.
    pose proof (poly_clock_linear_count_bound poly_variable_scan_factor 1
      (N.of_nat (length rows)) (N.of_nat (length rows + 1)) entry_work ltac:(lia) Hentry)
      as Hscan_work.
    assert (Hscan_total : (List.T_fold_left poly_variable_scan T_poly_variable_scan
      rows PTrieCode.empty <= (poly_variable_scan_factor + 2) * work)%N).
    { unfold work. eapply N.le_trans; [exact Hscan|].
      replace (poly_variable_scan_factor + 2)%N with
        (poly_variable_scan_factor + 1 + 1)%N by lia.
      rewrite N.mul_assoc. exact Hscan_work. }
    pose proof (poly_variable_rows_nodes rows PTrieCode.empty dim keys Hrows) as Hnodes.
    change (PTrie.nodes tr <= length rows * dim * keys) in Hnodes.
    assert (Hnodes_total : (N.of_nat (PTrie.nodes tr + 1) <= work)%N).
    { assert (Hnat : PTrie.nodes tr + 1 <=
        (length rows + 1) * (dim + 1) * (keys + 1)) by nia.
      unfold work, entry_work. rewrite N.mul_assoc, <- !Nat2N.inj_mul.
      clear -Hnat. lia. }
    pose proof (PTrieT.T9_fold_values X.t (list X.t) (fun acc x => x :: acc)
      (fun _ _ => 1%N) tr nil 1 (fun _ _ => N.le_refl 1%N)) as Hfold.
    assert (Hfold_total : (PTrieT.T_fold_values (fun acc x => x :: acc)
      (fun _ _ => 1%N) tr nil <= 2 * PTrieT.k_fold * work)%N).
    { eapply N.le_trans; [exact Hfold|].
      pose proof (N.mul_le_mono_l _ _ (2 * PTrieT.k_fold)%N Hnodes_total). nia. }
    time_unfold (@T_poly_variables). time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    change (1 + (List.T_fold_left poly_variable_scan T_poly_variable_scan
      rows PTrieCode.empty + PTrieT.T_fold_values (fun acc x => x :: acc)
        (fun _ _ => 1%N) tr nil) <=
      poly_variables_factor * N.of_nat (length rows + 1) *
        N.of_nat (dim + 1) * N.of_nat (keys + 1))%N.
    replace (poly_variables_factor * N.of_nat (length rows + 1) *
      N.of_nat (dim + 1) * N.of_nat (keys + 1))%N with
      (poly_variables_factor * work)%N by (unfold work, entry_work; ring).
    unfold poly_variables_factor.
    clear -Hscan_total Hfold_total Hwork. clearbody work. nia.
  Qed.

  (** Negation leaves the variable keys and arithmetic widths unchanged. *)
  Lemma poly_negate_row_key_bits : forall r,
    C.row_key_bits (poly_negate r) = C.row_key_bits r.
  Proof.
    intro r. unfold C.row_key_bits. cbn [poly_negate lhs].
    unfold poly_scale_coef. rewrite map_map. reflexivity.
  Qed.

  Lemma poly_negate_row_bits : forall r,
    C.row_bits (poly_negate r) = C.row_bits r.
  Proof.
    intro r. unfold C.row_bits. cbn [poly_negate lhs rhs].
    rewrite poly_size_opp. unfold poly_scale_coef. rewrite map_map.
    f_equal. apply map_ext. intros [x a]. cbn [fst snd].
    replace (-1 * a)%Z with (-a)%Z by ring. apply poly_size_opp.
  Qed.

  Lemma poly_negate_row_length : forall r : lcons X.t,
    length (lhs (poly_negate r)) = length (lhs r).
  Proof.
    intro r. cbn [poly_negate lhs]. unfold poly_scale_coef. apply length_map.
  Qed.

  Lemma poly_negate_row_normal : forall r : lcons X.t,
    NoDup (map fst (lhs r)) -> NoDup (map fst (lhs (poly_negate r))).
  Proof.
    intros r Hr. cbn [poly_negate lhs]. now rewrite poly_scale_coef_keys.
  Qed.

  (** Constructing the complement is linear in the target entries and their widths. *)
  Lemma T_poly_negate_bounded : forall r dim bits,
    length (lhs r) <= dim -> C.row_bits r <= bits ->
    (T_poly_negate r <= 40 * N.of_nat (dim + 1) * N.of_nat (bits + 1))%N.
  Proof.
    intros r dim bits Hdim Hbits.
    assert (Hentries : Forall (fun p => Z.size_nat (snd p) <= bits) (lhs r)).
    { apply Forall_forall. intros p Hp. pose proof (poly_row_entry_bits r p Hp). lia. }
    pose proof (T_poly_scale_coef_bounded (-1)%Z (lhs r) bits Hentries) as Hscale.
    assert (Hopp : (Z.T_opp (rhs r) <= 1)%N).
    { destruct (rhs r); time_unfold Z.T_opp; time_simpl; lia. }
    change (T_poly_scale_coef (-1)%Z (lhs r) <=
      16 * N.of_nat ((length (lhs r) + 1) * 2 * (bits + 1)))%N in Hscale.
    rewrite !Nat2N.inj_mul in Hscale.
    assert (Hwidth : (1 <= N.of_nat (bits + 1))%N) by lia.
    time_unfold (@T_poly_negate). time_simpl. clear Hbits Hentries. nia.
  Qed.

  Definition poly_entail_keys (P : list (lcons X.t)) (c : lcons X.t) : nat :=
    fold_right Nat.max 0 (map C.row_key_bits P) + C.row_key_bits c.

  Definition poly_entail_bits (P : list (lcons X.t)) (c : lcons X.t) : nat :=
    fold_right Nat.max 0 (map C.row_bits P) + C.row_bits c.

  (** Separate key and arithmetic maxima add to the exact frozen initial width. *)
  Lemma poly_entail_width : forall P c,
    poly_entail_keys P c + poly_entail_bits P c =
      ell P + C.row_bits c + C.row_key_bits c.
  Proof.
    intros P c. unfold poly_entail_keys, poly_entail_bits, ell. lia.
  Qed.

  (** The flagged target and source rows satisfy the normal initialization envelope. *)
  Lemma poly_entail_input_envelopes : forall P c,
    normal P -> normal [c] ->
    Forall (fun p => poly_input_envelope (n P + length (lhs c))
      (poly_entail_keys P c) (poly_entail_bits P c) (fst p))
      ((poly_negate c, true) :: map (fun r => (r, false)) P).
  Proof.
    intros P c HP Hc. unfold normal in Hc. apply Forall_inv in Hc.
    constructor.
    - cbn [fst]. unfold poly_input_envelope. split.
      + now apply poly_negate_row_normal.
      + split; [rewrite poly_negate_row_length; lia|]. split.
        * rewrite poly_negate_row_key_bits. unfold poly_entail_keys. lia.
        * rewrite poly_negate_row_bits. unfold poly_entail_bits. lia.
    - apply Forall_map, Forall_forall. intros r Hr. cbn [fst].
      unfold poly_input_envelope. split.
      + exact (proj1 (Forall_forall _ _) HP r Hr).
      + split.
        * pose proof (poly_row_dimension P r HP Hr). unfold n. lia.
        * split.
          -- pose proof (poly_max_member _ C.row_key_bits 0 P r Hr).
             unfold poly_entail_keys. lia.
          -- pose proof (poly_max_member _ C.row_bits 0 P r Hr).
             unfold poly_entail_bits. lia.
  Qed.

  (** Variable collection sees only rows within the original dimension and key maximum. *)
  Lemma poly_entail_variable_envelopes : forall P c,
    normal P ->
    Forall (fun r => length (lhs r) <= n P + length (lhs c) /\
      C.row_key_bits r <= poly_entail_keys P c) (c :: P).
  Proof.
    intros P c HP. constructor.
    - split; [lia|]. unfold poly_entail_keys. lia.
    - apply Forall_forall. intros r Hr. split.
      + pose proof (poly_row_dimension P r HP Hr). unfold n. lia.
      + pose proof (poly_max_member _ C.row_key_bits 0 P r Hr).
        unfold poly_entail_keys. lia.
  Qed.

  (** The actual initialized rows have the fixed support, multiplier length, and source widths. *)
  Lemma poly_entail_initial_envelopes : forall P c,
    normal P -> normal [c] ->
    Forall (poly_row_envelope (n P + length (lhs c)) (length P + 1)
      (poly_entail_keys P c) (poly_entail_bits P c))
      (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P)).
  Proof.
    intros P c HP Hc.
    pose proof (poly_initial_envelopes_from_sources
      ((poly_negate c, true) :: map (fun r => (r, false)) P)
      (n P + length (lhs c)) (poly_entail_keys P c) (poly_entail_bits P c)
      (poly_entail_input_envelopes P c HP Hc)) as Hinitial.
    cbn [length] in Hinitial. rewrite length_map in Hinitial.
    replace (S (length P)) with (length P + 1) in Hinitial by lia.
    exact Hinitial.
  Qed.

  (** The public recurrence covers normal initialization even at zero elimination fuel. *)
  Lemma poly_fmcost_initial_charge : forall dim mlen bits,
    (mlen + 1)^2 * (dim + 1) * (bits + 1) <=
      fmcost dim mlen dim mlen bits.
  Proof.
    intros [|dim] mlen bits.
    - cbn [fmcost Nat.pow]. nia.
    - change ((mlen + 1)^2 * (S dim + 1) * (bits + 1) <=
        (mlen + 1)^2 * (S dim + mlen + 1) * (bits + 1)^2 +
          fmcost (S dim) mlen dim (mlen^2 / 4 + mlen) (2 * bits + 1)).
      eapply Nat.le_trans with (m :=
        (mlen + 1)^2 * (S dim + mlen + 1) * (bits + 1)^2).
      + apply Nat.mul_le_mono.
        * apply Nat.mul_le_mono; [reflexivity|lia].
        * cbn [Nat.pow]. nia.
      + lia.
  Qed.

  Definition poly_setup_factor : N :=
    (poly_variables_factor + poly_initial_factor + 64)%N.

  (** Negation, flag construction, variable collection, and initialization fit the initial charge. *)
  Lemma T_poly_entail_setup_bounded : forall P c,
    normal P -> normal [c] ->
    (T_poly_negate c +
      ListDef.T_map (fun r => (r, false)) (fun _ => 1%N) P +
      T_poly_variables X.encode X.T_encode (c :: P) +
      T_poly_initial X.encode X.T_encode
        ((poly_negate c, true) :: map (fun r => (r, false)) P) <=
      poly_setup_factor * N.of_nat
        (fmcost (n P + length (lhs c)) (length P + 1)
          (n P + length (lhs c)) (length P + 1)
          (ell P + C.row_bits c + C.row_key_bits c)))%N.
  Proof.
    intros P c HP Hc.
    set (dim := n P + length (lhs c)).
    set (mlen := length P + 1).
    set (keys := poly_entail_keys P c).
    set (bits := poly_entail_bits P c).
    set (input := (poly_negate c, true) :: map (fun r => (r, false)) P).
    set (count := (N.of_nat (mlen + 1)^2)%N).
    set (entry_work := (N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N).
    set (work := (count * entry_work)%N).
    assert (Hcount : (N.of_nat (mlen + 1) <= count)%N).
    { unfold count. rewrite N.pow_2_r.
      assert (1 <= N.of_nat (mlen + 1))%N by lia. nia. }
    assert (Hcount_positive : (1 <= count)%N) by lia.
    assert (Hentry_positive : (1 <= entry_work)%N).
    { unfold entry_work. change (1 * 1 <=
        N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N.
      apply N.mul_le_mono; lia. }
    assert (Hcount_work : (count <= work)%N).
    { unfold work. pose proof (N.mul_le_mono_l _ _ count Hentry_positive) as Hproduct.
      rewrite N.mul_1_r in Hproduct. exact Hproduct. }
    assert (Hentry_work : (entry_work <= work)%N).
    { unfold work. pose proof (N.mul_le_mono_r _ _ entry_work Hcount_positive) as Hproduct.
      rewrite N.mul_1_l in Hproduct. exact Hproduct. }
    pose proof (T_poly_negate_bounded c dim bits ltac:(unfold dim; lia)
      ltac:(unfold bits, poly_entail_bits; lia)) as Hnegate.
    assert (Hnegate_total : (T_poly_negate c <= 40 * work)%N).
    { eapply N.le_trans; [exact Hnegate|].
      eapply N.le_trans with (m := (40 * entry_work)%N).
      - unfold entry_work. rewrite N.mul_assoc.
        apply N.mul_le_mono_l. lia.
      - now apply N.mul_le_mono_l. }
    pose proof (poly_T_map_members _ _ (fun r => (r, false)) (fun _ => 1%N) 1 P
      (fun _ _ => N.le_refl 1%N)) as Hmap.
    assert (Hmap_total : (ListDef.T_map (fun r => (r, false)) (fun _ => 1%N) P <=
      2 * work)%N).
    { unfold mlen in Hcount. clear -Hmap Hcount Hcount_work. lia. }
    pose proof (T_poly_variables_bounded (c :: P) dim keys
      (poly_entail_variable_envelopes P c HP)) as Hvariables.
    assert (Hrows_length : length (c :: P) = mlen) by (unfold mlen; cbn [length]; lia).
    rewrite Hrows_length in Hvariables.
    assert (Hvariables_total : (T_poly_variables X.encode X.T_encode (c :: P) <=
      poly_variables_factor * work)%N).
    { eapply N.le_trans; [exact Hvariables|]. unfold work, entry_work.
      rewrite !N.mul_assoc. apply N.mul_le_mono; [|lia].
      apply N.mul_le_mono_r, N.mul_le_mono_l. exact Hcount. }
    pose proof (T_poly_initial_bounded input dim keys bits
      (poly_entail_input_envelopes P c HP Hc)) as Hinitial.
    assert (Hinput_length : length input = mlen).
    { unfold input, mlen. cbn [length]. rewrite length_map. lia. }
    rewrite Hinput_length in Hinitial.
    assert (Hinitial_total : (T_poly_initial X.encode X.T_encode input <=
      poly_initial_factor * work)%N).
    { replace (poly_initial_factor * work)%N with
        (poly_initial_factor * N.of_nat (mlen + 1)^2 *
          N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N
        by (unfold work, count, entry_work; ring).
      exact Hinitial. }
    assert (Hsum : (T_poly_negate c +
      ListDef.T_map (fun r => (r, false)) (fun _ => 1%N) P +
      T_poly_variables X.encode X.T_encode (c :: P) +
      T_poly_initial X.encode X.T_encode input <= poly_setup_factor * work)%N).
    { unfold poly_setup_factor.
      clear -Hnegate_total Hmap_total Hvariables_total Hinitial_total.
      clearbody work. nia. }
    assert (Hwork_bound : (work <= N.of_nat (fmcost dim mlen dim mlen (keys + bits)))%N).
    { pose proof (poly_fmcost_initial_charge dim mlen (keys + bits)) as Hmeasure.
      replace work with (N.of_nat ((mlen + 1)^2 * (dim + 1) * (keys + bits + 1))).
      - clear -Hmeasure. lia.
      - unfold work, count, entry_work.
        rewrite !Nat2N.inj_mul, poly_nat_square, N.pow_2_r. ring. }
    eapply N.le_trans; [exact Hsum|]. apply N.mul_le_mono_l.
    fold dim mlen. rewrite <- poly_entail_width. exact Hwork_bound.
  Qed.


  (** Every natural number lies below its next binary logarithm power. *)
  Lemma poly_log_upper : forall count, count < 2 ^ (Nat.log2 count + 1).
  Proof.
    intros [|count]; [change (0 < 2); lia|].
    pose proof (Nat.log2_spec (S count) (Nat.lt_0_succ count)) as [_ Hupper].
    now replace (Nat.log2 (S count) + 1) with (S (Nat.log2 (S count))) by lia.
  Qed.

  (** A count of bounded summands gives a logarithmic coefficient-width bound. *)
  Lemma poly_count_magnitude_bits : forall z count bits,
    poly_magnitude z <= count * 2 ^ bits ->
    Z.size_nat z <= bits + Nat.log2 count + 1.
  Proof.
    intros z count bits Hmagnitude. apply poly_size_least.
    replace (bits + Nat.log2 count + 1) with (bits + (Nat.log2 count + 1)) by lia.
    rewrite Nat.pow_add_r.
    pose proof (poly_log_upper count) as Hcount.
    assert (Hpositive : 0 < 2 ^ bits).
    { pose proof (Nat.pow_nonzero 2 bits ltac:(lia)). lia. }
    nia.
  Qed.

  (** An accumulator magnitude budget counts all inserted raw occurrences. *)
  Definition poly_accum_magnitude (m : ptrie (X.t * Z)) (bound : nat) : Prop :=
    forall key p, PTrieCode.get key m = Some p -> poly_magnitude (snd p) <= bound.

  (** The next previous value obeys the table's magnitude budget, including missing keys. *)
  Lemma poly_previous_magnitude : forall m bound x,
    poly_accum_magnitude m bound -> poly_magnitude (poly_previous m x) <= bound.
  Proof.
    intros m bound x Hmagnitude. unfold poly_previous.
    destruct (PTrieCode.get (X.encode x) m) as [p|] eqn:Hget.
    - exact (Hmagnitude _ _ Hget).
    - change (0 <= bound). lia.
  Qed.

  (** One insertion adds at most its source coefficient magnitude to every table bound. *)
  Lemma poly_add_term_magnitude : forall m p bound bits,
    poly_accum_magnitude m bound -> Z.size_nat (snd p) <= bits ->
    poly_accum_magnitude (poly_add_term X.encode m p) (bound + 2 ^ bits).
  Proof.
    intros m p bound bits Hmagnitude Hbits key q Hget.
    change (PTrieCode.get key (PTrieCode.set (X.encode (fst p))
      (fst p, (poly_previous m (fst p) + snd p)%Z) m) = Some q) in Hget.
    destruct (Pos.eq_dec key (X.encode (fst p))) as [Hequal|Hother].
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Hequal. subst q.
      cbn [snd].
      pose proof (poly_magnitude_add (poly_previous m (fst p)) (snd p)) as Hadd.
      pose proof (poly_previous_magnitude m bound (fst p) Hmagnitude) as Hold.
      pose proof (poly_magnitude_upper (snd p)) as Hnew.
      assert (Hpower : 2 ^ Z.size_nat (snd p) <= 2 ^ bits).
      { apply Nat.pow_le_mono_r; lia. }
      lia.
    - rewrite PTrie.get_set_other in Hget by exact Hother.
      specialize (Hmagnitude _ _ Hget). lia.
  Qed.

  (** Accumulating a raw list adds one source-magnitude budget per occurrence. *)
  Lemma poly_accum_magnitude_fold : forall xs m bound bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    poly_accum_magnitude m bound ->
    poly_accum_magnitude (fold_left (poly_add_term X.encode) xs m)
      (bound + length xs * 2 ^ bits).
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m bound bits Hsizes Hmagnitude;
      cbn [fold_left length].
    - now rewrite Nat.add_0_r.
    - inversion Hsizes as [|q qs Hp Htail]; subst q qs.
      replace (bound + S (length xs) * 2 ^ bits) with
        ((bound + 2 ^ bits) + length xs * 2 ^ bits) by nia.
      apply IH; [exact Htail|]. now apply poly_add_term_magnitude.
  Qed.

  (** Normalized raw coefficients gain only the logarithm of the source occurrence count. *)
  Lemma poly_normal_coef_log_bits : forall xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Forall (fun p => Z.size_nat (snd p) <= bits + Nat.log2 (length xs) + 1)
      (poly_normal_coef X.encode xs).
  Proof.
    intros xs bits Hsizes.
    assert (Hempty : poly_accum_magnitude PTrieCode.empty 0).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (poly_accum_magnitude_fold xs PTrieCode.empty 0 bits Hsizes Hempty)
      as Hmagnitude.
    apply Forall_forall. intros p Hin. apply poly_count_magnitude_bits.
    destruct (poly_normal_coef_lookup _ _ _ _ Hin) as [key [Hget _]].
    exact (Hmagnitude _ _ Hget).
  Qed.

  (** A raw row's merged coefficients fit its declared width plus an occurrence logarithm. *)
  Lemma poly_normal_row_log_bits : forall r,
    C.row_bits (poly_normal_row X.encode r) <=
      C.row_bits r + Nat.log2 (length (lhs r)) + 1.
  Proof.
    intro r. unfold C.row_bits at 1. cbn [poly_normal_row lhs rhs].
    apply poly_max_bound.
    - pose proof (poly_row_rhs_bits r). lia.
    - apply poly_normal_coef_log_bits. apply Forall_forall. intros p Hin.
      unfold C.row_bits. exact (poly_max_member _ (fun p => Z.size_nat (snd p))
        (Z.size_nat (rhs r)) (lhs r) p Hin).
  Qed.

  (** A raw fold keeps a single width bound derived from its total occurrence count. *)
  Lemma T_poly_accum_log : forall xs m keys bits used total,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    poly_accum_magnitude m (used * 2 ^ bits) -> used + length xs <= total ->
    (List.T_fold_left (poly_add_term X.encode) (T_poly_add_term X.encode X.T_encode)
      xs m <= (poly_add_factor + 1) * N.of_nat (length xs) *
        N.of_nat (keys + 2 * bits + Nat.log2 total + 2) + 1)%N.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys bits used total Hsizes Hmagnitude Hcount.
    - time_unfold List.T_fold_left. cbn [length]. nia.
    - inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      assert (Hprevious : Z.size_nat (poly_previous m (fst p)) <=
        bits + Nat.log2 total + 1).
      { apply poly_count_magnitude_bits.
        pose proof (poly_previous_magnitude m (used * 2 ^ bits) (fst p) Hmagnitude).
        cbn [length] in Hcount. nia. }
      assert (Hnext : poly_accum_magnitude (poly_add_term X.encode m p)
        ((used + 1) * 2 ^ bits)).
      { replace ((used + 1) * 2 ^ bits) with (used * 2 ^ bits + 2 ^ bits) by nia.
        now apply poly_add_term_magnitude. }
      specialize (IH (poly_add_term X.encode m p) keys bits (used + 1) total Htail Hnext
        ltac:(cbn [length] in Hcount; lia)).
      pose proof (T_poly_add_term_bounded m p keys bits
        (bits + Nat.log2 total + 1) Hkey Hbits Hprevious) as Hhead.
      time_unfold List.T_fold_left. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  Definition poly_log_normal_factor : N :=
    (4 * (poly_add_factor + 1) + 6 * PTrieT.k_fold + 16)%N.

  (** Raw normalization pays once per occurrence for keys and logarithmic merged widths. *)
  Lemma T_poly_normal_log : forall xs keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (T_poly_normal_coef X.encode X.T_encode xs <=
      poly_log_normal_factor * N.of_nat (length xs + 1) *
        N.of_nat (keys + bits + Nat.log2 (length xs) + 1))%N.
  Proof.
    intros xs keys bits Hsizes.
    assert (Hempty : poly_accum_magnitude PTrieCode.empty (0 * 2 ^ bits)).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (T_poly_accum_log xs PTrieCode.empty keys bits 0 (length xs)
      Hsizes Hempty ltac:(lia)) as Haccum.
    set (tr := fold_left (poly_add_term X.encode) xs PTrieCode.empty).
    assert (Hkeys : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs).
    { eapply Forall_impl; [|exact Hsizes]. intros p [Hp _]. exact Hp. }
    pose proof (poly_accum_nodes xs PTrieCode.empty keys Hkeys) as Hnodes.
    change (PTrie.nodes tr <= length xs * keys) in Hnodes.
    pose proof (PTrieT.T9_fold_values (X.t * Z) (list (X.t * Z))
      poly_normal_keep T_poly_normal_keep tr nil 5 T_poly_normal_keep_le) as Hfold.
    time_unfold (@T_poly_normal_coef). fold tr.
    change (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc) with poly_normal_keep.
    unfold poly_log_normal_factor. time_simpl.
    change (fun (acc : PTrieCode.t (X.t * Z)) (p : X.t * Z) =>
      T_poly_add_term X.encode X.T_encode acc p) with
      (T_poly_add_term X.encode X.T_encode).
    change (fun (_ : list (X.t * Z)) (p : X.t * Z) =>
      (1 + (1 + Z.T_eqb (snd p) 0))%N) with T_poly_normal_keep.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** The scalar FM charge is the natural-number term of the frozen recurrence. *)
  Lemma poly_fm_charge_nat : forall count dim mlen keys bits,
    N.of_nat ((count + 1)^2 * (dim + mlen + 1) * (keys + bits + 1)^2) =
      (N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros count dim mlen keys bits. unfold poly_clock_span.
    rewrite !Nat2N.inj_mul, !poly_nat_square, !N.pow_2_r. ring.
  Qed.

  (** Every nonempty-stage charge has at least one unit of work. *)
  Lemma poly_fm_charge_positive : forall count dim mlen keys bits,
    (1 <= N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros count dim mlen keys bits.
    assert (Hcount : (1 <= N.of_nat (count + 1))%N) by lia.
    assert (Hsquare : (1 <= N.of_nat (count + 1)^2)%N).
    { rewrite N.pow_2_r.
      change (1 * 1 <= N.of_nat (count + 1) * N.of_nat (count + 1))%N.
      now apply N.mul_le_mono. }
    change (1 * 1 <= N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits)%N.
    apply N.mul_le_mono; [exact Hsquare|apply poly_span_positive].
  Qed.

  (** One public recurrence equation separates the current charge from the future work. *)
  Lemma poly_fmcost_clock_step : forall fuel count dim mlen keys bits,
    N.of_nat (fmcost dim mlen (S fuel) count (keys + bits)) =
      (N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits +
        N.of_nat (fmcost dim mlen fuel (count^2 / 4 + count)
          (2 * (keys + bits) + 1)))%N.
  Proof.
    intros fuel count dim mlen keys bits.
    change (N.of_nat ((count + 1)^2 * (dim + mlen + 1) * (keys + bits + 1)^2 +
      fmcost dim mlen fuel (count^2 / 4 + count) (2 * (keys + bits) + 1)) =
      (N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits +
        N.of_nat (fmcost dim mlen fuel (count^2 / 4 + count)
          (2 * (keys + bits) + 1)))%N).
    rewrite Nat2N.inj_add, poly_fm_charge_nat. reflexivity.
  Qed.

  Definition poly_run_search_factor : N :=
    (poly_step_factor + poly_terminal_factor + 16)%N.

  (** A spare recurrence stage pays for the final certificate scan over all generated rows. *)
  Lemma T_poly_run_search_bounded : forall xs P c vars rows dim mlen keys bits count,
    length vars <= dim ->
    Forall (poly_source_envelope dim (keys + bits)) (c :: P) ->
    length P <= mlen -> mlen <= count -> length rows <= count ->
    Forall (poly_reduced_row vars) rows ->
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs rows +
      T_find_certificate P c (poly_run X.encode X.eqb xs rows) <=
      poly_run_search_factor * N.of_nat
        (fmcost dim mlen (S (length xs)) count (keys + bits)))%N.
  Proof.
    intro xs. induction xs as [|x xs IH];
      intros P c vars rows dim mlen keys bits count
        Hdim Hsource HP HM HR Hsupport Henvelopes.
    - assert (Hterminal_rows : Forall (fun r =>
        C.row_bits (poly_constraint r) <= keys + bits /\
        length (poly_multipliers r) <= mlen /\
        Forall (fun m => Z.size_nat m <= keys + bits + 1) (poly_multipliers r)) rows).
      { eapply Forall_impl; [|exact Henvelopes].
        intros r (Hn & Hd & Hk & Hb & Hm & Hu). split; [lia|]. split; [exact Hm|].
        eapply Forall_impl; [|exact Hu]. intros z Hz.
        change (Z.size_nat z <= bits + 1) in Hz.
        change (Z.size_nat z <= keys + bits + 1). lia. }
      pose proof (T_find_certificate_bounded P c rows count dim mlen (keys + bits)
        Hsource HP HM HR Hterminal_rows) as Hterminal.
      set (work := (N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits)%N).
      assert (Hwork : (1 <= work)%N).
      { unfold work. apply poly_fm_charge_positive. }
      assert (Hterminal_work : (T_find_certificate P c rows <=
        poly_terminal_factor * work)%N).
      { unfold work, poly_clock_span. rewrite !N.mul_assoc. exact Hterminal. }
      cbn [length poly_run]. rewrite poly_fmcost_clock_step.
      fold work.
      eapply N.le_trans with (m := (poly_run_search_factor * work)%N).
      2: { apply N.mul_le_mono_l. apply N.le_add_r. }
      time_unfold (@T_poly_run). time_cbn.
      clear -Hterminal_work Hwork. clearbody work.
      unfold poly_run_search_factor. rewrite !N.mul_add_distr_r. lia.
    - set (next := poly_step X.encode X.eqb x rows).
      set (next_count := count^2 / 4 + count).
      assert (Hnext_count : length next <= next_count).
      { pose proof (poly_step_rows X.t X.encode X.eqb x rows) as Hstep_rows.
        pose proof (poly_rows_recurrence_mono (length rows) count HR).
        unfold next, next_count. lia. }
      assert (Hnext_mlen : mlen <= next_count) by (unfold next_count; lia).
      assert (Hnext_support : Forall (poly_reduced_row vars) next).
      { unfold next. now apply poly_step_reduced. }
      assert (Hnext_envelopes :
        Forall (poly_row_envelope dim mlen keys (2 * bits + 1)) next).
      { unfold next. now apply poly_step_envelopes with (vars := vars). }
      assert (Hnext_source : Forall (poly_source_envelope dim (keys + (2 * bits + 1)))
        (c :: P)).
      { eapply Forall_impl; [|exact Hsource]. intros r Hr.
        eapply poly_source_envelope_mono; [exact Hr|lia|lia]. }
      pose proof (IH P c vars next dim mlen keys (2 * bits + 1) next_count
        Hdim Hnext_source HP Hnext_mlen Hnext_count Hnext_support Hnext_envelopes)
        as Hrecursive.
      pose proof (poly_fmcost_params_mono (S (length xs))
        dim dim mlen mlen next_count next_count
        (keys + (2 * bits + 1)) (2 * (keys + bits) + 1)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) ltac:(lia)) as Hfuture.
      assert (Hrecursive_total :
        (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs next +
          T_find_certificate P c (poly_run X.encode X.eqb xs next) <=
          poly_run_search_factor * N.of_nat
            (fmcost dim mlen (S (length xs)) next_count (2 * (keys + bits) + 1)))%N).
      { eapply N.le_trans; [exact Hrecursive|]. apply N.mul_le_mono_l.
        clear -Hfuture. lia. }
      pose proof (T_poly_step_bounded x rows dim mlen keys bits Henvelopes) as Hstep.
      set (work := (N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits)%N).
      assert (Hhead : (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows <=
        poly_step_factor * work)%N).
      { eapply N.le_trans; [exact Hstep|]. unfold work. rewrite N.mul_assoc.
        apply N.mul_le_mono_r, N.mul_le_mono_l, N.pow_le_mono_l. lia. }
      assert (Hwork : (1 <= work)%N).
      { unfold work. apply poly_fm_charge_positive. }
      change (T_poly_run X.encode X.T_encode X.eqb X.T_eqb (x :: xs) rows +
        T_find_certificate P c (poly_run X.encode X.eqb xs next) <=
        poly_run_search_factor * N.of_nat
          (fmcost dim mlen (S (S (length xs))) count (keys + bits)))%N.
      rewrite poly_fmcost_clock_step. fold work next_count.
      time_unfold (@T_poly_run). time_simpl.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      fold next. clear -Hrecursive_total Hhead Hwork. clearbody work.
      unfold poly_run_search_factor in Hrecursive_total |- *. nia.
  Qed.

  (** The frozen normal-input budget is shared by setup, elimination, and checking. *)
  Definition poly_entail_budget (P : list (lcons X.t)) (c : lcons X.t) : nat :=
    fmcost (n P + length (lhs c)) (length P + 1)
      (n P + length (lhs c)) (length P + 1)
      (ell P + C.row_bits c + C.row_key_bits c).

  Lemma poly_entail_budget_positive : forall P c,
    (1 <= N.of_nat (poly_entail_budget P c))%N.
  Proof.
    intros P c. unfold poly_entail_budget.
    pose proof (poly_fmcost_positive (n P + length (lhs c)) (length P + 1)
      (n P + length (lhs c)) (length P + 1)
      (ell P + C.row_bits c + C.row_key_bits c)). lia.
  Qed.

  (** A nonempty source list supplies the additional terminal-checking recurrence stage. *)
  Lemma T_poly_entail_nonempty_tail : forall P c,
    normal P -> normal [c] -> P <> [] ->
    (T_poly_run X.encode X.T_encode X.eqb X.T_eqb
        (poly_variables X.encode (c :: P))
        (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P)) +
      T_find_certificate P c
        (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
          (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))) <=
      poly_run_search_factor * N.of_nat (poly_entail_budget P c))%N.
  Proof.
    intros P c HP Hc Hnonempty.
    set (dim := n P + length (lhs c)).
    set (mlen := length P + 1).
    set (keys := poly_entail_keys P c).
    set (bits := poly_entail_bits P c).
    set (vars := poly_entail_vars P c).
    set (xs := poly_variables X.encode (c :: P)).
    set (rows := poly_initial X.encode
      ((poly_negate c, true) :: map (fun r => (r, false)) P)).
    assert (Hdim : length vars <= dim) by apply poly_entail_vars_length.
    assert (Hsource : Forall (poly_source_envelope dim (keys + bits)) (c :: P)).
    { pose proof (poly_entail_source_envelopes P c HP) as Hsource.
      rewrite <- poly_entail_width in Hsource. exact Hsource. }
    assert (Hlength : length rows = mlen).
    { unfold rows, mlen. rewrite poly_initial_length. cbn [length].
      rewrite length_map. lia. }
    assert (Hsupport : Forall (poly_reduced_row vars) rows)
      by apply poly_entail_initial_reduced.
    assert (Henvelopes : Forall (poly_row_envelope dim mlen keys bits) rows)
      by now apply poly_entail_initial_envelopes.
    pose proof (T_poly_run_search_bounded xs P c vars rows dim mlen keys bits mlen
      Hdim Hsource ltac:(unfold mlen; lia) (Nat.le_refl _) ltac:(lia)
      Hsupport Henvelopes) as Hrun.
    pose proof (poly_entail_spare_fuel P c Hnonempty) as Hfuel.
    pose proof (poly_fmcost_fuel_mono (S (length xs)) dim Hfuel
      dim mlen mlen (keys + bits)) as Hbudget.
    eapply N.le_trans; [exact Hrun|]. apply N.mul_le_mono_l.
    unfold poly_entail_budget. fold dim mlen.
    rewrite <- poly_entail_width. fold keys bits.
    clear -Hbudget. lia.
  Qed.

  (** With no source rows, elimination retains the exact single complemented target or removes it. *)
  Lemma poly_entail_empty_shape : forall xs c, normal [c] ->
    length (poly_run X.encode X.eqb xs
      (poly_initial X.encode [(poly_negate c, true)])) <= 1 /\
    Forall (fun r => C.row_bits (poly_constraint r) <= C.row_bits c /\
      poly_multipliers r = [1%Z])
      (poly_run X.encode X.eqb xs
        (poly_initial X.encode [(poly_negate c, true)])).
  Proof.
    intros xs c Hnormal. unfold normal in Hnormal. apply Forall_inv in Hnormal.
    assert (Hbits : C.row_bits (poly_normal_row X.encode (poly_negate c)) <= C.row_bits c).
    { eapply Nat.le_trans; [apply poly_normal_row_bits, poly_negate_row_normal; exact Hnormal|].
      rewrite poly_negate_row_bits. reflexivity. }
    change (length (poly_run X.encode X.eqb xs
      [PolyRow X.t (poly_normal_row X.encode (poly_negate c)) [1%Z] true]) <= 1 /\
      Forall (fun r => C.row_bits (poly_constraint r) <= C.row_bits c /\
        poly_multipliers r = [1%Z])
        (poly_run X.encode X.eqb xs
          [PolyRow X.t (poly_normal_row X.encode (poly_negate c)) [1%Z] true])).
    destruct (poly_run_single_inequality xs
      (PolyRow X.t (poly_normal_row X.encode (poly_negate c)) [1%Z] true)
      eq_refl) as [Hkeep | Hdrop]; rewrite ?Hkeep, ?Hdrop.
    - split; [reflexivity|]. constructor; [split; [exact Hbits|reflexivity]|constructor].
    - split; [cbn [length]; lia|constructor].
  Qed.

  (** A unit certificate uses the linear base of the recurrence for an empty source list. *)
  Lemma T_poly_entail_empty_tail : forall c, normal [c] ->
    (T_poly_run X.encode X.T_encode X.eqb X.T_eqb
        (poly_variables X.encode [c])
        (poly_initial X.encode [(poly_negate c, true)]) +
      T_find_certificate [] c
        (poly_run X.encode X.eqb (poly_variables X.encode [c])
          (poly_initial X.encode [(poly_negate c, true)])) <=
      (poly_run_factor + poly_terminal_factor) *
        N.of_nat (poly_entail_budget [] c))%N.
  Proof.
    intros c Hc.
    assert (HP : normal []) by constructor.
    set (dim := n [] + length (lhs c)).
    set (keys := poly_entail_keys [] c).
    set (bits := poly_entail_bits [] c).
    set (vars := poly_entail_vars [] c).
    set (xs := poly_variables X.encode [c]).
    set (rows := poly_initial X.encode [(poly_negate c, true)]).
    assert (Hdim : length vars <= dim) by apply poly_entail_vars_length.
    assert (Hsupport : Forall (poly_reduced_row vars) rows)
      by apply poly_entail_initial_reduced.
    assert (Henvelopes : Forall (poly_row_envelope dim 1 keys bits) rows)
      by now apply poly_entail_initial_envelopes.
    assert (Hlength : length rows = 1) by reflexivity.
    assert (Hbudget : poly_entail_budget [] c = fmcost dim 1 dim 1 (keys + bits)).
    { unfold poly_entail_budget. fold dim. rewrite <- poly_entail_width. reflexivity. }
    pose proof (T_poly_run_bounded xs vars rows dim 1 keys bits
      Hdim Hsupport Henvelopes) as Hrun. rewrite Hlength in Hrun.
    pose proof (poly_entail_fuel [] c) as Hfuel.
    pose proof (poly_fmcost_fuel_mono (length xs) dim Hfuel
      dim 1 1 (keys + bits)) as Hrun_budget.
    assert (Hrun_total : (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs rows <=
      poly_run_factor * N.of_nat (poly_entail_budget [] c))%N).
    { eapply N.le_trans; [exact Hrun|]. apply N.mul_le_mono_l.
      rewrite Hbudget. clear -Hrun_budget. lia. }
    assert (Hsource : poly_source_envelope dim (keys + bits) c).
    { pose proof (poly_entail_source_envelopes [] c HP) as Hsource.
      rewrite <- poly_entail_width in Hsource. exact (Forall_inv Hsource). }
    destruct (poly_entail_empty_shape xs c Hc) as [Hcount Hshape].
    assert (Hterminal_rows : Forall (fun r =>
      C.row_bits (poly_constraint r) <= keys + bits /\
      poly_multipliers r = [1%Z]) (poly_run X.encode X.eqb xs rows)).
    { eapply Forall_impl; [|exact Hshape]. intros r [Hb Hm]. split; [|exact Hm].
      unfold bits, poly_entail_bits. cbn [map fold_right]. lia. }
    pose proof (T_find_certificate_empty_bounded c (poly_run X.encode X.eqb xs rows)
      1 dim (keys + bits) Hsource Hcount Hterminal_rows) as Hterminal.
    assert (Hterminal_base : (T_find_certificate [] c (poly_run X.encode X.eqb xs rows) <=
      poly_terminal_factor * N.of_nat (fmcost dim 1 0 1 (keys + bits)))%N).
    { change (T_find_certificate [] c (poly_run X.encode X.eqb xs rows) <=
        poly_terminal_factor * N.of_nat (2 * (dim + 1 + 1) * (keys + bits + 1)))%N.
      replace (dim + 1 + 1) with (dim + 2) by lia.
      rewrite !Nat2N.inj_mul. change (N.of_nat 2) with 2%N.
      rewrite !N.mul_assoc. exact Hterminal. }
    pose proof (poly_fmcost_fuel_mono 0 dim (Nat.le_0_l _)
      dim 1 1 (keys + bits)) as Hterminal_budget.
    assert (Hterminal_total : (T_find_certificate [] c (poly_run X.encode X.eqb xs rows) <=
      poly_terminal_factor * N.of_nat (poly_entail_budget [] c))%N).
    { eapply N.le_trans; [exact Hterminal_base|]. apply N.mul_le_mono_l.
      rewrite Hbudget. clear -Hterminal_budget. lia. }
    change (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs rows +
      T_find_certificate [] c (poly_run X.encode X.eqb xs rows) <=
      (poly_run_factor + poly_terminal_factor) * N.of_nat (poly_entail_budget [] c))%N.
    rewrite N.mul_add_distr_r. now apply N.add_le_mono.
  Qed.

  Definition poly_entail_factor : N :=
    (poly_setup_factor + poly_run_search_factor + poly_run_factor +
      poly_terminal_factor + 8)%N.

  (** Normal-input certificate production follows its frozen cost envelope. *)
  Lemma T_poly_entail_engine_bounded : forall P c, normal P -> normal [c] ->
    (T_entail_engine P c <= poly_entail_factor *
      N.of_nat (poly_entail_budget P c))%N.
  Proof.
    intros P c HP Hc.
    set (input := (poly_negate c, true) :: map (fun r => (r, false)) P).
    set (xs := poly_variables X.encode (c :: P)).
    set (rows := poly_initial X.encode input).
    set (work := N.of_nat (poly_entail_budget P c)).
    pose proof (poly_entail_budget_positive P c) as Hpositive. fold work in Hpositive.
    pose proof (T_poly_entail_setup_bounded P c HP Hc) as Hsetup.
    change (T_poly_negate c + ListDef.T_map (fun r => (r, false)) (fun _ => 1%N) P +
      T_poly_variables X.encode X.T_encode (c :: P) +
      T_poly_initial X.encode X.T_encode input <= poly_setup_factor * work)%N in Hsetup.
    assert (Htail : (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs rows +
      T_find_certificate P c (poly_run X.encode X.eqb xs rows) <=
      (poly_run_search_factor + poly_run_factor + poly_terminal_factor) * work)%N).
    { destruct P as [|p P].
      - eapply N.le_trans; [apply T_poly_entail_empty_tail; exact Hc|].
        fold work. apply N.mul_le_mono_r. lia.
      - eapply N.le_trans; [apply T_poly_entail_nonempty_tail; [exact HP|exact Hc|discriminate]|].
        fold work. apply N.mul_le_mono_r. lia. }
    time_unfold T_entail_engine. time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    change (fun x y : X.t => X.T_eqb x y) with X.T_eqb.
    fold input xs rows. fold work.
    unfold poly_entail_factor.
    clear -Hsetup Htail Hpositive. clearbody work. nia.
  Qed.

  Lemma poly_raw_source_width : forall P,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= nell (Reached P)) P.
  Proof.
    intros P. apply Forall_forall. intros p Hp.
    pose proof (poly_max_member _ C.row_key_bits 0 P p Hp).
    pose proof (poly_max_member _ C.row_bits 0 P p Hp).
    unfold nell, ell. cbn [prows]. lia.
  Qed.

  (** A source occurrence is charged once at the certificate multiplier's width. *)
  Lemma poly_csize_entry_bits : forall p m bits multbits,
    C.row_key_bits p + C.row_bits p <= bits -> Z.size_nat m <= multbits ->
    (length (lhs p) + 1) *
      (C.row_key_bits p + (Z.size_nat m + 1) * (C.row_bits p + 1)) <=
      (length (lhs p) + 1) * (multbits + 1) * (bits + 1).
  Proof.
    intros p m bits multbits Hrow Hmult.
    assert (Hproduct : (Z.size_nat m + 1) * (C.row_bits p + 1) <=
      (multbits + 1) * (C.row_bits p + 1)) by (apply Nat.mul_le_mono_r; lia).
    assert (Hwidth : (multbits + 1) *
      (C.row_key_bits p + C.row_bits p + 1) <= (multbits + 1) * (bits + 1))
      by (apply Nat.mul_le_mono_l; lia).
    assert (Hinner : C.row_key_bits p +
      (Z.size_nat m + 1) * (C.row_bits p + 1) <= (multbits + 1) * (bits + 1)) by nia.
    replace ((length (lhs p) + 1) * (multbits + 1) * (bits + 1)) with
      ((length (lhs p) + 1) * ((multbits + 1) * (bits + 1))) by nia.
    now apply Nat.mul_le_mono_l.
  Qed.

  (** The successor output count still fits the input successor square. *)
  Lemma poly_fm_output_count : forall x P,
    length (fm_elim x P) + 1 <= (length P + 1)^2.
  Proof.
    intros x P. unfold fm_elim. rewrite length_map.
    pose proof (poly_step_rows X.t X.encode X.eqb x
      (poly_initial X.encode (map (fun r => (r, false)) P))) as Hrows.
    rewrite poly_initial_length, length_map in Hrows.
    assert (Hdivision : length P ^ 2 / 4 <= length P ^ 2).
    { apply Nat.Div0.div_le_upper_bound; nia. }
    cbn [Nat.pow] in *. nia.
  Qed.

  Lemma poly_fm_multiplier_length : forall P x r, In r (fm_elim x P) ->
    length (mults_of r) = length P.
  Proof.
    intros P x r Hr.
    destruct (fm_step_mults_checked P x r Hr) as [s [Hcombine Hrow]].
    pose proof (C.combine_admissible P (mults_of r) s Hcombine) as Hadmissible.
    symmetry. exact (proj1 Hadmissible).
  Qed.

  (** Exact vector length makes the total raw charge the sum of source occurrences. *)
  Lemma poly_csize_terms : forall P ms bits multbits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    Forall (fun m => Z.size_nat m <= multbits) ms -> length ms = length P ->
    C.csize P ms <= (terms (Reached P) + length P) * (multbits + 1) * (bits + 1).
  Proof.
    intro P. induction P as [|p P IH]; intros ms bits multbits Hrows Hmult Hlength;
      destruct ms as [|m ms]; cbn [length] in Hlength; try discriminate.
    - change (0 <= 0). lia.
    - inversion Hrows as [|? ? Hp HP]; subst.
      inversion Hmult as [|? ? Hm Hms]; subst.
      injection Hlength as Hlength.
      pose proof (IH ms bits multbits HP Hms Hlength) as Htail.
      pose proof (poly_csize_entry_bits p m bits multbits Hp Hm) as Hhead.
      cbn [C.csize terms prows map fold_right length] in Htail |- *. nia.
  Qed.

  Lemma poly_cbits_source_bits : forall P ms bits multbits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    Forall (fun m => Z.size_nat m <= multbits) ms ->
    C.cbits P ms <= multbits + bits + Nat.log2 (length P) + 1.
  Proof.
    intros P ms bits multbits Hrows Hmult. unfold C.cbits.
    assert (Hmax : fold_right Nat.max 0
      (map (fun pm => Z.size_nat (snd pm) + C.row_bits (fst pm))
        (List.combine P ms)) <= multbits + bits).
    { apply poly_max_bound; [lia|]. apply Forall_forall. intros [p m] Hin.
      cbn [fst snd]. pose proof (in_combine_l _ _ _ _ Hin) as Hp.
      pose proof (in_combine_r _ _ _ _ Hin) as Hm.
      pose proof (proj1 (Forall_forall _ _) Hrows p Hp) as Hrow.
      pose proof (proj1 (Forall_forall _ _) Hmult m Hm) as Hwidth.
      change (C.row_key_bits p + C.row_bits p <= bits) in Hrow.
      change (Z.size_nat m <= multbits) in Hwidth. lia. }
    lia.
  Qed.

  (** One elimination step requires only a quadratic bit charge per raw source term. *)
  Lemma poly_scale_one_measure_terms : forall P c ms dim bits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    length ms = length P -> Forall (fun m => Z.size_nat m <= 2 * bits + 2) ms ->
    length (lhs c) <= dim -> C.row_key_bits c + C.row_bits c <= 2 * bits + 1 ->
    C.csize P ms + 2 * (C.lsize c + C.cbits P ms + 1) <=
      12 * (dim + terms (Reached P) + length P + 1) * (bits + 1)^2.
  Proof.
    intros P c ms dim bits Hrows Hlength Hmult Hdim Hwidth.
    pose proof (poly_csize_terms P ms bits (2 * bits + 2) Hrows Hmult Hlength) as Hsize.
    pose proof (poly_cbits_source_bits P ms bits (2 * bits + 2) Hrows Hmult) as Hcbits.
    assert (Hlog : Nat.log2 (length P) <= length P) by (apply Nat.log2_le_lin; lia).
    assert (Hlsize : C.lsize c <= 2 * (dim + 1) * (bits + 1)).
    { unfold C.lsize. eapply Nat.le_trans with (m := (dim + 1) * (2 * bits + 2)).
      - apply Nat.mul_le_mono; lia.
      - nia. }
    set (square := (bits + 1)^2).
    assert (Hsquare : bits + 1 <= square) by (unfold square; cbn [Nat.pow]; nia).
    assert (Hcert : C.csize P ms <= 3 * (terms (Reached P) + length P) * square).
    { eapply Nat.le_trans; [exact Hsize|]. unfold square.
      assert (Hbitproduct : (2 * bits + 2 + 1) * (bits + 1) <= 3 * (bits + 1)^2)
        by (cbn [Nat.pow]; nia).
      apply (Nat.mul_le_mono_l _ _ (terms (Reached P) + length P)) in Hbitproduct.
      nia. }
    assert (Hconclusion : 2 * C.lsize c <= 4 * (dim + 1) * square).
    { pose proof (Nat.mul_le_mono_l _ _ (4 * (dim + 1)) Hsquare). nia. }
    assert (Hwidthpart : 2 * (C.cbits P ms + 1) <= (2 * length P + 8) * square).
    { assert (Hlinear : 2 * (C.cbits P ms + 1) <=
        (2 * length P + 8) * (bits + 1)) by nia.
      eapply Nat.le_trans; [exact Hlinear|]. now apply Nat.mul_le_mono_l. }
    change (C.csize P ms + 2 * (C.lsize c + C.cbits P ms + 1) <=
      12 * (dim + terms (Reached P) + length P + 1) * square).
    clear -Hcert Hconclusion Hwidthpart. clearbody square. nia.
  Qed.

  Definition poly_projection_envelope (dim mlen bits : nat) (r : tracked X.t) : Prop :=
    length (lhs (row_of r)) <= dim /\
    C.row_key_bits (row_of r) + C.row_bits (row_of r) <= 2 * bits + 1 /\
    length (mults_of r) = mlen /\
    Forall (fun m => Z.size_nat m <= 2 * bits + 2) (mults_of r).

  Lemma poly_T_forallb_members : forall A (f : A -> bool) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (List.T_forallb f T_f xs <= (k + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f T_f k xs. induction xs as [|x xs IH]; intro Hf.
    - time_unfold List.T_forallb. cbn [length]. lia.
    - pose proof (Hf x (or_introl eq_refl)) as Hhead.
      specialize (IH (fun y Hy => Hf y (or_intror Hy))).
      time_unfold List.T_forallb. cbn [length]. time_simpl. nia.
  Qed.

  Definition poly_projection_key (x : X.t) (p : X.t * Z) : bool :=
    negb (X.eqb (fst p) x).
  TimeFun poly_projection_key.

  Lemma T_poly_projection_key_bounded : forall x p bits,
    Pos.size_nat (X.encode (fst p)) <= 2 * bits + 1 ->
    (T_poly_projection_key x p <= (2 * X.c_key + 3) * N.of_nat (bits + 1))%N.
  Proof.
    intros x p bits Hbits. pose proof (X.T_eqb_le (fst p) x) as Hkey.
    unfold X.bits in Hkey.
    assert (Hwidth : (N.of_nat (Pos.size_nat (X.encode (fst p)) + 1) <=
      2 * N.of_nat (bits + 1))%N) by lia.
    pose proof (N.mul_le_mono_l _ _ X.c_key Hwidth) as Hproduct.
    time_unfold T_poly_projection_key. time_simpl. nia.
  Qed.

  Definition poly_projection_factor : N := (12 * C.c_lc + 2 * X.c_key + 24)%N.

  Lemma T_checked_projection_bounded : forall P x r dim bits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    poly_projection_envelope dim (length P) bits r ->
    (T_checked_projection P x r <= poly_projection_factor *
      N.of_nat (dim + terms (Reached P) + length P + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros P x r dim bits Hsource [Hdim [Hwidth [Hlength Hmult]]].
    pose proof (poly_scale_one_measure_terms P (row_of r) (mults_of r) dim bits
      Hsource Hlength Hmult Hdim Hwidth) as Hmeasure.
    pose proof (C.T_check_entails_le P (row_of r) (Cert (mults_of r) 1 false)) as Hcheck.
    change (C.T_check_entails P (row_of r) (Cert (mults_of r) 1 false) <= C.c_lc *
      N.of_nat (C.csize P (mults_of r) + 2 *
        (C.lsize (row_of r) + C.cbits P (mults_of r) + 1)))%N in Hcheck.
    set (work := (N.of_nat (dim + terms (Reached P) + length P + 1) *
      N.of_nat (bits + 1)^2)%N).
    assert (Hcheck_total : (C.T_check_entails P (row_of r) (Cert (mults_of r) 1 false) <=
      12 * C.c_lc * work)%N).
    { eapply N.le_trans; [exact Hcheck|].
      assert (Htransport : (N.of_nat (C.csize P (mults_of r) + 2 *
        (C.lsize (row_of r) + C.cbits P (mults_of r) + 1)) <=
        N.of_nat (12 * (dim + terms (Reached P) + length P + 1) * (bits + 1)^2))%N) by lia.
      rewrite !Nat2N.inj_mul, Nat2N.inj_pow in Htransport.
      change (N.of_nat 2) with 2%N in Htransport.
      change (N.of_nat 12) with 12%N in Htransport.
      apply N.mul_le_mono_l with (p := C.c_lc) in Htransport.
      unfold work. nia. }
    assert (Hkeys : forall p, In p (lhs (row_of r)) ->
      (T_poly_projection_key x p <= (2 * X.c_key + 3) * N.of_nat (bits + 1))%N).
    { intros p Hp. apply T_poly_projection_key_bounded.
      pose proof (poly_row_key_member (row_of r) p Hp). lia. }
    pose proof (poly_T_forallb_members _ (poly_projection_key x) (T_poly_projection_key x)
      ((2 * X.c_key + 3) * N.of_nat (bits + 1))%N (lhs (row_of r)) Hkeys) as Hscan.
    assert (Hscan_linear : (List.T_forallb (poly_projection_key x) (T_poly_projection_key x)
      (lhs (row_of r)) <= (2 * X.c_key + 6) * N.of_nat (dim + 1) *
        N.of_nat (bits + 1))%N).
    { eapply N.le_trans; [exact Hscan|]. clear -Hdim. nia. }
    assert (Hextent : (N.of_nat (dim + 1) * N.of_nat (bits + 1) <= work)%N).
    { unfold work. apply N.mul_le_mono; [lia|rewrite N.pow_2_r; nia]. }
    assert (Hpositive : (1 <= work)%N).
    { eapply N.le_trans; [|exact Hextent].
      change (1 * 1 <= N.of_nat (dim + 1) * N.of_nat (bits + 1))%N.
      apply N.mul_le_mono; lia. }
    assert (Hscan_total : (List.T_forallb (poly_projection_key x) (T_poly_projection_key x)
      (lhs (row_of r)) <= (2 * X.c_key + 6) * work)%N).
    { eapply N.le_trans; [exact Hscan_linear|]. rewrite <- N.mul_assoc.
      now apply N.mul_le_mono_l. }
    time_unfold T_checked_projection. time_simpl.
    change (fun a b : X.t => X.T_eqb a b) with X.T_eqb.
    lazymatch goal with
    | |- context [List.T_forallb ?f ?Tf (lhs (row_of r))] =>
        change f with (poly_projection_key x);
        change Tf with (T_poly_projection_key x)
    end.
    replace (poly_projection_factor *
      N.of_nat (dim + terms (Reached P) + length P + 1) * N.of_nat (bits + 1)^2)%N
      with (poly_projection_factor * work)%N by (unfold work; ring).
    unfold poly_projection_factor. clear -Hcheck_total Hscan_total Hpositive.
    clearbody work. nia.
  Qed.

  (** Filtering and retaining checked output rows charges one certificate check per row. *)
  Lemma T_checked_projections_bounded : forall P x rows dim bits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    Forall (poly_projection_envelope dim (length P) bits) rows ->
    (List.T_filter (checked_projection P x) (T_checked_projection P x) rows +
      ListDef.T_map (@row_of X.t) (@T_row_of X.t)
        (filter (checked_projection P x) rows) <=
      (poly_projection_factor + 8) * N.of_nat (length rows + 1) *
        N.of_nat (dim + terms (Reached P) + length P + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros P x rows dim bits Hsource Hrows.
    set (work := (N.of_nat (dim + terms (Reached P) + length P + 1) *
      N.of_nat (bits + 1)^2)%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. change (1 * 1 <= N.of_nat (dim + terms (Reached P) + length P + 1) *
        N.of_nat (bits + 1)^2)%N. apply N.mul_le_mono; [lia|rewrite N.pow_2_r; nia]. }
    assert (Hcallback : forall r, In r rows ->
      (T_checked_projection P x r <= poly_projection_factor * work)%N).
    { intros r Hr. unfold work. rewrite N.mul_assoc.
      apply T_checked_projection_bounded; [exact Hsource|].
      exact (proj1 (Forall_forall _ _) Hrows r Hr). }
    pose proof (poly_T_filter_members _ (checked_projection P x) (T_checked_projection P x)
      (poly_projection_factor * work)%N rows Hcallback) as Hfilter.
    pose proof (poly_T_map_members _ _ (@row_of X.t) (@T_row_of X.t) 1
      (filter (checked_projection P x) rows)
      ltac:(intros r Hr; time_unfold (@T_row_of); lia)) as Hmap.
    pose proof (filter_length_le (checked_projection P x) rows) as Hlength.
    assert (Hmap_linear : (ListDef.T_map (@row_of X.t) (@T_row_of X.t)
      (filter (checked_projection P x) rows) <= 2 * N.of_nat (length rows) + 1)%N).
    { eapply N.le_trans; [exact Hmap|]. lia. }
    replace ((poly_projection_factor + 8) * N.of_nat (length rows + 1) *
      N.of_nat (dim + terms (Reached P) + length P + 1) * N.of_nat (bits + 1)^2)%N
      with ((poly_projection_factor + 8) * N.of_nat (length rows + 1) * work)%N
      by (unfold work; ring).
    eapply N.le_trans; [apply N.add_le_mono; [exact Hfilter|exact Hmap_linear]|].
    clear -Hpositive. clearbody work.
    rewrite Nat2N.inj_add. change (N.of_nat 1) with 1%N. nia.
  Qed.

  Lemma T_checked_fm_projections_bounded : forall P x dim bits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    Forall (poly_projection_envelope dim (length P) bits) (fm_elim x P) ->
    (List.T_filter (checked_projection P x) (T_checked_projection P x) (fm_elim x P) +
      ListDef.T_map (@row_of X.t) (@T_row_of X.t)
        (filter (checked_projection P x) (fm_elim x P)) <=
      (poly_projection_factor + 8) * N.of_nat (length P + 1)^2 *
        N.of_nat (dim + terms (Reached P) + length P + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros P x dim bits Hsource Hrows.
    eapply N.le_trans; [apply T_checked_projections_bounded; eassumption|].
    repeat apply N.mul_le_mono_r. apply N.mul_le_mono_l.
    pose proof (poly_fm_output_count x P) as Hcount.
    assert (HcountN : (N.of_nat (length (fm_elim x P) + 1) <=
      N.of_nat ((length P + 1)^2))%N) by lia.
    rewrite poly_nat_square, <- N.pow_2_r in HcountN. exact HcountN.
  Qed.
  Definition poly_raw_keys (P : list (lcons X.t)) : nat :=
    fold_right Nat.max 0 (map C.row_key_bits P).

  Definition poly_raw_bits (P : list (lcons X.t)) : nat :=
    fold_right Nat.max 0 (map C.row_bits P) + Nat.log2 (terms (Reached P)) + 1.

  (** Separate key and merged-coefficient widths add to the frozen raw width. *)
  Lemma poly_raw_width : forall P,
    poly_raw_keys P + poly_raw_bits P = nell (Reached P).
  Proof.
    intro P. unfold poly_raw_keys, poly_raw_bits, nell, ell. cbn [prows]. lia.
  Qed.

  (** One input row contributes at most all stored coefficient occurrences. *)
  Lemma poly_raw_row_terms : forall P r, In r P -> length (lhs r) <= terms (Reached P).
  Proof.
    intro P. induction P as [|p P IH]; intros r Hin; [contradiction|].
    change (length (lhs r) <= length (lhs p) + terms (Reached P)).
    destruct Hin as [Hequal|Hin].
    - subst r. lia.
    - specialize (IH r Hin). lia.
  Qed.

  (** Raw normalization bounds every row by the source maxima and total occurrence count. *)
  Lemma poly_raw_normal_widths : forall P r, In r P ->
    C.row_key_bits (poly_normal_row X.encode r) <= poly_raw_keys P /\
    C.row_bits (poly_normal_row X.encode r) <= poly_raw_bits P.
  Proof.
    intros P r Hr. split.
    - eapply Nat.le_trans; [apply poly_normal_row_key_bits|].
      exact (poly_max_member _ C.row_key_bits 0 P r Hr).
    - pose proof (poly_normal_row_log_bits r) as Hnormal.
      pose proof (poly_max_member _ C.row_bits 0 P r Hr) as Hrow.
      pose proof (poly_raw_row_terms P r Hr) as Hterms.
      pose proof (Nat.log2_le_mono _ _ Hterms) as Hlog.
      unfold poly_raw_bits. lia.
  Qed.

  (** Initializing raw rows gives distinct nonzero coefficients on the original variables. *)
  Lemma poly_raw_initial_reduced : forall P,
    Forall (poly_reduced_row (vars_of P))
      (poly_initial X.encode (map (fun r => (r, false)) P)).
  Proof.
    intro P. apply poly_initial_reduced. apply Forall_map, Forall_forall.
    intros r Hr p Hp. cbn [fst] in *. apply poly_vars_of_contains with (r := r).
    - exact Hr.
    - now apply in_map.
  Qed.

  (** Normalized raw inputs and unit vectors establish the complete one-step envelope. *)
  Lemma poly_raw_initial_envelopes : forall P,
    Forall (poly_row_envelope (n P) (length P) (poly_raw_keys P) (poly_raw_bits P))
      (poly_initial X.encode (map (fun r => (r, false)) P)).
  Proof.
    intro P. apply Forall_forall. intros r Hr.
    pose proof (poly_raw_initial_reduced P) as Hsupport.
    pose proof (proj1 (Forall_forall _ _) Hsupport r Hr) as Hreduced.
    pose proof (poly_reduced_dimension (vars_of P) r Hreduced) as Hdim.
    destruct (poly_initial_source P r Hr) as [p [Hp Hrow]].
    destruct (poly_raw_normal_widths P p Hp) as [Hkeys Hbits].
    pose proof (poly_initial_units X.t X.encode (map (fun p => (p, false)) P)) as Hunits.
    destruct (proj1 (Forall_forall _ _) Hunits r Hr) as [Hlength Hunit].
    rewrite length_map in Hlength.
    unfold poly_row_envelope. split; [exact (proj1 Hreduced)|]. split.
    - unfold n. lia.
    - split; [now rewrite Hrow|]. split; [now rewrite Hrow|]. split; [lia|].
      apply Forall_forall. intros z Hz.
      destruct (proj1 (Forall_forall _ _) Hunit z Hz) as [Hequal|Hequal]; subst z;
        cbn [Z.size_nat Pos.size_nat]; lia.
  Qed.

  (** One raw FM step retains the original dimension and bounded tracked coefficients. *)
  Lemma poly_raw_step_envelopes : forall P x,
    Forall (poly_row_envelope (n P) (length P) (poly_raw_keys P)
      (2 * poly_raw_bits P + 1))
      (poly_step X.encode X.eqb x
        (poly_initial X.encode (map (fun r => (r, false)) P))).
  Proof.
    intros P x. apply poly_step_envelopes with (vars := vars_of P).
    - unfold n. lia.
    - apply poly_raw_initial_reduced.
    - apply poly_raw_initial_envelopes.
  Qed.

  (** Every projected raw row fits the dimension and widths charged by havoc. *)
  Lemma poly_raw_fm_envelopes : forall P x,
    Forall (fun r =>
      length (lhs (row_of r)) <= n P /\
      C.row_key_bits (row_of r) + C.row_bits (row_of r) <= 2 * nell (Reached P) + 1 /\
      length (mults_of r) = length P /\
      Forall (fun m => Z.size_nat m <= 2 * nell (Reached P) + 2) (mults_of r))
      (fm_elim x P).
  Proof.
    intros P x. apply Forall_forall. intros r Hr.
    assert (Hlength : length (mults_of r) = length P).
    { destruct (fm_step_mults_checked P x r Hr) as [s [Hcombine Hrow]].
      pose proof (C.combine_admissible P (mults_of r) s Hcombine) as Hadmissible.
      symmetry. exact (proj1 Hadmissible). }
    unfold fm_elim in Hr. apply in_map_iff in Hr as [q [Hequal Hq]]. subst r.
    pose proof (poly_raw_step_envelopes P x) as Hstep.
    destruct (proj1 (Forall_forall _ _) Hstep q Hq) as
      [Hnormal [Hdim [Hkeys [Hbits [Hmult Hwidths]]]]].
    cbn [row_of mults_of] in *. split; [exact Hdim|]. split.
    - rewrite <- poly_raw_width. lia.
    - split; [exact Hlength|]. eapply Forall_impl; [|exact Hwidths]. intros m Hm.
      change (Z.size_nat m <= 2 * poly_raw_bits P + 1 + 1) in Hm.
      change (Z.size_nat m <= 2 * nell (Reached P) + 2).
      rewrite <- poly_raw_width. lia.
  Qed.

  (** Each linear-form entry fits the form's combined key and coefficient width. *)
  Lemma poly_form_entry_bits : forall f p, In p (coef f) ->
    X.bits (fst p) + Z.size_nat (snd p) <= F.form_bits f.
  Proof.
    intros f p Hin. unfold F.form_bits.
    exact (poly_max_member _ (fun p => X.bits (fst p) + Z.size_nat (snd p))
      (Z.size_nat (cst f)) (coef f) p Hin).
  Qed.

  (** The constant of a linear form fits the same width used for its entries. *)
  Lemma poly_form_constant_bits : forall f, Z.size_nat (cst f) <= F.form_bits f.
  Proof.
    intro f. unfold F.form_bits. apply poly_max_base.
  Qed.

  (** Atom subtraction preserves source entry widths before equal keys are merged. *)
  Lemma poly_atom_input_sizes : forall a bits,
    F.form_bits (al a) + F.form_bits (ar a) <= bits ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= bits /\
      Z.size_nat (snd p) <= bits)
      (coef (al a) ++ poly_scale_coef (-1)%Z (coef (ar a))).
  Proof.
    intros a bits Hbits. apply Forall_app. split.
    - apply Forall_forall. intros p Hin.
      pose proof (poly_form_entry_bits (al a) p Hin). unfold X.bits in *. split; lia.
    - unfold poly_scale_coef. apply Forall_map, Forall_forall. intros p Hin.
      pose proof (poly_form_entry_bits (ar a) p Hin). cbn [fst snd].
      replace (-1 * snd p)%Z with (- snd p)%Z by ring.
      rewrite poly_size_opp. unfold X.bits in *. split; lia.
  Qed.

  (** Normalizing an atom fits its source lengths and logarithmic merged width. *)
  Lemma T_poly_atom_normal_bounded : forall a count bits,
    length (coef (al a)) + length (coef (ar a)) <= count ->
    F.form_bits (al a) + F.form_bits (ar a) <= bits ->
    (T_poly_normal_coef X.encode X.T_encode
      (coef (al a) ++ poly_scale_coef (-1)%Z (coef (ar a))) <=
      (2 * poly_log_normal_factor) * N.of_nat (count + 1) *
        N.of_nat (bits + Nat.log2 count + 1))%N.
  Proof.
    intros a count bits Hlength Hbits.
    pose proof (T_poly_normal_log _ bits bits (poly_atom_input_sizes a bits Hbits))
      as Hnormal.
    assert (Hcount : length (coef (al a) ++ poly_scale_coef (-1)%Z (coef (ar a))) <= count).
    { unfold poly_scale_coef. rewrite length_app, length_map. exact Hlength. }
    pose proof (Nat.log2_le_mono _ _ Hcount) as Hlog.
    eapply N.le_trans; [exact Hnormal|].
    replace ((2 * poly_log_normal_factor) * N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N with
      (poly_log_normal_factor * N.of_nat (count + 1) *
        (2 * N.of_nat (bits + Nat.log2 count + 1)))%N by ring.
    apply N.mul_le_mono.
    - apply N.mul_le_mono_l. lia.
    - lia.
  Qed.

  Definition poly_atom_factor : N := (2 * poly_log_normal_factor + 128)%N.

  (** Converting one unwrapped atom pays for its normalization and integer differences. *)
  Lemma T_poly_atom_row_bounded : forall a count bits,
    length (coef (al a)) + length (coef (ar a)) <= count ->
    F.form_bits (al a) + F.form_bits (ar a) <= bits ->
    (T_atom_row a <= poly_atom_factor * N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N.
  Proof.
    intros a count bits Hlength Hbits.
    pose proof (T_poly_atom_normal_bounded a count bits Hlength Hbits) as Hnormal.
    assert (Hright : Forall (fun p => Z.size_nat (snd p) <= bits) (coef (ar a))).
    { apply Forall_forall. intros p Hin.
      pose proof (poly_form_entry_bits (ar a) p Hin). lia. }
    pose proof (T_poly_scale_coef_bounded (-1)%Z (coef (ar a)) bits Hright) as Hscale.
    pose proof (Datatypes.T_app_le (coef (al a))
      (poly_scale_coef (-1)%Z (coef (ar a)))) as Happ.
    pose proof (Z.T_sub_le (cst (ar a)) (cst (al a))) as Hsub.
    pose proof (Z.T_sub_le (cst (ar a) - cst (al a)) 1) as Hstrict.
    pose proof (poly_form_constant_bits (al a)) as Hleftbits.
    pose proof (poly_form_constant_bits (ar a)) as Hrightbits.
    assert (Hdifference : Z.size_nat (cst (ar a) - cst (al a)) <= bits + 1).
    { replace (cst (ar a) - cst (al a))%Z with
        (cst (ar a) + - cst (al a))%Z by ring.
      pose proof (poly_size_add (cst (ar a)) (- cst (al a))).
      rewrite poly_size_opp in *. lia. }
    set (work := (N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N).
    assert (Hcount_work : (N.of_nat (count + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_r (N.of_nat (count + 1))) at 1.
      apply N.mul_le_mono_l. lia. }
    assert (Hbits_work : (N.of_nat (bits + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_l (N.of_nat (bits + 1))) at 1.
      apply N.mul_le_mono; lia. }
    assert (Hpositive : (1 <= work)%N) by lia.
    assert (Hnormal_total : (T_poly_normal_coef X.encode X.T_encode
      (coef (al a) ++ poly_scale_coef (-1)%Z (coef (ar a))) <=
      (2 * poly_log_normal_factor) * work)%N).
    { unfold work. replace ((2 * poly_log_normal_factor) *
        (N.of_nat (count + 1) * N.of_nat (bits + Nat.log2 count + 1)))%N with
        ((2 * poly_log_normal_factor) * N.of_nat (count + 1) *
          N.of_nat (bits + Nat.log2 count + 1))%N by ring. exact Hnormal. }
    assert (Hscale_total : (T_poly_scale_coef (-1)%Z (coef (ar a)) <= 32 * work)%N).
    { change (T_poly_scale_coef (-1)%Z (coef (ar a)) <=
        16 * N.of_nat ((length (coef (ar a)) + 1) * 2 * (bits + 1)))%N in Hscale.
      rewrite !Nat2N.inj_mul in Hscale. change (N.of_nat 2) with 2%N in Hscale.
      eapply N.le_trans; [exact Hscale|].
      replace (16 * (N.of_nat (length (coef (ar a)) + 1) * 2 *
        N.of_nat (bits + 1)))%N with
        (32 * (N.of_nat (length (coef (ar a)) + 1) * N.of_nat (bits + 1)))%N by ring.
      apply N.mul_le_mono_l. unfold work. apply N.mul_le_mono; lia. }
    assert (Happ_total : (Datatypes.T_app (coef (al a))
      (poly_scale_coef (-1)%Z (coef (ar a))) <= work)%N) by lia.
    assert (Hsub_total : (Z.T_sub (cst (ar a)) (cst (al a)) <= 3 * work)%N).
    { assert (Hlinear : (Z.T_sub (cst (ar a)) (cst (al a)) <=
        3 * N.of_nat (bits + 1))%N) by lia.
      eapply N.le_trans; [exact Hlinear|]. now apply N.mul_le_mono_l. }
    assert (Hstrict_total : (Z.T_sub (cst (ar a) - cst (al a)) 1 <= 9 * work)%N).
    { change (Z.size_nat 1) with 1 in Hstrict.
      assert (Hlinear : (Z.T_sub (cst (ar a) - cst (al a)) 1 <=
        9 * N.of_nat (bits + 1))%N) by lia.
      eapply N.le_trans; [exact Hlinear|]. now apply N.mul_le_mono_l. }
    replace (poly_atom_factor * N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N with (poly_atom_factor * work)%N
      by (unfold work; ring).
    time_unfold T_atom_row.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    destruct (alw a), (arw a), (acmp a); time_simpl.
    all: clear -Hnormal_total Hscale_total Happ_total Hsub_total Hstrict_total Hpositive.
    all: clearbody work; unfold poly_atom_factor; rewrite N.mul_add_distr_r; lia.
  Qed.
  (** Emitting zero or one item per source keeps the output count below the input count. *)
  Lemma poly_optional_flat_map_length : forall (A B : Type) (f : A -> option B) xs,
    length (flat_map (fun x => match f x with Some y => [y] | None => [] end) xs) <=
      length xs.
  Proof.
    intros A B f xs. induction xs as [|x xs IH]; cbn [flat_map length]; [lia|].
    destruct (f x); cbn [app length]; lia.
  Qed.

  (** A flat map emitting at most one item pays a constant append charge per callback. *)
  Lemma poly_T_optional_flat_map : forall (A B : Type) (f : A -> option B)
      (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (List.T_flat_map (fun x => match f x with Some y => [y] | None => [] end)
      (fun x => (1 + T_f x)%N) xs <=
      (k + 4) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold List.T_flat_map. cbn [length]. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH (fun y Hy => Hcallback y (or_intror Hy))).
      pose proof (Datatypes.T_app_le
        (match f x with Some y => [y] | None => [] end)
        (flat_map (fun y => match f y with Some z => [z] | None => [] end) xs)) as Happ.
      assert (Hlength : length (match f x with Some y => [y] | None => [] end) <= 1).
      { destruct (f x); cbn [length]; lia. }
      time_unfold List.T_flat_map. cbn [length]. time_simpl. nia.
  Qed.

  Definition poly_assume_factor : N := (poly_atom_factor + 16)%N.

  (** Assumption work charges every atom conversion and adds the linearizer's own clock. *)
  Lemma T_poly_assume_bounded : forall g es s,
    (T_assume g es s <= poly_assume_factor *
      N.of_nat ((length (F.atoms_of g es) + 1) *
        (fold_right Nat.add 0%nat (map tsize es) + 1) *
        (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1)) +
      F.T_atoms_of g es)%N.
  Proof.
    intros g es s.
    set (count := fold_right Nat.add 0%nat (map tsize es)).
    set (bits := F.bits_es g es).
    assert (Hatom : forall a, In a (F.atoms_of g es) ->
      (T_atom_row a <= poly_atom_factor * N.of_nat (count + 1) *
        N.of_nat (bits + Nat.log2 count + 1))%N).
    { intros a Hin. destruct (F.atoms_of_size g es) as [_ Hsizes].
      destruct (proj1 (Forall_forall _ _) Hsizes a Hin) as [Hlength Hbits].
      apply T_poly_atom_row_bounded; [exact Hlength|]. unfold bits. lia. }
    pose proof (poly_T_optional_flat_map _ _ atom_row T_atom_row
      (poly_atom_factor * N.of_nat (count + 1) *
        N.of_nat (bits + Nat.log2 count + 1))%N (F.atoms_of g es) Hatom) as Hflat.
    pose proof (poly_optional_flat_map_length _ _ atom_row (F.atoms_of g es)) as Hlength.
    destruct s as [|P]; time_unfold T_assume; fold count bits.
    - unfold poly_assume_factor, poly_atom_factor.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add. cbn [N.of_nat]. nia.
    - pose proof (Datatypes.T_app_le
        (flat_map (fun a => match atom_row a with Some r => [r] | None => [] end)
          (F.atoms_of g es)) P) as Happ.
      time_simpl. unfold poly_assume_factor.
      rewrite !Nat2N.inj_mul, !Nat2N.inj_add in *; cbn [N.of_nat] in *. nia.
  Qed.

  (** The owner's pinned assumption work covers conversion and the original linearizer clock. *)
  Lemma T_poly_assume_contract : forall g es s,
    (T_assume g es s <= (poly_assume_factor + 1) *
      N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es s. pose proof (T_poly_assume_bounded g es s) as Htime.
    set (work := (length (F.atoms_of g es) + 1) *
      (fold_right Nat.add 0%nat (map tsize es) + 1) *
      (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1)) in *.
    assert (Hwork : (N.of_nat work + F.T_atoms_of g es <=
      N.of_nat (assume_work g es s))%N).
    { unfold assume_work. rewrite Nat2N.inj_add, N2Nat.id.
      apply N.add_le_mono_r.
      replace ((length (prows s) + 1) * (length (F.atoms_of g es) + 1) *
        (fold_right Nat.add 0%nat (map tsize es) + 1) *
        (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1))
        with ((length (prows s) + 1) * work) by (unfold work; nia).
      rewrite Nat2N.inj_mul. nia. }
    rewrite Nat2N.inj_add. cbn [N.of_nat].
    clearbody work. nia.
  Qed.

  Definition poly_raw_row_factor : N := (poly_log_normal_factor + 8)%N.

  (** Raw row normalization fits a uniform occurrence count and its logarithmic width. *)
  Lemma T_poly_raw_normal_row_bounded : forall r count keys bits,
    length (lhs r) <= count -> C.row_key_bits r <= keys -> C.row_bits r <= bits ->
    (T_poly_normal_row X.encode X.T_encode r <=
      poly_raw_row_factor * N.of_nat (count + 1) *
        N.of_nat (keys + bits + Nat.log2 count + 1))%N.
  Proof.
    intros r count keys bits Hlength Hkeys Hbits.
    pose proof (T_poly_normal_log (lhs r) keys bits
      (poly_row_entry_bounds r keys bits Hkeys Hbits)) as Hnormal.
    pose proof (Nat.log2_le_mono _ _ Hlength) as Hlog.
    set (work := (N.of_nat (count + 1) *
      N.of_nat (keys + bits + Nat.log2 count + 1))%N).
    assert (Hnormal_total : (T_poly_normal_coef X.encode X.T_encode (lhs r) <=
      poly_log_normal_factor * work)%N).
    { eapply N.le_trans; [exact Hnormal|]. unfold work.
      replace (poly_log_normal_factor * (N.of_nat (count + 1) *
        N.of_nat (keys + bits + Nat.log2 count + 1)))%N with
        (poly_log_normal_factor * N.of_nat (count + 1) *
          N.of_nat (keys + bits + Nat.log2 count + 1))%N by ring.
      apply N.mul_le_mono; [apply N.mul_le_mono_l|]; lia. }
    assert (Hpositive : (1 <= work)%N).
    { unfold work. change (1 * 1 <= N.of_nat (count + 1) *
        N.of_nat (keys + bits + Nat.log2 count + 1))%N.
      apply N.mul_le_mono; lia. }
    replace (poly_raw_row_factor * N.of_nat (count + 1) *
      N.of_nat (keys + bits + Nat.log2 count + 1))%N with
      (poly_raw_row_factor * work)%N by (unfold work; ring).
    time_unfold (@T_poly_normal_row). time_simpl.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    unfold poly_raw_row_factor. clear -Hnormal_total Hpositive. clearbody work.
    rewrite N.mul_add_distr_r. lia.
  Qed.

  Definition poly_raw_initial_factor : N := (poly_raw_row_factor + 16)%N.

  (** Initializing raw rows also pays for the quadratic identity-multiplier vectors. *)
  Lemma T_poly_initial_raw_bounded : forall inputs count keys bits,
    Forall (fun p => length (lhs (fst p)) <= count /\
      C.row_key_bits (fst p) <= keys /\ C.row_bits (fst p) <= bits) inputs ->
    (T_poly_initial X.encode X.T_encode inputs <=
      poly_raw_initial_factor * N.of_nat (length inputs + 1)^2 *
        N.of_nat (count + 1) * N.of_nat (keys + bits + Nat.log2 count + 1))%N.
  Proof.
    intro inputs. induction inputs as [|[r flag] inputs IH]; intros count keys bits Hrows.
    - assert (Hcount : (1 <= N.of_nat (count + 1))%N) by lia.
      assert (Hwidth : (1 <= N.of_nat (keys + bits + Nat.log2 count + 1))%N) by lia.
      time_unfold (@T_poly_initial). time_simpl.
      unfold poly_raw_initial_factor, poly_raw_row_factor. nia.
    - inversion Hrows as [|p ps [Hlength [Hkeys Hbits]] Htail]; subst p ps.
      specialize (IH count keys bits Htail).
      pose proof (T_poly_raw_normal_row_bounded r count keys bits Hlength Hkeys Hbits)
        as Hrow.
      pose proof (poly_T_map_members _ _ (fun _ : lcons X.t * bool => 0%Z)
        (fun _ : lcons X.t * bool => 1%N) 1 inputs
        (fun _ _ => N.le_refl 1%N)) as Hzeros.
      pose proof (poly_T_map_members _ _ (@poly_pad_row X.t) (@T_poly_pad_row X.t) 4
        (poly_initial X.encode inputs) ltac:(intros; apply T_poly_pad_row_le)) as Hpad.
      rewrite poly_initial_length in Hpad.
      assert (Hcount : (1 <= N.of_nat (count + 1))%N) by lia.
      assert (Hwidth : (1 <= N.of_nat (keys + bits + Nat.log2 count + 1))%N) by lia.
      time_unfold (@T_poly_initial). cbn [fst snd length].
      change (fun p => T_poly_pad_row p) with (@T_poly_pad_row X.t).
      unfold poly_raw_initial_factor in *. time_simpl.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      rewrite N.pow_2_r in IH |- *. nia.
  Qed.

  (** All raw source rows fit the total occurrence count and their original maxima. *)
  Lemma poly_raw_initial_sources : forall P,
    Forall (fun p => length (lhs (fst p)) <= terms (Reached P) /\
      C.row_key_bits (fst p) <= poly_raw_keys P /\
      C.row_bits (fst p) <= fold_right Nat.max 0 (map C.row_bits P))
      (map (fun r => (r, false)) P).
  Proof.
    intro P. apply Forall_map, Forall_forall. intros r Hr. cbn [fst]. split.
    - now apply poly_raw_row_terms.
    - split; apply poly_max_member; exact Hr.
  Qed.

  Definition poly_raw_fm_work (P : list (lcons X.t)) : N :=
    (N.of_nat (length P + 1)^2 *
      (N.of_nat (n P + terms (Reached P) + length P + 1) *
        N.of_nat (nell (Reached P) + 1)^2))%N.

  Lemma poly_raw_fm_work_positive : forall P, (1 <= poly_raw_fm_work P)%N.
  Proof.
    intro P. unfold poly_raw_fm_work.
    change (1 * (1 * 1) <= N.of_nat (length P + 1)^2 *
      (N.of_nat (n P + terms (Reached P) + length P + 1) *
        N.of_nat (nell (Reached P) + 1)^2))%N.
    apply N.mul_le_mono; [rewrite N.pow_2_r; nia|].
    apply N.mul_le_mono; [lia|rewrite N.pow_2_r; nia].
  Qed.

  Definition poly_raw_fm_factor : N := (poly_raw_initial_factor + poly_step_factor + 32)%N.

  (** Raw initialization and one elimination fit the same counted output stage. *)
  Lemma T_poly_fm_raw_bounded : forall x P,
    (T_fm_elim x P <= poly_raw_fm_factor * poly_raw_fm_work P)%N.
  Proof.
    intros x P.
    set (input := map (fun r => (r, false)) P).
    set (initial := poly_initial X.encode input).
    set (rows := poly_step X.encode X.eqb x initial).
    set (count := (N.of_nat (length P + 1)^2)%N).
    set (work := (N.of_nat (n P + terms (Reached P) + length P + 1) *
      N.of_nat (nell (Reached P) + 1)^2)%N).
    assert (Hcount : (N.of_nat (length P + 1) <= count)%N)
      by (unfold count; rewrite N.pow_2_r; nia).
    assert (Hcount_positive : (1 <= count)%N) by lia.
    assert (Hwork : (1 <= work)%N).
    { unfold work. change (1 * 1 <=
        N.of_nat (n P + terms (Reached P) + length P + 1) *
        N.of_nat (nell (Reached P) + 1)^2)%N.
      apply N.mul_le_mono; [lia|rewrite N.pow_2_r; nia]. }
    assert (Hlength : length initial = length P).
    { unfold initial, input. now rewrite poly_initial_length, length_map. }
    pose proof (T_poly_initial_raw_bounded input (terms (Reached P)) (poly_raw_keys P)
      (fold_right Nat.max 0 (map C.row_bits P)) (poly_raw_initial_sources P)) as Hinitial.
    assert (Hwidth : poly_raw_keys P + fold_right Nat.max 0 (map C.row_bits P) +
      Nat.log2 (terms (Reached P)) + 1 = nell (Reached P)).
    { unfold poly_raw_keys, nell, ell. cbn [prows]. lia. }
    rewrite Hwidth in Hinitial. unfold input in Hinitial. rewrite length_map in Hinitial.
    fold input count in Hinitial.
    assert (Hinitial_span : (N.of_nat (terms (Reached P) + 1) *
      N.of_nat (nell (Reached P)) <= work)%N).
    { unfold work. apply N.mul_le_mono; [lia|rewrite N.pow_2_r; nia]. }
    assert (Hinitial_total : (T_poly_initial X.encode X.T_encode input <=
      poly_raw_initial_factor * count * work)%N).
    { eapply N.le_trans; [exact Hinitial|].
      replace (poly_raw_initial_factor * count * N.of_nat (terms (Reached P) + 1) *
        N.of_nat (nell (Reached P)))%N with
        (poly_raw_initial_factor * count *
          (N.of_nat (terms (Reached P) + 1) * N.of_nat (nell (Reached P))))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (T_poly_step_bounded x initial (n P) (length P)
      (poly_raw_keys P) (poly_raw_bits P) (poly_raw_initial_envelopes P)) as Hstep.
    rewrite Hlength in Hstep. fold count in Hstep.
    assert (Hstep_span : (poly_clock_span (n P) (length P)
      (poly_raw_keys P) (poly_raw_bits P) <= work)%N).
    { unfold poly_clock_span, work. rewrite poly_raw_width.
      apply N.mul_le_mono; [lia|reflexivity]. }
    assert (Hstep_total : (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x initial <=
      poly_step_factor * count * work)%N).
    { eapply N.le_trans; [exact Hstep|]. now apply N.mul_le_mono_l. }
    pose proof (poly_T_map_members _ _ (fun r : lcons X.t => (r, false))
      (fun _ => 1%N) 1 P (fun _ _ => N.le_refl 1%N)) as Hinput.
    assert (Hinput_total : (ListDef.T_map (fun r : lcons X.t => (r, false))
      (fun _ => 1%N) P <= 2 * count * work)%N).
    { eapply N.le_trans with (m := (2 * count)%N); [lia|].
      rewrite <- (N.mul_1_r (2 * count)) at 1. now apply N.mul_le_mono_l. }
    pose proof (T_poly_track_map rows) as Houtput.
    pose proof (poly_fm_output_count x P) as Hrows.
    unfold fm_elim in Hrows. rewrite length_map in Hrows. fold input initial rows in Hrows.
    assert (HrowsN : (N.of_nat (length rows) + 1 <= count)%N).
    { assert (Htransport : (N.of_nat (length rows + 1) <=
        N.of_nat ((length P + 1)^2))%N) by (clear -Hrows; lia).
      rewrite Nat2N.inj_add, poly_nat_square in Htransport.
      change (N.of_nat 1) with 1%N in Htransport.
      unfold count. rewrite N.pow_2_r. exact Htransport. }
    assert (Houtput_total : (ListDef.T_map
      (fun r => Tracked X.t (poly_constraint r) (poly_multipliers r))
      (fun _ => 3%N) rows <= 5 * count * work)%N).
    { eapply N.le_trans with (m := (5 * count)%N); [lia|].
      rewrite <- (N.mul_1_r (5 * count)) at 1. now apply N.mul_le_mono_l. }
    assert (Hpositive : (1 <= count * work)%N).
    { change (1 * 1 <= count * work)%N. now apply N.mul_le_mono. }
    time_unfold T_fm_elim. fold input initial rows. time_simpl.
    change (fun _ : poly_row X.t => (1 + (1 + 1))%N)
      with (fun _ : poly_row X.t => 3%N).
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    unfold poly_raw_fm_factor, poly_raw_fm_work. fold count work.
    rewrite <- N.mul_assoc in Hinitial_total.
    rewrite <- N.mul_assoc in Hstep_total.
    rewrite <- N.mul_assoc in Hinput_total.
    rewrite <- N.mul_assoc in Houtput_total.
    set (total := (count * work)%N) in *.
    clear -Hinitial_total Hstep_total Hinput_total Houtput_total Hpositive.
    clearbody total. nia.
  Qed.

  (** Havoc's frozen width and dimension dominate the complete raw elimination stage. *)
  Lemma poly_raw_fm_work_havoc : forall x P,
    (poly_raw_fm_work P <= N.of_nat (havoc_work x (Reached P) + 1))%N.
  Proof.
    intros x P.
    assert (Hwidth : (nell (Reached P) + 1)^2 <=
      (nell (Reached P) + X.bits x + 1)^2) by (apply Nat.pow_le_mono_l; lia).
    assert (Hstage : (length P + 1)^2 *
      (n P + terms (Reached P) + length P + 1) * (nell (Reached P) + 1)^2 <=
      havoc_work x (Reached P) + 1).
    { pose proof (Nat.mul_le_mono_l _ _
        ((length P + 1)^2 * (n P + terms (Reached P) + length P + 1)) Hwidth).
      unfold havoc_work. cbn [prows]. lia. }
    change (N.of_nat (length P + 1)^2 *
      poly_clock_span (n P + terms (Reached P)) (length P) 0 (nell (Reached P)) <=
      N.of_nat (havoc_work x (Reached P) + 1))%N.
    rewrite <- poly_fm_charge_nat. cbn [Nat.add] in *.
    clear -Hstage. lia.
  Qed.

  Definition poly_havoc_factor : N :=
    (poly_raw_fm_factor + poly_projection_factor + 16)%N.

  Lemma T_poly_havoc_reached_bounded : forall x P,
    (T_havoc x (Reached P) <= poly_havoc_factor * poly_raw_fm_work P)%N.
  Proof.
    intros x P. pose proof (T_poly_fm_raw_bounded x P) as Hfm.
    pose proof (T_checked_fm_projections_bounded P x (n P) (nell (Reached P))
      (poly_raw_source_width P) (poly_raw_fm_envelopes P x)) as Hprojection.
    assert (Hprojection_total : (List.T_filter (checked_projection P x)
      (T_checked_projection P x) (fm_elim x P) +
      ListDef.T_map (@row_of X.t) (@T_row_of X.t)
        (filter (checked_projection P x) (fm_elim x P)) <=
      (poly_projection_factor + 8) * poly_raw_fm_work P)%N).
    { eapply N.le_trans; [exact Hprojection|]. unfold poly_raw_fm_work. ring_simplify. lia. }
    pose proof (poly_raw_fm_work_positive P) as Hpositive.
    time_unfold T_havoc. revert Hprojection_total. time_simpl. intro Hprojection_total.
    change (@T_row_of X.t) with (fun _ : tracked X.t => 1%N) in Hprojection_total.
    change (fun r : tracked X.t => T_checked_projection P x r)
      with (T_checked_projection P x).
    unfold poly_havoc_factor.
    set (work := poly_raw_fm_work P) in *.
    clear -Hfm Hprojection_total Hpositive. clearbody work. nia.
  Qed.

  (** Raw havoc pays for initialization, one FM step, and every independent projection check. *)
  Lemma T_poly_havoc_bounded : forall x s,
    (T_havoc x s <= poly_havoc_factor * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x [|P].
    - time_unfold T_havoc. change (1 * 1 <=
        poly_havoc_factor * N.of_nat (havoc_work x Unreached + 1))%N.
      apply N.mul_le_mono; [unfold poly_havoc_factor; lia|lia].
    - eapply N.le_trans; [apply T_poly_havoc_reached_bounded|].
      apply N.mul_le_mono_l. apply poly_raw_fm_work_havoc.
  Qed.

  (** Division by a positive integer cannot enlarge an integer's absolute value. *)
  Lemma poly_div_abs_le : forall a b, (0 < b)%Z ->
    (Z.abs (a / b) <= Z.abs a)%Z.
  Proof.
    intros a b Hb.
    pose proof (Z.abs_nonneg a) as Hnonnegative.
    assert (Hupper : (a <= Z.abs a)%Z) by (destruct a; cbn [Z.abs]; lia).
    assert (Hlower : (-a <= Z.abs a)%Z) by (destruct a; cbn [Z.abs]; lia).
    apply Z.abs_le. split.
    - apply Z.div_le_lower_bound; [exact Hb|]. nia.
    - apply Z.div_le_upper_bound; [exact Hb|]. nia.
  Qed.

  (** Rounded division by a positive divisor preserves the numerator's binary width bound. *)
  Lemma poly_div_size_le : forall a b, (0 < b)%Z ->
    Z.size_nat (a / b) <= Z.size_nat a.
  Proof.
    intros a b Hb. apply poly_size_least.
    eapply Nat.le_lt_trans; [|apply poly_magnitude_upper].
    unfold poly_magnitude. apply Z2Nat.inj_le;
      [apply Z.abs_nonneg|apply Z.abs_nonneg|].
    now apply poly_div_abs_le.
  Qed.

  Definition poly_bound_bits (b : bnd) : nat :=
    match b with Fin z => Z.size_nat z | _ => 0 end.

  (** Intersecting a lower endpoint selects one of the two finite values. *)
  Lemma poly_lower_bits : forall z b,
    poly_bound_bits (poly_lower z b) <= Nat.max (Z.size_nat z) (poly_bound_bits b).
  Proof.
    intros z [|n|]; cbn [poly_lower poly_bound_bits]; try lia.
    destruct (Z.le_ge_cases z n) as [Hle|Hle].
    - rewrite Z.max_r by exact Hle. lia.
    - rewrite Z.max_l by exact Hle. lia.
  Qed.

  (** Intersecting an upper endpoint selects one of the two finite values. *)
  Lemma poly_upper_bits : forall z b,
    poly_bound_bits (poly_upper z b) <= Nat.max (Z.size_nat z) (poly_bound_bits b).
  Proof.
    intros z [|n|]; cbn [poly_upper poly_bound_bits]; try lia.
    destruct (Z.le_ge_cases z n) as [Hle|Hle].
    - rewrite Z.min_l by exact Hle. lia.
    - rewrite Z.min_r by exact Hle. lia.
  Qed.

  Definition poly_bounds_width (bits : nat) (bounds : bnd * bnd) : Prop :=
    poly_bound_bits (fst bounds) <= bits /\ poly_bound_bits (snd bounds) <= bits.

  (** Every range-update endpoint fits the current bound or the incoming row's right-hand side. *)
  Lemma poly_range_update_width : forall a b is_eq bounds bits,
    Z.size_nat b <= bits -> poly_bounds_width bits bounds ->
    poly_bounds_width bits (range_update a b is_eq bounds).
  Proof.
    intros a b is_eq [lo hi] bits Hb [Hlo Hhi].
    cbn [fst snd] in Hlo, Hhi. unfold range_update.
    destruct (0 <? a)%Z eqn:Hpositive.
    - apply Z.ltb_lt in Hpositive.
      pose proof (poly_div_size_le b a Hpositive) as Hdiv.
      pose proof (poly_div_size_le (-b) a Hpositive) as Hnegdiv.
      rewrite poly_size_opp in Hnegdiv.
      pose proof (poly_lower_bits (-((-b)/a)) lo) as Hlower.
      pose proof (poly_upper_bits (b/a) hi) as Hupper.
      rewrite poly_size_opp in Hlower.
      destruct is_eq; unfold poly_bounds_width; cbn [fst snd]; split; lia.
    - destruct (a <? 0)%Z eqn:Hnegative; [|exact (conj Hlo Hhi)].
      apply Z.ltb_lt in Hnegative.
      assert (Hdivisor : (0 < -a)%Z) by lia.
      pose proof (poly_div_size_le b (-a) Hdivisor) as Hdiv.
      pose proof (poly_div_size_le (-b) (-a) Hdivisor) as Hnegdiv.
      rewrite poly_size_opp in Hnegdiv.
      pose proof (poly_lower_bits (-(b/(-a))) lo) as Hlower.
      pose proof (poly_upper_bits ((-b)/(-a)) hi) as Hupper.
      rewrite poly_size_opp in Hlower.
      destruct is_eq; unfold poly_bounds_width; cbn [fst snd]; split; lia.
  Qed.

  (** Certificate rejection leaves bounds unchanged, and acceptance uses only the projected RHS. *)
  Lemma poly_range_candidate_width : forall P f bounds r bits,
    Z.size_nat (rhs (poly_constraint r)) <= bits -> poly_bounds_width bits bounds ->
    poly_bounds_width bits (range_candidate P f bounds r).
  Proof.
    intros P f bounds r bits Hrhs Hbounds. unfold range_candidate.
    destruct (forallb _ _); [|exact Hbounds].
    destruct (poly_multipliers r) as [|m ms]; [exact Hbounds|].
    destruct (C.check_entails _ _ _); [|exact Hbounds].
    apply poly_range_update_width; assumption.
  Qed.

  (** The complete endpoint fold preserves a uniform right-hand-side width envelope. *)
  Lemma poly_range_fold_width : forall P f rows bounds bits,
    Forall (fun r => Z.size_nat (rhs (poly_constraint r)) <= bits) rows ->
    poly_bounds_width bits bounds ->
    poly_bounds_width bits (fold_left (range_candidate P f) rows bounds).
  Proof.
    intros P f rows. induction rows as [|r rows IH]; intros bounds bits Hrows Hbounds.
    - exact Hbounds.
    - inversion Hrows as [|q qs Hhead Htail]; subst q qs. cbn [fold_left].
      apply IH; [exact Htail|]. now apply poly_range_candidate_width.
  Qed.
  (** The doubled-width recurrence has an exact multiplicative successor form. *)
  Lemma poly_width_after_successor : forall fuel bits,
    poly_width_after fuel bits + 1 = 2 ^ fuel * (bits + 1).
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intro bits; cbn [poly_width_after].
    - cbn [Nat.pow]. lia.
    - rewrite IH. cbn [Nat.pow]. nia.
  Qed.

  (** Extra elimination fuel can only increase the width envelope. *)
  Lemma poly_width_after_fuel_mono : forall fuel fuel' bits,
    fuel <= fuel' -> poly_width_after fuel bits <= poly_width_after fuel' bits.
  Proof.
    intros fuel fuel' bits Hfuel.
    pose proof (poly_width_after_successor fuel bits) as Hleft.
    pose proof (poly_width_after_successor fuel' bits) as Hright.
    assert (Hpower : 2 ^ fuel <= 2 ^ fuel') by (apply Nat.pow_le_mono_r; lia).
    nia.
  Qed.

  (** A multiplicative initial width allowance remains valid after every elimination. *)
  Lemma poly_width_after_scaled : forall fuel small big factor,
    big + 1 <= factor * (small + 1) ->
    poly_width_after fuel big + 1 <= factor * (poly_width_after fuel small + 1).
  Proof.
    intros fuel small big factor Hwidth. rewrite !poly_width_after_successor.
    replace (factor * (2 ^ fuel * (small + 1))) with
      (2 ^ fuel * (factor * (small + 1))) by nia.
    now apply Nat.mul_le_mono_l.
  Qed.

  (** The terminal recurrence charge alone covers its complete final arithmetic width. *)
  Lemma poly_fmcost_terminal_width : forall fuel dim mlen rows bits,
    (dim + mlen + 1) * (poly_width_after fuel bits + 1) <=
      fmcost dim mlen fuel rows bits.
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros dim mlen rows bits.
    - cbn [poly_width_after fmcost]. nia.
    - cbn [poly_width_after fmcost].
      pose proof (IH dim mlen (rows ^ 2 / 4 + rows) (2 * bits + 1)). lia.
  Qed.

  (** A linear extra raw width is paid by the dimension factor in terminal work. *)
  Lemma poly_range_width_work : forall fuel dim mlen rows rawbits bits,
    fuel <= dim -> rawbits + 1 <= 2 * (dim + mlen + 1) * (bits + 1) ->
    poly_width_after fuel rawbits + 1 <= 2 * fmcost dim mlen dim rows bits.
  Proof.
    intros fuel dim mlen rows rawbits bits Hfuel Hwidth.
    pose proof (poly_width_after_fuel_mono fuel dim rawbits Hfuel) as Hgrowth.
    pose proof (poly_width_after_scaled dim bits rawbits (2 * (dim + mlen + 1))
      Hwidth) as Hscaled.
    pose proof (poly_fmcost_terminal_width dim dim mlen rows bits) as Hwork. nia.
  Qed.

  (** Adding raw occurrences increases the floor logarithm by at most their count. *)
  Lemma poly_log_add_count : forall a b, Nat.log2 (a + b) <= Nat.log2 a + b.
  Proof.
    intros a b. induction b as [|b IH].
    - rewrite Nat.add_0_r. lia.
    - rewrite Nat.add_succ_r. pose proof (Nat.log2_succ_le (a + b)). lia.
  Qed.

  (** A doubled initial bit width changes every stage charge by at most four. *)
  Lemma poly_fmcost_double_width : forall fuel dim mlen rows bits,
    fmcost dim mlen fuel rows (2 * bits + 1) <=
      4 * fmcost dim mlen fuel rows bits.
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros dim mlen rows bits.
    - change ((rows + 1) * (dim + mlen + 1) * (2 * bits + 1 + 1) <=
        4 * ((rows + 1) * (dim + mlen + 1) * (bits + 1))). nia.
    - change ((rows + 1)^2 * (dim + mlen + 1) * (2 * bits + 1 + 1)^2 +
        fmcost dim mlen fuel (rows^2 / 4 + rows) (2 * (2 * bits + 1) + 1) <=
        4 * ((rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2 +
          fmcost dim mlen fuel (rows^2 / 4 + rows) (2 * bits + 1))).
      specialize (IH dim mlen (rows^2 / 4 + rows) (2 * bits + 1)).
      assert (Hsquare : (2 * bits + 1 + 1)^2 = 4 * (bits + 1)^2)
        by (cbn [Nat.pow]; nia).
      rewrite Hsquare.
      rewrite (Nat.mul_add_distr_l 4
        ((rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2)
        (fmcost dim mlen fuel (rows^2 / 4 + rows) (2 * bits + 1))).
      apply Nat.add_le_mono; [nia|exact IH].
  Qed.

  Lemma poly_vars_fold_nodup : forall xs acc,
    NoDup acc -> NoDup (fold_left
      (fun acc y => if existsb (X.eqb y) acc then acc else y :: acc) xs acc).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros acc Hunique; [exact Hunique|].
    cbn [fold_left]. apply IH. destruct (existsb (X.eqb x) acc) eqn:Hpresent;
      [exact Hunique|]. constructor; [|exact Hunique]. intro Hin.
    assert (Htrue : existsb (X.eqb x) acc = true).
    { apply existsb_exists. exists x. split; [exact Hin|apply poly_key_eqb_refl]. }
    congruence.
  Qed.

  Lemma poly_vars_fold_support : forall xs acc x,
    In x (fold_left
      (fun acc y => if existsb (X.eqb y) acc then acc else y :: acc) xs acc) ->
    In x acc \/ In x xs.
  Proof.
    intro xs. induction xs as [|y xs IH]; intros acc x Hin; cbn [fold_left] in Hin.
    - now left.
    - destruct (IH _ x Hin) as [Hhead|Htail].
      + destruct (existsb (X.eqb y) acc); [now left|].
        destruct Hhead as [Hsame|Hhead]; [right; now left|now left].
      + right. now right.
  Qed.

  Lemma poly_vars_of_nodup : forall P, NoDup (vars_of P).
  Proof.
    intro P. unfold vars_of. apply poly_vars_fold_nodup. constructor.
  Qed.

  Lemma poly_vars_of_support : forall P x,
    In x (vars_of P) -> exists r, In r P /\ In x (map fst (lhs r)).
  Proof.
    intros P x Hin. unfold vars_of in Hin.
    apply poly_vars_fold_support in Hin as [Hempty|Hin]; [contradiction|].
    now apply in_flat_map in Hin.
  Qed.

  Lemma poly_normal_row_keys : forall r x,
    In x (map fst (lhs (poly_normal_row X.encode r))) -> In x (map fst (lhs r)).
  Proof.
    intros r x Hin. apply in_map_iff in Hin as [p [Hsame Hp]]. subst x.
    cbn [poly_normal_row lhs] in Hp. now apply poly_normal_coef_keys in Hp.
  Qed.

  Lemma poly_normal_rows_length : forall P, length (poly_normal_rows P) = length P.
  Proof. intro P. unfold poly_normal_rows. apply length_map. Qed.

  Lemma poly_normal_rows_normal : forall P, normal (poly_normal_rows P).
  Proof.
    intro P. unfold normal, poly_normal_rows. apply Forall_map, Forall_forall.
    intros r Hr. cbn [poly_normal_row lhs]. apply poly_normal_coef_nodup.
  Qed.

  Lemma poly_normal_row_length : forall r,
    length (lhs (poly_normal_row X.encode r)) <= length (lhs r).
  Proof.
    intro r. cbn [poly_normal_row lhs]. apply poly_normal_length.
  Qed.

  Lemma poly_normal_rows_variables : forall P,
    incl (vars_of (poly_normal_rows P)) (vars_of P).
  Proof.
    intros P x Hin. destruct (poly_vars_of_support _ _ Hin) as [r [Hr Hx]].
    unfold poly_normal_rows in Hr. apply in_map_iff in Hr as [p [Hsame Hp]]. subst r.
    apply poly_vars_of_contains with (r := p); [exact Hp|].
    now apply poly_normal_row_keys in Hx.
  Qed.

  Lemma poly_normal_rows_n : forall P, n (poly_normal_rows P) <= n P.
  Proof.
    intro P. unfold n. rewrite poly_normal_rows_length. apply Nat.add_le_mono_l.
    apply NoDup_incl_length; [apply poly_vars_of_nodup|apply poly_normal_rows_variables].
  Qed.

  Lemma poly_normal_entail_dimension : forall P c,
    n (poly_normal_rows P) + length (lhs (poly_normal_row X.encode c)) <=
      n P + length (lhs c).
  Proof.
    intros P c. apply Nat.add_le_mono; [apply poly_normal_rows_n|apply poly_normal_row_length].
  Qed.

  (** Normal sources do not gain width when they cross the normalized engine boundary. *)
  Lemma poly_normal_rows_ell : forall P, normal P -> ell (poly_normal_rows P) <= ell P.
  Proof.
    intros P Hnormal. unfold ell. apply Nat.add_le_mono.
    - apply poly_max_bound; [lia|]. unfold poly_normal_rows. apply Forall_map, Forall_forall.
      intros r Hr. eapply Nat.le_trans.
      + apply poly_normal_row_bits. exact (proj1 (Forall_forall _ _) Hnormal r Hr).
      + exact (poly_max_member _ C.row_bits 0 P r Hr).
    - apply poly_max_bound; [lia|]. unfold poly_normal_rows. apply Forall_map, Forall_forall.
      intros r Hr. eapply Nat.le_trans; [apply poly_normal_row_key_bits|].
      exact (poly_max_member _ C.row_key_bits 0 P r Hr).
  Qed.

  Lemma poly_normal_entail_width_normal : forall P c, normal P -> normal [c] ->
    ell (poly_normal_rows P) + C.row_bits (poly_normal_row X.encode c) +
      C.row_key_bits (poly_normal_row X.encode c) <=
      ell P + C.row_bits c + C.row_key_bits c.
  Proof.
    intros P c HP Hc. pose proof (poly_normal_rows_ell P HP) as Hrows.
    pose proof (poly_normal_row_bits c (Forall_inv Hc)) as Hbits.
    pose proof (poly_normal_row_key_bits c) as Hkeys. lia.
  Qed.

  (** Raw sources and the target share the same global logarithmic width. *)
  Lemma poly_normal_entail_width_raw : forall P c,
    ell (poly_normal_rows P) + C.row_bits (poly_normal_row X.encode c) +
      C.row_key_bits (poly_normal_row X.encode c) <=
      2 * nell (Reached (c :: P)) + 1.
  Proof.
    intros P c.
    destruct (poly_raw_normal_widths (c :: P) c (or_introl eq_refl)) as [Hck Hcb].
    assert (Hrows_bits : fold_right Nat.max 0 (map C.row_bits (poly_normal_rows P)) <=
      poly_raw_bits (c :: P)).
    { apply poly_max_bound; [lia|]. unfold poly_normal_rows. apply Forall_map, Forall_forall.
      intros r Hr. exact (proj2 (poly_raw_normal_widths (c :: P) r (or_intror Hr))). }
    assert (Hrows_keys : fold_right Nat.max 0 (map C.row_key_bits (poly_normal_rows P)) <=
      poly_raw_keys (c :: P)).
    { apply poly_max_bound; [lia|]. unfold poly_normal_rows. apply Forall_map, Forall_forall.
      intros r Hr. exact (proj1 (poly_raw_normal_widths (c :: P) r (or_intror Hr))). }
    unfold ell. rewrite <- poly_raw_width. lia.
  Qed.

  Lemma poly_normal_entail_budget_normal : forall P c, normal P -> normal [c] ->
    poly_entail_budget (poly_normal_rows P) (poly_normal_row X.encode c) <=
      poly_entail_budget P c.
  Proof.
    intros P c HP Hc. unfold poly_entail_budget. rewrite poly_normal_rows_length.
    pose proof (poly_normal_entail_dimension P c) as Hdim.
    pose proof (poly_normal_entail_width_normal P c HP Hc) as Hbits.
    apply poly_fmcost_mono; lia.
  Qed.

  Lemma poly_normal_entail_budget_raw : forall P c,
    poly_entail_budget (poly_normal_rows P) (poly_normal_row X.encode c) <=
      4 * fmcost (n P + length (lhs c)) (length P + 1)
        (n P + length (lhs c)) (length P + 1) (nell (Reached (c :: P))).
  Proof.
    intros P c. unfold poly_entail_budget. rewrite poly_normal_rows_length.
    pose proof (poly_normal_entail_dimension P c) as Hdim.
    pose proof (poly_normal_entail_width_raw P c) as Hbits.
    eapply Nat.le_trans; [|apply poly_fmcost_double_width].
    apply poly_fmcost_mono; lia.
  Qed.

  (** A uniform normal-row envelope also bounds a complete row-map normalization. *)
  Lemma T_poly_normal_rows_bounded : forall P dim keys bits,
    Forall (poly_input_envelope dim keys bits) P ->
    (T_poly_normal_rows P <= (poly_normal_row_factor + 4) * N.of_nat (length P + 1) *
      N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N.
  Proof.
    intros P dim keys bits Hrows.
    set (entry_work := (N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N).
    assert (Hpositive : (1 <= entry_work)%N).
    { unfold entry_work. change (1 * 1 <= N.of_nat (dim + 1) *
        N.of_nat (keys + bits + 1))%N. apply N.mul_le_mono; lia. }
    assert (Hcallback : forall r, In r P ->
      (T_poly_normal_row X.encode X.T_encode r <= poly_normal_row_factor * entry_work)%N).
    { intros r Hr. unfold entry_work. rewrite N.mul_assoc.
      apply T_poly_normal_row_bounded. exact (proj1 (Forall_forall _ _) Hrows r Hr). }
    pose proof (poly_T_map_members _ _ (poly_normal_row X.encode)
      (T_poly_normal_row X.encode X.T_encode) (poly_normal_row_factor * entry_work)%N P
      Hcallback) as Hmap.
    pose proof (poly_clock_linear_count_bound poly_normal_row_factor 1
      (N.of_nat (length P)) (N.of_nat (length P + 1)) entry_work ltac:(lia) Hpositive)
      as Hlinear.
    assert (Hmap_total : (ListDef.T_map (poly_normal_row X.encode)
      (T_poly_normal_row X.encode X.T_encode) P <=
      (poly_normal_row_factor + 2) * N.of_nat (length P + 1) * entry_work)%N).
    { eapply N.le_trans; [exact Hmap|].
      replace (poly_normal_row_factor + 1 + 1)%N with
        (poly_normal_row_factor + 2)%N in Hlinear by lia. exact Hlinear. }
    assert (Hmass : (1 <= N.of_nat (length P + 1) * entry_work)%N).
    { change (1 * 1 <= N.of_nat (length P + 1) * entry_work)%N.
      apply N.mul_le_mono; [lia|exact Hpositive]. }
    time_unfold T_poly_normal_rows. time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    change (1 + ListDef.T_map (poly_normal_row X.encode)
      (T_poly_normal_row X.encode X.T_encode) P <=
      (poly_normal_row_factor + 4) * N.of_nat (length P + 1) *
        N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N.
    replace ((poly_normal_row_factor + 4) * N.of_nat (length P + 1) *
      N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N with
      ((poly_normal_row_factor + 4) * N.of_nat (length P + 1) * entry_work)%N
      by (unfold entry_work; ring).
    clear -Hmap_total Hmass. clearbody entry_work. nia.
  Qed.

  (** The unflagged inputs satisfy the same dimensions and widths as initialization. *)
  Lemma poly_entail_plain_envelopes : forall P c, normal P -> normal [c] ->
    Forall (poly_input_envelope (n P + length (lhs c))
      (poly_entail_keys P c) (poly_entail_bits P c)) (c :: P).
  Proof.
    intros P c HP Hc. constructor.
    - unfold poly_input_envelope. split; [exact (Forall_inv Hc)|].
      split; [lia|]. unfold poly_entail_keys, poly_entail_bits. split; lia.
    - apply Forall_forall. intros r Hr. unfold poly_input_envelope. split.
      + exact (proj1 (Forall_forall _ _) HP r Hr).
      + split.
        * pose proof (poly_row_dimension P r HP Hr). unfold n. lia.
        * pose proof (poly_max_member _ C.row_key_bits 0 P r Hr).
          pose proof (poly_max_member _ C.row_bits 0 P r Hr).
          unfold poly_entail_keys, poly_entail_bits. split; lia.
  Qed.

  Definition poly_entail_normalize_factor : N := (2 * poly_normal_row_factor + 16)%N.

  Lemma T_poly_entail_normalize_normal : forall P c, normal P -> normal [c] ->
    (T_poly_normal_rows P + T_poly_normal_row X.encode X.T_encode c <=
      poly_entail_normalize_factor * N.of_nat (poly_entail_budget P c))%N.
  Proof.
    intros P c HP Hc.
    set (dim := n P + length (lhs c)).
    set (mlen := length P + 1).
    set (keys := poly_entail_keys P c).
    set (bits := poly_entail_bits P c).
    set (count := (N.of_nat (mlen + 1)^2)%N).
    set (entry_work := (N.of_nat (dim + 1) * N.of_nat (keys + bits + 1))%N).
    set (work := (count * entry_work)%N).
    pose proof (poly_entail_plain_envelopes P c HP Hc) as Henvelopes.
    pose proof (T_poly_normal_rows_bounded P dim keys bits (Forall_inv_tail Henvelopes)) as Hrows.
    pose proof (T_poly_normal_row_bounded c dim keys bits (Forall_inv Henvelopes)) as Htarget.
    assert (Hcount : (N.of_nat (length P + 1) <= count)%N).
    { unfold count, mlen. rewrite N.pow_2_r. nia. }
    assert (Hcount_positive : (1 <= count)%N) by (eapply N.le_trans; [|exact Hcount]; lia).
    assert (Hrows_total : (T_poly_normal_rows P <= (poly_normal_row_factor + 4) * work)%N).
    { eapply N.le_trans; [exact Hrows|]. unfold work, entry_work.
      rewrite !N.mul_assoc. apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_l.
      exact Hcount. }
    assert (Hentry : (entry_work <= work)%N).
    { unfold work. rewrite <- (N.mul_1_l entry_work) at 1.
      now apply N.mul_le_mono_r. }
    assert (Htarget_total : (T_poly_normal_row X.encode X.T_encode c <=
      poly_normal_row_factor * work)%N).
    { eapply N.le_trans; [exact Htarget|].
      replace (poly_normal_row_factor * N.of_nat (dim + 1) *
        N.of_nat (keys + bits + 1))%N with
        (poly_normal_row_factor * entry_work)%N by (unfold entry_work; ring).
      now apply N.mul_le_mono_l. }
    assert (Hsum : (T_poly_normal_rows P + T_poly_normal_row X.encode X.T_encode c <=
      poly_entail_normalize_factor * work)%N).
    { unfold poly_entail_normalize_factor. clear -Hrows_total Htarget_total.
      clearbody work. nia. }
    assert (Hwork_bound : (work <= N.of_nat (poly_entail_budget P c))%N).
    { pose proof (poly_fmcost_initial_charge dim mlen (keys + bits)) as Hmeasure.
      replace work with (N.of_nat ((mlen + 1)^2 * (dim + 1) * (keys + bits + 1))).
      - unfold poly_entail_budget. fold dim mlen. rewrite <- poly_entail_width. fold keys bits.
        clear -Hmeasure. lia.
      - unfold work, count, entry_work.
        rewrite !Nat2N.inj_mul, poly_nat_square, N.pow_2_r. ring. }
    eapply N.le_trans; [exact Hsum|]. now apply N.mul_le_mono_l.
  Qed.

  Definition poly_entail_wrapper_factor : N :=
    (poly_entail_factor + poly_entail_normalize_factor + 8)%N.

  (** The new wrapper preserves the existing normal-input public envelope. *)
  Lemma T_poly_entail_bounded : forall P c, normal P -> normal [c] ->
    (T_entail_cert P c <= poly_entail_wrapper_factor *
      N.of_nat (poly_entail_budget P c))%N.
  Proof.
    intros P c HP Hc.
    assert (Hnormal_P : normal (poly_normal_rows P)) by apply poly_normal_rows_normal.
    assert (Hnormal_c : normal [poly_normal_row X.encode c]).
    { change (normal (poly_normal_rows [c])). apply poly_normal_rows_normal. }
    pose proof (T_poly_entail_engine_bounded (poly_normal_rows P) (poly_normal_row X.encode c)
      Hnormal_P Hnormal_c) as Hengine.
    pose proof (poly_normal_entail_budget_normal P c HP Hc) as Hbudget.
    assert (Hengine_total : (T_entail_engine (poly_normal_rows P) (poly_normal_row X.encode c) <=
      poly_entail_factor * N.of_nat (poly_entail_budget P c))%N).
    { eapply N.le_trans; [exact Hengine|]. apply N.mul_le_mono_l. clear -Hbudget. lia. }
    pose proof (T_poly_entail_normalize_normal P c HP Hc) as Hnormalize.
    pose proof (poly_entail_budget_positive P c) as Hpositive.
    set (work := N.of_nat (poly_entail_budget P c)) in *.
    time_unfold T_entail_cert. time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    unfold poly_entail_wrapper_factor.
    clear -Hengine_total Hnormalize Hpositive. clearbody work. nia.
  Qed.

  (** A row pays for its own occurrences at the shared raw-input width. *)
  Lemma T_poly_raw_normal_row_global : forall Q r, In r Q ->
    (T_poly_normal_row X.encode X.T_encode r <=
      poly_raw_row_factor * N.of_nat (length (lhs r) + 1) *
        N.of_nat (nell (Reached Q) + 1))%N.
  Proof.
    intros Q r Hr.
    pose proof (T_poly_raw_normal_row_bounded r (length (lhs r))
      (C.row_key_bits r) (C.row_bits r) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _)) as Hrow.
    pose proof (poly_max_member _ C.row_key_bits 0 Q r Hr) as Hkeys.
    pose proof (poly_max_member _ C.row_bits 0 Q r Hr) as Hbits.
    pose proof (poly_raw_row_terms Q r Hr) as Hlength.
    pose proof (Nat.log2_le_mono _ _ Hlength) as Hlog.
    eapply N.le_trans; [exact Hrow|]. apply N.mul_le_mono_l.
    unfold nell, ell. cbn [prows]. lia.
  Qed.

  (** Mapping row normalization adds the occurrence charges, rather than their maximum. *)
  Lemma T_poly_normal_map_occurrences : forall P factor bits,
    (forall r, In r P -> (T_poly_normal_row X.encode X.T_encode r <=
      factor * N.of_nat (length (lhs r) + 1) * N.of_nat (bits + 1))%N) ->
    (ListDef.T_map (poly_normal_row X.encode) (T_poly_normal_row X.encode X.T_encode) P <=
      (factor + 2) * N.of_nat (terms (Reached P) + length P + 1) *
        N.of_nat (bits + 1))%N.
  Proof.
    intro P. induction P as [|p P IH]; intros factor bits Hrows.
    - time_unfold ListDef.T_map. time_cbn.
      change (1 <= (factor + 2) * 1 * N.of_nat (bits + 1))%N. nia.
    - pose proof (Hrows p (or_introl eq_refl)) as Hhead.
      specialize (IH factor bits (fun r Hr => Hrows r (or_intror Hr))).
      time_unfold ListDef.T_map. time_cbn.
      change (1 + (T_poly_normal_row X.encode X.T_encode p +
        ListDef.T_map (poly_normal_row X.encode) (T_poly_normal_row X.encode X.T_encode) P) <=
        (factor + 2) * N.of_nat
          (length (lhs p) + terms (Reached P) + S (length P) + 1) *
            N.of_nat (bits + 1))%N.
      rewrite !Nat2N.inj_add, Nat2N.inj_succ in *.
      change (N.of_nat 1) with 1%N in *.
      assert (Hwidth : (1 <= N.of_nat bits + 1)%N) by lia.
      clear -Hhead IH Hwidth. nia.
  Qed.

  Definition poly_entail_raw_budget (P : list (lcons X.t)) (c : lcons X.t) : nat :=
    terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
      fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
        (length P + 1) (nell (Reached (c :: P))).

  (** The terminal recurrence charge pays for one normalization unit per input row. *)
  Lemma poly_entail_raw_normalization_charge : forall P c,
    (terms (Reached (c :: P)) + length P + 2) *
      (nell (Reached (c :: P)) + 1) <= poly_entail_raw_budget P c.
  Proof.
    intros P c. set (dim := n P + length (lhs c)).
    set (mlen := length P + 1). set (bits := nell (Reached (c :: P))).
    pose proof (poly_fmcost_fuel_mono 0 dim (Nat.le_0_l _) dim mlen mlen bits) as Hfuel.
    change ((mlen + 1) * (dim + mlen + 1) * (bits + 1) <=
      fmcost dim mlen dim mlen bits) in Hfuel.
    assert (Hbase : (mlen + 1) * (bits + 1) <=
      (mlen + 1) * (dim + mlen + 1) * (bits + 1)).
    { apply Nat.mul_le_mono_r. nia. }
    unfold poly_entail_raw_budget. fold dim mlen bits.
    replace (terms (Reached (c :: P)) + length P + 2) with
      (terms (Reached (c :: P)) + (mlen + 1)) by (unfold mlen; lia).
    rewrite Nat.mul_add_distr_r. lia.
  Qed.

  Definition poly_entail_raw_normalize_factor : N := (poly_raw_row_factor + 8)%N.

  (** Normalizing the public raw boundary fits its explicit occurrence prefix. *)
  Lemma T_poly_entail_normalize_raw : forall P c,
    (T_poly_normal_rows P + T_poly_normal_row X.encode X.T_encode c <=
      poly_entail_raw_normalize_factor * N.of_nat (poly_entail_raw_budget P c))%N.
  Proof.
    intros P c. set (bits := nell (Reached (c :: P))).
    pose proof (T_poly_normal_map_occurrences P poly_raw_row_factor bits
      (fun r Hr => T_poly_raw_normal_row_global (c :: P) r (or_intror Hr))) as Hmap.
    pose proof (T_poly_raw_normal_row_global (c :: P) c (or_introl eq_refl)) as Htarget.
    fold bits in Htarget.
    set (source_mass := N.of_nat (terms (Reached P) + length P + 1)) in *.
    set (target_mass := N.of_nat (length (lhs c) + 1)) in *.
    set (width := N.of_nat (bits + 1)) in *.
    assert (Hpositive : (1 <= width)%N) by (unfold width; lia).
    assert (Hmass : (1 <= source_mass + target_mass)%N).
    { unfold source_mass, target_mass. lia. }
    assert (Hsum : (T_poly_normal_rows P + T_poly_normal_row X.encode X.T_encode c <=
      poly_entail_raw_normalize_factor * (source_mass + target_mass) * width)%N).
    { time_unfold T_poly_normal_rows. time_simpl.
      change (fun x : X.t => X.T_encode x) with X.T_encode.
      change (1 + ListDef.T_map (poly_normal_row X.encode)
        (T_poly_normal_row X.encode X.T_encode) P +
        T_poly_normal_row X.encode X.T_encode c <=
        poly_entail_raw_normalize_factor * (source_mass + target_mass) * width)%N.
      unfold poly_entail_raw_normalize_factor.
      clear -Hmap Htarget Hpositive Hmass.
      clearbody source_mass target_mass width. nia. }
    assert (Hmass_bound : ((source_mass + target_mass) * width <=
      N.of_nat (poly_entail_raw_budget P c))%N).
    { pose proof (poly_entail_raw_normalization_charge P c) as Hcharge.
      replace ((source_mass + target_mass) * width)%N with
        (N.of_nat ((terms (Reached (c :: P)) + length P + 2) * (bits + 1))).
      - unfold bits. clear -Hcharge. lia.
      - unfold source_mass, target_mass, width.
        change (N.of_nat ((length (lhs c) + terms (Reached P) + length P + 2) *
          (bits + 1)) =
          (N.of_nat (terms (Reached P) + length P + 1) +
            N.of_nat (length (lhs c) + 1)) * N.of_nat (bits + 1))%N.
        rewrite !Nat2N.inj_mul, !Nat2N.inj_add. cbn [N.of_nat]. ring. }
    eapply N.le_trans; [exact Hsum|]. rewrite <- N.mul_assoc.
    now apply N.mul_le_mono_l.
  Qed.

  Definition poly_entail_raw_factor : N :=
    (4 * poly_entail_factor + poly_entail_raw_normalize_factor + 8)%N.

  (** The normalized engine preserves the original raw-input time envelope. *)
  Lemma T_poly_entail_raw_bounded : forall P c,
    (T_entail_cert P c <= poly_entail_raw_factor *
      N.of_nat (poly_entail_raw_budget P c))%N.
  Proof.
    intros P c.
    assert (HP : normal (poly_normal_rows P)) by apply poly_normal_rows_normal.
    assert (Hc : normal [poly_normal_row X.encode c]).
    { change (normal (poly_normal_rows [c])). apply poly_normal_rows_normal. }
    pose proof (T_poly_entail_engine_bounded (poly_normal_rows P) (poly_normal_row X.encode c)
      HP Hc) as Hengine.
    pose proof (poly_normal_entail_budget_raw P c) as Hbudget.
    assert (Hbudget_raw : poly_entail_budget (poly_normal_rows P)
      (poly_normal_row X.encode c) <= 4 * poly_entail_raw_budget P c).
    { unfold poly_entail_raw_budget. lia. }
    assert (Hengine_total : (T_entail_engine (poly_normal_rows P) (poly_normal_row X.encode c)
      <= 4 * poly_entail_factor * N.of_nat (poly_entail_raw_budget P c))%N).
    { eapply N.le_trans; [exact Hengine|].
      replace (4 * poly_entail_factor * N.of_nat (poly_entail_raw_budget P c))%N
        with (poly_entail_factor * N.of_nat (4 * poly_entail_raw_budget P c))%N
        by (rewrite Nat2N.inj_mul; change (N.of_nat 4) with 4%N; ring).
      apply N.mul_le_mono_l. clear -Hbudget_raw. lia. }
    pose proof (T_poly_entail_normalize_raw P c) as Hnormalize.
    assert (Hpositive : (1 <= N.of_nat (poly_entail_raw_budget P c))%N).
    { unfold poly_entail_raw_budget. pose proof (poly_fmcost_positive
        (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
        (length P + 1) (nell (Reached (c :: P)))). lia. }
    set (work := N.of_nat (poly_entail_raw_budget P c)) in *.
    time_unfold T_entail_cert. time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    unfold poly_entail_raw_factor.
    clear -Hengine_total Hnormalize Hpositive. clearbody work. nia.
  Qed.


  Definition poly_occurrences (x : X.t) (xs : list X.t) : nat :=
    length (filter (X.eqb x) xs).

  (** Selected and unselected occurrences partition every key list. *)
  Lemma poly_occurrences_partition : forall x xs,
    poly_occurrences x xs + length (filter (fun y => negb (X.eqb x y)) xs) = length xs.
  Proof.
    intros x xs. induction xs as [|y xs IH]; unfold poly_occurrences in *;
      cbn [filter length]; [lia|].
    destruct (X.eqb x y); cbn [negb length]; lia.
  Qed.

  (** A key absent from a list contributes no selected occurrence. *)
  Lemma poly_occurrences_absent : forall x xs,
    ~ In x xs -> poly_occurrences x xs = 0.
  Proof.
    intros x xs. induction xs as [|y xs IH]; intro Habsent; [reflexivity|].
    unfold poly_occurrences in *. cbn [filter].
    destruct (X.eqb_spec x y) as [Hequal|Hother].
    - subst y. exfalso. apply Habsent. now left.
    - apply IH. intro Hin. apply Habsent. now right.
  Qed.

  (** A duplicate-free support contains at most one occurrence of any key. *)
  Lemma poly_occurrences_unique : forall xs, NoDup xs -> forall x,
    poly_occurrences x xs <= 1.
  Proof.
    intros xs Hunique. induction Hunique as [|y xs Habsent Hunique IH]; intro x.
    - change (0 <= 1). lia.
    - unfold poly_occurrences at 1. cbn [filter].
      destruct (X.eqb_spec x y) as [Hequal|Hother].
      + subst y. cbn [length]. fold (poly_occurrences x xs).
        rewrite (poly_occurrences_absent x xs Habsent). lia.
      + apply IH.
  Qed.

  (** Every additional distinct key removes one possible repetition of the selected key. *)
  Lemma poly_occurrences_budget : forall xs vars x,
    NoDup vars -> incl vars xs ->
    poly_occurrences x xs + length vars <= length xs + 1.
  Proof.
    intros xs vars x Hunique Hsupport.
    assert (Hfiltered : length (filter (fun y => negb (X.eqb x y)) vars) <=
      length (filter (fun y => negb (X.eqb x y)) xs)).
    { apply NoDup_incl_length; [now apply NoDup_filter|].
      intros y Hy. apply filter_In in Hy as [Hy Hkeep]. apply filter_In.
      split; [now apply Hsupport|exact Hkeep]. }
    pose proof (poly_occurrences_unique vars Hunique x) as Hone.
    pose proof (poly_occurrences_partition x vars) as Hvars.
    pose proof (poly_occurrences_partition x xs) as Hxs. lia.
  Qed.

  (** The total coefficient magnitude counts only occurrences of its own key. *)
  Lemma poly_coefficient_occurrence_magnitude : forall xs x bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    poly_magnitude (C.coef_of x xs) <=
      poly_occurrences x (map fst xs) * 2 ^ bits.
  Proof.
    intro xs. induction xs as [|[y a] xs IH]; intros x bits Hsizes.
    - change (0 <= 0). lia.
    - inversion Hsizes as [|p ps Ha Htail]; subst p ps.
      pose proof (IH x bits Htail) as Hrest.
      rewrite coef_of_cons. unfold poly_occurrences at 1. cbn [map fst filter].
      destruct (X.eqb x y).
      + cbn [length]. fold (poly_occurrences x (map fst xs)).
        pose proof (poly_magnitude_add a (C.coef_of x xs)) as Hsum.
        pose proof (poly_magnitude_upper a) as Hterm.
        assert (Hpower : 2 ^ Z.size_nat a <= 2 ^ bits).
        { apply Nat.pow_le_mono_r; cbn [snd] in Ha; lia. }
        nia.
      + exact Hrest.
  Qed.

  (** Merging coefficients needs a logarithm of duplicate surplus, not total input length. *)
  Lemma poly_normal_coef_duplicate_bits : forall xs vars bits,
    NoDup vars -> incl vars (map fst xs) ->
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Forall (fun p => Z.size_nat (snd p) <=
      bits + Nat.log2 (length xs - length vars + 1) + 1)
      (poly_normal_coef X.encode xs).
  Proof.
    intros xs vars bits Hunique Hsupport Hsizes.
    assert (Hcount : length vars <= length xs).
    { rewrite <- (length_map fst xs). now apply NoDup_incl_length. }
    apply Forall_forall. intros [x z] Hin. cbn [snd].
    pose proof (poly_coef_member x z (poly_normal_coef X.encode xs)
      (poly_normal_coef_nodup _ _ _) Hin) as Hcoefficient.
    rewrite coef_of_normal in Hcoefficient. rewrite <- Hcoefficient.
    apply poly_count_magnitude_bits.
    eapply Nat.le_trans; [apply poly_coefficient_occurrence_magnitude; exact Hsizes|].
    apply Nat.mul_le_mono_r.
    pose proof (poly_occurrences_budget (map fst xs) vars x Hunique Hsupport) as Hbudget.
    rewrite length_map in Hbudget. lia.
  Qed.

  Definition poly_form_variables (f : lin X.t) : list X.t :=
    poly_variables X.encode [LCons X.t (coef f) REq (cst f)].

  (** The executable distinct form support is included in its raw occurrences. *)
  Lemma poly_form_variables_support : forall f,
    incl (poly_form_variables f) (map fst (coef f)).
  Proof.
    intros f x Hx. destruct (poly_variables_support _ _ Hx) as [r [[Hr|Hr] Hterm]].
    - subst r. exact Hterm.
    - contradiction.
  Qed.

  (** The distinct support cannot outnumber the raw form entries. *)
  Lemma poly_form_variables_length : forall f,
    length (poly_form_variables f) <= length (coef f).
  Proof.
    intro f. rewrite <- (length_map fst (coef f)).
    apply NoDup_incl_length; [apply poly_variables_nodup|apply poly_form_variables_support].
  Qed.

  (** Each form coefficient uses only the logarithm of its duplicate surplus. *)
  Lemma poly_form_duplicate_bits : forall f,
    Forall (fun p => Z.size_nat (snd p) <= F.form_bits f +
      Nat.log2 (length (coef f) - length (poly_form_variables f) + 1) + 1)
      (poly_normal_coef X.encode (coef f)).
  Proof.
    intro f. apply poly_normal_coef_duplicate_bits.
    - apply poly_variables_nodup.
    - apply poly_form_variables_support.
    - apply Forall_forall. intros p Hp. pose proof (poly_form_entry_bits f p Hp). lia.
  Qed.

  (** Each duplicate occurrence provides a spare elimination stage beyond distinct-variable work. *)
  Lemma poly_range_distinct_fuel : forall P f,
    length (poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)) <=
      length (vars_of P) + length (poly_form_variables f).
  Proof.
    intros P f.
    assert (Hlength : length (poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)) <=
      length (vars_of P ++ poly_form_variables f)).
    { apply NoDup_incl_length; [apply poly_variables_nodup|].
      intros x Hx. destruct (poly_variables_support _ _ Hx) as [r [[Hr|Hr] Hterm]].
      - subst r. apply in_or_app. right.
        apply in_map_iff in Hterm as [[y a] [Hsame Hterm]]. cbn [fst] in Hsame. subst y.
        unfold poly_form_variables. apply poly_variables_contains with
          (r := LCons X.t (coef f) REq (cst f)) (a := a); [now left|exact Hterm].
      - apply in_map_iff in Hr as [p [Hsame Hp]]. subst r.
        apply in_or_app. left. apply poly_vars_of_contains with (r := p); [exact Hp|].
        apply in_map_iff in Hterm as [q [Hsame Hq]]. subst x.
        cbn [poly_normal_row lhs] in Hq. now apply poly_normal_coef_keys in Hq. }
    now rewrite length_app in Hlength.
  Qed.

  (** A nonempty source supplies one extra stage beyond all duplicate-growth allowances. *)
  Lemma poly_range_duplicate_fuel : forall P f count,
    P <> [] -> length (coef f) <= count ->
    length (coef f) - length (poly_form_variables f) +
      S (length (poly_variables X.encode
        (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P))) <=
      n P + count.
  Proof.
    intros P f count Hnonempty Hcount.
    pose proof (poly_form_variables_length f) as Hsupport.
    pose proof (poly_range_distinct_fuel P f) as Hfuel.
    unfold n. destruct P; [contradiction|]. cbn [length]. lia.
  Qed.

  (** Prefix stages pay their width growth and only increase the remaining row allowance. *)
  Lemma poly_fmcost_shift_width : forall extra fuel dim mlen rows bits,
    fmcost dim mlen fuel rows (poly_width_after extra bits) <=
      fmcost dim mlen (extra + fuel) rows bits.
  Proof.
    intro extra. induction extra as [|extra IH]; intros fuel dim mlen rows bits.
    - reflexivity.
    - cbn [poly_width_after Nat.add fmcost].
      eapply Nat.le_trans; [apply IH|].
      pose proof (poly_fmcost_params_mono (extra + fuel)
        dim dim mlen mlen rows (rows ^ 2 / 4 + rows) (2 * bits + 1) (2 * bits + 1)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hnext.
      lia.
  Qed.

  (** Linear width growth from duplicate surplus fits its exponential stage allowance. *)
  Lemma poly_duplicate_width_shift : forall extra bits,
    bits + Nat.log2 (extra + 1) + 1 <= poly_width_after extra (2 * bits + 1).
  Proof.
    intros extra bits.
    pose proof (Nat.log2_lt_lin (extra + 1) ltac:(lia)) as Hlog.
    pose proof (poly_width_after_successor extra (2 * bits + 1)) as Hwidth.
    assert (Hpower : extra + 1 <= 2 ^ extra).
    { clear -extra. induction extra as [|extra IH]; cbn [Nat.pow]; nia. }
    nia.
  Qed.

  (** One row test uses the recurrence already reserved by the lattice size. *)
  Definition poly_lattice_budget (m : nat) : nat :=
    fmcost m (m + 1) m (m + 1) (m + 1) + m^2 + 1.

  Definition poly_lattice_envelope (P : list (lcons X.t)) (c : lcons X.t)
      (m : nat) : Prop :=
    terms (Reached (c :: P)) <= m /\ n P + length (lhs c) <= m /\
    length P <= m /\ nell (Reached (c :: P)) <= m.

  Lemma poly_lattice_budget_positive : forall m, 1 <= poly_lattice_budget m.
  Proof. intro m. unfold poly_lattice_budget. lia. Qed.

  Lemma poly_lattice_budget_square : forall m,
    (m + 1)^2 <= 4 * poly_lattice_budget m.
  Proof.
    intro m. assert (Hsquare : (m + 1)^2 <= 4 * (m^2 + 1)).
    { destruct m; cbn [Nat.pow]; nia. }
    unfold poly_lattice_budget. lia.
  Qed.

  Lemma poly_lattice_mu_positive : forall s, 1 <= mu s.
  Proof. intro s. unfold mu, nell. lia. Qed.

  Lemma poly_lattice_rows_bound : forall s, length (prows s) <= mu s.
  Proof. intro s. unfold mu, n. lia. Qed.

  Lemma poly_lattice_mu_unreached : mu Unreached = 1.
  Proof. reflexivity. Qed.

  Lemma poly_lattice_ell_cons : forall P c,
    ell (c :: P) <= ell P + C.row_bits c + C.row_key_bits c.
  Proof. intros P c. unfold ell. cbn [map fold_right]. lia. Qed.

  (** A target from the other state fits the sum of their raw numeric sizes. *)
  Lemma poly_lattice_member_inputs : forall P Q r, In r Q ->
    poly_lattice_envelope P r (mu (Reached P) + mu (Reached Q)) /\
    length (lhs r) <= mu (Reached P) + mu (Reached Q) /\
    C.row_bits r <= mu (Reached P) + mu (Reached Q).
  Proof.
    intros P Q r Hr.
    pose proof (poly_raw_row_terms Q r Hr) as Hlength.
    pose proof (poly_max_member _ C.row_bits 0 Q r Hr) as Hbits.
    pose proof (poly_max_member _ C.row_key_bits 0 Q r Hr) as Hkeys.
    assert (Hrow_width : C.row_bits r + C.row_key_bits r <= ell Q)
      by (unfold ell; lia).
    pose proof (poly_lattice_ell_cons P r) as Hell.
    assert (Hlog : Nat.log2 (terms (Reached (r :: P))) <=
      terms (Reached (r :: P))) by (apply Nat.log2_le_lin; lia).
    assert (Hterms : terms (Reached (r :: P)) = length (lhs r) + terms (Reached P))
      by reflexivity.
    unfold poly_lattice_envelope, mu, nell. cbn [prows].
    rewrite Hterms in Hlog |- *.
    assert (Hcount : length P <= n P) by (unfold n; lia).
    repeat split; lia.
  Qed.

  (** Changing relation tags or coefficient signs preserves this size-only envelope. *)
  Lemma poly_lattice_envelope_shape : forall P r c m,
    length (lhs c) = length (lhs r) -> C.row_bits c = C.row_bits r ->
    C.row_key_bits c = C.row_key_bits r ->
    poly_lattice_envelope P r m -> poly_lattice_envelope P c m.
  Proof.
    intros P r c m Hlength Hbits Hkeys Henv.
    assert (Hterms : terms (Reached (c :: P)) = terms (Reached (r :: P))).
    { change (length (lhs c) + terms (Reached P) =
        length (lhs r) + terms (Reached P)). now rewrite Hlength. }
    assert (Hell : ell (c :: P) = ell (r :: P)).
    { unfold ell. cbn [map fold_right]. now rewrite Hbits, Hkeys. }
    assert (Hwidth : nell (Reached (c :: P)) = nell (Reached (r :: P))).
    { unfold nell. cbn [prows]. now rewrite Hell, Hterms. }
    unfold poly_lattice_envelope in *. now rewrite Hterms, Hwidth, Hlength.
  Qed.

  Definition poly_lattice_false_row : lcons X.t := LCons X.t nil RLe (-1)%Z.

  (** The false constant row adds at most one arithmetic bit to its source. *)
  Lemma poly_lattice_bottom_envelope : forall P m,
    mu (Reached P) + 1 <= m -> poly_lattice_envelope P poly_lattice_false_row m.
  Proof.
    intros P m Hm.
    pose proof (poly_lattice_ell_cons P poly_lattice_false_row) as Hell.
    change (ell (poly_lattice_false_row :: P) <= ell P + 1 + 0) in Hell.
    assert (Hterms : terms (Reached (poly_lattice_false_row :: P)) = terms (Reached P))
      by reflexivity.
    assert (Hwidth : nell (Reached (poly_lattice_false_row :: P)) <=
      nell (Reached P) + 1).
    { unfold nell. cbn [prows]. rewrite Hterms. lia. }
    unfold poly_lattice_envelope. rewrite Hterms.
    change (terms (Reached P) <= m /\ n P + 0 <= m /\ length P <= m /\
      nell (Reached (poly_lattice_false_row :: P)) <= m).
    unfold mu in Hm. cbn [prows] in Hm.
    assert (Hcount : length P <= n P) by (unfold n; lia).
    repeat split; lia.
  Qed.

  (** The raw preprocessing prefix and full elimination fit one common row budget. *)
  Lemma poly_lattice_entail_budget : forall P c m, poly_lattice_envelope P c m ->
    poly_entail_raw_budget P c <= 2 * poly_lattice_budget m.
  Proof.
    intros P c m [Hterms [Hdim [Hrows Hbits]]].
    assert (Hprefix : terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) <=
      m * (m + 1)) by (apply Nat.mul_le_mono; lia).
    assert (Hsquare : m * (m + 1) <= 2 * (m^2 + 1)).
    { destruct m; cbn [Nat.pow]; nia. }
    assert (Hrecurrence :
      fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
        (length P + 1) (nell (Reached (c :: P))) <=
      fmcost m (m + 1) m (m + 1) (m + 1)).
    { apply poly_fmcost_mono; lia. }
    unfold poly_entail_raw_budget, poly_lattice_budget. lia.
  Qed.

  Lemma poly_lattice_lat_charge : forall m,
    (N.of_nat (m + 1) * N.of_nat (poly_lattice_budget m) <= N.of_nat (lat m))%N.
  Proof.
    intro m. unfold lat. fold (poly_lattice_budget m).
    rewrite !Nat2N.inj_mul. change (N.of_nat 2) with 2%N. nia.
  Qed.

  Lemma poly_lattice_lat_budget : forall m,
    (N.of_nat (poly_lattice_budget m) <= N.of_nat (lat m))%N.
  Proof.
    intro m. eapply N.le_trans; [|apply poly_lattice_lat_charge].
    rewrite <- (N.mul_1_l (N.of_nat (poly_lattice_budget m))) at 1.
    apply N.mul_le_mono_r. lia.
  Qed.

  Lemma poly_lattice_lat_positive : forall m, (1 <= N.of_nat (lat m))%N.
  Proof.
    intro m. eapply N.le_trans; [|apply poly_lattice_lat_budget].
    pose proof (poly_lattice_budget_positive m). lia.
  Qed.

  Lemma poly_lattice_lat_mono : forall m n, m <= n -> lat m <= lat n.
  Proof.
    intros m n Hle. unfold lat. apply Nat.mul_le_mono; [lia|].
    apply Nat.add_le_mono; [apply Nat.add_le_mono|lia].
    - apply poly_fmcost_mono; lia.
    - now apply Nat.pow_le_mono_l.
  Qed.

  (** A shared raw size is paid by the two public state sizes. *)
  Lemma poly_lattice_lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  Proof.
    intros a b. unfold size.
    destruct (Nat.le_ge_cases (mu a) (mu b)) as [Hle|Hle].
    - pose proof (poly_lattice_lat_mono (mu a + mu b) (2 * mu b) ltac:(lia)). lia.
    - pose proof (poly_lattice_lat_mono (mu a + mu b) (2 * mu a) ltac:(lia)). lia.
  Qed.

  Definition poly_lattice_entail_factor : N := (2 * poly_entail_raw_factor + 4)%N.

  (** A successful certificate needs no second execution of the raw checker. *)
  Lemma T_poly_lattice_entails_row : forall P c m, poly_lattice_envelope P c m ->
    (T_entails_row P c <= poly_lattice_entail_factor * N.of_nat (poly_lattice_budget m))%N.
  Proof.
    intros P c m Henv.
    pose proof (T_poly_entail_raw_bounded P c) as Hproducer.
    pose proof (poly_lattice_entail_budget P c m Henv) as Hbudget.
    assert (Hproducer_total : (T_entail_cert P c <=
      2 * poly_entail_raw_factor * N.of_nat (poly_lattice_budget m))%N).
    { eapply N.le_trans; [exact Hproducer|].
      replace (2 * poly_entail_raw_factor * N.of_nat (poly_lattice_budget m))%N with
        (poly_entail_raw_factor * N.of_nat (2 * poly_lattice_budget m))%N
        by (rewrite Nat2N.inj_mul; change (N.of_nat 2) with 2%N; ring).
      apply N.mul_le_mono_l. clear -Hbudget. lia. }
    pose proof (poly_lattice_budget_positive m) as Hpositive.
    assert (Hwork : (1 <= N.of_nat (poly_lattice_budget m))%N) by lia.
    set (work := N.of_nat (poly_lattice_budget m)) in *.
    time_unfold T_entails_row. destruct (entail_cert P c); time_simpl;
      unfold poly_lattice_entail_factor; clear -Hproducer_total Hwork;
      clearbody work; rewrite N.mul_add_distr_r; lia.
  Qed.

  Definition poly_lattice_keep_factor : N := (2 * poly_lattice_entail_factor + 168)%N.

  (** Equality inclusion pays for its two inequality queries and one target negation. *)
  Lemma T_poly_lattice_keep_member : forall P Q r, In r Q ->
    (T_keep_row P r <= poly_lattice_keep_factor *
      N.of_nat (poly_lattice_budget (mu (Reached P) + mu (Reached Q))))%N.
  Proof.
    intros P Q r Hr. set (m := mu (Reached P) + mu (Reached Q)).
    destruct (poly_lattice_member_inputs P Q r Hr) as [Henv [Hlength Hbits]].
    assert (Hupper : poly_lattice_envelope P (LCons X.t (lhs r) RLe (rhs r)) m).
    { eapply poly_lattice_envelope_shape with (r := r); [reflexivity| | |exact Henv];
        destruct r; reflexivity. }
    assert (Hlower : poly_lattice_envelope P (poly_negate r) m).
    { eapply poly_lattice_envelope_shape with (r := r); [apply poly_negate_row_length|
        apply poly_negate_row_bits|apply poly_negate_row_key_bits|exact Henv]. }
    pose proof (T_poly_lattice_entails_row P r m Henv) as Hdirect.
    pose proof (T_poly_lattice_entails_row P _ m Hupper) as Hupper_time.
    pose proof (T_poly_lattice_entails_row P _ m Hlower) as Hlower_time.
    pose proof (T_poly_negate_bounded r m m Hlength Hbits) as Hnegate.
    assert (Hsquare : (N.of_nat ((m + 1)^2) <=
      4 * N.of_nat (poly_lattice_budget m))%N).
    { pose proof (poly_lattice_budget_square m) as Hsquare_nat.
      assert (Htransport : (N.of_nat ((m + 1)^2) <=
        N.of_nat (4 * poly_lattice_budget m))%N) by lia.
      rewrite Nat2N.inj_mul in Htransport. exact Htransport. }
    assert (Hnegate_total : (T_poly_negate r <=
      160 * N.of_nat (poly_lattice_budget m))%N).
    { eapply N.le_trans; [exact Hnegate|].
      replace (40 * N.of_nat (m + 1) * N.of_nat (m + 1))%N with
        (40 * N.of_nat ((m + 1)^2))%N by (rewrite poly_nat_square; ring).
      replace (160 * N.of_nat (poly_lattice_budget m))%N with
        (40 * (4 * N.of_nat (poly_lattice_budget m)))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hpositive : (1 <= N.of_nat (poly_lattice_budget m))%N)
      by (pose proof (poly_lattice_budget_positive m); lia).
    set (work := N.of_nat (poly_lattice_budget m)) in *.
    time_unfold T_keep_row. destruct (lrel r); time_simpl;
      unfold poly_lattice_keep_factor;
      clear -Hdirect Hupper_time Hlower_time Hnegate_total Hpositive;
      clearbody work; nia.
  Qed.

  Definition poly_lattice_scan_factor : N := (poly_lattice_keep_factor + 4)%N.

  Lemma T_poly_lattice_forallb : forall P Q,
    (List.T_forallb (keep_row P) (T_keep_row P) Q <= poly_lattice_scan_factor *
      N.of_nat (mu (Reached P) + mu (Reached Q) + 1) *
      N.of_nat (poly_lattice_budget (mu (Reached P) + mu (Reached Q))))%N.
  Proof.
    intros P Q. set (m := mu (Reached P) + mu (Reached Q)).
    set (work := N.of_nat (poly_lattice_budget m)).
    pose proof (poly_T_forallb_members _ (keep_row P) (T_keep_row P)
      (poly_lattice_keep_factor * work)%N Q (T_poly_lattice_keep_member P Q)) as Hscan.
    assert (Hcount : (N.of_nat (length Q + 1) <= N.of_nat (m + 1))%N).
    { pose proof (poly_lattice_rows_bound (Reached Q)) as Hrows. cbn [prows] in Hrows.
      unfold m. lia. }
    assert (Hpositive : (1 <= work)%N)
      by (unfold work; pose proof (poly_lattice_budget_positive m); lia).
    pose proof (poly_clock_linear_count_bound poly_lattice_keep_factor 2
      (N.of_nat (length Q)) (N.of_nat (m + 1)) work ltac:(lia) Hpositive) as Hlinear.
    eapply N.le_trans; [exact Hscan|]. eapply N.le_trans; [exact Hlinear|].
    repeat apply N.mul_le_mono_r. unfold poly_lattice_scan_factor. lia.
  Qed.

  Lemma T_poly_lattice_filter : forall P Q,
    (List.T_filter (keep_row P) (T_keep_row P) Q <= poly_lattice_scan_factor *
      N.of_nat (mu (Reached P) + mu (Reached Q) + 1) *
      N.of_nat (poly_lattice_budget (mu (Reached P) + mu (Reached Q))))%N.
  Proof.
    intros P Q. set (m := mu (Reached P) + mu (Reached Q)).
    set (work := N.of_nat (poly_lattice_budget m)).
    pose proof (poly_T_filter_members _ (keep_row P) (T_keep_row P)
      (poly_lattice_keep_factor * work)%N Q (T_poly_lattice_keep_member P Q)) as Hscan.
    assert (Hcount : (N.of_nat (length Q + 1) <= N.of_nat (m + 1))%N).
    { pose proof (poly_lattice_rows_bound (Reached Q)) as Hrows. cbn [prows] in Hrows.
      unfold m. lia. }
    assert (Hpositive : (1 <= work)%N)
      by (unfold work; pose proof (poly_lattice_budget_positive m); lia).
    pose proof (poly_clock_linear_count_bound poly_lattice_keep_factor 1
      (N.of_nat (length Q)) (N.of_nat (m + 1)) work ltac:(lia) Hpositive) as Hlinear.
    eapply N.le_trans; [exact Hscan|]. eapply N.le_trans; [exact Hlinear|].
    repeat apply N.mul_le_mono_r. unfold poly_lattice_scan_factor. lia.
  Qed.

  Definition poly_lattice_bottom_factor : N := (poly_lattice_entail_factor + 4)%N.

  Lemma T_poly_lattice_is_bot : forall s m, mu s + 1 <= m ->
    (T_is_bot s <= poly_lattice_bottom_factor * N.of_nat (poly_lattice_budget m))%N.
  Proof.
    intros [|P] m Hm.
    - assert (Hpositive : (1 <= N.of_nat (poly_lattice_budget m))%N)
        by (pose proof (poly_lattice_budget_positive m); lia).
      time_unfold T_is_bot. time_simpl. unfold poly_lattice_bottom_factor. nia.
    - pose proof (T_poly_lattice_entails_row P poly_lattice_false_row m
        (poly_lattice_bottom_envelope P m Hm)) as Hquery.
      assert (Hpositive : (1 <= N.of_nat (poly_lattice_budget m))%N)
        by (pose proof (poly_lattice_budget_positive m); lia).
      set (work := N.of_nat (poly_lattice_budget m)) in *.
      time_unfold T_is_bot. time_simpl. fold poly_lattice_false_row.
      unfold poly_lattice_bottom_factor. clear -Hquery Hpositive. clearbody work.
      rewrite N.mul_add_distr_r. lia.
  Qed.

  Lemma T_poly_lattice_forallb_lat : forall P Q,
    (List.T_forallb (keep_row P) (T_keep_row P) Q <= poly_lattice_scan_factor *
      N.of_nat (lat (mu (Reached P) + mu (Reached Q))))%N.
  Proof.
    intros P Q. eapply N.le_trans; [apply T_poly_lattice_forallb|].
    rewrite <- N.mul_assoc. apply N.mul_le_mono_l. apply poly_lattice_lat_charge.
  Qed.

  Lemma T_poly_lattice_filter_lat : forall P Q,
    (List.T_filter (keep_row P) (T_keep_row P) Q <= poly_lattice_scan_factor *
      N.of_nat (lat (mu (Reached P) + mu (Reached Q))))%N.
  Proof.
    intros P Q. eapply N.le_trans; [apply T_poly_lattice_filter|].
    rewrite <- N.mul_assoc. apply N.mul_le_mono_l. apply poly_lattice_lat_charge.
  Qed.

  Lemma T_poly_lattice_is_bot_lat : forall s m, mu s + 1 <= m ->
    (T_is_bot s <= poly_lattice_bottom_factor * N.of_nat (lat m))%N.
  Proof.
    intros s m Hm. eapply N.le_trans; [apply T_poly_lattice_is_bot; exact Hm|].
    apply N.mul_le_mono_l. apply poly_lattice_lat_budget.
  Qed.

  Definition poly_lattice_factor : N :=
    (2 * poly_lattice_scan_factor + 2 * poly_lattice_bottom_factor + 16)%N.

  Lemma poly_lattice_factor_positive : (1 <= poly_lattice_factor)%N.
  Proof. unfold poly_lattice_factor. lia. Qed.

  Lemma poly_lattice_unit_bound : forall m,
    (1 <= poly_lattice_factor * N.of_nat (lat m))%N.
  Proof.
    intro m. change (1 * 1 <= poly_lattice_factor * N.of_nat (lat m))%N.
    apply N.mul_le_mono; [exact poly_lattice_factor_positive|apply poly_lattice_lat_positive].
  Qed.

  (** Inclusion traverses the target rows and uses the raw producer once per test. *)
  Lemma T_poly_leb_lattice : forall a b,
    (T_leb a b <= poly_lattice_factor * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    intros [|P] [|Q].
    - time_unfold T_leb. time_simpl. apply poly_lattice_unit_bound.
    - time_unfold T_leb. time_simpl. apply poly_lattice_unit_bound.
    - pose proof (T_poly_lattice_is_bot_lat (Reached P)
        (mu (Reached P) + mu Unreached)
        ltac:(rewrite poly_lattice_mu_unreached; lia)) as Hbottom.
      pose proof (poly_lattice_lat_positive (mu (Reached P) + mu Unreached)) as Hpositive.
      set (work := N.of_nat (lat (mu (Reached P) + mu Unreached))) in *.
      time_unfold T_leb. time_simpl. unfold poly_lattice_factor.
      clear -Hbottom Hpositive. clearbody work. nia.
    - pose proof (T_poly_lattice_forallb_lat P Q) as Hscan.
      pose proof (poly_lattice_lat_positive (mu (Reached P) + mu (Reached Q))) as Hpositive.
      set (work := N.of_nat (lat (mu (Reached P) + mu (Reached Q)))) in *.
      time_unfold T_leb. time_simpl.
      change (fun r : lcons X.t => T_keep_row P r) with (T_keep_row P).
      unfold poly_lattice_factor. clear -Hscan Hpositive. clearbody work. nia.
  Qed.

  (** Appending the retained left rows costs no more than the shared lattice budget. *)
  Lemma T_poly_lattice_join_append : forall P Q,
    (Datatypes.T_app (filter (keep_row Q) P) (filter (keep_row P) Q) <=
      N.of_nat (lat (mu (Reached P) + mu (Reached Q))))%N.
  Proof.
    intros P Q. pose proof (Datatypes.T_app_le
      (filter (keep_row Q) P) (filter (keep_row P) Q)) as Happ.
    pose proof (filter_length_le (keep_row Q) P) as Hlength.
    pose proof (poly_lattice_rows_bound (Reached P)) as Hrows. cbn [prows] in Hrows.
    set (m := mu (Reached P) + mu (Reached Q)).
    eapply N.le_trans; [exact Happ|].
    eapply N.le_trans with (m := N.of_nat (m + 1)); [unfold m; lia|].
    eapply N.le_trans; [|apply poly_lattice_lat_charge].
    rewrite <- (N.mul_1_r (N.of_nat (m + 1))) at 1.
    apply N.mul_le_mono_l. pose proof (poly_lattice_budget_positive m). lia.
  Qed.

  (** Joining scans both raw states and concatenates the retained rows. *)
  Lemma T_poly_join_lattice : forall a b,
    (T_join a b <= poly_lattice_factor * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    intros [|P] [|Q].
    - time_unfold T_join. time_simpl. apply poly_lattice_unit_bound.
    - time_unfold T_join. time_simpl. apply poly_lattice_unit_bound.
    - time_unfold T_join. time_simpl. apply poly_lattice_unit_bound.
    - pose proof (T_poly_lattice_filter_lat Q P) as Hleft.
      rewrite (Nat.add_comm (mu (Reached Q)) (mu (Reached P))) in Hleft.
      pose proof (T_poly_lattice_filter_lat P Q) as Hright.
      pose proof (T_poly_lattice_join_append P Q) as Happ.
      pose proof (poly_lattice_lat_positive (mu (Reached P) + mu (Reached Q))) as Hpositive.
      set (work := N.of_nat (lat (mu (Reached P) + mu (Reached Q)))) in *.
      time_unfold T_join. time_simpl.
      change (fun r : lcons X.t => T_keep_row Q r) with (T_keep_row Q).
      change (fun r : lcons X.t => T_keep_row P r) with (T_keep_row P).
      unfold poly_lattice_factor. clear -Hleft Hright Happ Hpositive.
      clearbody work. nia.
  Qed.

  (** Widening scans the old rows, with one bottom query in its unreached branch. *)
  Lemma T_poly_widen_lattice : forall p a b,
    (T_widen p a b <= poly_lattice_factor * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    intros p [|P] b.
    - pose proof (T_poly_lattice_is_bot_lat b (mu Unreached + mu b)
        ltac:(rewrite poly_lattice_mu_unreached; lia)) as Hbottom.
      pose proof (poly_lattice_lat_positive (mu Unreached + mu b)) as Hpositive.
      set (work := N.of_nat (lat (mu Unreached + mu b))) in *.
      time_unfold T_widen. time_simpl. unfold poly_lattice_factor.
      clear -Hbottom Hpositive. clearbody work. nia.
    - destruct b as [|Q].
      + time_unfold T_widen. time_simpl. apply poly_lattice_unit_bound.
      + pose proof (T_poly_lattice_filter_lat Q P) as Hscan.
        rewrite (Nat.add_comm (mu (Reached Q)) (mu (Reached P))) in Hscan.
        pose proof (poly_lattice_lat_positive (mu (Reached P) + mu (Reached Q))) as Hpositive.
        set (work := N.of_nat (lat (mu (Reached P) + mu (Reached Q)))) in *.
        time_unfold T_widen. time_simpl.
        change (fun r : lcons X.t => T_keep_row Q r) with (T_keep_row Q).
        unfold poly_lattice_factor. clear -Hscan Hpositive. clearbody work. nia.
  Qed.

  (** A single state's public size reserves enough room for its bottom query. *)
  Lemma T_poly_is_bot_size : forall s,
    (T_is_bot s <= poly_lattice_factor * N.of_nat (size s + 1))%N.
  Proof.
    intro s. pose proof (poly_lattice_mu_positive s) as Hmu.
    eapply N.le_trans; [apply (T_poly_lattice_is_bot_lat s (2 * mu s)); lia|].
    apply N.mul_le_mono.
    - unfold poly_lattice_factor. lia.
    - unfold size. lia.
  Qed.

  Definition k_poly : N := poly_lattice_factor.


  (** One spare stage covers any terminal fold whose callback satisfies the row envelope. *)
  Lemma T_poly_run_fold_bounded : forall (A : Type)
    (f : A -> poly_row X.t -> A) (T_f : A -> poly_row X.t -> N) factor
    xs vars rows dim mlen keys bits count acc,
    length vars <= dim -> mlen <= count -> length rows <= count ->
    Forall (poly_reduced_row vars) rows ->
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    (forall wider a r, bits <= wider -> poly_row_envelope dim mlen keys wider r ->
      (T_f a r <= factor * N.of_nat (mlen + 1) *
        N.of_nat (dim + mlen + 1) * N.of_nat (keys + wider + 1)^2)%N) ->
    (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs rows +
      List.T_fold_left f T_f (poly_run X.encode X.eqb xs rows) acc <=
      (poly_step_factor + factor + 16) * N.of_nat
        (fmcost dim mlen (S (length xs)) count (keys + bits)))%N.
  Proof.
    intros A f T_f factor xs. induction xs as [|x xs IH];
      intros vars rows dim mlen keys bits count acc Hdim HM HR Hsupport Henvelopes Hcallback.
    - pose proof (poly_T_fold_left_members (poly_row X.t) A f T_f
        (factor * N.of_nat (mlen + 1) * N.of_nat (dim + mlen + 1) *
          N.of_nat (keys + bits + 1)^2)%N rows acc) as Hfold.
      specialize (Hfold ltac:(intros a r Hr; apply Hcallback with (wider := bits);
        [lia|exact (proj1 (Forall_forall _ _) Henvelopes r Hr)])).
      set (span := poly_clock_span dim mlen keys bits).
      set (work := (N.of_nat (count + 1)^2 * span)%N).
      assert (Hspan : (1 <= span)%N) by (unfold span; apply poly_span_positive).
      assert (Hwork : (1 <= work)%N) by (unfold work, span; apply poly_fm_charge_positive).
      assert (Hcallback_count : (N.of_nat (mlen + 1) * N.of_nat (length rows) <=
        N.of_nat (count + 1)^2)%N).
      { rewrite N.pow_2_r. apply N.mul_le_mono; lia. }
      assert (Hrows_work : (N.of_nat (length rows) <= work)%N).
      { unfold work. rewrite N.pow_2_r. nia. }
      assert (Hfold_work : (List.T_fold_left f T_f rows acc <= (factor + 2) * work)%N).
      { replace (factor * N.of_nat (mlen + 1) * N.of_nat (dim + mlen + 1) *
          N.of_nat (keys + bits + 1)^2)%N with
          (factor * N.of_nat (mlen + 1) * span)%N in Hfold
          by (unfold span, poly_clock_span; ring).
        assert (Hscaled : (factor * N.of_nat (mlen + 1) * span * N.of_nat (length rows) <=
          factor * work)%N).
        { unfold work. nia. }
        clear -Hfold Hscaled Hrows_work Hwork. clearbody work. nia. }
      cbn [length poly_run]. rewrite poly_fmcost_clock_step. fold span work.
      eapply N.le_trans with (m := ((poly_step_factor + factor + 16) * work)%N).
      2: { apply N.mul_le_mono_l. apply N.le_add_r. }
      time_unfold (@T_poly_run). time_cbn.
      clear -Hfold_work Hwork. clearbody work. nia.
    - set (next := poly_step X.encode X.eqb x rows).
      set (next_count := count^2 / 4 + count).
      assert (Hnext_count : length next <= next_count).
      { pose proof (poly_step_rows X.t X.encode X.eqb x rows) as Hrows.
        pose proof (poly_rows_recurrence_mono (length rows) count HR).
        unfold next, next_count. lia. }
      assert (Hnext_mlen : mlen <= next_count) by (unfold next_count; lia).
      assert (Hnext_support : Forall (poly_reduced_row vars) next).
      { unfold next. now apply poly_step_reduced. }
      assert (Hnext_envelopes : Forall (poly_row_envelope dim mlen keys (2 * bits + 1)) next).
      { unfold next. now apply poly_step_envelopes with (vars := vars). }
      pose proof (IH vars next dim mlen keys (2 * bits + 1) next_count acc
        Hdim Hnext_mlen Hnext_count Hnext_support Hnext_envelopes
        ltac:(intros wider a r Hwide Hr; apply Hcallback with (wider := wider);
          [lia|exact Hr])) as Hrecursive.
      pose proof (poly_fmcost_params_mono (S (length xs))
        dim dim mlen mlen next_count next_count
        (keys + (2 * bits + 1)) (2 * (keys + bits) + 1)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) ltac:(lia)) as Hfuture.
      assert (Hrecursive_total :
        (T_poly_run X.encode X.T_encode X.eqb X.T_eqb xs next +
          List.T_fold_left f T_f (poly_run X.encode X.eqb xs next) acc <=
          (poly_step_factor + factor + 16) * N.of_nat
            (fmcost dim mlen (S (length xs)) next_count (2 * (keys + bits) + 1)))%N).
      { eapply N.le_trans; [exact Hrecursive|]. apply N.mul_le_mono_l.
        clear -Hfuture. lia. }
      pose proof (T_poly_step_bounded x rows dim mlen keys bits Henvelopes) as Hstep.
      set (work := (N.of_nat (count + 1)^2 * poly_clock_span dim mlen keys bits)%N).
      assert (Hhead : (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows <=
        poly_step_factor * work)%N).
      { eapply N.le_trans; [exact Hstep|]. unfold work. rewrite N.mul_assoc.
        apply N.mul_le_mono_r, N.mul_le_mono_l, N.pow_le_mono_l. lia. }
      assert (Hwork : (1 <= work)%N) by (unfold work; apply poly_fm_charge_positive).
      change (T_poly_run X.encode X.T_encode X.eqb X.T_eqb (x :: xs) rows +
        List.T_fold_left f T_f (poly_run X.encode X.eqb xs next) acc <=
        (poly_step_factor + factor + 16) * N.of_nat
          (fmcost dim mlen (S (S (length xs))) count (keys + bits)))%N.
      rewrite poly_fmcost_clock_step. fold next_count work.
      time_unfold (@T_poly_run). fold next. time_simpl.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      set (future := N.of_nat
        (fmcost dim mlen (S (length xs)) next_count (2 * (keys + bits) + 1))) in *.
      clear -Hrecursive_total Hhead Hwork. clearbody work future.
      rewrite !N.mul_add_distr_l. nia.
  Qed.

  (** An allowance of at least two rows gains at least one row per recurrence step. *)
  Lemma poly_rows_allowance_grows : forall rows,
    2 <= rows -> rows + 1 <= rows^2 / 4 + rows.
  Proof.
    intros rows Hrows. assert (Hquarter : 1 <= rows^2 / 4).
    { apply Nat.div_le_lower_bound; [lia|]. cbn [Nat.pow]. nia. }
    lia.
  Qed.

  (** The terminal charge retains both the accumulated row and width allowances. *)
  Lemma poly_fmcost_terminal_count : forall fuel dim mlen rows bits,
    2 <= rows ->
    (rows + fuel + 1) * (dim + mlen + 1) * (poly_width_after fuel bits + 1) <=
      fmcost dim mlen fuel rows bits.
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros dim mlen rows bits Hrows.
    - cbn [poly_width_after fmcost]. nia.
    - pose proof (poly_rows_allowance_grows rows Hrows) as Hgrowth.
      pose proof (IH dim mlen (rows^2 / 4 + rows) (2 * bits + 1) ltac:(lia)) as Htail.
      cbn [poly_width_after fmcost].
      eapply Nat.le_trans with (m := fmcost dim mlen fuel (rows^2 / 4 + rows)
        (2 * bits + 1)); [|lia].
      eapply Nat.le_trans; [|exact Htail].
      apply Nat.mul_le_mono_r, Nat.mul_le_mono_r. lia.
  Qed.

  (** A squared dimension is bounded by a constant multiple of its power of two. *)
  Lemma poly_range_dimension_power : forall dim,
    (dim + 2)^2 <= 9 * 2^dim.
  Proof.
    induction dim as [|dim IH]; [cbn; lia|].
    rewrite (Nat.pow_succ_r 2 dim) by lia.
    destruct dim as [|dim]; [cbn; lia|].
    assert (Hstep : (S (S dim) + 2)^2 <= 2 * (S dim + 2)^2)
      by (cbn [Nat.pow]; nia).
    cbn [Nat.pow] in *. nia.
  Qed.

  (** The frozen full-fuel range budget pays a quartic setup polynomial at linear bit width. *)
  Lemma poly_range_budget_preprocessing : forall dim rows bits,
    (dim + 2)^4 * (bits + 1) <=
      9 * fmcost dim (rows + 2) dim (rows + 2) bits.
  Proof.
    intros dim rows bits.
    pose proof (poly_fmcost_terminal_count dim dim (rows + 2) (rows + 2) bits ltac:(lia))
      as Hterminal.
    rewrite poly_width_after_successor in Hterminal.
    pose proof (poly_range_dimension_power dim) as Hpower.
    assert (Hspan : (dim + 2)^2 <= (rows + 2 + dim + 1) * (dim + (rows + 2) + 1)).
    { cbn [Nat.pow]. nia. }
    assert (Hscale : (dim + 2)^2 * ((dim + 2)^2 * (bits + 1)) <=
      9 * ((dim + 2)^2 * (2^dim * (bits + 1)))).
    { pose proof (Nat.mul_le_mono_r _ _ ((dim + 2)^2 * (bits + 1)) Hpower).
      nia. }
    assert (Hscaled_span : (dim + 2)^2 * (2^dim * (bits + 1)) <=
      fmcost dim (rows + 2) dim (rows + 2) bits).
    { eapply Nat.le_trans; [|exact Hterminal].
      pose proof (Nat.mul_le_mono_r _ _ (2^dim * (bits + 1)) Hspan). nia. }
    replace ((dim + 2)^4) with ((dim + 2)^2 * (dim + 2)^2)
      by (cbn [Nat.pow]; nia).
    clear -Hscale Hscaled_span. nia.
  Qed.

  (** One auxiliary result coordinate increases every recurrence charge by at most a factor two. *)
  Lemma poly_fmcost_dimension_successor : forall fuel dim mlen rows bits,
    fmcost (dim + 1) mlen fuel rows bits <= 2 * fmcost dim mlen fuel rows bits.
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros dim mlen rows bits.
    - cbn [fmcost]. nia.
    - pose proof (IH dim mlen (rows^2 / 4 + rows) (2 * bits + 1)) as Htail.
      cbn [fmcost].
      assert (Hhead : (rows + 1)^2 * (dim + 1 + mlen + 1) * (bits + 1)^2 <=
        2 * ((rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2)).
      { assert (Hspan : dim + 1 + mlen + 1 <= 2 * (dim + mlen + 1)) by lia.
        pose proof (Nat.mul_le_mono_l _ _ ((rows + 1)^2) Hspan) as Hleft.
        pose proof (Nat.mul_le_mono_r _ _ ((bits + 1)^2) Hleft). nia. }
      lia.
  Qed.

  (** A canceled equality has zero right-hand side and zero summed coefficient at every key. *)
  Definition poly_zero_equality (r : poly_row X.t) : Prop :=
    lrel (poly_constraint r) = REq /\ rhs (poly_constraint r) = 0%Z /\
      forall y, poly_coefficient X.eqb y (poly_constraint r) = 0%Z.

  Lemma poly_self_cancel_zero : forall x r,
    lrel (poly_constraint r) = REq ->
    Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0 = false ->
    poly_zero_equality (poly_cancel X.encode X.eqb x r r).
  Proof.
    intros x r Hrel Hnonzero. unfold poly_zero_equality, poly_cancel. rewrite Hnonzero.
    split.
    - cbn [poly_add_rows poly_constraint lrel]. unfold poly_eq_used.
      rewrite Hrel. reflexivity.
    - split.
      + cbn [poly_add_rows poly_constraint rhs]. rewrite <- poly_sgn_abs. ring.
      + intro y. rewrite poly_add_rows_coefficient, <- poly_sgn_abs. ring.
  Qed.

  (** A singleton step either retains its equality or returns its zero self-cancellation. *)
  Lemma poly_equality_singleton_step : forall x r,
    lrel (poly_constraint r) = REq ->
    exists q, poly_step X.encode X.eqb x [r] = [q] /\ (q = r \/ poly_zero_equality q).
  Proof.
    intros x r Hrel.
    destruct (Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0) eqn:Hzero.
    - assert (Hpivot : poly_pivot X.eqb x r = false).
      { unfold poly_pivot. now rewrite Hrel, Hzero. }
      apply Z.eqb_eq in Hzero. exists r. split; [|now left].
      unfold poly_step. cbn [find]. rewrite Hpivot.
      cbn [filter flat_map map app]. rewrite Hzero. reflexivity.
    - assert (Hpivot : poly_pivot X.eqb x r = true).
      { unfold poly_pivot. now rewrite Hrel, Hzero. }
      exists (poly_cancel X.encode X.eqb x r r). split.
      + unfold poly_step. cbn [find]. now rewrite Hpivot.
      + right. now apply poly_self_cancel_zero.
  Qed.

  (** Any number of elimination columns preserves the same singleton dichotomy. *)
  Lemma poly_equality_singleton_run : forall xs r,
    lrel (poly_constraint r) = REq ->
    exists q, poly_run X.encode X.eqb xs [r] = [q] /\ (q = r \/ poly_zero_equality q).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros r Hrel.
    - exists r. split; [reflexivity|now left].
    - cbn [poly_run]. destruct (poly_equality_singleton_step x r Hrel)
        as [q [Hstep [Hsame|Hzero]]]; rewrite Hstep.
      + subst q. now apply IH.
      + destruct (IH q (proj1 Hzero)) as [s [Hrun [Hsame|Hzero_s]]].
        * exists s. split; [exact Hrun|]. right. now subst s.
        * exists s. split; [exact Hrun|now right].
  Qed.

  (** Each observable coordinate and the right-hand side are retained or become zero. *)
  Lemma poly_equality_singleton_observations : forall xs r x,
    lrel (poly_constraint r) = REq ->
    exists q, poly_run X.encode X.eqb xs [r] = [q] /\
      (poly_coefficient X.eqb x (poly_constraint q) =
        poly_coefficient X.eqb x (poly_constraint r) \/
        poly_coefficient X.eqb x (poly_constraint q) = 0%Z) /\
      (rhs (poly_constraint q) = rhs (poly_constraint r) \/ rhs (poly_constraint q) = 0%Z).
  Proof.
    intros xs r x Hrel.
    destruct (poly_equality_singleton_run xs r Hrel) as [q [Hrun [Hsame|Hzero]]].
    - subst q. exists r. split; [exact Hrun|]. split; now left.
    - destruct Hzero as [Hqrel [Hrhs Hcoef]]. exists q. split; [exact Hrun|].
      split; right; auto.
  Qed.

End PolyClockCore.

(** * Encoding support pays merged affine widths

    A coefficient support cannot exceed either its raw occurrences or its finite
    encoded-key space. Builds on: the frozen key encoding and natural logarithm. *)

(** Exponential growth covers the square of a logarithmic width increase. *)
Lemma poly_signed_log_square : forall j, (j + 2)^2 <= 9 * 2^j.
Proof.
  induction j as [|j IH]; [cbn; lia|].
  rewrite (Nat.pow_succ_r 2 j) by lia.
  destruct j as [|j]; [cbn; lia|].
  assert (Hstep : (S (S j) + 2)^2 <= 2 * (S j + 2)^2)
    by (cbn [Nat.pow]; nia).
  cbn [Nat.pow] in *. nia.
Qed.

(** The smaller support bound absorbs every logarithmic raw-multiplicity increase. *)
Lemma poly_signed_support_log_mass : forall support total bits,
  support <= total + 1 -> support <= 2^bits ->
  support * (bits + Nat.log2 (total + 1) + 1)^2 <=
    16 * (total + 1) * (bits + 1)^2.
Proof.
  intros support total bits Hcount Hkeys.
  pose proof (Nat.log2_spec (total + 1) ltac:(lia)) as [Hlower Hupper].
  set (q := Nat.log2 (total + 1)) in *.
  destruct (le_dec q bits) as [Hsmall|Hlarge].
  - assert (Hwidth : bits + q + 1 <= 2 * (bits + 1)) by lia.
    eapply Nat.le_trans with (m := (total + 1) * (2 * (bits + 1))^2).
    + apply Nat.mul_le_mono; [exact Hcount|now apply Nat.pow_le_mono_l].
    + rewrite Nat.pow_mul_l. cbn [Nat.pow]. clear -bits total. nia.
  - set (j := q - bits).
    assert (Hsplit : q = bits + j) by (unfold j; lia).
    assert (Hwidth : bits + q + 1 <= (bits + 1) * (j + 2)) by nia.
    pose proof (poly_signed_log_square j) as Hsquare.
    eapply Nat.le_trans with (m := 2^bits * ((bits + 1)^2 * (9 * 2^j))).
    + eapply Nat.le_trans with (m := 2^bits * ((bits + 1) * (j + 2))^2).
      * apply Nat.mul_le_mono; [exact Hkeys|now apply Nat.pow_le_mono_l].
      * rewrite Nat.pow_mul_l. apply Nat.mul_le_mono_l, Nat.mul_le_mono_l.
        exact Hsquare.
    + assert (Hpower : 2^bits * 2^j = 2^q) by (rewrite <- Nat.pow_add_r; now rewrite Hsplit).
      replace (2^bits * ((bits + 1)^2 * (9 * 2^j))) with
        (9 * (2^bits * 2^j) * (bits + 1)^2) by nia.
      rewrite Hpower. eapply Nat.le_trans with (m := 9 * (total + 1) * (bits + 1)^2).
      * apply Nat.mul_le_mono_r, Nat.mul_le_mono_l. exact Hlower.
      * clear -bits total. nia.
Qed.

Module PolySignedKeySupport (X : KEY).
  (** Encoding into natural numbers preserves key uniqueness. *)
  Lemma poly_signed_encoded_nodup : forall xs,
    NoDup xs -> NoDup (map (fun x => Pos.to_nat (X.encode x)) xs).
  Proof.
    intros xs Hunique. induction Hunique as [|x xs Hnot Hunique IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH]. intro Hin.
      apply in_map_iff in Hin as [y [Hsame Hy]].
      assert (Heq : y = x) by (apply X.encode_inj, Pos2Nat.inj; exact Hsame).
      subst y. contradiction.
  Qed.

  (** A bounded encoded-key space contains only finitely many distinct source keys. *)
  Lemma poly_signed_key_width_count : forall xs bits,
    NoDup xs -> Forall (fun x => X.bits x <= bits) xs -> length xs <= 2^bits.
  Proof.
    intros xs bits Hunique Hwidth.
    rewrite <- (length_map (fun x => Pos.to_nat (X.encode x)) xs),
      <- (length_seq (2^bits) 0).
    apply NoDup_incl_length; [now apply poly_signed_encoded_nodup|].
    intros value Hvalue. apply in_map_iff in Hvalue as [x [Hsame Hx]]. subst value.
    pose proof (proj1 (Forall_forall _ _) Hwidth x Hx) as Hbits.
    change (X.bits x <= bits) in Hbits.
    pose proof (Pos.size_nat_upper (X.encode x)) as Hupper.
    assert (Hpower : 2 ^ X.bits x <= 2 ^ bits) by (apply Nat.pow_le_mono_r; lia).
    unfold X.bits in Hpower. apply in_seq. lia.
  Qed.
End PolySignedKeySupport.

(** A logarithmic raw-size allowance also bounds the raw occurrence count exponentially. *)
Lemma poly_signed_log_capacity : forall count bits,
  Nat.log2 count + 1 <= bits -> count <= 2^bits.
Proof.
  intros count bits Hbits. destruct count as [|count]; [lia|].
  pose proof (Nat.log2_spec (S count) ltac:(lia)) as [_ Hupper].
  assert (Hpower : 2 ^ (Nat.log2 (S count) + 1) <= 2^bits)
    by (apply Nat.pow_le_mono_r; lia).
  rewrite Nat.add_1_r in Hpower.
  lia.
Qed.

(** A pivot's linear row count absorbs both encoded support and raw-check source mass. *)
Lemma poly_signed_assignment_pivot_mass : forall rows support terms expr bits,
  support <= terms + expr + 1 -> support <= 2^bits -> terms <= 2^bits ->
  1 <= bits ->
  (rows + 2) * (support + terms + rows + 3) *
      (bits + Nat.log2 (terms + expr + 1) + 1)^2 <=
    128 * (rows + 3)^2 * (terms + expr + rows + 3) * bits^2.
Proof.
  intros rows support terms expr bits Hsupport Hkeys Hterms Hbits.
  pose proof (poly_signed_support_log_mass support (terms + expr) bits
    Hsupport Hkeys) as Hdim.
  pose proof (poly_signed_support_log_mass terms (terms + expr) bits
    ltac:(lia) Hterms) as Hraw.
  assert (Honekey : 1 <= 2^bits).
  { assert (Hnonzero : 2^bits <> 0) by (apply Nat.pow_nonzero; lia). lia. }
  pose proof (poly_signed_support_log_mass 1 (terms + expr) bits
    ltac:(lia) Honekey) as Hone.
  assert (Hbitsquare : (bits + 1)^2 <= 4 * bits^2) by (cbn [Nat.pow]; nia).
  set (wide := (bits + Nat.log2 (terms + expr + 1) + 1)^2) in *.
  set (mass := (terms + expr + 1) * (bits + 1)^2) in *.
  assert (Hsum : (support + terms + rows + 3) * wide <=
      16 * (rows + 5) * mass) by nia.
  eapply Nat.le_trans with (m := (rows + 2) * (16 * (rows + 5) * mass)).
  - replace ((rows + 2) * (support + terms + rows + 3) * wide) with
      ((rows + 2) * ((support + terms + rows + 3) * wide)) by nia.
    now apply Nat.mul_le_mono_l.
  - unfold mass. assert (Hrows : (rows + 2) * (rows + 5) <= 2 * (rows + 3)^2)
      by (cbn [Nat.pow]; nia).
    eapply Nat.le_trans with
      (m := 32 * (rows + 3)^2 * (terms + expr + 1) * (bits + 1)^2).
    + nia.
    + eapply Nat.le_trans with
        (m := 128 * (rows + 3)^2 * (terms + expr + 1) * bits^2).
      * replace (128 * (rows + 3)^2 * (terms + expr + 1) * bits^2) with
          ((32 * (rows + 3)^2 * (terms + expr + 1)) * (4 * bits^2)) by ring.
        now apply Nat.mul_le_mono_l.
      * apply Nat.mul_le_mono_r, Nat.mul_le_mono_l. lia.
Qed.

(** * Assignment branch structure and normal-form substitution clocks

    The prepared affine equality either supplies the first pivot or remains a
    zero-coefficient head. Source-only candidates use zero-scaled affine terms.
    Builds on: checked Poly clock primitives and coefficient reflection. *)

(** Preparing a form cannot create more distinct coefficients than its raw list. *)
Lemma poly_prepare_form_length : forall A encode (f : lin A),
  length (coef (poly_prepare_form encode f)) <= length (coef f).
Proof.
  intros A encode f. cbn [poly_prepare_form coef]. rewrite poly_signed_normal_eq.
  rewrite <- (length_map fst (poly_normal_coef encode (coef f))),
    <- (length_map fst (coef f)).
  apply NoDup_incl_length; [apply poly_normal_coef_nodup|].
  intros x Hin. apply in_map_iff in Hin as [p [Heq Hin]]. subst x.
  exact (poly_normal_coef_keys _ encode (coef f) p Hin).
Qed.

(** A zero-coefficient head survives elimination without participating in any pair. *)
Lemma poly_assign_step_zero_head : forall A encode eqb x (z : poly_row A) rows,
  poly_coefficient eqb x (poly_constraint z) = 0%Z ->
  poly_step encode eqb x (z :: rows) = z :: poly_step encode eqb x rows.
Proof.
  intros A encode eqb x z rows Hzero.
  assert (Hpivot : poly_pivot eqb x z = false).
  { unfold poly_pivot. rewrite Hzero. destruct (lrel (poly_constraint z)); reflexivity. }
  unfold poly_step. cbn [find]. rewrite Hpivot.
  destruct (find (poly_pivot eqb x) rows) as [p|] eqn:Hfind.
  - cbn [map]. unfold poly_cancel at 1. rewrite Hzero. reflexivity.
  - cbn [filter]. rewrite Hzero. reflexivity.
Qed.

Module PolyAssignBranch (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X).
  Module Base := PolyClockCore X L N F C.
  Include Base.
  Module AssignKeySupport := PolySignedKeySupport X.

  Lemma poly_assign_raw_keys_length : forall P,
    length (flat_map (fun r => map fst (lhs r)) P) = terms (Reached P).
  Proof.
    intro P. induction P as [|p P IH]; [reflexivity|].
    cbn [flat_map]. rewrite length_app, length_map, IH. reflexivity.
  Qed.

  (** Distinct source support is bounded by the original occurrence count. *)
  Lemma poly_assign_variables_terms : forall P, length (vars_of P) <= terms (Reached P).
  Proof.
    intro P. rewrite <- poly_assign_raw_keys_length.
    apply NoDup_incl_length; [apply poly_vars_of_nodup|].
    intros x Hin. destruct (poly_vars_of_support P x Hin) as [r [Hr Hx]].
    apply in_flat_map. exists r. now split.
  Qed.

  (** The finite encoded-key space bounds the same distinct support independently. *)
  Lemma poly_assign_variables_space : forall P,
    length (vars_of P) <= 2 ^ poly_raw_keys P.
  Proof.
    intro P. apply AssignKeySupport.poly_signed_key_width_count;
      [apply poly_vars_of_nodup|].
    apply Forall_forall. intros x Hin.
    destruct (poly_vars_of_support P x Hin) as [r [Hr Hx]].
    apply in_map_iff in Hx as [p [Heq Hp]]. subst x.
    pose proof (poly_row_key_member r p Hp).
    pose proof (poly_max_member _ C.row_key_bits 0 P r Hr).
    unfold X.bits, poly_raw_keys. lia.
  Qed.

  Lemma poly_assign_terms_space : forall P,
    terms (Reached P) <= 2 ^ nell (Reached P).
  Proof.
    intro P. apply poly_signed_log_capacity. unfold nell. lia.
  Qed.

  (** Raw initialization admits the exact distinct-variable dimension. *)
  Lemma poly_assign_initial_envelopes : forall P,
    Forall (poly_row_envelope (length (vars_of P)) (length P)
      (poly_raw_keys P) (poly_raw_bits P))
      (poly_initial X.encode (map (fun r => (r, false)) P)).
  Proof.
    intro P. apply Forall_forall. intros r Hr.
    pose proof (proj1 (Forall_forall _ _) (poly_raw_initial_envelopes P) r Hr) as Hrow.
    pose proof (proj1 (Forall_forall _ _) (poly_raw_initial_reduced P) r Hr) as Hreduced.
    pose proof (poly_reduced_dimension _ _ Hreduced) as Hdim.
    destruct Hrow as [Hn [_ [Hk [Hb [Hm Hu]]]]].
    unfold poly_row_envelope. repeat split; assumption.
  Qed.

  Lemma poly_assign_step_envelopes : forall P x,
    Forall (poly_row_envelope (length (vars_of P)) (length P)
      (poly_raw_keys P) (2 * poly_raw_bits P + 1))
      (poly_step X.encode X.eqb x
        (poly_initial X.encode (map (fun r => (r, false)) P))).
  Proof.
    intros P x. apply poly_step_envelopes with (vars := vars_of P).
    - lia.
    - apply poly_raw_initial_reduced.
    - apply poly_assign_initial_envelopes.
  Qed.

  (** Adding one prepared row to raw initialization keeps its own normalization charge. *)
  Lemma T_poly_assign_initial_cons : forall r flag rows,
    (T_poly_initial X.encode X.T_encode ((r, flag) :: rows) <=
      T_poly_normal_row X.encode X.T_encode r + T_poly_initial X.encode X.T_encode rows +
      12 * N.of_nat (length rows + 1))%N.
  Proof.
    intros r flag rows.
    pose proof (poly_T_map_members _ _ (fun _ : lcons X.t * bool => 0%Z)
      (fun _ : lcons X.t * bool => 1%N) 1 rows
      (fun _ _ => N.le_refl 1%N)) as Hzeros.
    pose proof (poly_T_map_members _ _ (@poly_pad_row X.t) (@T_poly_pad_row X.t) 4
      (poly_initial X.encode rows) ltac:(intros; apply T_poly_pad_row_le)) as Hpad.
    rewrite poly_initial_length in Hpad.
    time_unfold (@T_poly_initial). cbn [fst snd]. time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    change (fun p => T_poly_pad_row p) with (@T_poly_pad_row X.t).
    nia.
  Qed.

  (** A nonzero summed coefficient must have an occurrence in the source list. *)
  Lemma poly_assign_coefficient_key : forall x xs,
    C.coef_of x xs <> 0%Z -> In x (map fst xs).
  Proof.
    intros x xs. induction xs as [|[y a] xs IH]; intro Hnonzero.
    - exfalso. apply Hnonzero. reflexivity.
    - rewrite coef_of_cons in Hnonzero. cbn [map fst].
      destruct (X.eqb_spec x y) as [Heq|Hneq].
      + left. symmetry. exact Heq.
      + right. now apply IH.
  Qed.

  (** Removing an absent variable preserves the complete coefficient list. *)
  Lemma poly_assign_filter_absent : forall x xs,
    ~ In x (map fst xs) -> filter (poly_without_key x) xs = xs.
  Proof.
    intros x xs. induction xs as [|[y a] xs IH]; intro Habsent; [reflexivity|].
    change ((if negb (X.eqb y x) then (y, a) :: filter (poly_without_key x) xs
      else filter (poly_without_key x) xs) = (y, a) :: xs).
    destruct (X.eqb_spec y x) as [Heq|Hneq].
    - subst y. exfalso. apply Habsent. now left.
    - cbn [negb]. f_equal. apply IH. intro Hin. apply Habsent. now right.
  Qed.

  (** Substitution at an absent key preserves every coefficient and the right-hand side. *)
  Lemma poly_assign_subst_absent_coefficients : forall x f r,
    ~ In x (map fst (lhs r)) ->
    (forall y, C.coef_of y (lhs (subst x f r)) = C.coef_of y (lhs r)) /\
    rhs (subst x f r) = rhs r.
  Proof.
    intros x f r Habsent.
    assert (Hzero : poly_coefficient X.eqb x r = 0%Z).
    { rewrite <- coef_of_poly_coefficient. now apply poly_coef_absent. }
    unfold subst, poly_substitute. rewrite Hzero. cbn [lhs rhs].
    change ((forall y, C.coef_of y (poly_normal_coef X.encode
      (filter (poly_without_key x) (lhs r) ++ poly_scale_coef 0 (coef f))) =
      C.coef_of y (lhs r)) /\ (rhs r - 0 * cst f)%Z = rhs r).
    rewrite (poly_assign_filter_absent x (lhs r) Habsent). split.
    - intro y. rewrite coef_of_normal, coef_of_app, coef_of_scale. ring.
    - ring.
  Qed.

  (** Zero-scaled affine entries cannot introduce a new retained coefficient. *)
  Lemma poly_assign_subst_absent_support : forall x f r p,
    ~ In x (map fst (lhs r)) -> In p (lhs (subst x f r)) ->
    In (fst p) (map fst (lhs r)).
  Proof.
    intros x f r [y a] Habsent Hin. cbn [fst].
    destruct (poly_assign_subst_absent_coefficients x f r Habsent) as [Hcoef _].
    pose proof (poly_coef_member y a (lhs (subst x f r))) as Hmember.
    assert (Hunique : NoDup (map fst (lhs (subst x f r)))).
    { unfold subst, poly_substitute. apply poly_normal_coef_nodup. }
    specialize (Hmember Hunique Hin). rewrite Hcoef in Hmember.
    assert (Hnonzero : a <> 0%Z).
    { unfold subst, poly_substitute in Hin. exact (poly_normal_coef_nonzero _ _ _ _ Hin). }
    apply poly_assign_coefficient_key. now rewrite Hmember.
  Qed.

  (** An absent-variable substitution retains the source row's size envelope. *)
  Lemma poly_assign_subst_absent_envelope : forall x f r,
    ~ In x (map fst (lhs r)) -> NoDup (map fst (lhs r)) ->
    length (lhs (subst x f r)) <= length (lhs r) /\
    C.row_key_bits (subst x f r) <= C.row_key_bits r /\
    C.row_bits (subst x f r) <= C.row_bits r.
  Proof.
    intros x f r Habsent Hnormal.
    destruct (poly_assign_subst_absent_coefficients x f r Habsent) as [Hcoef Hrhs].
    assert (Hunique : NoDup (map fst (lhs (subst x f r)))).
    { unfold subst, poly_substitute. apply poly_normal_coef_nodup. }
    split.
    - rewrite <- (length_map fst (lhs (subst x f r))), <- (length_map fst (lhs r)).
      apply NoDup_incl_length; [exact Hunique|]. intros y Hin.
      apply in_map_iff in Hin as [p [Heq Hin]]. subst y.
      now apply poly_assign_subst_absent_support with (x := x) (f := f).
    - split.
      + unfold C.row_key_bits at 1. apply poly_max_bound; [lia|].
        apply Forall_forall. intros p Hin.
        pose proof (poly_assign_subst_absent_support x f r p Habsent Hin) as Hkey.
        apply in_map_iff in Hkey as [q [Heq Hq]]. rewrite <- Heq.
        now apply poly_row_key_member.
      + unfold C.row_bits at 1. rewrite Hrhs. apply poly_max_bound;
          [apply poly_row_rhs_bits|].
        apply Forall_forall. intros [y a] Hin. cbn [snd].
        pose proof (poly_coef_member y a _ Hunique Hin) as Hmember.
        rewrite Hcoef in Hmember. rewrite <- Hmember, coef_of_poly_coefficient.
        now apply poly_row_coefficient_bits.
  Qed.

  (** Normal affine substitution preserves the key maximum and doubles arithmetic width. *)
  Lemma poly_assign_subst_normal_sizes : forall x f r keys bits,
    NoDup (map fst (lhs r)) -> NoDup (map fst (coef f)) ->
    C.row_key_bits r <= keys -> C.row_bits r <= bits ->
    C.row_key_bits (LCons X.t (coef f) REq (cst f)) <= keys ->
    C.row_bits (LCons X.t (coef f) REq (cst f)) <= bits ->
    length (lhs (subst x f r)) <= length (lhs r) + length (coef f) /\
    C.row_key_bits (subst x f r) <= keys /\ C.row_bits (subst x f r) <= 2 * bits + 1.
  Proof.
    intros x f r keys bits Hnr Hnf Hkr Hbr Hkf Hbf.
    set (a := poly_coefficient X.eqb x r).
    set (kept := filter (poly_without_key x) (lhs r)).
    assert (Ha : Z.size_nat a <= bits).
    { unfold a. pose proof (poly_row_coefficient_bits x r Hnr). lia. }
    assert (Hkept_unique : NoDup (map fst kept)).
    { unfold kept. now apply poly_nodup_map_filter. }
    assert (Hkept_bits : Forall (fun p => Z.size_nat (snd p) <= bits) kept).
    { apply Forall_forall. intros p Hin. unfold kept in Hin.
      apply filter_In in Hin as [Hin _]. pose proof (poly_row_entry_bits r p Hin). lia. }
    assert (Hform_bits : Forall (fun p => Z.size_nat (snd p) <= bits) (coef f)).
    { apply Forall_forall. intros p Hin.
      pose proof (poly_row_entry_bits (LCons X.t (coef f) REq (cst f)) p Hin). lia. }
    assert (Hout : lhs (subst x f r) =
      poly_normal_coef X.encode (kept ++ poly_scale_coef a (coef f))) by reflexivity.
    split.
    - rewrite Hout. eapply Nat.le_trans; [apply poly_normal_length|].
      unfold poly_scale_coef. rewrite length_app, length_map.
      unfold kept. apply Nat.add_le_mono_r, filter_length_le.
    - split.
      + unfold C.row_key_bits. rewrite Hout. apply poly_max_bound; [lia|].
        apply Forall_forall. intros p Hin.
        pose proof (poly_normal_coef_keys _ _ _ p Hin) as Hkey.
        rewrite map_app in Hkey. apply in_app_iff in Hkey as [Hkey|Hkey].
        * apply in_map_iff in Hkey as [q [Heq Hq]]. unfold kept in Hq.
          apply filter_In in Hq as [Hq _]. rewrite <- Heq.
          pose proof (poly_row_key_member r q Hq). lia.
        * unfold poly_scale_coef in Hkey. rewrite map_map in Hkey.
          apply in_map_iff in Hkey as [q [Heq Hq]]. cbn [fst] in Heq. rewrite <- Heq.
          pose proof (poly_row_key_member (LCons X.t (coef f) REq (cst f)) q Hq). lia.
      + unfold C.row_bits. apply poly_max_bound.
        * change (Z.size_nat (rhs r - a * cst f) <= 2 * bits + 1).
          pose proof (poly_row_rhs_bits r) as Hr.
          pose proof (poly_row_rhs_bits (LCons X.t (coef f) REq (cst f))) as Hf.
          cbn [rhs] in Hf. pose proof (poly_size_mul a (cst f)) as Hmul.
          pose proof (poly_size_add (rhs r) (- (a * cst f))) as Hadd.
          rewrite poly_size_opp in Hadd. change (Z.size_nat (rhs r + - (a * cst f)) <=
            2 * bits + 1). lia.
        * apply Forall_forall. intros [y z] Hin. cbn [snd]. rewrite Hout in Hin.
          pose proof (poly_coef_member y z _ (poly_normal_coef_nodup _ _ _) Hin) as Hcoef.
          rewrite coef_of_normal, coef_of_app, coef_of_scale in Hcoef.
          pose proof (poly_coef_bits y kept bits Hkept_unique Hkept_bits) as Hleft.
          pose proof (poly_coef_bits y (coef f) bits Hnf Hform_bits) as Hright.
          pose proof (poly_size_mul a (C.coef_of y (coef f))) as Hmul.
          pose proof (poly_size_add (C.coef_of y kept) (a * C.coef_of y (coef f))) as Hadd.
          rewrite <- Hcoef. lia.
  Qed.

  (** An existing pivot makes elimination linear in its row count. *)
  Lemma T_poly_assign_step_pivot_linear : forall x rows pivot dim mlen keys bits,
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    find (poly_pivot X.eqb x) rows = Some pivot ->
    (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows <=
      poly_step_factor * N.of_nat (length rows + 1) *
        poly_clock_span dim mlen keys bits)%N.
  Proof.
    intros x rows pivot dim mlen keys bits Hrows Hpivot.
    pose proof (poly_T_find_members _ (poly_pivot X.eqb x)
      (T_poly_pivot X.eqb X.T_eqb x)
      (poly_select_factor * poly_clock_span dim mlen keys bits)%N rows
      ltac:(intros r Hin; apply T_poly_pivot_bounded;
        exact (proj1 (Forall_forall _ _) Hrows r Hin))) as Hfind.
    pose proof Hpivot as Hmember. apply find_some in Hmember as [Hmember _].
    pose proof (proj1 (Forall_forall _ _) Hrows pivot Hmember) as Hp.
    pose proof (poly_T_map_members _ _ (poly_cancel X.encode X.eqb x pivot)
      (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot)
      (poly_cancel_factor * poly_clock_span dim mlen keys bits)%N rows
      ltac:(intros r Hin; apply T_poly_cancel_bounded; [exact Hp|];
        exact (proj1 (Forall_forall _ _) Hrows r Hin))) as Hmap.
    pose proof (poly_span_positive dim mlen keys bits) as Hpositive.
    set (work := poly_clock_span dim mlen keys bits) in *.
    time_unfold (@T_poly_step). rewrite Hpivot. time_simpl.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    change (fun r => T_poly_pivot X.eqb X.T_eqb x r)
      with (T_poly_pivot X.eqb X.T_eqb x).
    change (fun r => T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot r)
      with (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot).
    unfold poly_step_factor. clear -Hfind Hmap Hpositive. clearbody work. nia.
  Qed.

  (** Zero multiplication does not inspect the affine coefficient's magnitude. *)
  Lemma T_poly_assign_scale_zero : forall xs : list (X.t * Z),
    (T_poly_scale_coef 0 xs <= 8 * N.of_nat (length xs + 1))%N.
  Proof.
    intro xs. time_unfold (@T_poly_scale_coef).
    lazymatch goal with
    | |- context [ListDef.T_map ?f ?Tf xs] =>
      assert (Hmap : (ListDef.T_map f Tf xs <= 7 * N.of_nat (length xs) + 1)%N);
      [ apply (poly_T_map_members _ _ f Tf 6 xs); intros [x a] Hin;
        time_unfold Z.T_mul; time_simpl; lia
      | nia ]
    end.
  Qed.

  (** Every zero-scaled coefficient has zero width and retains only its original key. *)
  Lemma poly_assign_scale_zero_sizes : forall xs keys bits,
    Forall (fun p : X.t * Z => Pos.size_nat (X.encode (fst p)) <= keys) xs ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) (poly_scale_coef 0 xs).
  Proof.
    intros xs keys bits Hkeys. unfold poly_scale_coef. apply Forall_map.
    eapply Forall_impl; [|exact Hkeys]. intros [x a] Hkey.
    cbn [fst snd Z.mul Z.size_nat]. split; [exact Hkey|lia].
  Qed.

  Definition poly_assign_zero_subst_factor : N :=
    (4 * poly_normal_factor + 4 * poly_coef_factor + 4 * X.c_key + 96)%N.

  (** Normal source rows and zero-scaled normal forms incur only a linear width charge. *)
  Lemma T_poly_assign_subst_zero : forall x f r keys bits,
    NoDup (map fst (lhs r)) -> NoDup (map fst (coef f)) ->
    C.row_key_bits r <= keys -> C.row_bits r <= bits ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) (coef f) ->
    poly_coefficient X.eqb x r = 0%Z ->
    (T_subst x f r <= poly_assign_zero_subst_factor *
      N.of_nat (length (lhs r) + length (coef f) + 1) *
      N.of_nat (keys + bits + 1))%N.
  Proof.
    intros x f r keys bits Hnormal Hform Hkeys Hbits Hformkeys Hzero.
    set (kept := filter (poly_without_key x) (lhs r)).
    assert (Hkept_unique : NoDup (map fst kept)).
    { unfold kept. apply poly_nodup_map_filter. exact Hnormal. }
    assert (Hkept_sizes : Forall (fun p =>
      Pos.size_nat (X.encode (fst p)) <= keys /\ Z.size_nat (snd p) <= bits) kept).
    { apply Forall_forall. intros p Hin. unfold kept in Hin.
      apply filter_In in Hin as [Hin _].
      pose proof (poly_row_key_member r p Hin).
      pose proof (poly_row_entry_bits r p Hin). split; lia. }
    pose proof (T_poly_normal_pair kept (poly_scale_coef 0 (coef f)) keys bits
      Hkept_unique (poly_scale_nodup _ _ Hform) Hkept_sizes
      (poly_assign_scale_zero_sizes _ _ bits Hformkeys)) as Hnormal_time.
    assert (Hscaled_length : length (poly_scale_coef 0 (coef f)) = length (coef f))
      by (unfold poly_scale_coef; apply length_map).
    rewrite Hscaled_length in Hnormal_time.
    pose proof (T_poly_coefficient_normal x r keys bits Hnormal Hkeys Hbits) as Hlookup.
    pose proof (T_poly_assign_scale_zero (coef f)) as Hscale.
    pose proof (T_poly_without_filter_le x r) as Hfilter.
    pose proof (Datatypes.T_app_le kept (poly_scale_coef 0 (coef f))) as Happ.
    pose proof (filter_length_le (poly_without_key x) (lhs r)) as Hlength.
    fold kept in Hlength.
    pose proof (Z.T_sub_le (rhs r) 0) as Hsub.
    pose proof (poly_row_rhs_bits r) as Hrhs.
    assert (Hmul : (Z.T_mul 0 (cst f) <= 1)%N).
    { time_unfold Z.T_mul. time_simpl. lia. }
    assert (Hsize : C.lsize r <= (length (lhs r) + 1) * (keys + bits + 1)).
    { unfold C.lsize. apply Nat.mul_le_mono_l. lia. }
    set (work := (N.of_nat (length (lhs r) + length (coef f) + 1) *
      N.of_nat (keys + bits + 1))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. change (1 * 1 <= N.of_nat (length (lhs r) + length (coef f) + 1) *
        N.of_nat (keys + bits + 1))%N. apply N.mul_le_mono; lia. }
    assert (Hwidth_work : (N.of_nat (keys + bits + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_l (N.of_nat (keys + bits + 1))) at 1.
      apply N.mul_le_mono_r. lia. }
    assert (Hleft_work : (N.of_nat (length (lhs r) + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_r (N.of_nat (length (lhs r) + 1))) at 1.
      apply N.mul_le_mono; lia. }
    assert (Hright_work : (N.of_nat (length (coef f) + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_r (N.of_nat (length (coef f) + 1))) at 1.
      apply N.mul_le_mono; lia. }
    assert (Hnormal_total : (T_poly_normal_coef X.encode X.T_encode
      (kept ++ poly_scale_coef 0 (coef f)) <= poly_normal_factor * work)%N).
    { eapply N.le_trans; [exact Hnormal_time|]. rewrite <- N.mul_assoc.
      apply N.mul_le_mono_l. unfold work. apply N.mul_le_mono; [lia|reflexivity]. }
    assert (Hlookup_total : (T_poly_coefficient X.eqb X.T_eqb x r <=
      poly_coef_factor * work)%N).
    { eapply N.le_trans; [exact Hlookup|]. rewrite <- N.mul_assoc.
      apply N.mul_le_mono_l. unfold work. apply N.mul_le_mono; [lia|reflexivity]. }
    assert (Hscale_total : (T_poly_scale_coef 0 (coef f) <= 8 * work)%N).
    { eapply N.le_trans; [exact Hscale|]. now apply N.mul_le_mono_l. }
    assert (Hsize_work : (N.of_nat (C.lsize r) <= work)%N).
    { eapply N.le_trans with (m := N.of_nat ((length (lhs r) + 1) * (keys + bits + 1))).
      - lia.
      - rewrite Nat2N.inj_mul. unfold work. apply N.mul_le_mono; [lia|reflexivity]. }
    assert (Hfilter_total : (List.T_filter (poly_without_key x) (T_poly_without_key x)
      (lhs r) <= (X.c_key + 8) * work)%N).
    { eapply N.le_trans; [exact Hfilter|]. now apply N.mul_le_mono_l. }
    assert (Happ_total : (Datatypes.T_app kept (poly_scale_coef 0 (coef f)) <= work)%N)
      by lia.
    assert (Harithmetic : (Z.T_mul 0 (cst f) + Z.T_sub (rhs r) 0 <= 8 * work)%N).
    { cbn [Z.size_nat] in Hsub. rewrite Nat.add_0_r in Hsub.
      assert (Hlinear : (Z.T_sub (rhs r) 0 <= 4 * N.of_nat (keys + bits + 1))%N) by lia.
      nia. }
    replace (poly_assign_zero_subst_factor *
      N.of_nat (length (lhs r) + length (coef f) + 1) * N.of_nat (keys + bits + 1))%N
      with (poly_assign_zero_subst_factor * work)%N by (unfold work; ring).
    time_unfold T_subst. time_unfold (@T_poly_substitute). rewrite Hzero.
    time_simpl. change (fun u : X.t => X.T_encode u) with X.T_encode.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun p : X.t * Z => negb (X.eqb (fst p) x)) with (poly_without_key x).
    lazymatch goal with
    | |- context [List.T_filter (poly_without_key x) ?Tf (lhs r)] =>
      change Tf with (T_poly_without_key x)
    end.
    fold kept. change (0 * cst f)%Z with 0%Z. unfold poly_assign_zero_subst_factor.
    clear -Hnormal_total Hlookup_total Hscale_total Hfilter_total Happ_total Harithmetic Hpositive.
    clearbody work. nia.
  Qed.

  Definition poly_assign_normal_subst_factor : N :=
    (8 * poly_normal_factor + 4 * poly_coef_factor + 4 * X.c_key + 192)%N.

  (** Two normal coefficient lists require one quadratic bit charge per stored key. *)
  Lemma T_poly_assign_subst_normal : forall x f r dim keys bits,
    poly_input_envelope dim keys bits r ->
    poly_input_envelope dim keys bits (LCons X.t (coef f) REq (cst f)) ->
    (T_subst x f r <= poly_assign_normal_subst_factor *
      poly_clock_span dim 0 keys bits)%N.
  Proof.
    intros x f r dim keys bits
      (Hnr & Hdr & Hkr & Hbr) (Hnf & Hdf & Hkf & Hbf).
    cbn [lhs] in Hnf, Hdf.
    set (a := poly_coefficient X.eqb x r).
    set (kept := filter (poly_without_key x) (lhs r)).
    assert (Ha : Z.size_nat a <= bits).
    { unfold a. pose proof (poly_row_coefficient_bits x r Hnr). lia. }
    assert (Hform : poly_row_envelope dim 0 keys bits
      (PolyRow X.t (LCons X.t (coef f) REq (cst f)) [] false)).
    { unfold poly_row_envelope. cbn [poly_constraint poly_multipliers lhs length].
      repeat split; try assumption; [lia|constructor]. }
    pose proof (T_poly_scale_row_envelope a _ dim 0 keys bits Hform Ha) as Hscale.
    cbn [poly_constraint lhs] in Hscale.
    assert (Hkept_unique : NoDup (map fst kept)).
    { unfold kept. now apply poly_nodup_map_filter. }
    assert (Hkept_length : length kept <= dim).
    { unfold kept. pose proof (filter_length_le (poly_without_key x) (lhs r)). lia. }
    assert (Hkept_sizes : Forall (fun p =>
      Pos.size_nat (X.encode (fst p)) <= keys /\ Z.size_nat (snd p) <= 2 * bits) kept).
    { apply Forall_forall. intros p Hin. unfold kept in Hin.
      apply filter_In in Hin as [Hin _]. pose proof (poly_row_key_member r p Hin).
      pose proof (poly_row_entry_bits r p Hin). split; lia. }
    pose proof (poly_row_entry_bounds (LCons X.t (coef f) REq (cst f))
      keys bits Hkf Hbf) as Hentries.
    cbn [lhs] in Hentries.
    pose proof (T_poly_normal_pair kept (poly_scale_coef a (coef f)) keys (2 * bits)
      Hkept_unique (poly_scale_nodup _ _ Hnf) Hkept_sizes
      (poly_scale_entry_sizes a _ keys bits Ha Hentries)) as Hnormal.
    assert (Hscale_length : length (poly_scale_coef a (coef f)) = length (coef f))
      by (unfold poly_scale_coef; apply length_map).
    rewrite Hscale_length in Hnormal.
    pose proof (poly_span_normal_pair (length kept) (length (coef f))
      dim 0 keys bits Hkept_length Hdf) as Hnormal_span.
    assert (Hnormal_total : (T_poly_normal_coef X.encode X.T_encode
      (kept ++ poly_scale_coef a (coef f)) <=
      4 * poly_normal_factor * poly_clock_span dim 0 keys bits)%N).
    { eapply N.le_trans; [exact Hnormal|].
      pose proof (N.mul_le_mono_l _ _ poly_normal_factor Hnormal_span). nia. }
    pose proof (T_poly_coefficient_normal x r keys bits Hnr Hkr Hbr) as Hlookup.
    pose proof (poly_span_linear (length (lhs r)) (keys + bits)
      dim 0 keys bits ltac:(lia) ltac:(lia)) as Hlookup_span.
    assert (Hlookup_total : (T_poly_coefficient X.eqb X.T_eqb x r <=
      poly_coef_factor * poly_clock_span dim 0 keys bits)%N).
    { eapply N.le_trans; [exact Hlookup|]. rewrite <- N.mul_assoc.
      now apply N.mul_le_mono_l. }
    pose proof (T_poly_without_filter_le x r) as Hfilter.
    assert (Hlsize_span : (N.of_nat (C.lsize r) <= poly_clock_span dim 0 keys bits)%N).
    { unfold C.lsize. rewrite Nat2N.inj_mul.
      apply poly_span_linear; lia. }
    assert (Hfilter_total : (List.T_filter (poly_without_key x) (T_poly_without_key x)
      (lhs r) <= (X.c_key + 8) * poly_clock_span dim 0 keys bits)%N).
    { eapply N.le_trans; [exact Hfilter|]. now apply N.mul_le_mono_l. }
    pose proof (Datatypes.T_app_le kept (poly_scale_coef a (coef f))) as Happ.
    pose proof (poly_span_linear dim 0 dim 0 keys bits ltac:(lia) ltac:(lia)) as Hcount.
    rewrite N.mul_1_r in Hcount.
    assert (Happ_total : (Datatypes.T_app kept (poly_scale_coef a (coef f)) <=
      poly_clock_span dim 0 keys bits)%N) by lia.
    pose proof (poly_T_Z_mul_bilinear a (cst f)) as Hmul.
    pose proof (Z.T_sub_le (rhs r) (a * cst f)) as Hsub.
    pose proof (poly_row_rhs_bits r) as Hrhs.
    pose proof (poly_row_rhs_bits (LCons X.t (coef f) REq (cst f))) as Hcst.
    cbn [rhs] in Hcst.
    pose proof (poly_size_mul a (cst f)) as Hproduct.
    pose proof (poly_span_product 0 bits dim 0 keys bits ltac:(lia) ltac:(lia)) as Hscalar.
    rewrite N.mul_1_l in Hscalar.
    assert (Harithmetic : (Z.T_mul a (cst f) + Z.T_sub (rhs r) (a * cst f) <=
      32 * poly_clock_span dim 0 keys bits)%N).
    { assert (Hmul_width : (Z.T_mul a (cst f) <= 8 * N.of_nat (bits + 1)^2)%N).
      { eapply N.le_trans; [exact Hmul|].
        replace (8 * N.of_nat (bits + 1)^2)%N with
          ((8 * N.of_nat (bits + 1)) * N.of_nat (bits + 1))%N
          by (rewrite N.pow_2_r; ring).
        apply N.mul_le_mono; [apply N.mul_le_mono_l|]; lia. }
      assert (Hsub_width : (Z.T_sub (rhs r) (a * cst f) <=
        12 * N.of_nat (bits + 1)^2)%N) by (rewrite N.pow_2_r; nia).
      nia. }
    pose proof (poly_span_positive dim 0 keys bits) as Hpositive.
    set (work := poly_clock_span dim 0 keys bits) in *.
    time_unfold T_subst. time_unfold (@T_poly_substitute).
    change (fun p => negb (X.eqb (fst p) x)) with (poly_without_key x).
    fold a kept. time_simpl.
    lazymatch goal with
    | |- context [List.T_filter (poly_without_key x) ?Tf (lhs r)] =>
      change Tf with (T_poly_without_key x)
    end.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    fold a kept. unfold poly_assign_normal_subst_factor.
    clear -Hnormal_total Hlookup_total Hfilter_total Hscale Happ_total Harithmetic Hpositive.
    clearbody work. nia.
  Qed.

  (** One normal substitution increases only the fixed multiplier of a scale-one check. *)
  Lemma poly_assign_checker_measure : forall P c ms dim bits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    length ms = length P -> Forall (fun m => Z.size_nat m <= 2 * bits + 2) ms ->
    length (lhs c) <= dim -> C.row_key_bits c + C.row_bits c <= 3 * bits + 1 ->
    C.csize P ms + 2 * (C.lsize c + C.cbits P ms + 1) <=
      48 * (dim + terms (Reached P) + length P + 1) * (bits + 1)^2.
  Proof.
    intros P c ms dim bits Hsource Hlength Hmult Hdim Hwidth.
    assert (Hsource' : Forall (fun p => C.row_key_bits p + C.row_bits p <= 2 * bits + 1) P).
    { eapply Forall_impl; [|exact Hsource]. intros p Hp.
      change (C.row_key_bits p + C.row_bits p <= bits) in Hp.
      change (C.row_key_bits p + C.row_bits p <= 2 * bits + 1). lia. }
    assert (Hmult' : Forall (fun m => Z.size_nat m <= 2 * (2 * bits + 1) + 2) ms).
    { eapply Forall_impl; [|exact Hmult]. intros m Hm.
      change (Z.size_nat m <= 2 * bits + 2) in Hm.
      change (Z.size_nat m <= 2 * (2 * bits + 1) + 2). lia. }
    pose proof (poly_scale_one_measure_terms P c ms dim (2 * bits + 1)
      Hsource' Hlength Hmult' Hdim ltac:(lia)) as Hmeasure.
    replace (12 * (dim + terms (Reached P) + length P + 1) * (2 * bits + 1 + 1)^2)
      with (48 * (dim + terms (Reached P) + length P + 1) * (bits + 1)^2)
      in Hmeasure by (cbn [Nat.pow]; nia).
    exact Hmeasure.
  Qed.

  Lemma T_poly_assign_checker : forall P c ms dim bits,
    Forall (fun p => C.row_key_bits p + C.row_bits p <= bits) P ->
    length ms = length P -> Forall (fun m => Z.size_nat m <= 2 * bits + 2) ms ->
    length (lhs c) <= dim -> C.row_key_bits c + C.row_bits c <= 3 * bits + 1 ->
    (C.T_check_entails P c (Cert ms 1 false) <= 48 * C.c_lc *
      N.of_nat (dim + terms (Reached P) + length P + 1) * N.of_nat (bits + 1)^2)%N.
  Proof.
    intros P c ms dim bits Hsource Hlength Hmult Hdim Hwidth.
    pose proof (poly_assign_checker_measure P c ms dim bits
      Hsource Hlength Hmult Hdim Hwidth) as Hmeasure.
    pose proof (C.T_check_entails_le P c (Cert ms 1 false)) as Hcheck.
    change (C.T_check_entails P c (Cert ms 1 false) <= C.c_lc *
      N.of_nat (C.csize P ms + 2 * (C.lsize c + C.cbits P ms + 1)))%N in Hcheck.
    eapply N.le_trans; [exact Hcheck|].
    replace (48 * C.c_lc * N.of_nat (dim + terms (Reached P) + length P + 1) *
      N.of_nat (bits + 1)^2)%N with
      (C.c_lc * N.of_nat (48 * (dim + terms (Reached P) + length P + 1) * (bits + 1)^2))%N
      by (rewrite !Nat2N.inj_mul, poly_nat_square, N.pow_2_r;
        change (N.of_nat 48) with 48%N; ring).
    apply N.mul_le_mono_l. lia.
  Qed.
End PolyAssignBranch.


Module PolyAssignBranchExtended (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X).
  Include PolyAssignBranch X L N F C.
  (** Filtering evaluates exactly one predicate for each inspected occurrence. *)
  Lemma poly_assign_T_filter_cons : forall A (f : A -> bool) (Tf : A -> N) x xs,
    List.T_filter f Tf (x :: xs) = (1 + Tf x + List.T_filter f Tf xs)%N.
  Proof.
    intros A f Tf x xs. time_unfold List.T_filter. destruct (f x); time_simpl;
      fold (List.T_filter f Tf xs); ring.
  Qed.

  Lemma poly_assign_T_map_cons : forall A B (f : A -> B) (Tf : A -> N) x xs,
    ListDef.T_map f Tf (x :: xs) = (1 + Tf x + ListDef.T_map f Tf xs)%N.
  Proof.
    intros A B f Tf x xs. time_unfold ListDef.T_map. time_simpl.
    fold (ListDef.T_map f Tf xs). ring.
  Qed.

  Lemma poly_assign_T_find_false : forall A (f : A -> bool) (Tf : A -> N) x xs,
    f x = false ->
    List.T_find f Tf (x :: xs) = (1 + Tf x + List.T_find f Tf xs)%N.
  Proof.
    intros A f Tf x xs Hfalse. time_unfold List.T_find. rewrite Hfalse. time_simpl.
    fold (List.T_find f Tf xs). ring.
  Qed.

  Lemma poly_assign_T_app_cons : forall A (x : A) xs ys,
    Datatypes.T_app (x :: xs) ys = (1 + Datatypes.T_app xs ys)%N.
  Proof.
    intros A x xs ys. time_unfold Datatypes.T_app. time_simpl.
    fold (Datatypes.T_app xs ys). ring.
  Qed.

  (** The pivot test adds a fixed-cost zero test to its one coefficient lookup. *)
  Lemma T_poly_assign_pivot_lookup : forall x r,
    (T_poly_pivot X.eqb X.T_eqb x r <=
      T_poly_coefficient X.eqb X.T_eqb x (poly_constraint r) + 8)%N.
  Proof.
    intros x r. pose proof (T_poly_zero_test
      (poly_coefficient X.eqb x (poly_constraint r))) as Hzero.
    time_unfold (@T_poly_pivot). destruct (lrel (poly_constraint r)); time_simpl;
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb; lia.
  Qed.

  (** Cancelling a zero-coefficient row evaluates the two lookups and returns that row. *)
  Lemma T_poly_assign_cancel_zero : forall x pivot r,
    poly_coefficient X.eqb x (poly_constraint r) = 0%Z ->
    (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot r <=
      T_poly_coefficient X.eqb X.T_eqb x (poly_constraint pivot) +
      T_poly_coefficient X.eqb X.T_eqb x (poly_constraint r) + 8)%N.
  Proof.
    intros x pivot r Hzero. time_unfold (@T_poly_cancel). rewrite Hzero. time_simpl.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    time_unfold Z.T_eqb. time_simpl. cbn [Z.eqb]. lia.
  Qed.

  (** This proof-only branch keeps the native nested lambdas and adds no pair wrapper. *)
  Definition poly_assign_inequalities (x : X.t) (rows : list (poly_row X.t)) :=
    let pos := filter (fun r => (0 <? poly_coefficient X.eqb x (poly_constraint r))%Z) rows in
    let neg := filter (fun r => (poly_coefficient X.eqb x (poly_constraint r) <? 0)%Z) rows in
    filter (fun r => Z.eqb (poly_coefficient X.eqb x (poly_constraint r)) 0) rows ++
      flat_map (fun p => map (fun q =>
        poly_add_rows X.encode (- poly_coefficient X.eqb x (poly_constraint q))%Z p
          (poly_coefficient X.eqb x (poly_constraint p)) q) neg) pos.

  TimeFun poly_assign_inequalities.

  (** The actual step clock separates the pivot search from its selected traversal. *)
  Lemma T_poly_assign_step_split : forall x rows,
    T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows =
      (List.T_find (poly_pivot X.eqb x) (T_poly_pivot X.eqb X.T_eqb x) rows +
       match find (poly_pivot X.eqb x) rows with
       | Some pivot => 1 + ListDef.T_map (poly_cancel X.encode X.eqb x pivot)
           (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot) rows
       | None => T_poly_assign_inequalities x rows
       end)%N.
  Proof.
    intros x rows. time_unfold (@T_poly_step).
    destruct (find (poly_pivot X.eqb x) rows) as [pivot|].
    - time_simpl.
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      change (fun r => T_poly_pivot X.eqb X.T_eqb x r)
        with (T_poly_pivot X.eqb X.T_eqb x).
      change (fun r => T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot r)
        with (T_poly_cancel X.encode X.T_encode X.eqb X.T_eqb x pivot).
      ring.
    - unfold T_poly_assign_inequalities, poly_assign_inequalities.
      time_simpl.
      change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
      change (fun u : X.t => X.T_encode u) with X.T_encode.
      change (fun r => T_poly_pivot X.eqb X.T_eqb x r)
        with (T_poly_pivot X.eqb X.T_eqb x).
      ring.
  Qed.

  (** A zero head adds three tests and one retained list cell to the inequality branch. *)
  Lemma T_poly_assign_inequalities_zero_head : forall x z rows,
    poly_coefficient X.eqb x (poly_constraint z) = 0%Z ->
    (T_poly_assign_inequalities x (z :: rows) <= T_poly_assign_inequalities x rows +
      4 * T_poly_coefficient X.eqb X.T_eqb x (poly_constraint z) + 32)%N.
  Proof.
    intros x z rows Hzero. time_unfold T_poly_assign_inequalities.
    rewrite !poly_assign_T_filter_cons.
    cbn [filter]. rewrite Hzero. cbn [Z.ltb Z.eqb app].
    rewrite poly_assign_T_app_cons. time_simpl.
    change (fun u v : X.t => X.T_eqb u v) with X.T_eqb.
    change (fun u : X.t => X.T_encode u) with X.T_encode.
    rewrite !Z.ltb_irrefl. cbn beta iota zeta.
    pose proof (Z.T_ltb_le 0 0) as Hlt.
    pose proof (T_poly_zero_test 0) as Heq. cbn [Z.size_nat] in Hlt. lia.
  Qed.

  (** Separating an irrelevant affine equality preserves the source-only step charge. *)
  Lemma T_poly_assign_step_zero_head : forall x z rows bound,
    poly_coefficient X.eqb x (poly_constraint z) = 0%Z ->
    (forall r, In r rows ->
      (T_poly_coefficient X.eqb X.T_eqb x (poly_constraint r) <= bound)%N) ->
    (T_poly_step X.encode X.T_encode X.eqb X.T_eqb x (z :: rows) <=
      T_poly_step X.encode X.T_encode X.eqb X.T_eqb x rows + bound +
      8 * T_poly_coefficient X.eqb X.T_eqb x (poly_constraint z) + 64)%N.
  Proof.
    intros x z rows bound Hzero Hrows.
    assert (Hpivot : poly_pivot X.eqb x z = false).
    { unfold poly_pivot. rewrite Hzero. destruct (lrel (poly_constraint z)); reflexivity. }
    pose proof (T_poly_assign_pivot_lookup x z) as Htest.
    rewrite !T_poly_assign_step_split.
    rewrite (poly_assign_T_find_false _ _ _ _ _ Hpivot).
    cbn [find]. rewrite Hpivot.
    destruct (find (poly_pivot X.eqb x) rows) as [pivot|] eqn:Hfind.
    - pose proof Hfind as Hmember. apply find_some in Hmember as [Hmember _].
      specialize (Hrows pivot Hmember).
      pose proof (T_poly_assign_cancel_zero x pivot z Hzero) as Hcancel.
      rewrite poly_assign_T_map_cons. nia.
    - pose proof (T_poly_assign_inequalities_zero_head x z rows Hzero) as Hbranch. nia.
  Qed.

End PolyAssignBranchExtended.

Module PolyT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) <: POLY_ALL X L N F C.
  Include PolyClockCore X L N F C.

  Module RangeKey := PolyClockKey X.
  Module RangeCert := LinCertT RangeKey.
  Module RangeLinearize := PolyClockLinearize RangeKey L N.
  Module RangeCore := PolyClockCore RangeKey L N RangeLinearize RangeCert.
  Module AssignCore := PolyAssignBranchExtended X L N F C.

  Definition poly_range_input (P : list (lcons X.t)) (f : lin X.t) :=
    range_row f :: map (rename_row (@Some X.t)) (map (poly_normal_row X.encode) P).

  (** Renaming coordinates preserves every arithmetic coefficient width. *)
  Lemma poly_range_rename_bits : forall r,
    RangeCert.row_bits (rename_row (@Some X.t) r) = C.row_bits r.
  Proof.
    intro r. unfold RangeCert.row_bits, C.row_bits.
    cbn [rename_row lhs rhs]. rewrite map_map. reflexivity.
  Qed.

  (** Renaming coordinates preserves the stored occurrence count. *)
  Lemma poly_range_rename_terms : forall P,
    RangeCore.terms (Reached (map (rename_row (@Some X.t)) P)) = terms (Reached P).
  Proof.
    intro P. induction P as [|p P IH].
    - reflexivity.
    - change (length (lhs (rename_row (@Some X.t) p)) +
        RangeCore.terms (Reached (map (rename_row (@Some X.t)) P)) =
        length (lhs p) + terms (Reached P)).
      cbn [rename_row lhs]. now rewrite length_map, IH.
  Qed.

  (** Removing duplicate coefficients does not increase the total source occurrence count. *)
  Lemma poly_range_normal_terms : forall P,
    terms (Reached (map (poly_normal_row X.encode) P)) <= terms (Reached P).
  Proof.
    intro P. induction P as [|p P IH].
    - change (0 <= 0). lia.
    - change (length (poly_normal_coef X.encode (lhs p)) +
        terms (Reached (map (poly_normal_row X.encode) P)) <=
        length (lhs p) + terms (Reached P)).
      pose proof (poly_normal_length (lhs p)). lia.
  Qed.

  (** The temporary result coordinate adds exactly one occurrence before normalization. *)
  Lemma poly_range_input_terms : forall P f,
    RangeCore.terms (Reached (poly_range_input P f)) <=
      terms (Reached P) + length (coef f) + 1.
  Proof.
    intros P f.
    change (S (length (map (fun p => (Some (fst p), (-snd p)%Z)) (coef f))) +
      RangeCore.terms (Reached (map (rename_row (@Some X.t))
        (map (poly_normal_row X.encode) P))) <= terms (Reached P) + length (coef f) + 1).
    rewrite length_map, poly_range_rename_terms.
    pose proof (poly_range_normal_terms P). lia.
  Qed.

  (** The query equation contains the original form coefficients and a unit result coefficient. *)
  Lemma poly_range_row_bits : forall f,
    RangeCert.row_bits (range_row f) <= F.form_bits f + 1.
  Proof.
    intro f. unfold RangeCert.row_bits. cbn [range_row lhs rhs map snd].
    change (Nat.max 1 (fold_right Nat.max (Z.size_nat (cst f))
      (map (fun p => Z.size_nat (snd p))
        (map (fun p => (Some (fst p), (-snd p)%Z)) (coef f)))) <= F.form_bits f + 1).
    apply Nat.max_lub; [lia|]. apply poly_max_bound.
    - pose proof (poly_form_constant_bits f). lia.
    - apply Forall_map, Forall_forall. intros p Hp. cbn [snd].
      rewrite poly_size_opp. pose proof (poly_form_entry_bits f p Hp). lia.
  Qed.

  (** Original rows and the query share a uniform arithmetic width before the final normalization. *)
  Lemma poly_range_input_bits : forall P f,
    Forall (fun r => RangeCert.row_bits r <= nell (Reached P) + F.form_bits f + 1)
      (poly_range_input P f).
  Proof.
    intros P f. unfold poly_range_input. constructor.
    - pose proof (poly_range_row_bits f). lia.
    - apply Forall_map, Forall_map, Forall_forall. intros r Hr.
      rewrite poly_range_rename_bits.
      pose proof (proj2 (poly_raw_normal_widths P r Hr)) as Hwidth.
      pose proof (poly_raw_width P). lia.
  Qed.

  (** Raw form multiplicity is bounded by its count for the endpoint-size proof. *)
  Lemma poly_range_initial_width : forall P f,
    RangeCore.poly_raw_bits (poly_range_input P f) <=
      2 * nell (Reached P) + F.form_bits f + length (coef f) + 2.
  Proof.
    intros P f. change (fold_right Nat.max 0
      (map RangeCert.row_bits (poly_range_input P f)) +
      Nat.log2 (RangeCore.terms (Reached (poly_range_input P f))) + 1 <=
      2 * nell (Reached P) + F.form_bits f + length (coef f) + 2).
    assert (Hmax : fold_right Nat.max 0 (map RangeCert.row_bits (poly_range_input P f)) <=
      nell (Reached P) + F.form_bits f + 1).
    { apply poly_max_bound; [lia|apply poly_range_input_bits]. }
    pose proof (Nat.log2_le_mono _ _ (poly_range_input_terms P f)) as Hlog.
    pose proof (poly_log_add_count (terms (Reached P)) (length (coef f) + 1)) as Hcount.
    replace (terms (Reached P) + (length (coef f) + 1)) with
      (terms (Reached P) + length (coef f) + 1) in Hcount by lia.
    assert (Hbase : Nat.log2 (terms (Reached P)) + 1 <= nell (Reached P)).
    { unfold nell. lia. }
    lia.
  Qed.

  (** Every coordinate retained by row normalization came from that same raw row. *)
  Lemma poly_range_normal_key : forall r x,
    In x (map fst (lhs (poly_normal_row X.encode r))) -> In x (map fst (lhs r)).
  Proof.
    intros r x Hin. apply in_map_iff in Hin as [p [Hsame Hp]]. subst x.
    cbn [poly_normal_row lhs] in Hp. now apply poly_normal_coef_keys in Hp.
  Qed.

  (** The actual range fuel counts distinct form and source coordinates only. *)
  Lemma poly_range_fuel : forall P f,
    length (poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)) <=
      n P + length (coef f).
  Proof.
    intros P f.
    assert (Hlength : length (poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)) <=
      length (map fst (coef f) ++ vars_of P)).
    { apply NoDup_incl_length; [apply poly_variables_nodup|].
      intros x Hx. destruct (poly_variables_support _ _ Hx) as [r [Hr Hterm]].
      destruct Hr as [Hsame|Hr].
      - subst r. apply in_or_app. now left.
      - apply in_map_iff in Hr as [p [Hsame Hp]]. subst r.
        apply in_or_app. right. apply poly_vars_of_contains with (r := p); [exact Hp|].
        now apply poly_range_normal_key in Hterm. }
    rewrite length_app, length_map in Hlength. unfold n. lia.
  Qed.

  (** Every range endpoint fits the doubled-width envelope of its actual elimination run. *)
  Lemma poly_range_linear_width : forall P f,
    poly_bounds_width
      (poly_width_after (length (poly_variables X.encode
        (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)))
        (RangeCore.poly_raw_bits (poly_range_input P f))) (range_linear P f).
  Proof.
    intros P f. set (input := poly_range_input P f).
    set (vars := poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)).
    pose proof (RangeCore.poly_run_envelopes (map (@Some X.t) vars)
      (RangeCore.vars_of input)
      (poly_initial RangeKey.encode (map (fun r => (r, false)) input))
      (RangeCore.n input) (length input)
      (RangeCore.poly_raw_keys input) (RangeCore.poly_raw_bits input)
      ltac:(unfold RangeCore.n; lia)
      (RangeCore.poly_raw_initial_reduced input)
      (RangeCore.poly_raw_initial_envelopes input)) as Hrows.
    unfold range_linear. fold vars. change (poly_bounds_width
      (poly_width_after (length vars) (RangeCore.poly_raw_bits input))
      (fold_left (range_candidate (map (poly_normal_row X.encode) P) f)
        (poly_run tmp_encode tmp_eqb (map (@Some X.t) vars)
          (poly_initial tmp_encode (map (fun r => (r, false)) input))) (NegInf, PosInf))).
    apply poly_range_fold_width.
    - eapply Forall_impl; [|exact Hrows].
      intros r (Hnormal & Hdim & Hkeys & Hbits & Hmult & Hweights).
      rewrite length_map in Hbits.
      eapply Nat.le_trans; [apply RangeCore.poly_row_rhs_bits|exact Hbits].
    - unfold poly_bounds_width. cbn [fst snd poly_bound_bits]. split; lia.
  Qed.

  (** The frozen recurrence pays both finite endpoints, even for a raw duplicate form. *)
  Lemma poly_range_linear_size : forall P f,
    poly_bound_bits (fst (range_linear P f)) + poly_bound_bits (snd (range_linear P f)) <=
      4 * fmcost (n P + length (coef f)) (length P + 2)
        (n P + length (coef f)) (length P + 2) (nell (Reached P) + F.form_bits f + 1).
  Proof.
    intros P f. destruct (poly_range_linear_width P f) as [Hlower Hupper].
    pose proof (poly_range_initial_width P f) as Hinitial.
    pose proof (poly_range_width_work
      (length (poly_variables X.encode
        (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P)))
      (n P + length (coef f)) (length P + 2) (length P + 2)
      (RangeCore.poly_raw_bits (poly_range_input P f))
      (nell (Reached P) + F.form_bits f + 1)
      (poly_range_fuel P f) ltac:(nia)) as Hwork.
    lia.
  Qed.

  (** Even zero elimination fuel charges at least the initial arithmetic width. *)
  Lemma poly_fmcost_initial_bits : forall dim mlen fuel rows bits,
    bits + 1 <= fmcost dim mlen fuel rows bits.
  Proof.
    intros dim mlen fuel rows bits.
    pose proof (poly_width_after_fuel_mono 0 fuel bits ltac:(lia)) as Hwidth.
    cbn [poly_width_after] in Hwidth.
    pose proof (poly_fmcost_terminal_width fuel dim mlen rows bits) as Hwork. nia.
  Qed.

  (** Linearization's size contract transports both affine and wrapped endpoint bounds. *)
  Lemma poly_range_size_bounded : forall e s,
    (N.of_nat (poly_bound_bits (fst (range e s)) + poly_bound_bits (snd (range e s))) <=
      4 * N.of_nat (range_bits e s + 1))%N.
  Proof.
    intros e [|P]; [cbn [range fst snd poly_bound_bits]; lia|].
    unfold range. destruct (F.lin_of e) as [[f wr]|] eqn:Hlinear;
      [|cbn [fst snd poly_bound_bits]; lia].
    destruct (F.lin_of_size _ _ _ Hlinear) as [Hlength Hbits].
    destruct wr as [|lo hi].
    - pose proof (poly_range_linear_size P f) as Hsize.
      pose proof (poly_fmcost_mono
        (n P + length (coef f)) (n P + tsize e)
        (length P + 2) (length P + 2)
        (n P + length (coef f)) (n P + tsize e)
        (length P + 2) (length P + 2)
        (nell (Reached P) + F.form_bits f + 1)
        (nell (Reached P) + F.bits_e e + 1)
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(cbn [F.wrap_bits] in Hbits; lia)) as Hbudget.
      unfold range_bits, range_work. cbn [prows]. rewrite !Nat2N.inj_add. nia.
    - destruct (lo <=? hi)%Z; cbn [fst snd poly_bound_bits]; [|lia].
      cbn [F.wrap_bits] in Hbits.
      pose proof (poly_fmcost_initial_bits (n P + tsize e) (length P + 2)
        (n P + tsize e) (length P + 2) (nell (Reached P) + F.bits_e e + 1)) as Hbudget.
      unfold range_bits, range_work. cbn [prows]. rewrite !Nat2N.inj_add. nia.
  Qed.

  (** Wrapping distinct keys preserves their uniqueness. *)
  Lemma poly_some_nodup : forall xs : list X.t,
    NoDup xs -> NoDup (map (@Some X.t) xs).
  Proof.
    intros xs Hunique. induction Hunique as [|x xs Habsent Hunique IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH]. intro Hin.
      apply in_map_iff in Hin as [y [Hsame Hin]]. injection Hsame as Hsame.
      subst y. contradiction.
  Qed.

  Definition poly_range_fixed_support (P : list (lcons X.t)) (f : lin X.t) :
      list (option X.t) :=
    None :: map (@Some X.t) (vars_of P ++ poly_form_variables f).

  (** Original source variables and distinct form variables bound the tagged support. *)
  Lemma poly_range_fixed_support_length : forall P f,
    length (poly_range_fixed_support P f) <= n P + length (coef f) + 1.
  Proof.
    intros P f. unfold poly_range_fixed_support, n. cbn [length].
    rewrite length_map, length_app. pose proof (poly_form_variables_length f). lia.
  Qed.

  (** Normalizing a source row retains at most its original system's distinct coordinates. *)
  Lemma poly_range_normal_source_dimension : forall P r, In r P ->
    length (lhs (poly_normal_row X.encode r)) <= length (vars_of P).
  Proof.
    intros P r Hr. rewrite <- (length_map fst (lhs (poly_normal_row X.encode r))).
    apply NoDup_incl_length; [apply poly_normal_coef_nodup|].
    intros x Hx. apply poly_normal_row_keys in Hx.
    now apply poly_vars_of_contains with (r := r).
  Qed.

  (** The temporary result coordinate is distinct from every original form coordinate. *)
  Lemma poly_range_form_support_unique : forall f,
    NoDup (None :: map (@Some X.t) (poly_form_variables f)).
  Proof.
    intro f. constructor.
    - intro Hin. apply in_map_iff in Hin as [x [Hsame _]]. discriminate.
    - apply poly_some_nodup. apply poly_variables_nodup.
  Qed.

  (** Every distinct form coordinate occurs in its temporary range equation. *)
  Lemma poly_range_form_support : forall f,
    incl (None :: map (@Some X.t) (poly_form_variables f)) (map fst (lhs (range_row f))).
  Proof.
    intros f x [Hresult|Hin].
    - subst x. now left.
    - apply in_map_iff in Hin as [y [Hsame Hy]]. subst x.
      pose proof (poly_form_variables_support f y Hy) as Hsource.
      apply in_map_iff in Hsource as [p [Hkey Hp]]. subst y.
      cbn [range_row lhs map fst]. right. rewrite map_map.
      apply in_map_iff. exists p. split; [reflexivity|exact Hp].
  Qed.

  (** Only repeated occurrences enlarge the normalized query-equation coefficients. *)
  Lemma poly_range_row_duplicate_bits : forall f,
    RangeCert.row_bits (poly_normal_row tmp_encode (range_row f)) <=
      F.form_bits f + Nat.log2 (length (coef f) - length (poly_form_variables f) + 1) + 2.
  Proof.
    intro f.
    assert (Hsizes : Forall (fun p => Z.size_nat (snd p) <= F.form_bits f + 1)
      (lhs (range_row f))).
    { cbn [range_row lhs]. constructor; [cbn [snd Z.size_nat Pos.size_nat]; lia|].
      apply Forall_map, Forall_forall. intros p Hp. cbn [snd].
      rewrite poly_size_opp. pose proof (poly_form_entry_bits f p Hp). lia. }
    pose proof (RangeCore.poly_normal_coef_duplicate_bits (lhs (range_row f))
      (None :: map (@Some X.t) (poly_form_variables f)) (F.form_bits f + 1)
      (poly_range_form_support_unique f) (poly_range_form_support f) Hsizes) as Hnormalized.
    unfold RangeCert.row_bits. cbn [poly_normal_row rhs lhs range_row].
    apply poly_max_bound.
    - pose proof (poly_form_constant_bits f). lia.
    - eapply Forall_impl; [|exact Hnormalized]. intros p Hp.
      cbn [range_row lhs length] in Hp. rewrite !length_map in Hp.
      cbn [Nat.sub] in Hp. lia.
  Qed.

  (** Renaming an ordinary row adds one tag bit to each retained key. *)
  Lemma poly_range_rename_keys : forall r,
    RangeCert.row_key_bits (rename_row (@Some X.t) r) <= C.row_key_bits r + 1.
  Proof.
    intro r. unfold RangeCert.row_key_bits. cbn [rename_row lhs].
    apply poly_max_bound; [lia|]. apply Forall_map, Forall_forall. intros p Hp.
    change (S (Pos.size_nat (X.encode (fst p))) <= C.row_key_bits r + 1).
    pose proof (poly_row_key_member r p Hp). lia.
  Qed.

  (** The raw temporary query equation has one tag bit beyond its form key widths. *)
  Lemma poly_range_row_keys : forall f,
    RangeCert.row_key_bits (range_row f) <= F.form_bits f + 1.
  Proof.
    intro f. unfold RangeCert.row_key_bits. cbn [range_row lhs].
    apply poly_max_bound; [lia|]. constructor.
    - change (1 <= F.form_bits f + 1). lia.
    - apply Forall_map, Forall_forall. intros p Hp.
      change (S (Pos.size_nat (X.encode (fst p))) <= F.form_bits f + 1).
      pose proof (poly_form_entry_bits f p Hp). unfold X.bits in *. lia.
  Qed.

  (** Every source and query key fits the same fixed tagged-key allowance. *)
  Lemma poly_range_input_keys : forall P f,
    Forall (fun r => RangeCert.row_key_bits r <= nell (Reached P) + F.form_bits f + 1)
      (poly_range_input P f).
  Proof.
    intros P f. unfold poly_range_input. constructor.
    - pose proof (poly_range_row_keys f). lia.
    - apply Forall_map, Forall_map, Forall_forall. intros r Hr.
      eapply Nat.le_trans; [apply poly_range_rename_keys|].
      pose proof (poly_normal_row_key_bits r) as Hnormal.
      pose proof (poly_max_member _ C.row_key_bits 0 P r Hr) as Hkeys.
      unfold nell, ell. cbn [prows]. lia.
  Qed.

  (** Tagged normal source rows remain normal. *)
  Lemma poly_range_normal_rename_unique : forall r,
    NoDup (map fst (lhs (rename_row (@Some X.t) (poly_normal_row X.encode r)))).
  Proof.
    intro r. cbn [rename_row lhs]. rewrite map_map.
    change (NoDup (map (fun p => Some (fst p)) (lhs (poly_normal_row X.encode r)))).
    rewrite <- (map_map fst (@Some X.t) (lhs (poly_normal_row X.encode r))).
    apply poly_some_nodup. apply poly_normal_coef_nodup.
  Qed.

  (** Range initialization keeps its rows on a fixed source-and-form support. *)
  Lemma poly_range_initial_reduced : forall P f,
    Forall (RangeCore.poly_reduced_row (poly_range_fixed_support P f))
      (poly_initial tmp_encode (map (fun r => (r, false)) (poly_range_input P f))).
  Proof.
    intros P f. apply RangeCore.poly_initial_reduced.
    apply Forall_map, Forall_forall. intros r Hr p Hp. cbn [fst] in Hp.
    unfold poly_range_input in Hr. destruct Hr as [Htarget|Hsource].
    - subst r. cbn [range_row lhs] in Hp. destruct Hp as [Hresult|Hform].
      + subst p. unfold poly_range_fixed_support. now left.
      + apply in_map_iff in Hform as [q [Hsame Hq]]. subst p. cbn [fst].
        unfold poly_range_fixed_support. right. apply in_map. apply in_or_app. right.
        unfold poly_form_variables. apply poly_variables_contains with
          (r := LCons X.t (coef f) REq (cst f)) (a := snd q).
        * now left.
        * destruct q. exact Hq.
    - apply in_map_iff in Hsource as [normalized [Hsame Hnormalized]]. subst r.
      apply in_map_iff in Hnormalized as [source [Hsame Hsource]]. subst normalized.
      cbn [rename_row lhs] in Hp. apply in_map_iff in Hp as [q [Hsame Hq]]. subst p.
      cbn [fst]. unfold poly_range_fixed_support. right. apply in_map. apply in_or_app. left.
      apply poly_vars_of_contains with (r := source); [exact Hsource|].
      apply poly_normal_row_keys. now apply in_map.
  Qed.

  (** The initial arithmetic width uses duplicate surplus only in the query equation. *)
  Lemma poly_range_normalized_input_bits : forall P f,
    Forall (fun r => RangeCert.row_bits (poly_normal_row tmp_encode r) <=
      nell (Reached P) + F.form_bits f + 1 +
        Nat.log2 (length (coef f) - length (poly_form_variables f) + 1) + 1)
      (poly_range_input P f).
  Proof.
    intros P f. unfold poly_range_input. constructor.
    - pose proof (poly_range_row_duplicate_bits f). lia.
    - apply Forall_map, Forall_map, Forall_forall. intros r Hr.
      eapply Nat.le_trans; [apply RangeCore.poly_normal_row_bits;
        apply poly_range_normal_rename_unique|].
      rewrite poly_range_rename_bits.
      pose proof (proj2 (poly_raw_normal_widths P r Hr)) as Hwidth.
      pose proof (poly_raw_width P). lia.
  Qed.

  (** Query initialization combines fixed support, unit weights and duplicate-aware widths. *)
  Lemma poly_range_initial_envelopes : forall P f,
    Forall (RangeCore.poly_row_envelope (n P + length (coef f) + 1) (length P + 1)
      (nell (Reached P) + F.form_bits f + 1)
      (nell (Reached P) + F.form_bits f + 1 +
        Nat.log2 (length (coef f) - length (poly_form_variables f) + 1) + 1))
      (poly_initial tmp_encode (map (fun r => (r, false)) (poly_range_input P f))).
  Proof.
    intros P f. apply Forall_forall. intros r Hr.
    pose proof (proj1 (Forall_forall _ _) (poly_range_initial_reduced P f) r Hr) as Hreduced.
    pose proof (RangeCore.poly_reduced_dimension (poly_range_fixed_support P f) r Hreduced)
      as Hdim.
    pose proof (poly_range_fixed_support_length P f) as Hsupport_length.
    destruct (RangeCore.poly_initial_source (poly_range_input P f) r Hr) as [p [Hp Hrow]].
    pose proof (proj1 (Forall_forall _ _) (poly_range_input_keys P f) p Hp) as Hkeys.
    pose proof (proj1 (Forall_forall _ _) (poly_range_normalized_input_bits P f) p Hp)
      as Hbits.
    pose proof (poly_initial_units (option X.t) tmp_encode
      (map (fun r => (r, false)) (poly_range_input P f))) as Hunits.
    destruct (proj1 (Forall_forall _ _) Hunits r Hr) as [Hlength Hunit].
    rewrite length_map in Hlength. unfold poly_range_input in Hlength.
    cbn [length] in Hlength. rewrite !length_map in Hlength.
    unfold RangeCore.poly_row_envelope. split; [exact (proj1 Hreduced)|]. split.
    - eapply Nat.le_trans; [exact Hdim|exact Hsupport_length].
    - split.
      + rewrite Hrow. eapply Nat.le_trans;
          [apply RangeCore.poly_normal_row_key_bits|exact Hkeys].
      + split; [now rewrite Hrow|]. split.
        * exact (@eq_ind_r nat (S (length P)) (fun count => count <= length P + 1)
            ltac:(cbn beta; rewrite Nat.add_1_r; apply Nat.le_refl)
            (length (poly_multipliers r)) Hlength).
        * apply Forall_forall. intros z Hz.
          destruct (proj1 (Forall_forall _ _) Hunit z Hz) as [Hzero|Hone]; subst z;
            cbn [Z.size_nat Pos.size_nat]; lia.
  Qed.

  (** Canonical source rows fit the original normalization width and variable support. *)
  Lemma poly_range_sources_envelope : forall P f,
    Forall (poly_source_envelope (n P + length (coef f) + 1)
      (nell (Reached P) + F.form_bits f + 1)) (map (poly_normal_row X.encode) P).
  Proof.
    intros P f. apply Forall_map, Forall_forall. intros r Hr.
    unfold poly_source_envelope. split.
    - pose proof (poly_range_normal_source_dimension P r Hr). unfold n. lia.
    - destruct (poly_raw_normal_widths P r Hr) as [Hkeys Hbits].
      pose proof (poly_raw_width P). lia.
  Qed.

  (** The original rows and raw form determine the frozen range preprocessing budget. *)
  Definition poly_range_setup_budget (P : list (lcons X.t)) (f : lin X.t) : nat :=
    terms (Reached P) * (nell (Reached P) + 1) +
      fmcost (n P + length (coef f)) (length P + 2) (n P + length (coef f))
        (length P + 2) (nell (Reached P) + F.form_bits f + 1).

  (** These are exactly the native preprocessing clocks, with three fixed body/projection calls. *)
  Definition poly_range_setup_cost (P : list (lcons X.t)) (f : lin X.t) : N :=
    let rows := map (poly_normal_row X.encode) P in
    let input := poly_range_input P f in
    let vars := poly_variables X.encode (LCons X.t (coef f) REq (cst f) :: rows) in
    (3 + ListDef.T_map (poly_normal_row X.encode)
      (T_poly_normal_row X.encode X.T_encode) P + T_range_row f +
      ListDef.T_map (rename_row (@Some X.t))
        (T_rename_row (@Some X.t) (fun _ => 1%N)) rows +
      T_poly_variables X.encode X.T_encode (LCons X.t (coef f) REq (cst f) :: rows) +
      ListDef.T_map (@Some X.t) (fun _ => 1%N) vars +
      ListDef.T_map (fun r : lcons (option X.t) => (r, false)) (fun _ => 1%N) input +
      T_poly_initial tmp_encode T_tmp_encode
        (map (fun r : lcons (option X.t) => (r, false)) input))%N.

  (** Building the result equation only tags and negates the original coefficient occurrences. *)
  Lemma T_poly_range_row_bounded : forall f,
    (T_range_row f <= 8 * N.of_nat (length (coef f) + 1))%N.
  Proof.
    intro f. time_unfold T_range_row. time_simpl.
    lazymatch goal with
    | |- context [ListDef.T_map ?body ?clock (coef f)] =>
      assert (Hmap : (ListDef.T_map body clock (coef f) <=
        (4 + 1) * N.of_nat (length (coef f)) + 1)%N);
      [ apply (poly_T_map_members _ _ body clock 4 (coef f));
        intros [x z] Hin; cbn [fst snd];
        assert (Hopp : (Z.T_opp z <= 1)%N)
          by (destruct z; time_unfold Z.T_opp; time_simpl; lia);
        time_simpl; lia
      | lia ]
    end.
  Qed.

  (** Tagging an already normalized row has a constant cost per occurrence. *)
  Lemma T_poly_range_rename_some_bounded : forall r,
    (T_rename_row (@Some X.t) (fun _ => 1%N) r <=
      8 * N.of_nat (length (lhs r) + 1))%N.
  Proof.
    intro r. time_unfold T_rename_row. time_simpl.
    lazymatch goal with
    | |- context [ListDef.T_map ?body ?clock (lhs r)] =>
      assert (Hmap : (ListDef.T_map body clock (lhs r) <=
        (4 + 1) * N.of_nat (length (lhs r)) + 1)%N);
      [ apply (poly_T_map_members _ _ body clock 4 (lhs r));
        intros [x z] Hin; time_simpl; cbn [fst snd]; lia
      | lia ]
    end.
  Qed.

  (** Query construction and tagged normalized source rows fit one extra result coordinate. *)
  Lemma poly_range_input_dimensions : forall P f,
    Forall (fun r => length (lhs r) <= n P + length (coef f) + 1)
      (poly_range_input P f).
  Proof.
    intros P f. unfold poly_range_input. constructor.
    - cbn [range_row lhs length]. rewrite length_map. lia.
    - apply Forall_map, Forall_map, Forall_forall. intros r Hr.
      cbn [rename_row lhs]. rewrite length_map.
      pose proof (poly_range_normal_source_dimension P r Hr). unfold n. lia.
  Qed.

  (** Variable collection reads the raw form and the normalized source rows. *)
  Lemma poly_range_variable_envelopes : forall P f,
    Forall (fun r => length (lhs r) <= n P + length (coef f) /\
      C.row_key_bits r <= nell (Reached P) + F.form_bits f + 1)
      (LCons X.t (coef f) REq (cst f) :: map (poly_normal_row X.encode) P).
  Proof.
    intros P f. constructor.
    - split; [cbn [lhs]; lia|].
      unfold C.row_key_bits. cbn [lhs]. apply poly_max_bound; [lia|].
      apply Forall_forall. intros p Hp.
      pose proof (poly_form_entry_bits f p Hp). unfold X.bits in *. lia.
    - apply Forall_map, Forall_forall. intros r Hr. split.
      + pose proof (poly_range_normal_source_dimension P r Hr). unfold n. lia.
      + pose proof (poly_normal_row_key_bits r) as Hnormal.
        pose proof (poly_max_member _ C.row_key_bits 0 P r Hr) as Hkeys.
        unfold nell, ell. cbn [prows]. lia.
  Qed.

  (** Every setup count is polynomial in the frozen dimension allowance. *)
  Lemma poly_range_setup_polynomial : forall dim bits,
    (dim + 2)^2 * (bits + 1) <= (dim + 2)^4 * (bits + 1).
  Proof.
    intros dim bits. apply Nat.mul_le_mono_r. apply Nat.pow_le_mono_r; lia.
  Qed.

  Definition poly_range_setup_factor : N :=
    (9 * (poly_raw_row_factor + poly_variables_factor +
      RangeCore.poly_raw_initial_factor + 40))%N.

  (** Shared normalization is charged by occurrences; all later setup fits the recurrence. *)
  Lemma T_poly_range_setup_bounded : forall P f,
    (poly_range_setup_cost P f <=
      poly_range_setup_factor * N.of_nat (poly_range_setup_budget P f))%N.
  Proof.
    intros P f.
    set (dim := n P + length (coef f)).
    set (mlen := length P).
    set (bits := nell (Reached P) + F.form_bits f + 1).
    set (rows := map (poly_normal_row X.encode) P).
    set (input := poly_range_input P f).
    set (vrows := LCons X.t (coef f) REq (cst f) :: rows).
    set (vars := poly_variables X.encode vrows).
    set (polynomial := (dim + 2)^4 * (bits + 1)).
    set (prefix := terms (Reached P) * (nell (Reached P) + 1)).
    set (work := N.of_nat (prefix + polynomial)).
    assert (Hrows_length : length rows = mlen) by (unfold rows, mlen; apply length_map).
    assert (Hinput_length : length input = mlen + 1).
    { unfold input, poly_range_input, mlen. cbn [length]. rewrite !length_map. lia. }
    assert (Hvrows_length : length vrows = mlen + 1) by (unfold vrows; cbn [length]; lia).
    assert (Hcount : mlen <= dim) by (unfold mlen, dim, n; lia).
    assert (Hform : length (coef f) <= dim) by (unfold dim; lia).
    assert (Hbits : nell (Reached P) <= bits) by (unfold bits; lia).
    assert (Hsquare : (dim + 2)^2 * (bits + 1) <= polynomial)
      by (unfold polynomial; apply poly_range_setup_polynomial).
    assert (Hsmall : (dim + 1) * (bits + 1) <= polynomial).
    { eapply Nat.le_trans; [|exact Hsquare]. apply Nat.mul_le_mono_r. cbn [Nat.pow]. nia. }
    assert (Hdim_small : dim + 1 <= polynomial) by nia.
    assert (Hpositive_nat : 1 <= polynomial) by nia.
    assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
    assert (Hpolynomial_work : (N.of_nat polynomial <= work)%N) by (unfold work; lia).

    pose proof (T_poly_normal_map_occurrences P poly_raw_row_factor (nell (Reached P))
      (T_poly_raw_normal_row_global P)) as Hnormal.
    assert (Hnormal_charge :
      (terms (Reached P) + length P + 1) * (nell (Reached P) + 1) <= prefix + polynomial).
    { assert (Htail : (length P + 1) * (nell (Reached P) + 1) <= polynomial).
      { eapply Nat.le_trans; [|exact Hsmall]. apply Nat.mul_le_mono; [unfold mlen in Hcount; lia|lia]. }
      unfold prefix. nia. }
    assert (Hnormal_total : (ListDef.T_map (poly_normal_row X.encode)
      (T_poly_normal_row X.encode X.T_encode) P <= (poly_raw_row_factor + 2) * work)%N).
    { eapply N.le_trans; [exact Hnormal|]. rewrite <- N.mul_assoc.
      apply N.mul_le_mono_l. rewrite <- Nat2N.inj_mul. unfold work. clear -Hnormal_charge. lia. }

    pose proof (T_poly_range_row_bounded f) as Hquery.
    assert (Hquery_total : (T_range_row f <= 8 * work)%N).
    { eapply N.le_trans; [exact Hquery|]. apply N.mul_le_mono_l.
      unfold work. clear -Hform Hdim_small. lia. }

    pose proof (poly_T_map_members _ _ (rename_row (@Some X.t))
      (T_rename_row (@Some X.t) (fun _ => 1%N)) (8 * N.of_nat (dim + 1))%N rows)
      as Hrename.
    specialize (Hrename ltac:(intros r Hr; apply in_map_iff in Hr as [p [Hsame Hp]];
      subst r; eapply N.le_trans; [apply T_poly_range_rename_some_bounded|];
      apply N.mul_le_mono_l; pose proof (poly_range_normal_source_dimension P p Hp);
      unfold dim, n; lia)).
    rewrite Hrows_length in Hrename.
    pose proof (poly_clock_linear_count_bound 8 1 (N.of_nat mlen)
      (N.of_nat (mlen + 1)) (N.of_nat (dim + 1)) ltac:(lia) ltac:(lia)) as Hrename_linear.
    assert (Hrename_charge : (mlen + 1) * (dim + 1) <= polynomial).
    { eapply Nat.le_trans; [|exact Hsquare]. clear -Hcount.
      eapply Nat.le_trans with (m := (dim + 2)^2).
      - cbn [Nat.pow]. nia.
      - rewrite <- (Nat.mul_1_r ((dim + 2)^2)) at 1.
        apply Nat.mul_le_mono_l. lia. }
    assert (Hrename_total : (ListDef.T_map (rename_row (@Some X.t))
      (T_rename_row (@Some X.t) (fun _ => 1%N)) rows <= 10 * work)%N).
    { eapply N.le_trans; [exact Hrename|]. eapply N.le_trans; [exact Hrename_linear|].
      change (10 * N.of_nat (mlen + 1) * N.of_nat (dim + 1) <= 10 * work)%N.
      rewrite <- N.mul_assoc. apply N.mul_le_mono_l. rewrite <- Nat2N.inj_mul.
      unfold work. clear -Hrename_charge. lia. }

    pose proof (T_poly_variables_bounded vrows dim bits
      (poly_range_variable_envelopes P f)) as Hvariables.
    rewrite Hvrows_length in Hvariables.
    assert (Hvariables_charge : (mlen + 1 + 1) * (dim + 1) * (bits + 1) <= polynomial).
    { eapply Nat.le_trans; [|exact Hsquare]. apply Nat.mul_le_mono_r.
      clear -Hcount. cbn [Nat.pow]. nia. }
    assert (Hvariables_total : (T_poly_variables X.encode X.T_encode vrows <=
      poly_variables_factor * work)%N).
    { eapply N.le_trans; [exact Hvariables|].
      replace (poly_variables_factor * N.of_nat (mlen + 1 + 1) * N.of_nat (dim + 1) *
        N.of_nat (bits + 1))%N with
        (poly_variables_factor * N.of_nat ((mlen + 1 + 1) * (dim + 1) * (bits + 1)))%N
        by (rewrite !Nat2N.inj_mul; ring).
      apply N.mul_le_mono_l. unfold work. clear -Hvariables_charge. lia. }

    pose proof (poly_range_fuel P f) as Hfuel.
    change (length vars <= dim) in Hfuel.
    pose proof (poly_T_map_members _ _ (@Some X.t) (fun _ => 1%N) 1 vars
      (fun _ _ => N.le_refl 1%N)) as Hsome.
    assert (Hsome_total : (ListDef.T_map (@Some X.t) (fun _ => 1%N) vars <= 2 * work)%N).
    { eapply N.le_trans; [exact Hsome|].
      change (2 * N.of_nat (length vars) + 1 <= 2 * work)%N.
      unfold work. clear -Hfuel Hdim_small. lia. }
    pose proof (poly_T_map_members _ _ (fun r : lcons (option X.t) => (r, false))
      (fun _ => 1%N) 1 input (fun _ _ => N.le_refl 1%N)) as Hflags.
    rewrite Hinput_length in Hflags.
    assert (Hflags_total : (ListDef.T_map (fun r : lcons (option X.t) => (r, false))
      (fun _ => 1%N) input <= 4 * work)%N).
    { eapply N.le_trans; [exact Hflags|]. unfold work. clear -Hcount Hdim_small. lia. }

    assert (Hinitial_rows : Forall (fun p =>
      length (lhs (fst p)) <= dim + 1 /\ RangeCert.row_key_bits (fst p) <= bits /\
        RangeCert.row_bits (fst p) <= bits)
      (map (fun r : lcons (option X.t) => (r, false)) input)).
    { apply Forall_map, Forall_forall. intros r Hr. cbn [fst]. split.
      - exact (proj1 (Forall_forall _ _) (poly_range_input_dimensions P f) r Hr).
      - split.
        + exact (proj1 (Forall_forall _ _) (poly_range_input_keys P f) r Hr).
        + exact (proj1 (Forall_forall _ _) (poly_range_input_bits P f) r Hr). }
    pose proof (RangeCore.T_poly_initial_raw_bounded
      (map (fun r : lcons (option X.t) => (r, false)) input)
      (dim + 1) bits bits Hinitial_rows) as Hinitial.
    change (T_poly_initial tmp_encode T_tmp_encode
      (map (fun r : lcons (option X.t) => (r, false)) input) <=
      RangeCore.poly_raw_initial_factor *
        N.of_nat (length (map (fun r : lcons (option X.t) => (r, false)) input) + 1)^2 *
        N.of_nat (dim + 1 + 1) * N.of_nat (bits + bits + Nat.log2 (dim + 1) + 1))%N in Hinitial.
    rewrite length_map, Hinput_length in Hinitial.
    assert (Hinitial_charge : (mlen + 1 + 1)^2 * (dim + 1 + 1) *
      (bits + bits + Nat.log2 (dim + 1) + 1) <= polynomial).
    { pose proof (Nat.log2_lt_lin (dim + 1) ltac:(lia)) as Hlog.
      assert (Hwidth : bits + bits + Nat.log2 (dim + 1) + 1 <= (dim + 2) * (bits + 1))
        by (clear -Hlog; nia).
      clear -Hcount Hwidth.
      eapply Nat.le_trans with (m := (dim + 2)^2 * (dim + 2) * ((dim + 2) * (bits + 1))).
      - apply Nat.mul_le_mono; [apply Nat.mul_le_mono; [apply Nat.pow_le_mono_l; lia|lia]|exact Hwidth].
      - unfold polynomial. cbn [Nat.pow]. nia. }
    assert (Hinitial_total : (T_poly_initial tmp_encode T_tmp_encode
      (map (fun r : lcons (option X.t) => (r, false)) input) <=
      RangeCore.poly_raw_initial_factor * work)%N).
    { eapply N.le_trans; [exact Hinitial|].
      replace (RangeCore.poly_raw_initial_factor * N.of_nat (mlen + 1 + 1)^2 *
        N.of_nat (dim + 1 + 1) * N.of_nat (bits + bits + Nat.log2 (dim + 1) + 1))%N with
        (RangeCore.poly_raw_initial_factor * N.of_nat ((mlen + 1 + 1)^2 *
          (dim + 1 + 1) * (bits + bits + Nat.log2 (dim + 1) + 1)))%N
        by (rewrite !Nat2N.inj_mul, poly_nat_square, N.pow_2_r; ring).
      apply N.mul_le_mono_l. unfold work. clear -Hinitial_charge. lia. }

    assert (Hsum : (poly_range_setup_cost P f <=
      (poly_raw_row_factor + poly_variables_factor + RangeCore.poly_raw_initial_factor + 40) * work)%N).
    { unfold poly_range_setup_cost. fold rows input vrows vars.
      clear -Hnormal_total Hquery_total Hrename_total Hvariables_total Hsome_total Hflags_total
        Hinitial_total Hpositive. clearbody work. nia. }
    assert (Hbudget : (work <= 9 * N.of_nat (poly_range_setup_budget P f))%N).
    { pose proof (poly_range_budget_preprocessing dim mlen bits) as Hcharge.
      fold polynomial in Hcharge. unfold work, poly_range_setup_budget. fold dim mlen bits prefix.
      assert (Hnat : prefix + polynomial <=
        9 * (prefix + fmcost dim (mlen + 2) dim (mlen + 2) bits)) by lia.
      rewrite <- (Nat2N.inj_mul 9). clear -Hnat. lia. }
    eapply N.le_trans; [exact Hsum|]. unfold poly_range_setup_factor.
    replace (9 * (poly_raw_row_factor + poly_variables_factor +
      RangeCore.poly_raw_initial_factor + 40) *
        N.of_nat (poly_range_setup_budget P f))%N with
      ((poly_raw_row_factor + poly_variables_factor +
        RangeCore.poly_raw_initial_factor + 40) *
          (9 * N.of_nat (poly_range_setup_budget P f)))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** Range's native clock separates into preprocessing, elimination, and its terminal fold. *)
  Lemma T_poly_range_linear_setup : forall P f,
    let rows := map (poly_normal_row X.encode) P in
    let input := poly_range_input P f in
    let vars := poly_variables X.encode (LCons X.t (coef f) REq (cst f) :: rows) in
    let initial := poly_initial tmp_encode (map (fun r => (r, false)) input) in
    (T_range_linear P f <= poly_range_setup_cost P f +
      T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb (map (@Some X.t) vars) initial +
      List.T_fold_left (range_candidate rows f) (T_range_candidate rows f)
        (poly_run tmp_encode tmp_eqb (map (@Some X.t) vars) initial) (NegInf, PosInf))%N.
  Proof.
    intros P f rows input vars initial. time_unfold T_range_linear. time_simpl.
    change (fun x : X.t => X.T_encode x) with X.T_encode.
    change (fun x : option X.t => T_tmp_encode x) with T_tmp_encode.
    change (fun x y : option X.t => T_tmp_eqb x y) with T_tmp_eqb.
    unfold poly_range_setup_cost. fold rows input vars initial.
    change (range_row f :: map (rename_row (@Some X.t)) rows) with input.
    fold initial.
    change (fun r => T_poly_normal_row X.encode X.T_encode r)
      with (T_poly_normal_row X.encode X.T_encode).
    change (fun r => T_rename_row (@Some X.t) (fun _ => 1%N) r)
      with (T_rename_row (@Some X.t) (fun _ => 1%N)).
    change (fun bounds r => T_range_candidate rows f bounds r)
      with (T_range_candidate rows f).
    lia.
  Qed.

  Lemma T_poly_lower_bounded : forall z b,
    (T_poly_lower z b <= N.of_nat (Z.size_nat z) + 8)%N.
  Proof.
    intros z [|n|]; time_unfold T_poly_lower; time_simpl; try lia.
    pose proof (Z.T_max_le z n). lia.
  Qed.

  Lemma T_poly_upper_bounded : forall z b,
    (T_poly_upper z b <= N.of_nat (Z.size_nat z) + 8)%N.
  Proof.
    intros z [|n|]; time_unfold T_poly_upper; time_simpl; try lia.
    pose proof (Z.T_min_le z n). lia.
  Qed.

  Lemma T_poly_range_update_unit : forall a b is_eq bounds,
    a = 0%Z \/ a = 1%Z ->
    (T_range_update a b is_eq bounds <= 128 * N.of_nat (Z.size_nat b + 1))%N.
  Proof.
    intros a b is_eq [lo hi] [Hzero|Hone]; subst a.
    - time_unfold T_range_update. cbn [Z.ltb Z.compare]. time_simpl.
      change (Z.T_ltb 0 0) with 2%N. nia.
    - pose proof (T_poly_div_one b) as Hpositive_div.
      pose proof (T_poly_div_one (-b)) as Hnegative_div.
      rewrite poly_size_opp in Hnegative_div.
      pose proof (Z.T_opp_le b) as Hopp.
      pose proof (Z.T_opp_le (-b)) as Hopp2.
      pose proof (T_poly_lower_bounded b lo) as Hlower.
      pose proof (T_poly_upper_bounded b hi) as Hupper.
      time_unfold T_range_update. cbn [Z.ltb Z.compare].
      rewrite !Z.div_1_r, Z.opp_involutive.
      destruct is_eq; time_simpl; cbn [fst snd]; change (Z.T_ltb 0 1) with 2%N;
        rewrite Nat2N.inj_add; change (N.of_nat 1) with 1%N; nia.
  Qed.

  (** Division of two bounded row coefficients fits a quadratic width charge. *)
  Lemma T_poly_range_div_width : forall a b bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    (Z.T_div a b <= 512 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros a b bits Ha Hb.
    set (n := 2 * (bits + 1)).
    assert (Hsize : Z.size_nat a + Z.size_nat b + 1 <= n)
      by (unfold n; lia).
    assert (Hdiv : (Z.T_div a b <= 64 * N.of_nat (n^2))%N).
    { pose proof (Z.T_div_le a b) as Hdivide.
      apply time_of_nat_le in Hsize.
      rewrite !Nat2N.inj_pow, !Nat2N.inj_add in *. time_cbn_all.
      assert (Hproduct : ((N.of_nat (Z.size_nat a) + 1) *
        (N.of_nat (Z.size_nat a) + N.of_nat (Z.size_nat b) + 2) <=
        N.of_nat n * (2 * N.of_nat n))%N).
      { apply N.mul_le_mono; lia. }
      clear -Hdivide Hproduct Hsize. nia. }
    eapply N.le_trans; [exact Hdiv|].
    unfold n. rewrite !Nat2N.inj_pow, !Nat2N.inj_mul, !Nat2N.inj_add.
    change (N.of_nat 1) with 1%N. nia.
  Qed.

  (** Updating either endpoint charges only the incoming coefficient and right-hand side. *)
  Lemma T_poly_range_update_width : forall a b is_eq bounds bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    (T_range_update a b is_eq bounds <=
      4096 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros a b is_eq [lo hi] bits Ha Hb.
    pose proof (Z.T_ltb_le 0 a) as Hpositive_clock.
    pose proof (Z.T_ltb_le a 0) as Hnegative_clock.
    pose proof (Z.T_opp_le a) as Hoppa.
    pose proof (Z.T_opp_le b) as Hoppb.
    assert (Hopp_a : Z.size_nat (-a) <= bits)
      by (rewrite poly_size_opp; exact Ha).
    assert (Hopp_b : Z.size_nat (-b) <= bits)
      by (rewrite poly_size_opp; exact Hb).
    pose proof (T_poly_range_div_width b a bits Hb Ha) as Hdiv_pos.
    pose proof (T_poly_range_div_width (-b) a bits Hopp_b Ha) as Hdiv_pos_neg.
    pose proof (T_poly_range_div_width b (-a) bits Hb Hopp_a) as Hdiv_neg.
    pose proof (T_poly_range_div_width (-b) (-a) bits Hopp_b Hopp_a)
      as Hdiv_neg_neg.
    assert (Hwork : (1 <= N.of_nat ((bits + 1)^2))%N)
      by (rewrite Nat2N.inj_pow, Nat2N.inj_add; nia).
    set (work := N.of_nat ((bits + 1)^2)) in *.
    assert (Hbit_work : (N.of_nat (bits + 1) <= work)%N).
    { assert (Hnat : bits + 1 <= (bits + 1)^2) by (cbn [Nat.pow]; nia).
      unfold work. now apply time_of_nat_le. }
    assert (Hpositive_total : (Z.T_ltb 0 a <= 8 * work)%N).
    { change (Z.T_ltb 0 a <= 4)%N in Hpositive_clock.
      clear -Hpositive_clock Hwork. nia. }
    assert (Hnegative_total : (Z.T_ltb a 0 <= 8 * work)%N).
    { pose proof (poly_negative_test_clock bits a Ha) as Htest.
      clear -Htest Hbit_work Hwork. nia. }
    assert (Hoppa_total : (Z.T_opp a <= 8 * work)%N)
      by (clear -Hoppa Ha Hbit_work Hwork; lia).
    assert (Hoppb_total : (Z.T_opp b <= 8 * work)%N)
      by (clear -Hoppb Hb Hbit_work Hwork; lia).
    time_unfold T_range_update.
    destruct (0 <? a)%Z eqn:Hpositive.
    - apply Z.ltb_lt in Hpositive.
      pose proof (poly_div_size_le b a Hpositive) as Hquot_pos.
      pose proof (poly_div_size_le (-b) a Hpositive) as Hquot_neg.
      rewrite poly_size_opp in Hquot_neg.
      pose proof (T_poly_lower_bounded (-((-b) / a)) lo) as Hlower.
      pose proof (T_poly_upper_bounded (b / a) hi) as Hupper.
      pose proof (Z.T_opp_le ((-b) / a)) as Hopp_quot.
      rewrite poly_size_opp in Hlower.
      assert (Hlower_total : (T_poly_lower (-((-b) / a)) lo <= 16 * work)%N)
        by (clear -Hlower Hquot_neg Hb Hbit_work Hwork; lia).
      assert (Hupper_total : (T_poly_upper (b / a) hi <= 16 * work)%N)
        by (clear -Hupper Hquot_pos Hb Hbit_work Hwork; lia).
      assert (Hopp_quot_total : (Z.T_opp ((-b) / a) <= 8 * work)%N)
        by (clear -Hopp_quot Hquot_neg Hb Hbit_work Hwork; lia).
      destruct is_eq; time_simpl; cbn [fst snd]; fold work;
        clear -Hpositive_total Hoppb_total Hdiv_pos Hdiv_pos_neg
          Hlower_total Hupper_total Hopp_quot_total Hwork;
        clearbody work; nia.
    - destruct (a <? 0)%Z eqn:Hnegative.
      + apply Z.ltb_lt in Hnegative.
        assert (Hdivisor : (0 < -a)%Z) by lia.
        pose proof (poly_div_size_le b (-a) Hdivisor) as Hquot_pos.
        pose proof (poly_div_size_le (-b) (-a) Hdivisor) as Hquot_neg.
        rewrite poly_size_opp in Hquot_neg.
        pose proof (T_poly_lower_bounded (-(b / (-a))) lo) as Hlower.
        pose proof (T_poly_upper_bounded ((-b) / (-a)) hi) as Hupper.
        pose proof (Z.T_opp_le (b / (-a))) as Hopp_quot.
        rewrite poly_size_opp in Hlower.
        assert (Hlower_total : (T_poly_lower (-(b / (-a))) lo <= 16 * work)%N)
          by (clear -Hlower Hquot_pos Hb Hbit_work Hwork; lia).
        assert (Hupper_total : (T_poly_upper ((-b) / (-a)) hi <= 16 * work)%N)
          by (clear -Hupper Hquot_neg Hb Hbit_work Hwork; lia).
        assert (Hopp_quot_total : (Z.T_opp (b / (-a)) <= 8 * work)%N)
          by (clear -Hopp_quot Hquot_pos Hb Hbit_work Hwork; lia).
        destruct is_eq; time_simpl; cbn [fst snd]; fold work;
          clear -Hpositive_total Hnegative_total Hoppa_total Hoppb_total
            Hdiv_neg Hdiv_neg_neg Hlower_total Hupper_total Hopp_quot_total Hwork;
          clearbody work; nia.
      + time_simpl; fold work;
          clear -Hpositive_total Hnegative_total Hwork;
          clearbody work; nia.
  Qed.


  Definition poly_range_result_key (p : option X.t * Z) : bool :=
    match fst p with None => true | Some _ => false end.
  TimeFun poly_range_result_key.

  (** Testing the temporary result coordinate does not inspect an original key. *)
  Lemma T_poly_range_result_key_bounded : forall p,
    (T_poly_range_result_key p <= 2)%N.
  Proof.
    intros [x z]. time_unfold T_poly_range_result_key. time_simpl. lia.
  Qed.

  (** A checked range conclusion scales the form and subtracts its scaled constant. *)
  Lemma poly_range_conclusion_envelope : forall f a (r : lcons (option X.t)) dim bits,
    length (coef f) <= dim -> F.form_bits f <= bits ->
    Z.size_nat a <= bits -> Z.size_nat (rhs r) <= bits ->
    poly_source_envelope dim (4 * bits + 1)
      (LCons X.t (poly_scale_coef a (coef f)) (lrel r) (rhs r - a * cst f)%Z).
  Proof.
    intros f a r dim bits Hlength Hform Ha Hr.
    pose proof (poly_form_constant_bits f) as Hconstant.
    assert (Hkeys : C.row_key_bits
      (LCons X.t (poly_scale_coef a (coef f)) (lrel r) (rhs r - a * cst f)%Z) <= bits).
    { unfold C.row_key_bits. cbn [lhs]. apply poly_max_bound; [lia|].
      unfold poly_scale_coef. apply Forall_map, Forall_forall. intros p Hp.
      cbn [fst]. pose proof (poly_form_entry_bits f p Hp). unfold X.bits in *. lia. }
    assert (Harithmetic : C.row_bits
      (LCons X.t (poly_scale_coef a (coef f)) (lrel r) (rhs r - a * cst f)%Z) <=
        2 * bits + 1).
    { unfold C.row_bits. cbn [lhs rhs]. apply poly_max_bound.
      - replace (rhs r - a * cst f)%Z with (rhs r + -(a * cst f))%Z by ring.
        pose proof (poly_size_add (rhs r) (-(a * cst f))) as Hsum.
        rewrite poly_size_opp in Hsum.
        pose proof (poly_size_mul a (cst f)). lia.
      - unfold poly_scale_coef. apply Forall_map, Forall_forall. intros p Hp.
        cbn [snd]. pose proof (poly_form_entry_bits f p Hp).
        pose proof (poly_size_mul a (snd p)). lia. }
    unfold poly_source_envelope. split.
    - change (length (poly_scale_coef a (coef f)) <= dim).
      unfold poly_scale_coef. rewrite length_map. exact Hlength.
    - lia.
  Qed.

  (** Checking a bounded result row costs at most a quadratic final-width charge. *)
  Lemma T_poly_range_checker_width : forall P f a (r : lcons (option X.t)) ms dim mlen bits,
    Forall (poly_source_envelope dim bits) P -> length P <= mlen ->
    length ms <= mlen ->
    Forall (fun m => Z.size_nat m <= bits + 1) ms ->
    length (coef f) <= dim -> F.form_bits f <= bits ->
    Z.size_nat a <= bits -> Z.size_nat (rhs r) <= bits ->
    let conclusion := LCons X.t (poly_scale_coef a (coef f)) (lrel r)
      (rhs r - a * cst f)%Z in
    (C.T_check_entails P conclusion (Cert ms 1 false) <=
      C.c_lc * N.of_nat (128 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2))%N.
  Proof.
    intros P f a r ms dim mlen bits Hsource HP Hms Hweights Hform Hformbits
      Ha Hr conclusion.
    assert (Hconclusion : poly_source_envelope dim (4 * bits + 1) conclusion).
    { unfold conclusion. now apply poly_range_conclusion_envelope. }
    assert (Hsources : Forall (poly_source_envelope dim (4 * bits + 1))
      (conclusion :: P)).
    { constructor; [exact Hconclusion|].
      eapply Forall_impl; [|exact Hsource].
      intros row [Hdim Hbits]. split; lia. }
    assert (Hweights' : Forall (fun m => Z.size_nat m <= 4 * bits + 1 + 1) ms).
    { apply Forall_forall. intros m Hin.
      pose proof (proj1 (Forall_forall _ _) Hweights m Hin) as Hm.
      eapply Nat.le_trans; [exact Hm|]. lia. }
    pose proof (poly_checker_measure_envelope P conclusion ms 1 dim mlen
      (4 * bits + 1) Hsources HP Hms Hweights'
      ltac:(cbn [Z.size_nat Pos.size_nat]; lia)) as Hmeasure.
    assert (Hsquare : (4 * bits + 2)^2 <= 16 * (bits + 1)^2)
      by (cbn [Nat.pow]; nia).
    assert (Htotal : C.csize P ms + 2 *
      (C.lsize conclusion + C.cbits P ms + 1) <=
      128 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2).
    { assert (Hbase : 4 * bits + 1 + 1 <= 4 * bits + 2) by lia.
      assert (Hwidth : (4 * bits + 1 + 1)^2 <= 16 * (bits + 1)^2).
      { eapply Nat.le_trans; [apply Nat.pow_le_mono_l; exact Hbase|exact Hsquare]. }
      pose proof (Nat.mul_le_mono_l _ _
        (8 * (mlen + 1) * (dim + mlen + 1)) Hwidth) as Hscaled.
      assert (Heq : (8 * (mlen + 1) * (dim + mlen + 1)) *
        (16 * (bits + 1)^2) =
        128 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2) by ring.
      rewrite Heq in Hscaled.
      eapply Nat.le_trans; [exact Hmeasure|exact Hscaled]. }
    pose proof (C.T_check_entails_le P conclusion (Cert ms 1 false)) as Hcheck.
    change (C.T_check_entails P conclusion (Cert ms 1 false) <=
      C.c_lc * N.of_nat (C.csize P ms + 2 *
        (C.lsize conclusion + C.cbits P ms + 1)))%N in Hcheck.
    eapply N.le_trans; [exact Hcheck|].
    apply N.mul_le_mono_l. lia.
  Qed.

  (** One final-stage charge pays every linear and quadratic terminal component. *)
  Lemma poly_range_candidate_work : forall dim mlen keys bits len amount,
    1 <= mlen -> len <= dim -> amount <= bits ->
    let width := keys + bits + 1 in
    let work := (mlen + 1) * (dim + mlen + 1) * width * width in
    (len + 1) * (amount + 1) * (bits + 1) <= work /\
    (bits + 1) * (bits + 1) <= work /\
    (dim + 2) * width <= work /\
    (mlen + 1) * (dim + mlen + 1) * (bits + 1) * (bits + 1) <= work.
  Proof.
    intros dim mlen keys bits len amount Hmlen Hlen Hamount width work.
    unfold work, width. repeat split.
    - replace ((len + 1) * (amount + 1) * (bits + 1)) with
        (1 * (len + 1) * (amount + 1) * (bits + 1)) by ring.
      repeat apply Nat.mul_le_mono; lia.
    - replace ((bits + 1) * (bits + 1)) with
        (1 * 1 * (bits + 1) * (bits + 1)) by ring.
      repeat apply Nat.mul_le_mono; lia.
    - replace ((dim + 2) * (keys + bits + 1)) with
        (1 * (dim + 2) * (keys + bits + 1) * 1) by ring.
      repeat apply Nat.mul_le_mono; lia.
    - repeat apply Nat.mul_le_mono; lia.
  Qed.

  (** Candidate dispatch adds fixed projections to its scan, arithmetic, check, and update. *)
  Lemma T_poly_range_candidate_frame : forall P f bounds
      (r : poly_row (option X.t)) pre branch,
    let c := poly_constraint r in
    let a := poly_coefficient tmp_eqb None c in
    let conclusion := LCons X.t (poly_scale_coef a (coef f)) (lrel c)
      (rhs c - a * cst f)%Z in
    (T_poly_scale_coef a (coef f) + Z.T_mul a (cst f) +
      Z.T_sub (rhs c) (a * cst f) <= pre)%N ->
    (forall head ms, poly_multipliers r = head :: ms ->
      (C.T_check_entails P conclusion (Cert ms 1 false) +
        T_range_update a (rhs c)
          (match lrel c with REq => true | RLe => false end) bounds <= branch)%N) ->
    (T_range_candidate P f bounds r <=
      List.T_forallb poly_range_result_key T_poly_range_result_key (lhs c) +
      T_poly_coefficient tmp_eqb T_tmp_eqb None c + pre + branch + 32)%N.
  Proof.
    intros P f bounds r pre branch c a conclusion Hpre Hbranch.
    time_unfold T_range_candidate. time_simpl.
    change (fun p : option X.t * Z =>
      match fst p with Some _ => false | None => true end) with poly_range_result_key.
    change (fun u v : option X.t => T_tmp_eqb u v) with T_tmp_eqb.
    lazymatch goal with
    | |- context [List.T_forallb poly_range_result_key ?Tf ?xs] =>
        change Tf with T_poly_range_result_key
    end.
    unfold conclusion, a, c in *.
    destruct (forallb poly_range_result_key (lhs (poly_constraint r)));
      time_simpl; try nia.
    destruct (poly_multipliers r) as [|head ms] eqn:Hmult; time_simpl; try nia.
    pose proof (Hbranch head ms eq_refl) as Hsuffix.
    destruct (C.check_entails P
      (LCons X.t
        (poly_scale_coef (poly_coefficient tmp_eqb None (poly_constraint r)) (coef f))
        (lrel (poly_constraint r))
        (rhs (poly_constraint r) -
          poly_coefficient tmp_eqb None (poly_constraint r) * cst f)%Z)
      (Cert ms 1 false)); time_simpl; nia.
  Qed.

  Definition poly_range_candidate_factor : N :=
    (128 * C.c_lc + RangeCore.poly_coef_factor + 4200)%N.

  (** A bounded terminal row pays for its complete range candidate callback. *)
  Lemma T_poly_range_candidate_bounded : forall P f bounds r dim mlen keys bits,
    1 <= mlen -> length P <= mlen ->
    Forall (poly_source_envelope dim bits) P ->
    length (coef f) <= dim -> F.form_bits f <= bits ->
    RangeCore.poly_row_envelope dim (mlen + 1) keys bits r ->
    (T_range_candidate P f bounds r <= poly_range_candidate_factor *
      N.of_nat ((mlen + 1) * (dim + mlen + 1) *
        (keys + bits + 1) * (keys + bits + 1)))%N.
  Proof.
    intros P f bounds r dim mlen keys bits Hmlen HP Hsource Hform Hformbits
      (Hnormal & Hdim & Hkeys & Hbits & Hmultlen & Hmultbits).
    set (c := poly_constraint r).
    set (a := poly_coefficient tmp_eqb None c).
    set (width := keys + bits + 1).
    set (stage := (mlen + 1) * (dim + mlen + 1) * width * width).
    set (work := N.of_nat stage).
    assert (Ha : Z.size_nat a <= bits).
    { unfold a, c. eapply Nat.le_trans;
        [apply RangeCore.poly_row_coefficient_bits; exact Hnormal|exact Hbits]. }
    assert (Hr : Z.size_nat (rhs c) <= bits).
    { unfold c. eapply Nat.le_trans; [apply RangeCore.poly_row_rhs_bits|exact Hbits]. }
    pose proof (poly_range_candidate_work dim mlen keys bits
      (length (coef f)) (Z.size_nat a) Hmlen Hform Ha) as Hcharges.
    change ((length (coef f) + 1) * (Z.size_nat a + 1) * (bits + 1) <= stage /\
      (bits + 1) * (bits + 1) <= stage /\
      (dim + 2) * width <= stage /\
      (mlen + 1) * (dim + mlen + 1) * (bits + 1) * (bits + 1) <= stage)
      in Hcharges.
    destruct Hcharges as [Hscale_work [Hsquare_work [Hlinear_work Hcheck_work]]].
    assert (Hwork : (1 <= work)%N).
    { unfold work. assert (Hnat : 1 <= stage).
      { pose proof Hsquare_work. nia. }
      lia. }
    assert (Hrowdim : length (lhs c) <= dim) by exact Hdim.
    assert (Hentry : (N.of_nat (length (lhs c) + 1) <= work)%N).
    { unfold work. apply time_of_nat_le.
      eapply Nat.le_trans; [|exact Hlinear_work].
      assert (Hdim' : length (lhs c) + 1 <= dim + 2) by lia.
      assert (Hproduct : dim + 2 <= (dim + 2) * width).
      { eapply Nat.le_trans with (m := (dim + 2) * 1); [lia|].
        apply Nat.mul_le_mono_l. unfold width. lia. }
      lia. }
    pose proof (List.T_forallb_le poly_range_result_key T_poly_range_result_key 2
      (lhs c) T_poly_range_result_key_bounded) as Hscan.
    assert (Hscan_total : (List.T_forallb poly_range_result_key T_poly_range_result_key
      (lhs c) <= 5 * work)%N).
    { change (List.T_forallb poly_range_result_key T_poly_range_result_key (lhs c) <=
        4 * N.of_nat (length (lhs c)) + 1)%N in Hscan.
      clear -Hscan Hentry Hwork. lia. }
    pose proof (RangeCore.T_poly_coefficient_normal None c keys bits
      Hnormal Hkeys Hbits) as Hcoefficient.
    change (T_poly_coefficient tmp_eqb T_tmp_eqb None c <=
      RangeCore.poly_coef_factor * N.of_nat (length (lhs c) + 1) *
        N.of_nat width)%N in Hcoefficient.
    assert (Hcoefficient_total : (T_poly_coefficient tmp_eqb T_tmp_eqb None c <=
      RangeCore.poly_coef_factor * work)%N).
    { eapply N.le_trans; [exact Hcoefficient|].
      assert (Hnat : (length (lhs c) + 1) * width <= stage).
      { eapply Nat.le_trans; [|exact Hlinear_work].
        apply Nat.mul_le_mono_r. lia. }
      unfold work. rewrite <- N.mul_assoc.
      apply N.mul_le_mono_l. rewrite <- Nat2N.inj_mul.
      now apply time_of_nat_le. }
    assert (Hform_coefficients :
      Forall (fun p => Z.size_nat (snd p) <= bits) (coef f)).
    { apply Forall_forall. intros p Hp.
      pose proof (poly_form_entry_bits f p Hp). lia. }
    pose proof (T_poly_scale_coef_bounded a (coef f) bits Hform_coefficients) as Hscale.
    assert (Hscale_total : (T_poly_scale_coef a (coef f) <= 16 * work)%N).
    { eapply N.le_trans; [exact Hscale|].
      apply N.mul_le_mono_l. unfold work. now apply time_of_nat_le. }
    pose proof (poly_form_constant_bits f) as Hconstant.
    pose proof (poly_T_Z_mul_bilinear a (cst f)) as Hmultiply.
    pose proof (poly_size_mul a (cst f)) as Hproduct_width.
    assert (Hmultiply_total : (Z.T_mul a (cst f) <= 8 * work)%N).
    { eapply N.le_trans; [exact Hmultiply|].
      assert (Hnat : (Z.size_nat a + 1) * (Z.size_nat (cst f) + 1) <= stage).
      { eapply Nat.le_trans; [|exact Hsquare_work].
        apply Nat.mul_le_mono; lia. }
      rewrite <- N.mul_assoc.
      replace (N.of_nat (Z.size_nat a + 1) * N.of_nat (Z.size_nat (cst f) + 1))%N
        with (N.of_nat ((Z.size_nat a + 1) * (Z.size_nat (cst f) + 1)))
        by (rewrite Nat2N.inj_mul; reflexivity).
      apply N.mul_le_mono_l. unfold work. now apply time_of_nat_le. }
    pose proof (Z.T_sub_le (rhs c) (a * cst f)) as Hsubtract.
    assert (Hsubtract_total : (Z.T_sub (rhs c) (a * cst f) <= 12 * work)%N).
    { assert (Hsum : (N.of_nat (Z.size_nat (rhs c) + Z.size_nat (a * cst f)) <=
        3 * N.of_nat (bits + 1))%N)
        by (clear -Hr Hproduct_width Ha Hconstant Hformbits; lia).
      assert (Hbits_work : (N.of_nat (bits + 1) <= work)%N).
      { unfold work. apply time_of_nat_le.
        eapply Nat.le_trans; [|exact Hsquare_work]. nia. }
      clear -Hsubtract Hsum Hbits_work Hwork. nia. }
    pose proof (T_poly_range_update_width a (rhs c)
      (match lrel c with REq => true | RLe => false end) bounds bits Ha Hr) as Hupdate.
    assert (Hupdate_total : (T_range_update a (rhs c)
      (match lrel c with REq => true | RLe => false end) bounds <=
      4096 * work)%N).
    { eapply N.le_trans; [exact Hupdate|].
      apply N.mul_le_mono_l. unfold work. apply time_of_nat_le.
      replace ((bits + 1)^2) with ((bits + 1) * (bits + 1))
        by (cbn [Nat.pow]; ring).
      exact Hsquare_work. }
    assert (Hpre : (T_poly_scale_coef a (coef f) + Z.T_mul a (cst f) +
      Z.T_sub (rhs c) (a * cst f) <= 36 * work)%N)
      by (clear -Hscale_total Hmultiply_total Hsubtract_total; lia).
    assert (Hbranch : forall head ms, poly_multipliers r = head :: ms ->
      (C.T_check_entails P
        (LCons X.t (poly_scale_coef a (coef f)) (lrel c)
          (rhs c - a * cst f)%Z) (Cert ms 1 false) +
        T_range_update a (rhs c)
          (match lrel c with REq => true | RLe => false end) bounds <=
        (128 * C.c_lc + 4096) * work)%N).
    { intros head ms Hmult.
      assert (Hms : length ms <= mlen).
      { rewrite Hmult in Hmultlen. cbn [length] in Hmultlen. lia. }
      assert (Hweights : Forall (fun m => Z.size_nat m <= bits + 1) ms).
      { rewrite Hmult in Hmultbits. now inversion Hmultbits. }
      pose proof (T_poly_range_checker_width P f a c ms dim mlen bits
        Hsource HP Hms Hweights Hform Hformbits Ha Hr) as Hcheck.
      cbn zeta in Hcheck.
      assert (Hcheck_total : (C.T_check_entails P
        (LCons X.t (poly_scale_coef a (coef f)) (lrel c)
          (rhs c - a * cst f)%Z) (Cert ms 1 false) <=
        128 * C.c_lc * work)%N).
      { eapply N.le_trans; [exact Hcheck|].
        replace (128 * C.c_lc * work)%N with
          (C.c_lc * (128 * work))%N by ring.
        apply N.mul_le_mono_l.
        unfold work.
        replace (128 * N.of_nat stage)%N with (N.of_nat (128 * stage))
          by (rewrite Nat2N.inj_mul; reflexivity).
        apply time_of_nat_le.
        replace (128 * (mlen + 1) * (dim + mlen + 1) * (bits + 1)^2)
          with (128 * ((mlen + 1) * (dim + mlen + 1) * (bits + 1) * (bits + 1)))
          by (cbn [Nat.pow]; ring).
        now apply Nat.mul_le_mono_l. }
      clear -Hcheck_total Hupdate_total. nia. }
    pose proof (T_poly_range_candidate_frame P f bounds r
      (36 * work) ((128 * C.c_lc + 4096) * work) Hpre Hbranch) as Hframe.
    cbn zeta in Hframe. fold c in Hframe.
    eapply N.le_trans; [exact Hframe|].
    unfold poly_range_candidate_factor.
    fold c width stage work.
    change (List.T_forallb poly_range_result_key T_poly_range_result_key (lhs c) +
      T_poly_coefficient tmp_eqb T_tmp_eqb None c + 36 * work +
      (128 * C.c_lc + 4096) * work + 32 <=
      (128 * C.c_lc + RangeCore.poly_coef_factor + 4200) * work)%N.
    clear -Hscan_total Hcoefficient_total Hwork. clearbody work.
    nia.
  Qed.


  (** The terminal callback fits the row allowance used by the run-fold recurrence. *)
  Lemma T_poly_range_candidate_recurrence : forall P f bounds r dim keys bits,
    P <> [] -> Forall (poly_source_envelope dim bits) P ->
    length (coef f) <= dim -> F.form_bits f <= bits ->
    RangeCore.poly_row_envelope dim (length P + 1) keys bits r ->
    (T_range_candidate P f bounds r <= poly_range_candidate_factor *
      N.of_nat (length P + 2) * N.of_nat (dim + length P + 2) *
        N.of_nat (keys + bits + 1)^2)%N.
  Proof.
    intros P f bounds r dim keys bits Hnonempty Hsource Hform Hbits Hr.
    pose proof (T_poly_range_candidate_bounded P f bounds r dim (length P)
      keys bits ltac:(destruct P; [contradiction|cbn; lia])
      ltac:(lia) Hsource Hform Hbits Hr) as Hcandidate.
    set (width := keys + bits + 1).
    assert (Hstage : (length P + 1) * (dim + length P + 1) * width * width <=
      (length P + 2) * (dim + length P + 2) * width * width).
    { repeat apply Nat.mul_le_mono; lia. }
    eapply N.le_trans; [exact Hcandidate|].
    replace (poly_range_candidate_factor * N.of_nat (length P + 2) *
      N.of_nat (dim + length P + 2) * N.of_nat width^2)%N
      with (poly_range_candidate_factor * N.of_nat
        ((length P + 2) * (dim + length P + 2) * width * width))%N
      by (rewrite !Nat2N.inj_mul, N.pow_2_r; ring).
    apply N.mul_le_mono_l. now apply time_of_nat_le.
  Qed.

  Definition poly_range_empty_candidate_factor : N :=
    (32 * C.c_lc + RangeCore.poly_coef_factor + 256)%N.

  (** An empty-source result has a unit or zero result coefficient, so its check is linear in width. *)
  Lemma T_poly_range_empty_candidate : forall f bounds r dim keys bits,
    length (coef f) <= dim -> F.form_bits f <= bits ->
    RangeCore.poly_row_envelope dim 1 keys bits r ->
    (poly_coefficient tmp_eqb None (poly_constraint r) = 0%Z \/
      poly_coefficient tmp_eqb None (poly_constraint r) = 1%Z) ->
    (T_range_candidate [] f bounds r <= poly_range_empty_candidate_factor *
      N.of_nat (dim + 2) * N.of_nat (keys + bits + 1))%N.
  Proof.
    intros f bounds r dim keys bits Hform_length Hform
      (Hnormal & Hdim & Hkeys & Hbits & Hmlen & Hmult) Hunit.
    unfold RangeKey.t in *.
    set (c := poly_constraint r). fold c in Hnormal, Hdim, Hkeys, Hbits, Hunit.
    set (a := poly_coefficient tmp_eqb None c). fold a in Hunit.
    set (conclusion := LCons X.t (poly_scale_coef a (coef f)) (lrel c)
      (rhs c - a * cst f)%Z).
    assert (Ha : Z.size_nat a <= bits).
    { unfold a, c. eapply Nat.le_trans;
        [apply RangeCore.poly_row_coefficient_bits; exact Hnormal|exact Hbits]. }
    assert (Ha_unit : Z.size_nat a <= 1).
    { destruct Hunit as [Hunit|Hunit]; rewrite Hunit; cbn [Z.size_nat Pos.size_nat]; lia. }
    assert (Hrhs : Z.size_nat (rhs c) <= bits).
    { unfold c. eapply Nat.le_trans; [apply RangeCore.poly_row_rhs_bits|exact Hbits]. }
    assert (Hconclusion : poly_source_envelope dim (4 * bits + 1) conclusion).
    { unfold conclusion. apply poly_range_conclusion_envelope; assumption. }
    pose proof (poly_lsize_envelope conclusion dim (4 * bits + 1) Hconclusion) as Hlsize.
    pose proof (RangeCore.T_poly_coefficient_normal None c keys bits
      Hnormal Hkeys Hbits) as Hcoefficient.
    change (T_poly_coefficient tmp_eqb T_tmp_eqb None c <=
      RangeCore.poly_coef_factor * N.of_nat (length (lhs c) + 1) *
        N.of_nat (keys + bits + 1))%N in Hcoefficient.
    pose proof (List.T_forallb_le poly_range_result_key T_poly_range_result_key 2
      (lhs c) T_poly_range_result_key_bounded) as Hscan.
    assert (Hform_coefficients : Forall (fun p => Z.size_nat (snd p) <= bits) (coef f)).
    { apply Forall_forall. intros p Hp. pose proof (poly_form_entry_bits f p Hp). lia. }
    pose proof (T_poly_scale_coef_bounded a (coef f) bits Hform_coefficients) as Hscale.
    pose proof (poly_form_constant_bits f) as Hconstant.
    pose proof (poly_T_Z_mul_bilinear a (cst f)) as Hmultiply.
    pose proof (Z.T_sub_le (rhs c) (a * cst f)) as Hsubtract.
    pose proof (poly_size_mul a (cst f)) as Hproduct_width.
    pose proof (T_poly_range_update_unit a (rhs c)
      (match lrel c with REq => true | RLe => false end) bounds Hunit) as Hupdate.
    set (work := (N.of_nat (dim + 2) * N.of_nat (keys + bits + 1))%N).
    assert (Hwidth : (N.of_nat (bits + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_l (N.of_nat (bits + 1))) at 1.
      apply N.mul_le_mono; lia. }
    assert (Hpositive : (1 <= work)%N) by lia.
    assert (Hlength : (N.of_nat (length (lhs c) + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_r (N.of_nat (length (lhs c) + 1))) at 1.
      apply N.mul_le_mono; lia. }
    assert (Hcoefficient_total : (T_poly_coefficient tmp_eqb T_tmp_eqb None c <=
      RangeCore.poly_coef_factor * work)%N).
    { eapply N.le_trans; [exact Hcoefficient|]. unfold work. rewrite N.mul_assoc.
      apply N.mul_le_mono_r, N.mul_le_mono_l. lia. }
    assert (Hscan_total : (List.T_forallb poly_range_result_key T_poly_range_result_key
      (lhs c) <= 5 * work)%N).
    { clear -Hscan Hlength. clearbody work.
      change (List.T_forallb poly_range_result_key T_poly_range_result_key (lhs c) <=
        4 * N.of_nat (length (lhs c)) + 1)%N in Hscan.
      rewrite Nat2N.inj_add in Hlength. change (N.of_nat 1) with 1%N in Hlength. lia. }
    assert (Hscale_total : (T_poly_scale_coef a (coef f) <= 32 * work)%N).
    { eapply N.le_trans; [exact Hscale|].
      assert (Hproduct : (length (coef f) + 1) * (Z.size_nat a + 1) * (bits + 1) <=
        2 * ((dim + 2) * (keys + bits + 1))).
      { replace (2 * ((dim + 2) * (keys + bits + 1))) with
          ((dim + 2) * 2 * (keys + bits + 1)) by (clear -dim keys bits; nia).
        apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|lia]. }
      assert (Htransport : (N.of_nat ((length (coef f) + 1) *
        (Z.size_nat a + 1) * (bits + 1)) <= 2 * work)%N).
      { unfold work. rewrite <- Nat2N.inj_mul, <- (Nat2N.inj_mul 2). clear -Hproduct. lia. }
      clear -Htransport. nia. }
    assert (Hmultiply_total : (Z.T_mul a (cst f) <= 16 * work)%N).
    { assert (Hproduct : (N.of_nat (Z.size_nat a + 1) *
        N.of_nat (Z.size_nat (cst f) + 1) <= 2 * N.of_nat (bits + 1))%N).
      { apply N.mul_le_mono; lia. }
      clear -Hmultiply Hproduct Hwidth. nia. }
    assert (Hsubtract_total : (Z.T_sub (rhs c) (a * cst f) <= 12 * work)%N).
    { assert (Hsum : (N.of_nat (Z.size_nat (rhs c) + Z.size_nat (a * cst f)) <=
        3 * N.of_nat (bits + 1))%N).
      { clear -Hrhs Hproduct_width Ha_unit Hconstant Hform. lia. }
      clear -Hsubtract Hsum Hwidth Hpositive. nia. }
    assert (Hupdate_total : (T_range_update a (rhs c)
      (match lrel c with REq => true | RLe => false end) bounds <= 128 * work)%N).
    { eapply N.le_trans; [exact Hupdate|]. apply N.mul_le_mono_l.
      eapply N.le_trans; [|exact Hwidth]. lia. }
    assert (Hcheck_total : (C.T_check_entails [] conclusion (Cert [] 1 false) <=
      32 * C.c_lc * work)%N).
    { pose proof (C.T_check_entails_le [] conclusion (Cert [] 1 false)) as Hcheck.
      change (C.T_check_entails [] conclusion (Cert [] 1 false) <=
        C.c_lc * N.of_nat (2 * (C.lsize conclusion + 1 + 1)))%N in Hcheck.
      replace (C.lsize conclusion + 1 + 1) with (C.lsize conclusion + 2) in Hcheck by lia.
      assert (Hmeasure : 2 * (C.lsize conclusion + 2) <=
        32 * ((dim + 2) * (keys + bits + 1))) by (clear -Hlsize; nia).
      assert (Htransport : (N.of_nat (2 * (C.lsize conclusion + 2)) <= 32 * work)%N).
      { unfold work. rewrite <- Nat2N.inj_mul, <- (Nat2N.inj_mul 32).
        clear -Hmeasure. lia. }
      clear -Hcheck Htransport. nia. }
    time_unfold T_range_candidate. time_simpl.
    change (fun p : option X.t * Z =>
      match fst p with Some _ => false | None => true end) with poly_range_result_key.
    change (fun u v : option X.t => T_tmp_eqb u v) with T_tmp_eqb.
    lazymatch goal with
    | |- context [List.T_forallb poly_range_result_key ?Tf ?xs] =>
        change Tf with T_poly_range_result_key
    end.
    unfold conclusion, a, c in *.
    destruct (forallb poly_range_result_key (lhs (poly_constraint r))); time_simpl.
    - destruct (poly_multipliers r) as [|m ms] eqn:Hmultipliers; time_simpl.
      + replace (poly_range_empty_candidate_factor * N.of_nat (dim + 2) *
          N.of_nat (keys + bits + 1))%N with (poly_range_empty_candidate_factor * work)%N
          by (unfold work; ring).
        unfold poly_range_empty_candidate_factor.
        clear -Hcoefficient_total Hscan_total Hscale_total Hmultiply_total Hsubtract_total
          Hpositive. clearbody work. nia.
      + assert (Htail : ms = []).
        { destruct ms; [reflexivity|cbn [length] in Hmlen; lia]. }
        subst ms. destruct (C.check_entails []
          (LCons X.t (poly_scale_coef (poly_coefficient tmp_eqb None (poly_constraint r)) (coef f))
            (lrel (poly_constraint r))
            (rhs (poly_constraint r) - poly_coefficient tmp_eqb None (poly_constraint r) * cst f)%Z)
          (Cert [] 1 false)); time_simpl.
        all: replace (poly_range_empty_candidate_factor * N.of_nat (dim + 2) *
          N.of_nat (keys + bits + 1))%N with (poly_range_empty_candidate_factor * work)%N
          by (unfold work; ring).
        all: unfold poly_range_empty_candidate_factor;
          clear -Hcoefficient_total Hscan_total Hscale_total Hmultiply_total Hsubtract_total
            Hupdate_total Hcheck_total Hpositive; clearbody work; nia.
    - replace (poly_range_empty_candidate_factor * N.of_nat (dim + 2) *
        N.of_nat (keys + bits + 1))%N with (poly_range_empty_candidate_factor * work)%N
        by (unfold work; ring).
      unfold poly_range_empty_candidate_factor. clear -Hscan_total Hpositive.
      clearbody work. nia.
  Qed.

  (** Duplicate surplus consumes fuel before the actual elimination columns. *)
  Lemma poly_range_empty_budget_transport : forall dim fuel extra bits,
    extra + fuel <= dim ->
    fmcost (dim + 1) 1 fuel 1 (2 * bits + Nat.log2 (extra + 1) + 1) <=
      32 * fmcost dim 2 dim 2 bits.
  Proof.
    intros dim fuel extra bits Hfuel.
    assert (Hwidth : 2 * bits + Nat.log2 (extra + 1) + 1 <=
      poly_width_after extra (2 * (2 * bits + 1) + 1)).
    { eapply Nat.le_trans; [apply poly_duplicate_width_shift|].
      apply poly_width_after_mono. lia. }
    eapply Nat.le_trans with (m := fmcost (dim + 1) 1 fuel 1
      (poly_width_after extra (2 * (2 * bits + 1) + 1))).
    { apply poly_fmcost_params_mono; lia. }
    eapply Nat.le_trans; [apply poly_fmcost_shift_width|].
    eapply Nat.le_trans with (m := fmcost (dim + 1) 2 dim 2 (2 * (2 * bits + 1) + 1)).
    { apply poly_fmcost_mono; lia. }
    pose proof (poly_fmcost_dimension_successor dim dim 2 2 (2 * (2 * bits + 1) + 1))
      as Hdimension.
    pose proof (poly_fmcost_double_width dim dim 2 2 (2 * bits + 1)) as Hdouble.
    pose proof (poly_fmcost_double_width dim dim 2 2 bits) as Hbase.
    lia.
  Qed.

  Definition poly_range_empty_initial (f : lin X.t) : poly_row (option X.t) :=
    PolyRow (option X.t) (poly_normal_row tmp_encode (range_row f)) [1%Z] false.

  (** The normalized result equation has coefficient one at the fresh None coordinate. *)
  Lemma poly_range_empty_initial_none : forall f,
    poly_coefficient tmp_eqb None (poly_constraint (poly_range_empty_initial f)) = 1%Z.
  Proof.
    intro f. unfold poly_range_empty_initial. cbn [poly_constraint].
    change (poly_coefficient RangeKey.eqb None
      (poly_normal_row RangeKey.encode (range_row f)) = 1%Z).
    rewrite RangeCore.poly_coefficient_normal.
    change (poly_coefficient tmp_eqb None (range_row f) = 1%Z).
    unfold poly_coefficient, range_row. cbn [lhs].
    induction (coef f) as [|[x z] xs IH]; cbn [map fold_right fst snd tmp_eqb] in *;
      [reflexivity|exact IH].
  Qed.

  (** Empty-source elimination retains exactly one equality with result coefficient zero or one. *)
  Lemma poly_range_empty_output : forall f,
    exists r,
      poly_run tmp_encode tmp_eqb (map (@Some X.t) (poly_form_variables f))
        (poly_initial tmp_encode
          (map (fun r => (r, false)) (poly_range_input [] f))) = [r] /\
      (poly_coefficient tmp_eqb None (poly_constraint r) = 0%Z \/
        poly_coefficient tmp_eqb None (poly_constraint r) = 1%Z).
  Proof.
    intro f.
    assert (Hinitial : poly_initial tmp_encode
      (map (fun r => (r, false)) (poly_range_input [] f)) = [poly_range_empty_initial f])
      by reflexivity.
    rewrite Hinitial.
    destruct (RangeCore.poly_equality_singleton_observations
      (map (@Some X.t) (poly_form_variables f)) (poly_range_empty_initial f) None eq_refl)
      as [r [Hrun [Hcoefficient Hrhs]]].
    exists r. split; [exact Hrun|].
    destruct Hcoefficient as [Hsame|Hzero]; [right|now left].
    eapply eq_trans; [exact Hsame|apply poly_range_empty_initial_none].
  Qed.

  Definition poly_range_empty_factor : N :=
    (poly_range_setup_factor +
      32 * (RangeCore.poly_run_factor + poly_range_empty_candidate_factor + 4))%N.

  (** A singleton terminal check fits the existing terminal recurrence charge, without extra fuel. *)
  Lemma T_poly_range_empty_bounded : forall f,
    (T_range_linear [] f <= poly_range_empty_factor * N.of_nat
      (fmcost (length (coef f)) 2 (length (coef f)) 2
        (nell (Reached []) + F.form_bits f + 1)))%N.
  Proof.
    intro f.
    set (dim := length (coef f)).
    set (bits := nell (Reached []) + F.form_bits f + 1).
    set (extra := dim - length (poly_form_variables f)).
    set (fuel := length (poly_form_variables f)).
    set (initial_bits := bits + Nat.log2 (extra + 1) + 1).
    set (xs := map (@Some X.t) (poly_form_variables f)).
    set (support := poly_range_fixed_support [] f).
    set (initial := poly_initial tmp_encode
      (map (fun r => (r, false)) (poly_range_input [] f))).
    set (final_bits := poly_width_after fuel initial_bits).
    set (stage := N.of_nat (fmcost (dim + 1) 1 fuel 1 (bits + initial_bits))).
    set (work := N.of_nat (fmcost dim 2 dim 2 bits)).
    assert (Hfuel : extra + fuel <= dim).
    { unfold extra, fuel. pose proof (poly_form_variables_length f). unfold dim. lia. }
    assert (Hsupport : length support <= dim + 1).
    { pose proof (poly_range_fixed_support_length [] f) as Hsupport.
      change (length support <= dim + 1) in Hsupport. exact Hsupport. }
    assert (Hreduced : Forall (RangeCore.poly_reduced_row support) initial).
    { exact (poly_range_initial_reduced [] f). }
    assert (Henvelopes : Forall (RangeCore.poly_row_envelope
      (dim + 1) 1 bits initial_bits) initial).
    { exact (poly_range_initial_envelopes [] f). }
    assert (Hinitial_length : length initial = 1) by reflexivity.
    assert (Hxs_length : length xs = fuel) by (unfold xs, fuel; apply length_map).
    pose proof (RangeCore.T_poly_run_bounded xs support initial (dim + 1) 1 bits initial_bits
      Hsupport Hreduced Henvelopes) as Hrun.
    change (T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb xs initial <=
      RangeCore.poly_run_factor * N.of_nat
        (fmcost (dim + 1) 1 (length xs) (length initial) (bits + initial_bits)))%N in Hrun.
    rewrite Hxs_length, Hinitial_length in Hrun. fold stage in Hrun.
    pose proof (RangeCore.poly_run_envelopes xs support initial (dim + 1) 1 bits initial_bits
      Hsupport Hreduced Henvelopes) as Hrows.
    change (Forall (RangeCore.poly_row_envelope (dim + 1) 1 bits
      (poly_width_after (length xs) initial_bits)) (poly_run tmp_encode tmp_eqb xs initial)) in Hrows.
    rewrite Hxs_length in Hrows. fold final_bits in Hrows.
    destruct (poly_range_empty_output f) as [r [Houtput Hunit]].
    change (poly_run tmp_encode tmp_eqb xs initial = [r]) in Houtput.
    rewrite Houtput in Hrows.
    assert (Hr : RangeCore.poly_row_envelope (dim + 1) 1 bits final_bits r).
    { exact (proj1 (Forall_forall _ _) Hrows r (or_introl eq_refl)). }
    assert (Hform_final : F.form_bits f <= final_bits).
    { pose proof (poly_width_after_fuel_mono 0 fuel initial_bits ltac:(lia)) as Hgrowth.
      cbn [poly_width_after] in Hgrowth. clear -Hgrowth.
      unfold final_bits, initial_bits, bits in *. lia. }
    assert (Hterminal : (N.of_nat (dim + 1 + 2) *
      N.of_nat (bits + final_bits + 1) <= stage)%N).
    { pose proof (poly_fmcost_terminal_width fuel (dim + 1) 1 1 (bits + initial_bits))
        as Hterminal_nat.
      pose proof (poly_width_after_fixed_keys fuel bits initial_bits) as Hwidth.
      fold final_bits in Hwidth.
      assert (Hnat : (dim + 1 + 2) * (bits + final_bits + 1) <=
        fmcost (dim + 1) 1 fuel 1 (bits + initial_bits)).
      { eapply Nat.le_trans; [|exact Hterminal_nat]. apply Nat.mul_le_mono; lia. }
      unfold stage. rewrite <- Nat2N.inj_mul. clear -Hnat. lia. }
    assert (Hstage_positive : (1 <= stage)%N).
    { unfold stage. pose proof (poly_fmcost_positive (dim + 1) 1 fuel 1 (bits + initial_bits)). lia. }
    assert (Hcandidate : forall bounds,
      (T_range_candidate [] f bounds r <= poly_range_empty_candidate_factor * stage)%N).
    { intro bounds. eapply N.le_trans.
      - apply (T_poly_range_empty_candidate f bounds r (dim + 1) bits final_bits);
          [unfold dim; lia|exact Hform_final|exact Hr|exact Hunit].
      - rewrite <- N.mul_assoc. now apply N.mul_le_mono_l. }
    pose proof (poly_T_fold_left_members (poly_row (option X.t)) (bnd * bnd)
      (range_candidate [] f) (T_range_candidate [] f)
      (poly_range_empty_candidate_factor * stage)%N [r] (NegInf, PosInf)
      ltac:(intros acc q [Hq|Hq]; [subst q; apply Hcandidate|contradiction])) as Hfold.
    change (List.T_fold_left (range_candidate [] f) (T_range_candidate [] f)
      [r] (NegInf, PosInf) <= (poly_range_empty_candidate_factor * stage + 1) * 1 + 1)%N in Hfold.
    assert (Hfold_total : (List.T_fold_left (range_candidate [] f) (T_range_candidate [] f)
      [r] (NegInf, PosInf) <= (poly_range_empty_candidate_factor + 2) * stage)%N).
    { clear -Hfold Hstage_positive. clearbody stage. nia. }
    assert (Hstage : (stage <= 32 * work)%N).
    { pose proof (poly_range_empty_budget_transport dim fuel extra bits Hfuel) as Hstage_nat.
      unfold stage, initial_bits, work.
      replace (bits + (bits + Nat.log2 (extra + 1) + 1)) with
        (2 * bits + Nat.log2 (extra + 1) + 1) by lia.
      rewrite <- (Nat2N.inj_mul 32). clear -Hstage_nat. lia. }
    assert (Hrun_total : (T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb xs initial <=
      (32 * RangeCore.poly_run_factor) * work)%N).
    { eapply N.le_trans; [exact Hrun|].
      replace (32 * RangeCore.poly_run_factor * work)%N with
        (RangeCore.poly_run_factor * (32 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hfold_work : (List.T_fold_left (range_candidate [] f) (T_range_candidate [] f)
      [r] (NegInf, PosInf) <= (32 * (poly_range_empty_candidate_factor + 2)) * work)%N).
    { eapply N.le_trans; [exact Hfold_total|].
      replace (32 * (poly_range_empty_candidate_factor + 2) * work)%N with
        ((poly_range_empty_candidate_factor + 2) * (32 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (T_poly_range_setup_bounded [] f) as Hsetup.
    change (poly_range_setup_cost [] f <= poly_range_setup_factor * work)%N in Hsetup.
    pose proof (T_poly_range_linear_setup [] f) as Hnative.
    change (T_range_linear [] f <= poly_range_setup_cost [] f +
      T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb xs initial +
      List.T_fold_left (range_candidate [] f) (T_range_candidate [] f)
        (poly_run tmp_encode tmp_eqb xs initial) (NegInf, PosInf))%N in Hnative.
    rewrite Houtput in Hnative. fold dim bits work.
    unfold poly_range_empty_factor.
    clear -Hsetup Hnative Hrun_total Hfold_work. clearbody work. nia.
  Qed.

  (** Duplicate form entries consume stages before the nonempty range recurrence. *)
  Lemma poly_range_nonempty_budget_transport : forall dim mlen fuel extra bits,
    extra + fuel <= dim ->
    fmcost (dim + 1) mlen fuel mlen (2 * bits + Nat.log2 (extra + 1) + 1) <=
      32 * fmcost dim (mlen + 1) dim (mlen + 1) bits.
  Proof.
    intros dim mlen fuel extra bits Hfuel.
    assert (Hwidth : 2 * bits + Nat.log2 (extra + 1) + 1 <=
      poly_width_after extra (2 * (2 * bits + 1) + 1)).
    { eapply Nat.le_trans; [apply poly_duplicate_width_shift|].
      apply poly_width_after_mono. lia. }
    eapply Nat.le_trans with (m := fmcost (dim + 1) mlen fuel mlen
      (poly_width_after extra (2 * (2 * bits + 1) + 1))).
    { apply poly_fmcost_params_mono; lia. }
    eapply Nat.le_trans; [apply poly_fmcost_shift_width|].
    eapply Nat.le_trans with (m := fmcost (dim + 1) (mlen + 1) dim
      (mlen + 1) (2 * (2 * bits + 1) + 1)).
    { apply poly_fmcost_mono; lia. }
    pose proof (poly_fmcost_dimension_successor dim dim (mlen + 1)
      (mlen + 1) (2 * (2 * bits + 1) + 1)) as Hdimension.
    pose proof (poly_fmcost_double_width dim dim (mlen + 1)
      (mlen + 1) (2 * bits + 1)) as Hdouble.
    pose proof (poly_fmcost_double_width dim dim (mlen + 1)
      (mlen + 1) bits) as Hbase.
    lia.
  Qed.

  (** A nonempty source lets the terminal checker share the elimination recurrence. *)
  Lemma T_poly_range_nonempty_fold : forall P f,
    P <> [] ->
    let rows := map (poly_normal_row X.encode) P in
    let input := poly_range_input P f in
    let vars := poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: rows) in
    let xs := map (@Some X.t) vars in
    let initial := poly_initial tmp_encode
      (map (fun r => (r, false)) input) in
    let dim := n P + length (coef f) in
    let mlen := length P + 1 in
    let keys := nell (Reached P) + F.form_bits f + 1 in
    let initial_bits := keys +
      Nat.log2 (length (coef f) - length (poly_form_variables f) + 1) + 1 in
    (T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb xs initial +
      List.T_fold_left (range_candidate rows f) (T_range_candidate rows f)
        (poly_run tmp_encode tmp_eqb xs initial) (NegInf, PosInf) <=
      (RangeCore.poly_step_factor + poly_range_candidate_factor + 16) *
        N.of_nat (fmcost (dim + 1) mlen (S (length xs)) mlen
          (keys + initial_bits)))%N.
  Proof.
    intros P f Hnonempty rows input vars xs initial dim mlen keys initial_bits.
    assert (Hsupport : length (poly_range_fixed_support P f) <= dim + 1).
    { exact (poly_range_fixed_support_length P f). }
    assert (Hinitial_length : length initial = mlen).
    { unfold initial, input, mlen, poly_range_input.
      rewrite poly_initial_length, length_map. cbn [length]. rewrite !length_map. lia. }
    assert (Hreduced : Forall
      (RangeCore.poly_reduced_row (poly_range_fixed_support P f)) initial).
    { exact (poly_range_initial_reduced P f). }
    assert (Henvelopes : Forall (RangeCore.poly_row_envelope
      (dim + 1) mlen keys initial_bits) initial).
    { exact (poly_range_initial_envelopes P f). }
    assert (Hsources : Forall (poly_source_envelope (dim + 1) keys) rows).
    { exact (poly_range_sources_envelope P f). }
    eapply RangeCore.T_poly_run_fold_bounded with
      (vars := poly_range_fixed_support P f) (count := mlen).
    - exact Hsupport.
    - lia.
    - rewrite <- Hinitial_length. apply Nat.le_refl.
    - exact Hreduced.
    - exact Henvelopes.
    - intros wider bounds r Hwide Hr.
      assert (Hsource_wide : Forall (poly_source_envelope (dim + 1) wider) rows).
      { eapply Forall_impl; [|exact Hsources].
        intros q Hq. eapply poly_source_envelope_mono; [exact Hq|lia|].
        unfold initial_bits, keys in *. lia. }
      assert (Hrow : RangeCore.poly_row_envelope
        (dim + 1) (length rows + 1) keys wider r).
      { replace (length rows + 1) with mlen
          by (unfold rows, mlen; rewrite length_map; lia).
        exact Hr. }
      assert (Hformbits : F.form_bits f <= wider)
        by (unfold initial_bits, keys in *; lia).
      pose proof (T_poly_range_candidate_recurrence rows f bounds r
        (dim + 1) keys wider
        ltac:(unfold rows; destruct P; [contradiction|discriminate])
        Hsource_wide ltac:(lia) Hformbits Hrow) as Hcandidate.
      replace (length rows + 2) with (mlen + 1) in Hcandidate
        by (unfold rows, mlen; rewrite length_map; lia).
      replace (dim + 1 + length rows + 2) with (dim + 1 + mlen + 1)
        in Hcandidate by (unfold rows, mlen; rewrite length_map; lia).
      exact Hcandidate.
  Qed.

  Definition poly_range_nonempty_factor : N :=
    (poly_range_setup_factor +
      32 * (RangeCore.poly_step_factor + poly_range_candidate_factor + 16))%N.

  (** The nonempty affine branch fits the original preprocessing budget. *)
  Lemma T_poly_range_nonempty_bounded : forall P f,
    P <> [] ->
    (T_range_linear P f <= poly_range_nonempty_factor *
      N.of_nat (poly_range_setup_budget P f))%N.
  Proof.
    intros P f Hnonempty.
    set (rows := map (poly_normal_row X.encode) P).
    set (input := poly_range_input P f).
    set (vars := poly_variables X.encode
      (LCons X.t (coef f) REq (cst f) :: rows)).
    set (xs := map (@Some X.t) vars).
    set (initial := poly_initial tmp_encode (map (fun r => (r, false)) input)).
    set (dim := n P + length (coef f)).
    set (mlen := length P + 1).
    set (keys := nell (Reached P) + F.form_bits f + 1).
    set (extra := length (coef f) - length (poly_form_variables f)).
    set (initial_bits := keys + Nat.log2 (extra + 1) + 1).
    set (stage := N.of_nat
      (fmcost (dim + 1) mlen (S (length xs)) mlen (keys + initial_bits))).
    set (work := N.of_nat (poly_range_setup_budget P f)).
    assert (Hfuel : extra + S (length xs) <= dim).
    { pose proof (poly_range_duplicate_fuel P f (length (coef f)) Hnonempty
        ltac:(lia)) as Hbound.
      unfold extra, xs, vars, rows, dim. rewrite length_map. exact Hbound. }
    pose proof (poly_range_nonempty_budget_transport dim mlen
      (S (length xs)) extra keys Hfuel) as Htransport.
    assert (Hstage : (stage <= 32 * work)%N).
    { unfold stage, initial_bits.
      replace (keys + (keys + Nat.log2 (extra + 1) + 1)) with
        (2 * keys + Nat.log2 (extra + 1) + 1) by lia.
      eapply N.le_trans with (m := N.of_nat
        (32 * fmcost dim (mlen + 1) dim (mlen + 1) keys)).
      - now apply time_of_nat_le.
      - rewrite Nat2N.inj_mul. unfold work, poly_range_setup_budget, dim, mlen, keys.
        replace (length P + 1 + 1) with (length P + 2) by lia.
        rewrite Nat2N.inj_add. apply N.mul_le_mono_l. apply N.le_add_l. }
    pose proof (T_poly_range_nonempty_fold P f Hnonempty) as Hfold.
    cbn zeta in Hfold.
    change (T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb xs initial +
      List.T_fold_left (range_candidate rows f) (T_range_candidate rows f)
        (poly_run tmp_encode tmp_eqb xs initial) (NegInf, PosInf) <=
      (RangeCore.poly_step_factor + poly_range_candidate_factor + 16) * stage)%N
      in Hfold.
    assert (Hfold_total : (T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb
      xs initial + List.T_fold_left (range_candidate rows f)
        (T_range_candidate rows f) (poly_run tmp_encode tmp_eqb xs initial)
        (NegInf, PosInf) <=
      (32 * (RangeCore.poly_step_factor + poly_range_candidate_factor + 16)) * work)%N).
    { eapply N.le_trans; [exact Hfold|].
      replace (32 * (RangeCore.poly_step_factor + poly_range_candidate_factor + 16) *
        work)%N with
        ((RangeCore.poly_step_factor + poly_range_candidate_factor + 16) *
          (32 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (T_poly_range_setup_bounded P f) as Hsetup.
    change (poly_range_setup_cost P f <= poly_range_setup_factor * work)%N in Hsetup.
    pose proof (T_poly_range_linear_setup P f) as Hnative.
    cbn zeta in Hnative.
    change (T_range_linear P f <= poly_range_setup_cost P f +
      T_poly_run tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb xs initial +
      List.T_fold_left (range_candidate rows f) (T_range_candidate rows f)
        (poly_run tmp_encode tmp_eqb xs initial) (NegInf, PosInf))%N in Hnative.
    unfold poly_range_nonempty_factor. fold work.
    clear -Hnative Hsetup Hfold_total. clearbody work. nia.
  Qed.

  Definition poly_range_affine_factor : N :=
    (poly_range_empty_factor + poly_range_nonempty_factor)%N.

  Lemma T_poly_range_affine_bounded : forall P f,
    (T_range_linear P f <= poly_range_affine_factor *
      N.of_nat (poly_range_setup_budget P f))%N.
  Proof.
    intros [|r P] f.
    - eapply N.le_trans; [apply T_poly_range_empty_bounded|].
      unfold poly_range_affine_factor. now apply N.mul_le_mono_r, N.le_add_r.
    - eapply N.le_trans; [apply T_poly_range_nonempty_bounded; discriminate|].
      unfold poly_range_affine_factor. now apply N.mul_le_mono_r, N.le_add_l.
  Qed.

  (** A completed affine-case bound lifts through linearization and the wrapped/unknown branches. *)
  Lemma T_poly_range_from_linear : forall factor,
    (forall P f, (T_range_linear P f <=
      factor * N.of_nat (poly_range_setup_budget P f))%N) ->
    forall e s, (T_range e s <= (factor + 32) * N.of_nat (range_work e s + 1))%N.
  Proof.
    intros factor Hlinear e [|P].
    - time_unfold T_range. time_simpl. nia.
    - set (work := N.of_nat (range_work e (Reached P) + 1)).
      assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
      assert (Hlin_clock : (F.T_lin_of e <= work)%N).
      { unfold work, range_work. rewrite !Nat2N.inj_add, N2Nat.id. lia. }
      pose proof (poly_fmcost_initial_bits (n P + tsize e) (length P + 2)
        (n P + tsize e) (length P + 2) (nell (Reached P) + F.bits_e e + 1)) as Hbase.
      assert (Hwidth : (N.of_nat (F.bits_e e + 1) <= work)%N).
      { unfold work, range_work. cbn [prows]. lia. }
      time_unfold T_range.
      destruct (F.lin_of e) as [[f wr]|] eqn:Hlin; time_simpl.
      + destruct (F.lin_of_size _ _ _ Hlin) as [Hlength Hbits].
        destruct wr as [|lo hi]; time_simpl.
        * pose proof (Hlinear P f) as Haffine.
          assert (Hbudget : poly_range_setup_budget P f <= range_work e (Reached P) + 1).
          { pose proof (poly_fmcost_mono
              (n P + length (coef f)) (n P + tsize e)
              (length P + 2) (length P + 2)
              (n P + length (coef f)) (n P + tsize e)
              (length P + 2) (length P + 2)
              (nell (Reached P) + F.form_bits f + 1)
              (nell (Reached P) + F.bits_e e + 1)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(cbn [F.wrap_bits] in Hbits; lia)) as Hfm.
            unfold poly_range_setup_budget, range_work. cbn [prows]. lia. }
          assert (Haffine_total : (T_range_linear P f <= factor * work)%N).
          { eapply N.le_trans; [exact Haffine|]. apply N.mul_le_mono_l.
            unfold work. clear -Hbudget. lia. }
          fold work. clear -Haffine_total Hlin_clock Hpositive. clearbody work. nia.
        * pose proof (Z.T_leb_le lo hi) as Hcompare.
          cbn [F.wrap_bits] in Hbits.
          assert (Hcompare_total : (Z.T_leb lo hi <= 16 * work)%N).
          { clear -Hcompare Hbits Hwidth Hpositive. clearbody work. nia. }
          destruct (lo <=? hi)%Z; time_simpl; fold work;
            clear -Hcompare_total Hlin_clock Hpositive; clearbody work; nia.
      + fold work. clear -Hlin_clock Hpositive. clearbody work. nia.
  Qed.

  Definition c_lat : N := (poly_lattice_factor + 1)%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. lia.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply T_poly_leb_lattice|].
    apply N.mul_le_mono; [unfold c_lat; lia|].
    pose proof (poly_lattice_lat_size a b). lia.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply T_poly_join_lattice|].
    apply N.mul_le_mono; [unfold c_lat; lia|].
    pose proof (poly_lattice_lat_size a b). lia.
  Qed.
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_lat * N.of_nat (size s + 1))%N.
  Proof.
    intro s. eapply N.le_trans; [apply T_poly_is_bot_size|].
    apply N.mul_le_mono_r. unfold c_lat. lia.
  Qed.
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b. eapply N.le_trans; [apply T_poly_widen_lattice|].
    apply N.mul_le_mono; [unfold c_lat; lia|].
    pose proof (poly_lattice_lat_size a b). lia.
  Qed.
(** * Temporary-key invariants for affine assignment

    Renaming moves the old assigned variable to None and reserves Some x for
    its new value. Source-only elimination therefore cannot create that key.
    Builds on: the checked temporary-key core and normalized coefficient support. *)


  Lemma poly_assign_nodup_map : forall A B (f : A -> B),
    (forall x y, f x = f y -> x = y) ->
    forall xs, NoDup xs -> NoDup (map f xs).
  Proof.
    intros A B f Hinjective xs Hunique.
    induction Hunique as [|x xs Hnot Hunique IH]; cbn [map]; [constructor|].
    constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin as [y [Heq Hin]].
    apply Hinjective in Heq. subst y. contradiction.
  Qed.

  (** Both branches of old-variable renaming are injective. *)
  Lemma poly_assign_rename_injective : forall x y z,
    rename_old x y = rename_old x z -> y = z.
  Proof.
    intros x y z Heq. unfold rename_old in Heq.
    destruct (X.eqb_spec y x) as [Hy|Hy];
      destruct (X.eqb_spec z x) as [Hz|Hz]; try discriminate; congruence.
  Qed.

  (** The renamed source excludes the new assigned coordinate. *)
  Lemma poly_assign_rename_fresh : forall x y, rename_old x y <> Some x.
  Proof.
    intros x y Hsame. unfold rename_old in Hsame.
    destruct (X.eqb_spec y x) as [Heq|Hneq]; [discriminate|].
    injection Hsame as Hsame. contradiction.
  Qed.

  (** The temporary tag adds at most one key bit. *)
  Lemma poly_assign_rename_key_bits : forall x y,
    RangeKey.bits (rename_old x y) <= X.bits y + 1.
  Proof.
    intros x y. unfold rename_old. destruct (X.eqb y x);
      unfold RangeKey.bits, RangeKey.encode; cbn [Pos.size_nat]; unfold X.bits; lia.
  Qed.

  (** Source renaming preserves coefficient widths and raw occurrence counts. *)
  Lemma poly_assign_rename_row_bits : forall x r,
    RangeCert.row_bits (rename_row (rename_old x) r) = C.row_bits r /\
    length (lhs (rename_row (rename_old x) r)) = length (lhs r).
  Proof.
    intros x r. split.
    - unfold RangeCert.row_bits, C.row_bits. cbn [rename_row lhs rhs].
      rewrite map_map. reflexivity.
    - cbn [rename_row lhs]. apply length_map.
  Qed.

  Lemma poly_assign_rename_row_keys : forall x r,
    RangeCert.row_key_bits (rename_row (rename_old x) r) <= C.row_key_bits r + 1.
  Proof.
    intros x r. unfold RangeCert.row_key_bits. cbn [rename_row lhs].
    rewrite map_map. apply poly_max_bound; [lia|].
    apply Forall_forall. intros [y a] Hin. cbn [fst].
    pose proof (poly_assign_rename_key_bits x y) as Hkey.
    pose proof (poly_row_key_member r (y, a) Hin) as Hrow.
    unfold RangeKey.bits, X.bits in *. cbn [fst] in Hrow. lia.
  Qed.

  Lemma poly_assign_rename_row_absent : forall x r,
    ~ In (Some x) (map fst (lhs (rename_row (rename_old x) r))).
  Proof.
    intros x r Hin. cbn [rename_row lhs] in Hin. rewrite map_map in Hin.
    apply in_map_iff in Hin as [p [Heq _]]. cbn [fst] in Heq.
    exact (poly_assign_rename_fresh x (fst p) Heq).
  Qed.

  (** The affine equation is already unique once its form has been prepared. *)
  Lemma poly_assign_prepared_row_nodup : forall x f,
    NoDup (map fst (lhs (assignment_row x (poly_prepare_form X.encode f)))).
  Proof.
    intros x f. cbn [assignment_row lhs map fst]. rewrite map_map. constructor.
    - intro Hin. apply in_map_iff in Hin as [p [Heq _]]. cbn [fst] in Heq.
      exact (poly_assign_rename_fresh x (fst p) Heq).
    - pose proof (poly_assign_nodup_map X.t (option X.t) (rename_old x)
        (poly_assign_rename_injective x)
        (map fst (coef (poly_prepare_form X.encode f)))
        (poly_prepare_form_nodup X.t X.encode f)) as Hkeys.
      rewrite map_map in Hkeys. exact Hkeys.
  Qed.

  Lemma poly_assign_form_row_bounds : forall f,
    C.row_key_bits (LCons X.t (coef f) REq (cst f)) <= F.form_bits f /\
    C.row_bits (LCons X.t (coef f) REq (cst f)) <= F.form_bits f.
  Proof.
    intro f. split.
    - unfold C.row_key_bits. cbn [lhs]. apply poly_max_bound; [lia|].
      apply Forall_forall. intros p Hp. pose proof (poly_form_entry_bits f p Hp).
      unfold X.bits in *. lia.
    - unfold C.row_bits. cbn [lhs rhs]. apply poly_max_bound.
      + apply poly_form_constant_bits.
      + apply Forall_forall. intros p Hp. pose proof (poly_form_entry_bits f p Hp). lia.
  Qed.

  (** The signed preparer returns exactly the existing canonical form row. *)
  Lemma poly_assign_prepared_form_row : forall f,
    LCons X.t (coef (poly_prepare_form X.encode f)) REq (cst (poly_prepare_form X.encode f)) =
      poly_normal_row X.encode (LCons X.t (coef f) REq (cst f)).
  Proof.
    intro f. cbn [poly_prepare_form coef cst poly_normal_row lhs lrel rhs].
    now rewrite poly_signed_normal_eq.
  Qed.

  (** Prepared affine coefficients grow only by the logarithm of raw multiplicity. *)
  Lemma poly_assign_prepared_form_bounds : forall f,
    C.row_key_bits (LCons X.t (coef (poly_prepare_form X.encode f)) REq
      (cst (poly_prepare_form X.encode f))) <= F.form_bits f /\
    C.row_bits (LCons X.t (coef (poly_prepare_form X.encode f)) REq
      (cst (poly_prepare_form X.encode f))) <=
      F.form_bits f + Nat.log2 (length (coef f)) + 1.
  Proof.
    intro f. rewrite poly_assign_prepared_form_row.
    destruct (poly_assign_form_row_bounds f) as [Hkeys Hbits]. split.
    - eapply Nat.le_trans; [apply poly_normal_row_key_bits|exact Hkeys].
    - pose proof (poly_normal_row_log_bits (LCons X.t (coef f) REq (cst f))) as Hnormal.
      cbn [lhs] in Hnormal. lia.
  Qed.

  (** The new-variable unit coefficient adds at most one bit to the form row width. *)
  Lemma poly_assign_row_bits : forall x f,
    RangeCert.row_bits (assignment_row x f) <=
      C.row_bits (LCons X.t (coef f) REq (cst f)) + 1.
  Proof.
    intros x f. unfold RangeCert.row_bits. cbn [assignment_row lhs rhs].
    apply poly_max_bound.
    - pose proof (poly_row_rhs_bits (LCons X.t (coef f) REq (cst f))). cbn [rhs] in *. lia.
    - constructor.
      + cbn [snd Z.size_nat Pos.size_nat]. lia.
      + apply Forall_map, Forall_forall. intros p Hp. cbn [snd]. rewrite poly_size_opp.
        pose proof (poly_row_entry_bits (LCons X.t (coef f) REq (cst f)) p Hp). lia.
  Qed.

  Lemma poly_assign_row_keys : forall x f,
    RangeCert.row_key_bits (assignment_row x f) <=
      X.bits x + C.row_key_bits (LCons X.t (coef f) REq (cst f)) + 1.
  Proof.
    intros x f. unfold RangeCert.row_key_bits. cbn [assignment_row lhs].
    apply poly_max_bound; [lia|]. constructor.
    - cbn [fst RangeKey.encode Pos.size_nat]. unfold X.bits. lia.
    - apply Forall_map, Forall_forall. intros p Hp. cbn [fst].
      pose proof (poly_assign_rename_key_bits x (fst p)) as Hrename.
      pose proof (poly_row_key_member (LCons X.t (coef f) REq (cst f)) p Hp) as Hkey.
      unfold RangeKey.bits, X.bits in *. lia.
  Qed.

  Definition poly_assign_sources (x : X.t) (P : list (lcons X.t)) :=
    map (rename_row (rename_old x)) P.

  Definition poly_assign_input (x : X.t) (f : lin X.t)
      (P : list (lcons X.t)) :=
    assignment_row x f :: poly_assign_sources x P.

  Lemma poly_assign_input_rows : forall x f P,
    map (fun r => (r, false)) (poly_assign_input x f P) =
      (assignment_row x f, false) ::
        map (fun r => (rename_row (rename_old x) r, false)) P.
  Proof.
    intros x f P. unfold poly_assign_input, poly_assign_sources.
    cbn [map]. now rewrite map_map.
  Qed.

  Lemma poly_assign_sources_length : forall x P,
    length (poly_assign_sources x P) = length P.
  Proof. intros. unfold poly_assign_sources. apply length_map. Qed.

  Lemma poly_assign_sources_terms : forall x P,
    RangeCore.terms (Reached (poly_assign_sources x P)) = terms (Reached P).
  Proof.
    intros x P. unfold RangeCore.terms, terms, poly_assign_sources.
    cbn [RangeCore.prows prows]. rewrite map_map.
    apply f_equal. apply map_ext. intro r.
    exact (proj2 (poly_assign_rename_row_bits x r)).
  Qed.

  Lemma poly_assign_sources_row_bits : forall x P,
    fold_right Nat.max 0 (map RangeCert.row_bits (poly_assign_sources x P)) =
      fold_right Nat.max 0 (map C.row_bits P).
  Proof.
    intros x P. unfold poly_assign_sources. rewrite map_map.
    apply f_equal. apply map_ext. intro r.
    exact (proj1 (poly_assign_rename_row_bits x r)).
  Qed.

  (** Renamed raw sources retain their original merged arithmetic width. *)
  Lemma poly_assign_sources_raw_bits : forall x P,
    RangeCore.poly_raw_bits (poly_assign_sources x P) = poly_raw_bits P.
  Proof.
    intros x P. unfold RangeCore.poly_raw_bits, poly_raw_bits.
    now rewrite poly_assign_sources_row_bits, poly_assign_sources_terms.
  Qed.

  (** Their key-width maximum changes by at most the temporary tag bit. *)
  Lemma poly_assign_sources_raw_keys : forall x P,
    RangeCore.poly_raw_keys (poly_assign_sources x P) <= poly_raw_keys P + 1.
  Proof.
    intros x P. unfold RangeCore.poly_raw_keys, poly_assign_sources.
    rewrite map_map. apply poly_max_bound; [lia|].
    apply Forall_forall. intros r Hr.
    pose proof (poly_assign_rename_row_keys x r) as Hrename.
    pose proof (poly_max_member _ C.row_key_bits 0 P r Hr) as Hsource.
    unfold poly_raw_keys. lia.
  Qed.

  (** Normalizing one renamed source cannot introduce the new assigned variable. *)
  Lemma poly_assign_normal_source_absent : forall x r,
    ~ In (Some x) (map fst (lhs
      (poly_normal_row tmp_encode (rename_row (rename_old x) r)))).
  Proof.
    intros x r Hin. apply in_map_iff in Hin as [p [Heq Hin]].
    cbn [poly_normal_row lhs] in Hin.
    pose proof (poly_normal_coef_keys _ tmp_encode _ p Hin) as Hsource.
    rewrite Heq in Hsource. exact (poly_assign_rename_row_absent x r Hsource).
  Qed.

  (** Successful untagging changes only the temporary key constructor. *)
  Lemma poly_assign_untag_entries : forall xs ys, untag xs = Some ys ->
    map (fun p => (Some (fst p), snd p)) ys = xs.
  Proof.
    intro xs. induction xs as [|[[x|] a] xs IH]; intros ys Hresult;
      cbn [untag] in Hresult; try discriminate.
    - injection Hresult as Hsame. subst ys. reflexivity.
    - destruct (untag xs) as [zs|] eqn:Htail; [|discriminate].
      injection Hresult as Hsame. subst ys. cbn [map fst snd].
      f_equal. now apply IH.
  Qed.

  (** Untagging preserves counts and coefficient widths and removes the key tag bit. *)
  Lemma poly_assign_untag_envelope : forall r xs,
    untag (lhs r) = Some xs ->
    length xs = length (lhs r) /\
    C.row_bits (LCons X.t xs (lrel r) (rhs r)) = RangeCert.row_bits r /\
    C.row_key_bits (LCons X.t xs (lrel r) (rhs r)) <= RangeCert.row_key_bits r.
  Proof.
    intros r xs Hresult.
    pose proof (poly_assign_untag_entries (lhs r) xs Hresult) as Hentries.
    split.
    - apply f_equal with (f := @length (option X.t * Z)) in Hentries.
      now rewrite length_map in Hentries.
    - split.
      + unfold C.row_bits, RangeCert.row_bits, RangeKey.t. cbn [lhs rhs].
        rewrite <- Hentries, map_map. reflexivity.
      + unfold C.row_key_bits. cbn [lhs]. apply poly_max_bound; [lia|].
        apply Forall_forall. intros [y a] Hin. cbn [fst].
        assert (Hmapped : In (Some y, a) (lhs r)).
        { rewrite <- Hentries. apply in_map_iff. exists (y, a). split; [reflexivity|exact Hin]. }
        pose proof (RangeCore.poly_row_key_member r (Some y, a) Hmapped) as Hkey.
        cbn [fst RangeKey.encode Pos.size_nat] in Hkey. lia.
  Qed.

  (** A missing temporary new-value key remains absent after successful untagging. *)
  Lemma poly_assign_untag_absent : forall x r xs,
    untag (lhs r) = Some xs ->
    ~ In (Some x) (map fst (lhs r)) -> ~ In x (map fst xs).
  Proof.
    intros x r xs Hresult Habsent Hin. apply Habsent.
    rewrite (untag_keys _ _ Hresult). now apply in_map.
  Qed.

  (** Untagging stops early or visits each temporary coefficient once. *)
  Lemma T_poly_assign_untag : forall xs,
    (T_untag xs <= 2 * N.of_nat (length xs + 1))%N.
  Proof.
    intro xs. induction xs as [|[[x|] a] xs IH].
    - time_unfold T_untag. time_simpl. lia.
    - time_unfold T_untag. destruct (untag xs); time_simpl; cbn [length]; nia.
    - time_unfold T_untag. time_simpl. cbn [length]. nia.
  Qed.

  (** Candidate dispatch adds fixed projections to untagging, substitution, and checking. *)
  Lemma T_poly_assign_candidate_frame : forall P x f r budget,
    (forall xs head ms,
      untag (lhs (poly_constraint r)) = Some xs ->
      poly_multipliers r = head :: ms ->
      let c := LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r)) in
      (T_subst x f c + C.T_check_entails P (subst x f c) (Cert ms 1 false) <= budget)%N) ->
    (T_assigned_candidate P x f r <=
      T_untag (lhs (poly_constraint r)) + budget + 16)%N.
  Proof.
    intros P x f r budget Hcost. time_unfold T_assigned_candidate.
    destruct (untag (lhs (poly_constraint r))) as [xs|] eqn:Huntag;
      destruct (poly_multipliers r) as [|head ms] eqn:Hmults; time_simpl; try lia.
    pose proof (Hcost xs head ms eq_refl eq_refl) as Hbranch.
    cbn zeta in Hbranch. lia.
  Qed.

  (** Renaming compares the stored key and otherwise only chooses its option tag. *)
  Lemma T_poly_assign_rename_old : forall x y,
    (T_rename_old x y <= (X.c_key + 2) * N.of_nat (X.bits y + 1))%N.
  Proof.
    intros x y. pose proof (X.T_eqb_le y x) as Htest.
    time_unfold T_rename_old. destruct (X.eqb y x); time_simpl; nia.
  Qed.

  Lemma T_poly_assign_rename_row : forall x r,
    (T_rename_row (rename_old x) (T_rename_old x) r <=
      (X.c_key + 16) * N.of_nat (length (lhs r) + 1) *
        N.of_nat (C.row_key_bits r + 1))%N.
  Proof.
    intros x r. time_unfold T_rename_row.
    lazymatch goal with
    | |- context [ListDef.T_map ?body ?clock (lhs r)] =>
      assert (Hmap : (ListDef.T_map body clock (lhs r) <=
        ((X.c_key + 8) * N.of_nat (C.row_key_bits r + 1) + 1) *
          N.of_nat (length (lhs r)) + 1)%N);
      [ apply poly_T_map_members; intros [y a] Hin;
        pose proof (T_poly_assign_rename_old x y) as Hrename;
        pose proof (poly_row_key_member r (y, a) Hin) as Hkey;
        cbn [fst] in Hkey; unfold X.bits in Hrename; time_simpl; cbn [fst snd]; nia
      | revert Hmap; time_simpl; intro Hmap; nia ]
    end.
  Qed.

  (** Building the prepared equation inspects key widths but not coefficient magnitudes. *)
  Lemma T_poly_assign_row : forall x f keys,
    Forall (fun p => X.bits (fst p) <= keys) (coef f) ->
    (T_assignment_row x f <= (X.c_key + 24) *
      N.of_nat (length (coef f) + 1) * N.of_nat (keys + 1))%N.
  Proof.
    intros x f keys Hkeys. time_unfold T_assignment_row.
    lazymatch goal with
    | |- context [ListDef.T_map ?body ?clock (coef f)] =>
      assert (Hmap : (ListDef.T_map body clock (coef f) <=
        ((X.c_key + 8) * N.of_nat (keys + 1) + 1) *
          N.of_nat (length (coef f)) + 1)%N);
      [ apply poly_T_map_members; intros [y a] Hin;
        pose proof (T_poly_assign_rename_old x y) as Hrename;
        pose proof (proj1 (Forall_forall _ _) Hkeys (y, a) Hin) as Hkey;
        cbn [fst] in Hkey;
        assert (Hopp : (Z.T_opp a <= 1)%N)
          by (destruct a; time_unfold Z.T_opp; time_simpl; lia);
        time_simpl; cbn [fst snd]; nia
      | revert Hmap; time_simpl; intro Hmap; nia ]
    end.
  Qed.

  (** Mapping the renamed raw sources fits their total occurrence and maximum key budgets. *)
  Lemma T_poly_assign_sources : forall P x keys,
    Forall (fun r => C.row_key_bits r <= keys) P ->
    (ListDef.T_map (fun r => (rename_row (rename_old x) r, false))
      (fun r => (1 + T_rename_row (rename_old x) (T_rename_old x) r)%N) P <=
      (X.c_key + 20) * N.of_nat (length P + 1) *
        (N.of_nat (terms (Reached P) + 1) * N.of_nat (keys + 1)))%N.
  Proof.
    intros P x keys Hkeys.
    set (work := (N.of_nat (terms (Reached P) + 1) * N.of_nat (keys + 1))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. change (1 * 1 <= N.of_nat (terms (Reached P) + 1) * N.of_nat (keys + 1))%N.
      apply N.mul_le_mono; lia. }
    assert (Hcallback : forall r, In r P ->
      ((1 + T_rename_row (rename_old x) (T_rename_old x) r) <=
        (X.c_key + 16) * work + 1)%N).
    { intros r Hr. pose proof (T_poly_assign_rename_row x r) as Hrow.
      pose proof (poly_raw_row_terms P r Hr) as Hlength.
      pose proof (proj1 (Forall_forall _ _) Hkeys r Hr) as Hkey.
      cbn beta in Hkey.
      assert (Hrow_total : (T_rename_row (rename_old x) (T_rename_old x) r <=
        (X.c_key + 16) * work)%N).
      { eapply N.le_trans; [exact Hrow|]. rewrite <- N.mul_assoc.
        apply N.mul_le_mono_l. unfold work. apply N.mul_le_mono; lia. }
      lia. }
    pose proof (poly_T_map_members _ _ (fun r => (rename_row (rename_old x) r, false))
      (fun r => (1 + T_rename_row (rename_old x) (T_rename_old x) r)%N)
      ((X.c_key + 16) * work + 1)%N P Hcallback) as Hmap.
    pose proof (poly_clock_linear_count_bound (X.c_key + 16) 2
      (N.of_nat (length P)) (N.of_nat (length P + 1)) work ltac:(lia) Hpositive) as Hcount.
    fold work. eapply N.le_trans; [exact Hmap|].
    replace ((X.c_key + 16) * work + 1 + 1)%N with
      ((X.c_key + 16) * work + 2)%N by ring.
    eapply N.le_trans; [exact Hcount|]. apply N.mul_le_mono_r, N.mul_le_mono_r. lia.
  Qed.

  (** Source-only assignment rows reserve the first certificate position for the affine row. *)
  Definition poly_assign_tail (x : X.t) (P : list (lcons X.t)) :=
    map (@poly_pad_row (option X.t))
      (poly_initial tmp_encode
        (map (fun r => (rename_row (rename_old x) r, false)) P)).

  Definition poly_assign_head (x : X.t) (f : lin X.t)
      (P : list (lcons X.t)) : poly_row (option X.t) :=
    PolyRow (option X.t) (poly_normal_row tmp_encode (assignment_row x f))
      (1%Z :: map (fun _ => 0%Z) P) false.

  Lemma poly_assign_row_nodup_normal : forall x f,
    NoDup (map fst (coef f)) -> NoDup (map fst (lhs (assignment_row x f))).
  Proof.
    intros x f Hform. cbn [assignment_row lhs map fst]. rewrite map_map.
    constructor.
    - intro Hin. apply in_map_iff in Hin as [p [Heq _]]. cbn [fst] in Heq.
      exact (poly_assign_rename_fresh x (fst p) Heq).
    - pose proof (poly_assign_nodup_map X.t (option X.t) (rename_old x)
        (poly_assign_rename_injective x) (map fst (coef f)) Hform) as Hkeys.
      rewrite map_map in Hkeys. exact Hkeys.
  Qed.

  (** A normal prepared equation fits one head row at its own form width. *)
  Lemma poly_assign_head_envelope : forall x f P,
    NoDup (map fst (coef f)) ->
    RangeCore.poly_row_envelope (length (coef f) + 1) (length P + 1)
      (X.bits x + F.form_bits f + 1) (F.form_bits f + 1)
      (poly_assign_head x f P).
  Proof.
    intros x f P Hform.
    pose proof (poly_assign_form_row_bounds f) as [Hformkeys Hformbits].
    pose proof (poly_assign_row_nodup_normal x f Hform) as Hrowunique.
    unfold RangeCore.poly_row_envelope, poly_assign_head.
    cbn [poly_constraint poly_multipliers length].
    split; [apply poly_normal_coef_nodup|]. split.
    - eapply Nat.le_trans; [apply RangeCore.poly_normal_length|].
      cbn [assignment_row lhs length]. rewrite length_map. lia.
    - split.
      + eapply Nat.le_trans; [apply RangeCore.poly_normal_row_key_bits|].
        pose proof (poly_assign_row_keys x f). lia.
      + split.
        * eapply Nat.le_trans; [apply RangeCore.poly_normal_row_bits; exact Hrowunique|].
          pose proof (poly_assign_row_bits x f). lia.
        * split.
          -- rewrite length_map. lia.
          -- constructor; [cbn [Z.size_nat Pos.size_nat]; lia|].
             apply Forall_map, Forall_forall. intros p _. cbn [Z.size_nat]. lia.
  Qed.

  Lemma poly_assign_row_envelope_mono : forall r dim dim' mlen keys keys' bits bits',
    RangeCore.poly_row_envelope dim mlen keys bits r ->
    dim <= dim' -> keys <= keys' -> bits <= bits' ->
    RangeCore.poly_row_envelope dim' mlen keys' bits' r.
  Proof.
    intros r dim dim' mlen keys keys' bits bits'
      (Hnormal & Hdim & Hkeys & Hbits & Hcount & Hmult) HD HK HB.
    unfold RangeCore.poly_row_envelope. repeat split; try assumption; try lia.
    eapply Forall_impl; [|exact Hmult]. intros z Hz.
    eapply Nat.le_trans; [exact Hz|]. lia.
  Qed.

  (** The prepared equation is the first initialized row; the old sources form its tail. *)
  Lemma poly_assign_initial_head : forall x f P,
    poly_initial tmp_encode
      ((assignment_row x f, false) ::
        map (fun r => (rename_row (rename_old x) r, false)) P) =
      poly_assign_head x f P :: poly_assign_tail x P.
  Proof.
    intros x f P.
    assert (Hzeros : map (fun _ : lcons (option X.t) * bool => 0%Z)
      (map (fun r => (rename_row (rename_old x) r, false)) P) =
      map (fun _ : lcons X.t => 0%Z) P).
    { induction P as [|r P IH]; [reflexivity|]. cbn [map]. now f_equal. }
    unfold poly_assign_head, poly_assign_tail.
    cbn [poly_initial fst snd]. now rewrite Hzeros.
  Qed.

  (** The renamed source list is shared by all support and width bounds. *)
  Lemma poly_assign_tail_sources : forall x P,
    poly_assign_tail x P = map (@poly_pad_row (option X.t))
      (poly_initial tmp_encode
        (map (fun r => (r, false)) (poly_assign_sources x P))).
  Proof.
    intros x P. unfold poly_assign_tail, poly_assign_sources. now rewrite map_map.
  Qed.

  (** Padding multiplier vectors does not change the source row count. *)
  Lemma poly_assign_tail_length : forall x P,
    length (poly_assign_tail x P) = length P.
  Proof.
    intros x P. rewrite poly_assign_tail_sources, length_map, poly_initial_length,
      length_map, poly_assign_sources_length. reflexivity.
  Qed.

  (** Padded source multipliers retain the common exact length and unit entries. *)
  Lemma poly_assign_tail_units : forall x P,
    Forall (fun r => length (poly_multipliers r) = length P + 1 /\
      Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers r))
      (poly_assign_tail x P).
  Proof.
    intros x P. rewrite poly_assign_tail_sources. apply Forall_map, Forall_forall.
    intros r Hr.
    pose proof (poly_initial_units (option X.t) tmp_encode
      (map (fun p => (p, false)) (poly_assign_sources x P))) as Hunits.
    destruct (proj1 (Forall_forall _ _) Hunits r Hr) as [Hlength Hunit].
    rewrite length_map, poly_assign_sources_length in Hlength.
    cbn [poly_pad_row poly_multipliers length]. split; [lia|].
    constructor; [left; reflexivity|exact Hunit].
  Qed.

  (** The new assigned coordinate never belongs to the renamed source support. *)
  Lemma poly_assign_tail_support_absent : forall x P,
    ~ In (Some x) (RangeCore.vars_of (poly_assign_sources x P)).
  Proof.
    intros x P Hin.
    destruct (RangeCore.poly_vars_of_support _ _ Hin) as [r [Hr Hkey]].
    unfold poly_assign_sources in Hr.
    apply in_map_iff in Hr as [p [Hsame Hp]]. subst r.
    exact (poly_assign_rename_row_absent x p Hkey).
  Qed.

  (** Initial normalization keeps all source rows on the fixed renamed support. *)
  Lemma poly_assign_tail_reduced : forall x P,
    Forall (RangeCore.poly_reduced_row (RangeCore.vars_of (poly_assign_sources x P)))
      (poly_assign_tail x P).
  Proof.
    intros x P. rewrite poly_assign_tail_sources. apply Forall_map.
    exact (RangeCore.poly_raw_initial_reduced (poly_assign_sources x P)).
  Qed.

  (** Any normalized row on that support omits the fresh assigned coordinate. *)
  Lemma poly_assign_tail_reduced_absent : forall x P r,
    RangeCore.poly_reduced_row (RangeCore.vars_of (poly_assign_sources x P)) r ->
    ~ In (Some x) (map fst (lhs (poly_constraint r))).
  Proof.
    intros x P r [_ Hsupport] Hin.
    apply in_map_iff in Hin as [p [Hsame Hp]].
    destruct (proj1 (Forall_forall _ _) Hsupport p Hp) as [_ Hkey].
    rewrite Hsame in Hkey. exact (poly_assign_tail_support_absent x P Hkey).
  Qed.

  Lemma poly_assign_tail_absent : forall x P,
    Forall (fun r => ~ In (Some x) (map fst (lhs (poly_constraint r))))
      (poly_assign_tail x P).
  Proof.
    intros x P. eapply Forall_impl; [|exact (poly_assign_tail_reduced x P)].
    intros r Hr. exact (poly_assign_tail_reduced_absent x P r Hr).
  Qed.

  (** Padding preserves source arithmetic width and adds only the reserved multiplier slot. *)
  Lemma poly_assign_tail_envelopes : forall x P,
    Forall (RangeCore.poly_row_envelope
      (length (RangeCore.vars_of (poly_assign_sources x P))) (length P + 1)
      (poly_raw_keys P + 1) (poly_raw_bits P)) (poly_assign_tail x P).
  Proof.
    intros x P. rewrite poly_assign_tail_sources. apply Forall_map, Forall_forall.
    intros r Hr.
    pose proof (RangeCore.poly_raw_initial_reduced (poly_assign_sources x P)) as Hsupport.
    pose proof (proj1 (Forall_forall _ _) Hsupport r Hr) as Hreduced.
    pose proof (RangeCore.poly_reduced_dimension
      (RangeCore.vars_of (poly_assign_sources x P)) r Hreduced) as Hdim.
    pose proof (RangeCore.poly_raw_initial_envelopes (poly_assign_sources x P)) as Hrows.
    destruct (proj1 (Forall_forall _ _) Hrows r Hr)
      as (Hunique & Hwide & Hkeys & Hbits & Hlength & Hmults).
    rewrite poly_assign_sources_raw_bits in Hbits, Hmults.
    rewrite poly_assign_sources_length in Hlength.
    pose proof (poly_assign_sources_raw_keys x P) as Hkey_bound.
    unfold RangeCore.poly_row_envelope.
    cbn [poly_pad_row poly_constraint poly_multipliers length].
    split; [exact Hunique|]. split; [exact Hdim|].
    split; [eapply Nat.le_trans; [exact Hkeys|exact Hkey_bound]|].
    split; [exact Hbits|]. split.
    - replace (length P + 1) with (S (length P)) by lia.
      apply le_n_S. exact Hlength.
    -
    constructor; [cbn [Z.size_nat]; lia|exact Hmults].
  Qed.

  (** The complete initialized system shares one envelope for its head and sources. *)
  Lemma poly_assign_initial_envelope : forall x f P,
    NoDup (map fst (coef f)) ->
    Forall (RangeCore.poly_row_envelope
      (length (RangeCore.vars_of (poly_assign_sources x P)) + length (coef f) + 1)
      (length P + 1)
      (poly_raw_keys P + X.bits x + F.form_bits f + 1)
      (poly_raw_bits P + F.form_bits f + 1))
      (poly_initial tmp_encode
        ((assignment_row x f, false) ::
          map (fun r => (rename_row (rename_old x) r, false)) P)).
  Proof.
    intros x f P Hform. rewrite poly_assign_initial_head. constructor.
    - eapply poly_assign_row_envelope_mono.
      + apply poly_assign_head_envelope. exact Hform.
      + lia.
      + lia.
      + lia.
    - eapply Forall_impl; [|apply poly_assign_tail_envelopes].
      intros r Hr. eapply poly_assign_row_envelope_mono;
        [exact Hr|lia|lia|lia].
  Qed.

  (** The raw input support is covered by the old support and the prepared equation. *)
  Lemma poly_assign_input_support_length : forall x f P,
    length (RangeCore.vars_of (poly_assign_input x f P)) <=
      length (RangeCore.vars_of (poly_assign_sources x P)) + length (coef f) + 1.
  Proof.
    intros x f P.
    replace (length (RangeCore.vars_of (poly_assign_sources x P)) +
      length (coef f) + 1) with
      (length (RangeCore.vars_of (poly_assign_sources x P)) +
        length (map fst (lhs (assignment_row x f))))
      by (rewrite length_map; cbn [assignment_row lhs length]; rewrite length_map; lia).
    rewrite <- length_app.
    apply NoDup_incl_length; [apply RangeCore.poly_vars_of_nodup|].
    intros y Hy.
    destruct (RangeCore.poly_vars_of_support (poly_assign_input x f P) y Hy)
      as [r [Hr Hkey]].
    unfold poly_assign_input in Hr. destruct Hr as [Hhead|Hsource].
    - subst r. apply in_or_app. right. exact Hkey.
    - apply in_or_app. left.
      now apply RangeCore.poly_vars_of_contains with (r := r).
  Qed.

  (** One elimination preserves the full head-and-source dimension and doubles width. *)
  Lemma poly_assign_output_envelope : forall x f P,
    NoDup (map fst (coef f)) ->
    Forall (RangeCore.poly_row_envelope
      (length (RangeCore.vars_of (poly_assign_sources x P)) + length (coef f) + 1)
      (length P + 1)
      (poly_raw_keys P + X.bits x + F.form_bits f + 1)
      (2 * (poly_raw_bits P + F.form_bits f + 1) + 1))
      (poly_step tmp_encode tmp_eqb None
        (poly_initial tmp_encode
          ((assignment_row x f, false) ::
            map (fun r => (rename_row (rename_old x) r, false)) P))).
  Proof.
    intros x f P Hform.
    apply RangeCore.poly_step_envelopes
      with (vars := RangeCore.vars_of (poly_assign_input x f P)).
    - apply poly_assign_input_support_length.
    - rewrite <- poly_assign_input_rows.
      apply RangeCore.poly_raw_initial_reduced.
    - apply poly_assign_initial_envelope. exact Hform.
  Qed.

  (** The prepared head and sources share the public quadratic step allowance. *)
  Lemma T_poly_assign_full_step_bounded : forall x f P,
    NoDup (map fst (coef f)) ->
    (T_poly_step tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb None
      (poly_initial tmp_encode
        ((assignment_row x f, false) ::
          map (fun r => (rename_row (rename_old x) r, false)) P)) <=
      RangeCore.poly_step_factor * N.of_nat (length P + 2)^2 *
        RangeCore.poly_clock_span
          (length (RangeCore.vars_of (poly_assign_sources x P)) + length (coef f) + 1)
          (length P + 1)
          (poly_raw_keys P + X.bits x + F.form_bits f + 1)
          (poly_raw_bits P + F.form_bits f + 1))%N.
  Proof.
    intros x f P Hform.
    pose proof (RangeCore.T_poly_step_bounded None
      (poly_initial tmp_encode
        ((assignment_row x f, false) ::
          map (fun r => (rename_row (rename_old x) r, false)) P))
      (length (RangeCore.vars_of (poly_assign_sources x P)) + length (coef f) + 1)
      (length P + 1)
      (poly_raw_keys P + X.bits x + F.form_bits f + 1)
      (poly_raw_bits P + F.form_bits f + 1)
      (poly_assign_initial_envelope x f P Hform)) as Hstep.
    rewrite poly_initial_length in Hstep. cbn [length] in Hstep.
    rewrite length_map in Hstep.
    replace (S (length P) + 1) with (length P + 2) in Hstep by lia.
    change (T_poly_step tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb None
      (poly_initial tmp_encode
        ((assignment_row x f, false) ::
          map (fun r => (rename_row (rename_old x) r, false)) P)) <=
      RangeCore.poly_step_factor * N.of_nat (length P + 2)^2 *
        RangeCore.poly_clock_span
          (length (RangeCore.vars_of (poly_assign_sources x P)) + length (coef f) + 1)
          (length P + 1)
          (poly_raw_keys P + X.bits x + F.form_bits f + 1)
          (poly_raw_bits P + F.form_bits f + 1))%N in Hstep.
    exact Hstep.
  Qed.

  (** Every output certificate retains one prepared-head slot and one slot per source. *)
  Lemma poly_assign_output_multiplier_bits : forall x f P,
    NoDup (map fst (coef f)) ->
    Forall (fun r => length (poly_multipliers r) = length P + 1 /\
      Forall (fun m => Z.size_nat m <=
        (poly_raw_bits P + F.form_bits f + 1) + 1) (poly_multipliers r))
      (poly_step tmp_encode tmp_eqb None
        (poly_initial tmp_encode
          ((assignment_row x f, false) ::
            map (fun r => (rename_row (rename_old x) r, false)) P))).
  Proof.
    intros x f P Hform.
    eapply RangeCore.poly_step_multiplier_bits with
      (count := length P + 1) (bits := poly_raw_bits P + F.form_bits f + 1).
    apply Forall_forall. intros r Hr.
    pose proof (poly_initial_units (option X.t) tmp_encode
      ((assignment_row x f, false) ::
        map (fun p => (rename_row (rename_old x) p, false)) P)) as Hunits.
    destruct (proj1 (Forall_forall _ _) Hunits r Hr) as [Hlength Hunit].
    cbn [length] in Hlength. rewrite length_map in Hlength.
    replace (S (length P)) with (length P + 1) in Hlength by lia.
    destruct (proj1 (Forall_forall _ _) (poly_assign_initial_envelope x f P Hform)
      r Hr) as (Hnormal & Hdim & Hkeys & Hbits & Hcount & Hmult).
    split; [exact Hlength|]. split; [exact Hunit|].
    eapply Nat.le_trans; [apply RangeCore.poly_row_coefficient_bits; exact Hnormal|].
    exact Hbits.
  Qed.

  (** Only the old assigned coordinate is eliminated from the source-only tail. *)
  Definition poly_assign_tail_step (x : X.t) (P : list (lcons X.t)) :=
    poly_step tmp_encode tmp_eqb None (poly_assign_tail x P).

  (** When the prepared equation omits the old key, elimination leaves it at the front. *)
  Lemma poly_assign_zero_head_step : forall x f P,
    poly_coefficient tmp_eqb None (poly_constraint (poly_assign_head x f P)) = 0%Z ->
    poly_step tmp_encode tmp_eqb None
      (poly_initial tmp_encode
        ((assignment_row x f, false) ::
          map (fun r => (rename_row (rename_old x) r, false)) P)) =
      poly_assign_head x f P :: poly_assign_tail_step x P.
  Proof.
    intros x f P Hzero. rewrite poly_assign_initial_head.
    unfold poly_assign_tail_step. now apply poly_assign_step_zero_head.
  Qed.

  (** Source-only elimination preserves its original support and distinct coefficients. *)
  Lemma poly_assign_tail_step_reduced : forall x P,
    Forall (RangeCore.poly_reduced_row (RangeCore.vars_of (poly_assign_sources x P)))
      (poly_assign_tail_step x P).
  Proof.
    intros x P. unfold poly_assign_tail_step.
    apply RangeCore.poly_step_reduced. apply poly_assign_tail_reduced.
  Qed.

  (** A source pivot cannot create the new assigned variable. *)
  Lemma poly_assign_tail_step_absent : forall x P,
    Forall (fun r => ~ In (Some x) (map fst (lhs (poly_constraint r))))
      (poly_assign_tail_step x P).
  Proof.
    intros x P. eapply Forall_impl; [|exact (poly_assign_tail_step_reduced x P)].
    intros r Hr. exact (poly_assign_tail_reduced_absent x P r Hr).
  Qed.

  (** The tail step keeps its dimension and key width while doubling source arithmetic width. *)
  Lemma poly_assign_tail_step_envelopes : forall x P,
    Forall (RangeCore.poly_row_envelope
      (length (RangeCore.vars_of (poly_assign_sources x P))) (length P + 1)
      (poly_raw_keys P + 1) (2 * poly_raw_bits P + 1)) (poly_assign_tail_step x P).
  Proof.
    intros x P. unfold poly_assign_tail_step.
    apply RangeCore.poly_step_envelopes
      with (vars := RangeCore.vars_of (poly_assign_sources x P)).
    - lia.
    - apply poly_assign_tail_reduced.
    - apply poly_assign_tail_envelopes.
  Qed.

  (** Initial unit vectors give the sharper one-step multiplier bound without form growth. *)
  Lemma poly_assign_tail_step_multiplier_bits : forall x P,
    Forall (fun r => length (poly_multipliers r) = length P + 1 /\
      Forall (fun m => Z.size_nat m <= poly_raw_bits P + 1) (poly_multipliers r))
      (poly_assign_tail_step x P).
  Proof.
    intros x P. unfold poly_assign_tail_step. apply RangeCore.poly_step_multiplier_bits.
    apply Forall_forall. intros r Hr.
    destruct (proj1 (Forall_forall _ _) (poly_assign_tail_units x P) r Hr)
      as [Hlength Hunit].
    destruct (proj1 (Forall_forall _ _) (poly_assign_tail_envelopes x P) r Hr)
      as (Hunique & Hdim & Hkeys & Hbits & Hcount & Hmults).
    split; [exact Hlength|]. split; [exact Hunit|].
    eapply Nat.le_trans; [apply RangeCore.poly_row_coefficient_bits; exact Hunique|].
    exact Hbits.
  Qed.

  (** Every resulting source-only constraint has zero coefficient for the new variable. *)
  Lemma poly_assign_tail_step_fresh_zero : forall x P,
    Forall (fun r => poly_coefficient tmp_eqb (Some x) (poly_constraint r) = 0%Z)
      (poly_assign_tail_step x P).
  Proof.
    intros x P. eapply Forall_impl; [|exact (poly_assign_tail_step_absent x P)].
    intros r Hr. now apply RangeCore.poly_coefficient_absent.
  Qed.

  (** The source-only assignment step uses the established quadratic row charge. *)
  Lemma T_poly_assign_tail_step_bounded : forall x P,
    (T_poly_step tmp_encode T_tmp_encode tmp_eqb T_tmp_eqb None
      (poly_assign_tail x P) <= RangeCore.poly_step_factor *
        N.of_nat (length P + 1)^2 * RangeCore.poly_clock_span
          (length (RangeCore.vars_of (poly_assign_sources x P)))
          (length P + 1) (poly_raw_keys P + 1) (poly_raw_bits P))%N.
  Proof.
    intros x P.
    pose proof (RangeCore.T_poly_step_bounded None (poly_assign_tail x P)
      (length (RangeCore.vars_of (poly_assign_sources x P)))
      (length P + 1) (poly_raw_keys P + 1) (poly_raw_bits P)
      (poly_assign_tail_envelopes x P)) as Hstep.
    now rewrite poly_assign_tail_length in Hstep.
  Qed.

  (** Untagged source-only results are normal and omit the new assigned key. *)
  Lemma poly_assign_tail_candidate_envelope : forall x P r xs,
    In r (poly_assign_tail_step x P) ->
    untag (lhs (poly_constraint r)) = Some xs ->
    let c := LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r)) in
    NoDup (map fst (lhs c)) /\
    length (lhs c) <= length (RangeCore.vars_of (poly_assign_sources x P)) /\
    C.row_key_bits c <= poly_raw_keys P + 1 /\
    C.row_bits c <= 2 * poly_raw_bits P + 1 /\
    poly_coefficient X.eqb x c = 0%Z.
  Proof.
    intros x P r xs Hr Huntag c.
    destruct (proj1 (Forall_forall _ _) (poly_assign_tail_step_envelopes x P)
      r Hr) as (Hnormal & Hdim & Hkeys & Hbits & _).
    pose proof (poly_assign_untag_envelope (poly_constraint r) xs Huntag)
      as (Hlength & Hbits_eq & Hkeys_le).
    pose proof (proj1 (Forall_forall _ _) (poly_assign_tail_step_absent x P)
      r Hr) as Habsent.
    pose proof (poly_assign_untag_absent x (poly_constraint r) xs Huntag
      Habsent) as Hfresh.
    repeat split.
    - apply untag_nodup with (xs := lhs (poly_constraint r)); assumption.
    - unfold c. cbn [lhs]. rewrite Hlength. exact Hdim.
    - eapply Nat.le_trans; [exact Hkeys_le|exact Hkeys].
    - unfold c. rewrite Hbits_eq. exact Hbits.
    - apply poly_coefficient_absent. exact Hfresh.
  Qed.

  (** Source-only assignment candidates preserve the original width through substitution. *)
  Lemma T_poly_assign_tail_candidate_branch : forall x P f r xs head ms,
    In r (poly_assign_tail_step x P) ->
    untag (lhs (poly_constraint r)) = Some xs ->
    poly_multipliers r = head :: ms ->
    NoDup (map fst (coef f)) ->
    C.row_key_bits (LCons X.t (coef f) REq (cst f)) <= F.form_bits f ->
    let c := LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r)) in
    let dim := length (RangeCore.vars_of (poly_assign_sources x P)) in
    let rawkeys := poly_raw_keys P in
    let rawbits := poly_raw_bits P in
    let width := nell (Reached P) + 1 in
    (T_subst x f c + C.T_check_entails P (subst x f c) (Cert ms 1 false) <=
      AssignCore.poly_assign_zero_subst_factor * N.of_nat (dim + length (coef f) + 1) *
        N.of_nat (rawkeys + F.form_bits f + 2 * rawbits + 3) +
      48 * C.c_lc * N.of_nat (dim + terms (Reached P) + length P + 1) *
        N.of_nat (width + 1)^2)%N.
  Proof.
    intros x P f r xs head ms Hr Huntag Hmult Hform Hformkeys
      c dim rawkeys rawbits width.
    destruct (poly_assign_tail_candidate_envelope x P r xs Hr Huntag)
      as (Hnormal & Hdim & Hkeys & Hbits & Hzero).
    cbn zeta in Hnormal, Hdim, Hkeys, Hbits, Hzero.
    assert (Hfresh : ~ In x (map fst (lhs c))).
    { unfold c. eapply poly_assign_untag_absent; [exact Huntag|].
      exact (proj1 (Forall_forall _ _) (poly_assign_tail_step_absent x P) r Hr). }
    assert (Hformentries : Forall (fun p =>
      Pos.size_nat (X.encode (fst p)) <= rawkeys + F.form_bits f + 1) (coef f)).
    { apply Forall_forall. intros p Hp.
      pose proof (poly_row_key_member
        (LCons X.t (coef f) REq (cst f)) p Hp) as Hkey.
      lia. }
    assert (Hkeys_total : C.row_key_bits c <= rawkeys + F.form_bits f + 1).
    { eapply Nat.le_trans; [exact Hkeys|]. lia. }
    pose proof (AssignCore.T_poly_assign_subst_zero x f c
      (rawkeys + F.form_bits f + 1) (2 * rawbits + 1)
      Hnormal Hform Hkeys_total Hbits Hformentries Hzero) as Hsubst.
    assert (Hsubstdim : length (lhs (subst x f c)) <= dim).
    { destruct (AssignCore.poly_assign_subst_absent_envelope x f c Hfresh Hnormal)
        as [Hlength _]. eapply Nat.le_trans; [exact Hlength|exact Hdim]. }
    assert (Hsubstwidth : C.row_key_bits (subst x f c) +
      C.row_bits (subst x f c) <= 3 * width + 1).
    { destruct (AssignCore.poly_assign_subst_absent_envelope x f c Hfresh Hnormal)
        as [_ [Hkey Hbit]].
      change (C.row_key_bits (subst x f c) <= C.row_key_bits c) in Hkey.
      change (C.row_bits (subst x f c) <= C.row_bits c) in Hbit.
      change (C.row_key_bits c <= rawkeys + 1) in Hkeys.
      change (C.row_bits c <= 2 * rawbits + 1) in Hbits.
      unfold width, rawkeys, rawbits in *.
      pose proof (poly_raw_width P). lia. }
    destruct (proj1 (Forall_forall _ _) (poly_assign_tail_step_multiplier_bits x P)
      r Hr) as [Hmultlen Hmultbits].
    rewrite Hmult in Hmultlen, Hmultbits.
    cbn [length] in Hmultlen. inversion Hmultbits as [|? ? _ Hmsbits]; subst.
    assert (Hsource : Forall (fun p =>
      C.row_key_bits p + C.row_bits p <= width) P).
    { eapply Forall_impl; [|apply poly_raw_source_width].
      intros p Hp. eapply Nat.le_trans; [exact Hp|]. unfold width. lia. }
    assert (Hms : Forall (fun m => Z.size_nat m <= 2 * width + 2) ms).
    { eapply Forall_impl; [|exact Hmsbits].
      intros m Hm. unfold width, rawbits in *.
      pose proof (poly_raw_width P). lia. }
    pose proof (AssignCore.T_poly_assign_checker P (subst x f c) ms dim width
      Hsource ltac:(lia) Hms Hsubstdim Hsubstwidth) as Hcheck.
    change (T_subst x f c <= AssignCore.poly_assign_zero_subst_factor *
      N.of_nat (length (lhs c) + length (coef f) + 1) *
      N.of_nat (rawkeys + F.form_bits f + 1 + (2 * rawbits + 1) + 1))%N in Hsubst.
    replace (rawkeys + F.form_bits f + 1 + (2 * rawbits + 1) + 1) with
      (rawkeys + F.form_bits f + 2 * rawbits + 3) in Hsubst by lia.
    assert (Hsubst_total : (T_subst x f c <=
      AssignCore.poly_assign_zero_subst_factor *
        N.of_nat (dim + length (coef f) + 1) *
        N.of_nat (rawkeys + F.form_bits f + 2 * rawbits + 3))%N).
    { eapply N.le_trans; [exact Hsubst|].
      apply N.mul_le_mono_r, N.mul_le_mono_l, time_of_nat_le.
      change (length (lhs c) <= dim) in Hdim. lia. }
    change (C.T_check_entails P (subst x f c) (Cert ms 1 false) <=
      48 * C.c_lc * N.of_nat (dim + terms (Reached P) + length P + 1) *
        N.of_nat (width + 1)^2)%N in Hcheck.
    cbn zeta. eapply N.add_le_mono; [exact Hsubst_total|exact Hcheck].
  Qed.

  (** Untagging and branch dispatch add a linear row scan to the source-only check. *)
  Lemma T_poly_assign_tail_candidate_bounded : forall x P f r,
    In r (poly_assign_tail_step x P) ->
    NoDup (map fst (coef f)) ->
    C.row_key_bits (LCons X.t (coef f) REq (cst f)) <= F.form_bits f ->
    let dim := length (RangeCore.vars_of (poly_assign_sources x P)) in
    let rawkeys := poly_raw_keys P in
    let rawbits := poly_raw_bits P in
    let width := nell (Reached P) + 1 in
    (T_assigned_candidate P x f r <=
      2 * N.of_nat (dim + 1) +
      AssignCore.poly_assign_zero_subst_factor *
        N.of_nat (dim + length (coef f) + 1) *
          N.of_nat (rawkeys + F.form_bits f + 2 * rawbits + 3) +
      48 * C.c_lc * N.of_nat (dim + terms (Reached P) + length P + 1) *
        N.of_nat (width + 1)^2 + 16)%N.
  Proof.
    intros x P f r Hr Hform Hformkeys dim rawkeys rawbits width.
    set (budget := (AssignCore.poly_assign_zero_subst_factor *
      N.of_nat (dim + length (coef f) + 1) *
        N.of_nat (rawkeys + F.form_bits f + 2 * rawbits + 3) +
      48 * C.c_lc * N.of_nat (dim + terms (Reached P) + length P + 1) *
        N.of_nat (width + 1)^2)%N).
    assert (Hbranch : forall xs head ms,
      untag (lhs (poly_constraint r)) = Some xs ->
      poly_multipliers r = head :: ms ->
      let c := LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r)) in
      (T_subst x f c + C.T_check_entails P (subst x f c)
        (Cert ms 1 false) <= budget)%N).
    { intros xs head ms Huntag Hmult c.
      pose proof (T_poly_assign_tail_candidate_branch x P f r xs head ms
        Hr Huntag Hmult Hform Hformkeys) as Hcost.
      cbn zeta in Hcost. exact Hcost. }
    pose proof (T_poly_assign_candidate_frame P x f r budget Hbranch) as Hframe.
    pose proof (T_poly_assign_untag (lhs (poly_constraint r))) as Huntime.
    destruct (proj1 (Forall_forall _ _) (poly_assign_tail_step_envelopes x P)
      r Hr) as (_ & Hdim & _).
    assert (Huntag_total :
      (T_untag (lhs (poly_constraint r)) <= 2 * N.of_nat (dim + 1))%N).
    { eapply N.le_trans; [exact Huntime|].
      apply N.mul_le_mono_l, time_of_nat_le.
      change (length (lhs (poly_constraint r)) <= dim) in Hdim.
      apply Nat.add_le_mono_r. exact Hdim. }
    eapply N.le_trans; [exact Hframe|].
    fold budget. clear -Huntag_total. lia.
  Qed.

  Definition c_num : N := (poly_assume_factor + poly_havoc_factor + 1)%N.
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x s. eapply N.le_trans; [apply T_poly_havoc_bounded|].
    apply N.mul_le_mono_r. unfold c_num. lia.
  Qed.
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es s. eapply N.le_trans; [apply T_poly_assume_contract|].
    apply N.mul_le_mono_r. unfold c_num. lia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. time_unfold T_narrow.
    change (1 * 1 <= c_lat * N.of_nat (size a + size b + 1))%N.
    apply N.mul_le_mono; [exact c_lat_pos|lia].
  Qed.
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof.
    intros e s. eapply N.le_trans; [apply poly_range_size_bounded|].
    apply N.mul_le_mono_r. unfold c_num, poly_assume_factor. lia.
  Qed.
  Definition c_poly : N := (poly_subst_factor + poly_fm_factor + poly_entail_wrapper_factor + 1)%N.
  Lemma T_subst_le : forall x f r,
    (T_subst x f r <= c_poly * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof.
    intros x f r. pose proof (T_poly_subst_bounded x f r) as Hsubst.
    eapply N.le_trans; [exact Hsubst|]. unfold c_poly. apply N.mul_le_mono; [lia|].
    assert (Hsquare : (C.lsize (LCons X.t (coef f) REq (cst f)) + C.lsize r + 1)^2 <=
      (X.bits x + C.lsize (LCons X.t (coef f) REq (cst f)) + C.lsize r + 1)^2).
    { apply Nat.pow_le_mono_l. lia. }
    lia.
  Qed.

  Lemma T_fm_elim_le : forall x P, normal P ->
    (T_fm_elim x P <= c_poly * N.of_nat (((length P + 1)^2)%nat) *
      N.of_nat ((n P + length P + 1)%nat) * N.of_nat (((ell P + 1)^2)%nat))%N.
  Proof.
    intros x P Hnormal.
    eapply N.le_trans; [apply T_poly_fm_bounded; exact Hnormal|].
    rewrite !Nat2N.inj_pow. repeat apply N.mul_le_mono_r.
    unfold c_poly. lia.
  Qed.
  Lemma T_entail_cert_le : forall P c, normal P -> normal (c :: nil) ->
    (T_entail_cert P c <= c_poly *
      N.of_nat (fmcost (n P + length (lhs c)) (length P + 1)
        (n P + length (lhs c)) (length P + 1)
        (ell P + C.row_bits c + C.row_key_bits c)))%N.
  Proof.
    intros P c HP Hc.
    eapply N.le_trans; [apply T_poly_entail_bounded; assumption|].
    unfold poly_entail_budget. apply N.mul_le_mono_r. unfold c_poly. lia.
  Qed.
  (** Assignment charges row normalization and one elimination after linearization. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) = N.of_nat (terms s * (nell s + 1) +
      (length (prows s) + 3)^2 *
      (n (prows s) + terms s + tsize e + length (prows s) + 3) *
      (nell s + X.bits x + F.bits_e e + 1)^2) + F.T_lin_of e)%N.
  Proof.
    intros x e s. unfold assign_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  (** Havoc charges row normalization and one elimination of the selected variable. *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (length (prows s) + 1)^2 * (n (prows s) + terms s + length (prows s) + 1) *
      (nell s + X.bits x + 1)^2.
  Proof.
    reflexivity.
  Qed.
  (** Assumption charges every emitted atom and the bits of its merged coefficients. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat ((length (prows s) + 1) * (length (F.atoms_of g es) + 1) *
        (fold_right Nat.add 0%nat (map tsize es) + 1) *
        (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1)) +
      F.T_atoms_of g es)%N.
  Proof.
    intros g es s. unfold assume_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Definition k_cert : N := poly_entail_raw_factor.
  Lemma T_entail_cert_raw : forall P c,
    (T_entail_cert P c <= k_cert * N.of_nat
      (terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
       fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
         (length P + 1) (nell (Reached (c :: P)))))%N.
  Proof.
    intros P c. exact (T_poly_entail_raw_bounded P c).
  Qed.
  (** One spare FM stage pays a quadratic charge at the final multiplier width. *)
  Lemma poly_fmcost_spare_square : forall fuel dim mlen rows bits,
    mlen <= rows ->
    (mlen + 1)^2 * (dim + mlen + 1) * (poly_width_after fuel bits + 1)^2 <=
      fmcost dim mlen (S fuel) rows bits.
  Proof.
    intro fuel. induction fuel as [|fuel IH]; intros dim mlen rows bits Hrows.
    - cbn [poly_width_after fmcost].
      eapply Nat.le_trans with (m :=
        (rows + 1)^2 * (dim + mlen + 1) * (bits + 1)^2).
      + apply Nat.mul_le_mono; [apply Nat.mul_le_mono; [apply Nat.pow_le_mono_l; lia|lia]|lia].
      + lia.
    - cbn [poly_width_after fmcost].
      eapply Nat.le_trans with
        (m := fmcost dim mlen (S fuel) (rows^2 / 4 + rows) (2 * bits + 1)).
      2: { apply Nat.le_add_l. }
      pose proof (poly_rows_recurrence_mono mlen rows Hrows) as Hmono.
      assert (mlen <= mlen^2 / 4 + mlen) by lia.
      apply IH. lia.
  Qed.
  (** A returned terminal certificate inherits its tracked row's multiplier widths. *)
  Lemma poly_returned_certificate_weights : forall P c rows k dim mlen keys bits,
    Forall (poly_row_envelope dim mlen keys bits) rows ->
    find_certificate P c rows = Some k ->
    length (mults k) <= mlen /\
    Forall (fun m => Z.size_nat m <= bits + 1) (mults k) /\
    Z.size_nat (scale k) <= bits + 1.
  Proof.
    intros P c rows. induction rows as [|r rows IH];
      intros k dim mlen keys bits Hrows Hresult.
    - discriminate.
    - inversion Hrows as [|? ? Hr Htail]; subst.
      cbn [find_certificate] in Hresult.
      destruct (candidate P c r) as [found|] eqn:Hcandidate.
      + injection Hresult as Hsame. subst found.
        unfold candidate in Hcandidate.
        destruct (poly_contradiction r); [|discriminate].
        destruct (poly_multipliers r) as [|sc ms] eqn:Hweights; [discriminate|].
        destruct (poly_canonical_guard P c r sc ms); [|discriminate].
        destruct (C.check_entails P c (Cert ms (poly_canonical_scale sc) false));
          [|discriminate].
        injection Hcandidate as Hsame. subst k. cbn [mults scale].
        destruct Hr as (_ & _ & _ & _ & Hmultlength & Hmultbits).
        rewrite Hweights in Hmultlength, Hmultbits. cbn [length] in Hmultlength.
        inversion Hmultbits as [|? ? Hscale Hms]; subst.
        split; [lia|]. split; [exact Hms|].
        { unfold poly_canonical_scale. destruct (Z.eqb sc 0);
            [cbn [Z.size_nat Pos.size_nat]; lia|lia]. }
      + eapply IH; [exact Htail|exact Hresult].
  Qed.
  (** A public certificate uses only multiplier widths reached by the normalized FM run. *)
  Lemma poly_entail_cert_weights : forall P c k,
    entail_cert P c = Some k ->
    let fuel := length (poly_variables X.encode
      (poly_normal_row X.encode c :: poly_normal_rows P)) in
    let bits := nell (Reached (c :: P)) in
    length (mults k) <= length P + 1 /\
    Forall (fun m => Z.size_nat m <= poly_width_after fuel (2 * bits + 1) + 1)
      (mults k) /\
    Z.size_nat (scale k) <= poly_width_after fuel (2 * bits + 1) + 1.
  Proof.
    intros P c k Hresult fuel bits.
    set (P' := poly_normal_rows P).
    set (c' := poly_normal_row X.encode c).
    set (dim := n P' + length (lhs c')).
    set (mlen := length P' + 1).
    set (keys := poly_entail_keys P' c').
    set (rowbits := poly_entail_bits P' c').
    set (vars := poly_entail_vars P' c').
    set (initial := poly_initial X.encode
      ((poly_negate c', true) :: map (fun r => (r, false)) P')).
    unfold entail_cert, entail_engine in Hresult.
    change (find_certificate P' c'
      (poly_run X.encode X.eqb (poly_variables X.encode (c' :: P')) initial) = Some k)
      in Hresult.
    assert (HP : normal P') by apply poly_normal_rows_normal.
    assert (Hc : normal [c']).
    { change (normal (poly_normal_rows [c])). apply poly_normal_rows_normal. }
    assert (Hdim : length vars <= dim) by apply poly_entail_vars_length.
    assert (Hreduced : Forall (poly_reduced_row vars) initial)
      by apply poly_entail_initial_reduced.
    assert (Hinitial : Forall (poly_row_envelope dim mlen keys rowbits) initial)
      by (apply poly_entail_initial_envelopes; assumption).
    pose proof (poly_run_envelopes
      (poly_variables X.encode (c' :: P')) vars initial dim mlen keys rowbits
      Hdim Hreduced Hinitial) as Hfinal.
    assert (Hweights : length (mults k) <= mlen /\
      Forall (fun m => Z.size_nat m <=
        poly_width_after fuel rowbits + 1) (mults k) /\
      Z.size_nat (scale k) <= poly_width_after fuel rowbits + 1).
    { apply (poly_returned_certificate_weights P' c'
        (poly_run X.encode X.eqb (poly_variables X.encode (c' :: P')) initial)
        k dim mlen keys
        (poly_width_after fuel rowbits)).
      - change (Forall (poly_row_envelope dim mlen keys
          (poly_width_after (length (poly_variables X.encode (c' :: P'))) rowbits))
          (poly_run X.encode X.eqb (poly_variables X.encode (c' :: P')) initial)).
        exact Hfinal.
      - exact Hresult. }
    assert (Hwidth : keys + rowbits <= 2 * bits + 1).
    { unfold keys, rowbits. rewrite poly_entail_width.
      unfold P', c', bits.
      apply poly_normal_entail_width_raw. }
    assert (Hfinal_width : keys + poly_width_after fuel rowbits <=
      poly_width_after fuel (2 * bits + 1)).
    { eapply Nat.le_trans; [apply poly_width_after_fixed_keys|].
      now apply poly_width_after_mono. }
    destruct Hweights as [Hlength [Hmult Hscale]].
    split; [rewrite <- poly_normal_rows_length; exact Hlength|].
    split.
    - apply Forall_forall. intros m Hin.
      pose proof (proj1 (Forall_forall _ _) Hmult m Hin) as Hm.
      eapply Nat.le_trans; [exact Hm|]. apply Nat.add_le_mono_r.
      eapply Nat.le_trans; [apply Nat.le_add_l|exact Hfinal_width].
    - eapply Nat.le_trans; [exact Hscale|]. apply Nat.add_le_mono_r.
      eapply Nat.le_trans; [apply Nat.le_add_l|exact Hfinal_width].
  Qed.
  (** A singleton run can return only a unit certificate with no source multipliers. *)
  Lemma poly_empty_returned_unit : forall c rows k,
    Forall (fun r => poly_multipliers r = [1%Z]) rows ->
    find_certificate [] c rows = Some k -> k = Cert [] 1 false.
  Proof.
    intros c rows. induction rows as [|r rows IH]; intros k Hrows Hresult.
    - discriminate.
    - inversion Hrows as [|? ? Hunit Htail]; subst.
      cbn [find_certificate] in Hresult.
      destruct (candidate [] c r) as [found|] eqn:Hcandidate.
      + injection Hresult as Hsame. subst found.
        unfold candidate in Hcandidate.
        destruct (poly_contradiction r); [|discriminate].
        rewrite Hunit in Hcandidate.
        destruct (poly_canonical_guard [] c r 1 []); [|discriminate].
        destruct (C.check_entails [] c (Cert [] (poly_canonical_scale 1) false));
          [|discriminate].
        injection Hcandidate as Hsame. subst k. reflexivity.
      + now apply IH.
  Qed.

  (** Empty-source entailment returns a unit certificate whenever it succeeds. *)
  Lemma poly_entail_cert_empty_unit : forall c k,
    entail_cert [] c = Some k -> k = Cert [] 1 false.
  Proof.
    intros c k Hresult.
    set (c' := poly_normal_row X.encode c).
    assert (Hnormal : normal [c']).
    { change (normal (poly_normal_rows [c])). apply poly_normal_rows_normal. }
    pose proof (poly_entail_empty_shape (poly_variables X.encode [c']) c' Hnormal)
      as [_ Hshape].
    assert (Hunits : Forall (fun r => poly_multipliers r = [1%Z])
      (poly_run X.encode X.eqb (poly_variables X.encode [c'])
        (poly_initial X.encode [(poly_negate c', true)]))).
    { eapply Forall_impl; [|exact Hshape]. intros r [_ Hunit]. exact Hunit. }
    unfold entail_cert, entail_engine in Hresult.
    change (find_certificate [] c'
      (poly_run X.encode X.eqb (poly_variables X.encode [c'])
        (poly_initial X.encode [(poly_negate c', true)])) = Some k) in Hresult.
    now apply poly_empty_returned_unit with (c := c') (rows :=
      poly_run X.encode X.eqb (poly_variables X.encode [c'])
        (poly_initial X.encode [(poly_negate c', true)])); assumption.
  Qed.
  (** Original normal rows fit twice the raw global bit width used by FM. *)
  Lemma poly_entail_raw_source_width : forall P c, normal P ->
    Forall (poly_source_envelope (n P + length (lhs c))
      (2 * nell (Reached (c :: P)) + 1)) (c :: P).
  Proof.
    intros P c HP.
    assert (Hwidth : ell P + C.row_bits c + C.row_key_bits c <=
      2 * nell (Reached (c :: P)) + 1).
    { unfold nell, ell. cbn [prows map fold_right terms].
      set (source_bits := fold_right Nat.max 0 (map C.row_bits P)).
      set (source_keys := fold_right Nat.max 0 (map C.row_key_bits P)).
      pose proof (Nat.le_max_l (C.row_bits c) source_bits) as Hb_c.
      pose proof (Nat.le_max_r (C.row_bits c) source_bits) as Hb_P.
      pose proof (Nat.le_max_l (C.row_key_bits c) source_keys) as Hk_c.
      pose proof (Nat.le_max_r (C.row_key_bits c) source_keys) as Hk_P.
      lia. }
    eapply Forall_impl; [|apply poly_entail_source_envelopes; exact HP].
    intros r [Hdim Hbits]. split; [exact Hdim|lia].
  Qed.
  Lemma entail_cert_size : forall P c k, normal P -> normal (c :: nil) ->
    entail_cert P c = Some k ->
    (N.of_nat (C.csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (C.lsize c + C.cbits P (mults k) + 1)) <=
      k_cert * N.of_nat
        (terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
         fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
           (length P + 1) (nell (Reached (c :: P)))))%N.
  Proof.
    intros P c k HP Hc Hresult.
    assert (Hfactor : (32 <= k_cert)%N).
    { unfold k_cert, poly_entail_raw_factor, poly_entail_factor, poly_setup_factor. nia. }
    destruct P as [|p P].
    - pose proof (poly_entail_cert_empty_unit c k Hresult) as Hunit. subst k.
      set (dim := length (lhs c)).
      set (bits := nell (Reached [c])).
      set (budget := fmcost dim 1 dim 1 bits).
      assert (Hlsize : C.lsize c <= (dim + 1) * (bits + 1)).
      { unfold C.lsize, dim, bits, nell, ell.
        cbn [prows terms map fold_right]. apply Nat.mul_le_mono_l. lia. }
      pose proof (poly_fmcost_initial_charge dim 1 bits) as Hcharge.
      change (4 * (dim + 1) * (bits + 1) <= budget) in Hcharge.
      assert (Hsize : 2 * (C.lsize c + 2) <= 32 * budget) by nia.
      assert (Hempty : C.csize [] [] = 0 /\ C.cbits [] [] = 1 /\
        Z.size_nat 1 = 1) by (repeat split; reflexivity).
      destruct Hempty as [Hcsize [Hcbits Hscalebits]].
      cbn [mults scale]. rewrite ?Hcsize, ?Hcbits, ?Hscalebits.
      eapply N.le_trans with (m := N.of_nat (2 * (C.lsize c + 2))).
      + lia.
      + eapply N.le_trans with (m := (32 * N.of_nat budget)%N).
        * replace (32 * N.of_nat budget)%N with (N.of_nat (32 * budget))
            by (rewrite Nat2N.inj_mul; reflexivity). lia.
        * apply N.mul_le_mono; [exact Hfactor|].
          rewrite Nat2N.inj_add. apply N.le_add_l.
    - set (dim := n (p :: P) + length (lhs c)).
      set (mlen := length (p :: P) + 1).
      set (bits := nell (Reached (c :: p :: P))).
      set (fuel := length (poly_variables X.encode
        (poly_normal_row X.encode c :: poly_normal_rows (p :: P)))).
      set (width := poly_width_after fuel (2 * bits + 1)).
      set (budget := fmcost dim mlen dim mlen bits).
      pose proof (poly_entail_cert_weights (p :: P) c k Hresult) as Hweights.
      change (length (mults k) <= mlen /\
        Forall (fun m => Z.size_nat m <= width + 1) (mults k) /\
        Z.size_nat (scale k) <= width + 1) in Hweights.
      destruct Hweights as [Hlength [Hmult Hscale]].
      pose proof (poly_entail_raw_source_width (p :: P) c HP) as Hraw.
      assert (Hwidth : 2 * bits + 1 <= width).
      { unfold width. pose proof (poly_width_after_fuel_mono 0 fuel (2 * bits + 1)
          (Nat.le_0_l _)) as Hgrowth.
        cbn [poly_width_after] in Hgrowth. exact Hgrowth. }
      assert (Hsource : Forall (poly_source_envelope dim width) (c :: p :: P)).
      { eapply Forall_impl; [|exact Hraw]. intros r [Hdim Hbits]. split; lia. }
      pose proof (poly_checker_measure_envelope (p :: P) c (mults k) (scale k)
        dim mlen width Hsource ltac:(lia) Hlength Hmult Hscale) as Hmeasure.
      assert (Hfuel : S fuel <= dim).
      { pose proof (poly_entail_spare_fuel (poly_normal_rows (p :: P))
          (poly_normal_row X.encode c) ltac:(unfold poly_normal_rows; discriminate))
          as Hspare.
        pose proof (poly_normal_entail_dimension (p :: P) c) as Hdimension.
        unfold fuel, dim in *. lia. }
      pose proof (poly_fmcost_spare_square fuel dim mlen mlen (2 * bits + 1)
        (Nat.le_refl _)) as Hsquare.
      pose proof (poly_fmcost_fuel_mono (S fuel) dim Hfuel dim mlen mlen
        (2 * bits + 1)) as Hmono.
      pose proof (poly_fmcost_double_width dim dim mlen mlen bits) as Hdouble.
      assert (Hsize : C.csize (p :: P) (mults k) + (Z.size_nat (scale k) + 1) *
        (C.lsize c + C.cbits (p :: P) (mults k) + 1) <= 32 * budget).
      { assert (Hcount : mlen + 1 <= (mlen + 1)^2) by (cbn [Nat.pow]; nia).
        set (span := (dim + mlen + 1) * (width + 1)^2).
        pose proof (Nat.mul_le_mono_r _ _ span Hcount) as Hcount_span.
        assert (Hsquare_span : (mlen + 1)^2 * span <=
          fmcost dim mlen (S fuel) mlen (2 * bits + 1)).
        { unfold span, width.
          replace ((mlen + 1)^2 *
            ((dim + mlen + 1) * (poly_width_after fuel (2 * bits + 1) + 1)^2))
            with ((mlen + 1)^2 * (dim + mlen + 1) *
              (poly_width_after fuel (2 * bits + 1) + 1)^2) by ring.
          exact Hsquare. }
        assert (Hstage : (mlen + 1)^2 * span <= 4 * budget).
        { eapply Nat.le_trans; [exact Hsquare_span|].
          eapply Nat.le_trans; [exact Hmono|exact Hdouble]. }
        eapply Nat.le_trans; [exact Hmeasure|].
        replace (8 * (mlen + 1) * (dim + mlen + 1) * (width + 1)^2)
          with (8 * ((mlen + 1) * span)) by (unfold span; ring).
        eapply Nat.le_trans with (m := 8 * ((mlen + 1)^2 * span)).
        - apply Nat.mul_le_mono_l. exact Hcount_span.
        - clear -Hstage. nia. }
      change (N.of_nat (C.csize (p :: P) (mults k) +
        (Z.size_nat (scale k) + 1) * (C.lsize c + C.cbits (p :: P) (mults k) + 1)) <=
        k_cert * N.of_nat (terms (Reached (c :: p :: P)) * (bits + 1) + budget))%N.
      eapply N.le_trans with (m := (32 * N.of_nat budget)%N).
      + replace (32 * N.of_nat budget)%N with (N.of_nat (32 * budget))
          by (rewrite Nat2N.inj_mul; reflexivity). lia.
      + apply N.mul_le_mono; [exact Hfactor|].
        rewrite Nat2N.inj_add. apply N.le_add_l.
  Qed.
  Lemma fm_mults_size : forall x P r, normal P -> In r (fm_elim x P) ->
    length (mults_of r) = length P /\
    Forall (fun m => Z.size_nat m <= ell P + 1) (mults_of r).
  Proof.
    intros x P r Hnormal Hin. unfold fm_elim in Hin.
    apply in_map_iff in Hin as [p [Heq Hin]]. subst r.
    cbn [mults_of].
    assert (Hinitial : Forall (fun r => length (poly_multipliers r) = length P /\
      Forall (fun m => m = 0%Z \/ m = 1%Z) (poly_multipliers r) /\
      Z.size_nat (poly_coefficient X.eqb x (poly_constraint r)) <=
        fold_right Nat.max 0 (map C.row_bits P))
      (poly_initial X.encode (map (fun p => (p, false)) P))).
    { apply Forall_forall. intros q Hq.
      pose proof (poly_initial_units X.t X.encode (map (fun p => (p, false)) P)) as Hunit.
      destruct (proj1 (Forall_forall _ _) Hunit q Hq) as [Hlength Hunitq].
      rewrite length_map in Hlength. split; [exact Hlength|]. split; [exact Hunitq|].
      now apply poly_initial_coefficient_bits. }
    pose proof (poly_step_multiplier_bits _ _ _ _ Hinitial) as Hstep.
    destruct (proj1 (Forall_forall _ _) Hstep p Hin) as [Hlength Hbits].
    split; [exact Hlength|]. apply Forall_forall. intros m Hm.
    eapply Nat.le_trans; [exact (proj1 (Forall_forall _ _) Hbits m Hm)|].
    unfold ell. lia.
  Qed.

  (** Top has no repeated coefficients. *)
  Lemma normal_top : normal_s top.
  Proof.
    constructor.
  Qed.
  (** Join keeps rows free of repeated keys. *)
  Lemma normal_join : forall a b, normal_s a -> normal_s b -> normal_s (join a b).
  Proof.
    intros [|P] [|Q] HP HQ; cbn [normal_s join] in *; try assumption.
    apply Forall_app. split; apply Forall_forall; intros r Hin;
      apply filter_In in Hin as [Hin _].
    - exact (proj1 (Forall_forall _ _) HP r Hin).
    - exact (proj1 (Forall_forall _ _) HQ r Hin).
  Qed.
  (** Widening keeps rows free of repeated keys. *)
  Lemma normal_widen : forall p a b,
    normal_s a -> normal_s b -> normal_s (widen p a b).
  Proof.
    intros p [|P] [|Q] HP HQ; cbn [normal_s widen] in *.
    - exact I.
    - destruct (is_bot (Reached Q)); [exact I|exact HQ].
    - exact HP.
    - apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
      exact (proj1 (Forall_forall _ _) HP r Hin).
  Qed.
  (** Narrowing keeps rows free of repeated keys. *)
  Lemma normal_narrow : forall a b, normal_s a -> normal_s b -> normal_s (narrow a b).
  Proof.
    intros a b Ha Hb. exact Hb.
  Qed.
  (** Assignment normalizes its new rows. *)
  Lemma normal_assign : forall x e s, normal_s s -> normal_s (assign x e s).
  Proof.
    intros x e [|P] Hnormal; [exact I|]. unfold assign.
    destruct (F.lin_of e) as [[f wr]|]; [destruct wr|].
    - apply assign_linear_nodup.
    - apply havoc_rows_nodup.
    - apply havoc_rows_nodup.
  Qed.
  (** Havoc keeps rows free of repeated keys. *)
  Lemma normal_havoc : forall x s, normal_s s -> normal_s (havoc x s).
  Proof.
    intros x [|P] Hnormal; [exact I|]. apply havoc_rows_nodup.
  Qed.
  (** Assumption normalizes the rows it adds. *)
  Lemma normal_assume : forall g es s, normal_s s -> normal_s (assume g es s).
  Proof.
    intros g es [|P] Hnormal; [exact I|]. apply Forall_app. split.
    - apply assume_rows_nodup.
    - exact Hnormal.
  Qed.
  (** This widening has no repeated threshold search. *)
  Lemma F_wunits : forall s, wunits s = 0.
  Proof.
    reflexivity.
  Qed.
  Lemma fm_step_mults : forall P x r, In r (fm_elim x P) ->
    exists s, C.combine P (mults_of r) = Some s /\ lrel s = lrel (row_of r) /\
      rhs s = rhs (row_of r) /\
      forall v : X.t -> Z, eval_coef v (lhs s) = eval_coef v (lhs (row_of r)).
  Proof.
    apply fm_step_mults_checked.
  Qed.
  Lemma entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof.
    intros P c k Hresult. exact (proj1 (entail_cert_returned P c k Hresult)).
  Qed.
  (** Generated entailment certificates use rationally valid combinations. *)
  Lemma entail_cert_nocut : forall P c k, entail_cert P c = Some k -> cut k = false.
  Proof.
    intros P c k Hresult. exact (proj2 (entail_cert_returned P c k Hresult)).
  Qed.
  (** Elimination keeps rows free of repeated keys. *)
  Lemma normal_fm_elim : forall x P, normal P -> normal (map row_of (fm_elim x P)).
  Proof.
    intros x P Hnormal. apply Forall_map. apply fm_elim_nodup.
  Qed.
  Lemma fm_complete_Q : forall P c, lrel c = RLe -> entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  Proof.
    exact poly_failed_certificate_model_Q.
  Qed.
  Lemma fm_rows_le : forall x P, length (fm_elim x P) <= (length P)^2 / 4 + length P.
  Proof.
    intros x P. unfold fm_elim. rewrite length_map.
    pose proof (poly_step_rows X.t X.encode X.eqb x
      (poly_initial X.encode (map (fun r => (r, false)) P))) as Hrows.
    rewrite !poly_initial_length, !length_map in Hrows. exact Hrows.
  Qed.

  Lemma ell_fm_le : forall x P, normal P ->
    ell (map row_of (fm_elim x P)) <= 2 * ell P + 1.
  Proof.
    intros x P Hnormal.
    pose proof (poly_step_sizes x _ _ _ (poly_initial_sizes P Hnormal)) as Hstep.
    unfold fm_elim, ell. rewrite !map_map. cbn [row_of].
    assert (Hbits : fold_right Nat.max 0
      (map (fun r => C.row_bits (poly_constraint r))
        (poly_step X.encode X.eqb x
          (poly_initial X.encode (map (fun r => (r, false)) P)))) <=
      2 * fold_right Nat.max 0 (map C.row_bits P) + 1).
    { apply poly_max_bound; [lia|]. apply Forall_forall. intros r Hin.
      exact (proj1 (proj1 (Forall_forall _ _) Hstep r Hin)). }
    assert (Hkeys : fold_right Nat.max 0
      (map (fun r => C.row_key_bits (poly_constraint r))
        (poly_step X.encode X.eqb x
          (poly_initial X.encode (map (fun r => (r, false)) P)))) <=
      fold_right Nat.max 0 (map C.row_key_bits P)).
    { apply poly_max_bound; [lia|]. apply Forall_forall. intros r Hin.
      exact (proj2 (proj1 (Forall_forall _ _) Hstep r Hin)). }
    lia.
  Qed.

  Lemma subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof.
    apply subst_sat_checked.
  Qed.
  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof.
    reflexivity.
  Qed.
  Definition keep (P : list (lcons X.t)) (r : lcons X.t) : bool := keep_row P r.
  TimeFun keep.
  Definition entails (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match entail_cert P r with Some k => C.check_entails P r k | None => false end.
  Lemma F_leb_keep : forall a b, leb (Reached b) (Reached a) = forallb (keep b) a.
  Proof.
    reflexivity.
  Qed.
  Lemma F_widen_keep : forall p a b,
    widen p (Reached a) (Reached b) = Reached (filter (keep b) a).
  Proof.
    reflexivity.
  Qed.
  Lemma F_leb_split : forall a b, leb (Reached a) (Reached b) =
    forallb (fun r => match lrel r with
      | RLe => entails a r
      | REq => andb (entails a (LCons _ (lhs r) RLe (rhs r)))
          (entails a (LCons _ (map (fun p => (fst p, (- snd p)%Z)) (lhs r)) RLe
            (- rhs r)%Z))
      end) b.
  Proof.
    intros a b. unfold leb.
    assert (Hentails : forall r, entails_row a r = entails a r).
    { intro r. unfold entails_row, entails.
      destruct (entail_cert a r) as [k|] eqn:Hcertificate; [|reflexivity].
      symmetry. exact (proj1 (entail_cert_returned a r k Hcertificate)). }
    assert (Hhead : forall r, keep_row a r =
      match lrel r with
      | RLe => entails a r
      | REq => andb (entails a (LCons _ (lhs r) RLe (rhs r)))
          (entails a (LCons _ (map (fun p => (fst p, (- snd p)%Z)) (lhs r)) RLe
            (- rhs r)%Z))
      end).
    { intro r. unfold keep_row. destruct (lrel r); rewrite !Hentails; [|reflexivity].
      assert (Hnegative : poly_scale_coef (-1)%Z (lhs r) =
        map (fun p => (fst p, (- snd p)%Z)) (lhs r)).
      { unfold poly_scale_coef. apply map_ext. intros [x z]. cbn [fst snd]. f_equal. }
      unfold poly_negate. rewrite Hnegative. reflexivity. }
    induction b as [|r b IH]; cbn [forallb]; [reflexivity|].
    now rewrite Hhead, IH.
  Qed.
  (** State size charges all stored numeric data. *)
  Lemma lat_mono : forall m n, m <= n -> lat m <= lat n.
  Proof.
    exact poly_lattice_lat_mono.
  Qed.

  Lemma lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  Proof.
    exact poly_lattice_lat_size.
  Qed.

  Lemma T1_leb : forall a b,
    (T_leb a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    exact T_poly_leb_lattice.
  Qed.
  Lemma T1_join : forall a b,
    (T_join a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    exact T_poly_join_lattice.
  Qed.
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    exact T_poly_widen_lattice.
  Qed.
  Lemma T1_narrow : forall a b,
    (T_narrow a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof.
    intros a b. time_unfold T_narrow. unfold k_poly.
    change (1 * 1 <= poly_lattice_factor * N.of_nat (lat (mu a + mu b)))%N.
    apply N.mul_le_mono; [exact poly_lattice_factor_positive|apply poly_lattice_lat_positive].
  Qed.
  Lemma F_size : forall s, size s = lat (2 * mu s).
  Proof.
    reflexivity.
  Qed.
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat (terms s * (nell s + 1) +
      fmcost (n (prows s) + tsize e) (length (prows s) + 2) (n (prows s) + tsize e)
        (length (prows s) + 2) (nell s + F.bits_e e + 1)) + F.T_lin_of e)%N.
  Proof.
    intros e s. unfold range_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Lemma F_range_bits : forall e s, range_bits e s = range_work e s.
  Proof.
    reflexivity.
  Qed.
End PolyT.
