(** * Certified polyhedral states

    Fourier-Motzkin elimination tracks combinations of the input constraints.
    For example, eliminating x from x + y <= 3 and -x <= -1 gives y <= 2.
    Builds on: PolySig, LinCertSig and the concrete binary trie. *)
From Stdlib Require Import List ZArith NArith QArith Qfield Bool Lia Ring Psatz Wf_nat.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig PolySig.
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

  Definition candidate (P : list (lcons X.t)) (c : lcons X.t) (r : poly_row X.t)
      : option cert :=
    if poly_contradiction r then
      match poly_multipliers r with
      | sc :: ms =>
        let k := Cert ms (if C.check_empty P ms then 1%Z else sc) false in
        if C.check_entails P c k then Some k else None
      | nil => None
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
  Definition entail_cert (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    let input := (poly_negate c, true) :: map (fun r => (r, false)) P in
    find_certificate P c
      (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
        (poly_initial X.encode input)).

  Definition entails_row (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match entail_cert P r with Some k => C.check_entails P r k | None => false end.

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
      | Some (f, NoWrap) => Reached (assign_linear x f P)
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
    destruct (poly_contradiction r); [| discriminate].
    destruct (poly_multipliers r) as [|sc ms]; [discriminate |].
    destruct (C.check_entails P c
      (Cert ms (if C.check_empty P ms then 1%Z else sc) false)) eqn:Hcheck;
      [| discriminate].
    injection Hresult as Hsame. subst k. split; [exact Hcheck | reflexivity].
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

  (** Every produced entailment certificate is checked and is valid without cuts. *)
  Lemma entail_cert_returned : forall P c k, entail_cert P c = Some k ->
    C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c k Hresult. unfold entail_cert in Hresult.
    now apply find_certificate_returned in Hresult.
  Qed.

  (** Successful row inclusion retains every integer model of its input. *)
  Lemma entails_row_sound : forall P r v,
    entails_row P r = true -> Forall (sat v) P -> sat v r.
  Proof.
    intros P r v Hcheck Hmodels. unfold entails_row in Hcheck.
    destruct (entail_cert P r) as [k|]; [| discriminate].
    exact (C.check_entails_sound P r k Hcheck v Hmodels).
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
    { pose proof (proj1 Htracks) as Hadmissible. rewrite Hweights in Hadmissible.
      apply poly_admissible_cons in Hadmissible as [Hhead _]. apply Hhead. reflexivity. }
    destruct (C.check_empty P ms) eqn:Hempty.
    - assert (Hcheck : C.check_entails P c (Cert ms 1%Z false) = true).
      { apply C.check_entails_empty. exact Hempty. }
      exists (Cert ms 1%Z false). unfold candidate.
      now rewrite Hcontra, Hweights, Hempty, Hcheck.
    - assert (Hpositive : (0 < sc)%Z).
      { destruct (Z.eq_dec sc 0) as [Hzero|Hnonzero]; [|lia]. subst sc.
        pose proof (poly_zero_target_empty P c r ms Htracks Hstrict Hweights Hcontra).
        congruence. }
      pose proof (poly_positive_target_checked P c r sc ms
        Htarget Htracks Hweights Hpositive Hcontra) as Hcheck.
      exists (Cert ms sc false). unfold candidate.
      now rewrite Hcontra, Hweights, Hempty, Hcheck.
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
    lrel c = RLe -> entail_cert P c = None ->
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
    unfold entail_cert in Hnone. rewrite Hnone in Hfound. discriminate.
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
    lrel c = RLe -> entail_cert P c = None ->
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
  Lemma poly_failed_certificate_model_Q : forall P c,
    lrel c = RLe -> entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  Proof.
    intros P c Hrel Hnone.
    destruct (poly_run_model_lift (poly_variables X.encode (c :: P))
      (poly_initial X.encode ((poly_negate c, true) :: map (fun r => (r, false)) P))
      (fun _ => 0%Q) (poly_entailment_initial_nonstrict P c)
      (poly_entail_terminal_model_Q P c Hrel Hnone)) as [v Hmodels].
    exists v. now apply poly_entailment_initial_models_Q.
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

  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    destruct a; reflexivity.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    destruct a; reflexivity.
  Qed.
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
        pose proof (assign_linear_sound x f P (fun y => N.num (st y)) Hmodels) as Hpost.
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

Module PolyT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) <: POLY_ALL X L N F C.
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
  Definition k_poly : N := 1. (* STUB *)
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
  TimeFun candidate.
  TimeFun find_certificate.
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
  Definition c_lat : N := 1. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_lat * N.of_nat (size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Definition c_num : N := 1. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition c_poly : N := 1. (* STUB *)
  Lemma T_subst_le : forall x f r,
    (T_subst x f r <= c_poly * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fm_elim_le : forall x P, normal P ->
    (T_fm_elim x P <= c_poly * N.of_nat (((length P + 1)^2)%nat) *
      N.of_nat ((n P + length P + 1)%nat) * N.of_nat (((ell P + 1)^2)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_entail_cert_le : forall P c, normal P -> normal (c :: nil) ->
    (T_entail_cert P c <= c_poly *
      N.of_nat (fmcost (n P + length (lhs c)) (length P + 1)
        (n P + length (lhs c)) (length P + 1)
        (ell P + C.row_bits c + C.row_key_bits c)))%N.
  Proof. Admitted. (* STUB *)
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
  Definition k_cert : N := 1%N. (* STUB *)
  Lemma T_entail_cert_raw : forall P c,
    (T_entail_cert P c <= k_cert * N.of_nat
      (terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
       fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
         (length P + 1) (nell (Reached (c :: P)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_size : forall P c k, entail_cert P c = Some k ->
    (N.of_nat (C.csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (C.lsize c + C.cbits P (mults k) + 1)) <=
      k_cert * N.of_nat
        (terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
         fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
           (length P + 1) (nell (Reached (c :: P)))))%N.
  Proof. Admitted. (* STUB *)
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
    assert (Hhead : forall r, keep_row a r =
      match lrel r with
      | RLe => entails a r
      | REq => andb (entails a (LCons _ (lhs r) RLe (rhs r)))
          (entails a (LCons _ (map (fun p => (fst p, (- snd p)%Z)) (lhs r)) RLe
            (- rhs r)%Z))
      end).
    { intro r. unfold keep_row. destruct (lrel r); [|reflexivity].
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
    intros m n Hle. unfold lat. apply Nat.mul_le_mono; [lia|].
    apply Nat.add_le_mono; [apply Nat.add_le_mono|lia].
    - apply poly_fmcost_mono; lia.
    - now apply Nat.pow_le_mono_l.
  Qed.

  Lemma lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  Proof.
    intros a b. unfold size. destruct (Nat.le_ge_cases (mu a) (mu b)) as [Hle|Hle].
    - pose proof (lat_mono (mu a + mu b) (2 * mu b) ltac:(lia)). lia.
    - pose proof (lat_mono (mu a + mu b) (2 * mu a) ltac:(lia)). lia.
  Qed.

  Lemma T1_leb : forall a b,
    (T_leb a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_join : forall a b,
    (T_join a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_narrow : forall a b,
    (T_narrow a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
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
