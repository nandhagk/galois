(** * Linear certificate checking

    The checker combines admissible rows and compares their summed coefficients.
    For example, opposite occurrences of one variable cancel before comparison.
    Builds on: LinCertSig. *)

From Stdlib Require Import List ZArith QArith Lia Bool Lqa.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Trie.
From Galois.Relational Require Import LinForm LinCertSig.
Local Open Scope nat_scope.

(** Positive and negative contributions grow separately until the final subtraction. *)
Definition lc_add_signed (z : Z) (s : Z * Z) : Z * Z :=
  if (0 <=? z)%Z then (fst s + z, snd s)%Z else (fst s, snd s - z)%Z.

TimeFun lc_add_signed.

(** A partial combination retains raw terms and separate right-hand-side sums. *)
Record lc_sum (X : Type) := LCSum {
  lc_terms : list (X * Z);
  lc_sums : Z * Z;
  lc_equal : bool
}.

Arguments lc_terms {X} _.
Arguments lc_sums {X} _.
Arguments lc_equal {X} _.
TimeFun lc_terms.
TimeFun lc_sums.
TimeFun lc_equal.

Module LinCertCode (X : KEY_OPS) <: LINCERT_OPS X.
  Definition scale_terms (m : Z) (xs : list (X.t * Z)) : list (X.t * Z) :=
    map (fun p => (fst p, (m * snd p)%Z)) xs.

  Definition allowed (r : lcons X.t) (m : Z) : bool :=
    match lrel r with REq => true | RLe => (0 <=? m)%Z end.

  Definition equality_used (r : lcons X.t) (m : Z) : bool :=
    match lrel r with REq => true | RLe => (m =? 0)%Z end.

  (** The original traversal retains zero-coefficient occurrences as a specification. *)
  Fixpoint combine_rows_spec (P : list (lcons X.t)) (ms : list Z)
      : option (lc_sum X.t) :=
    match P, ms with
    | nil, nil => Some (LCSum _ nil (0%Z, 0%Z) true)
    | p :: ps, m :: ns =>
      if allowed p m then
        match combine_rows_spec ps ns with
        | Some s => Some (LCSum _ (scale_terms m (lhs p) ++ lc_terms s)
            (lc_add_signed (m * rhs p)%Z (lc_sums s))
            (equality_used p m && lc_equal s))
        | None => None
        end
      else None
    | _, _ => None
    end.

  (** A zero multiplier contributes no terms, sums or inequality provenance. *)
  Fixpoint combine_rows (P : list (lcons X.t)) (ms : list Z) : option (lc_sum X.t) :=
    match P, ms with
    | nil, nil => Some (LCSum _ nil (0%Z, 0%Z) true)
    | p :: ps, m :: ns =>
      if Z.eqb m 0 then combine_rows ps ns
      else if allowed p m then
        match combine_rows ps ns with
        | Some s => Some (LCSum _ (scale_terms m (lhs p) ++ lc_terms s)
            (lc_add_signed (m * rhs p)%Z (lc_sums s))
            (equality_used p m && lc_equal s))
        | None => None
        end
      else None
    | _, _ => None
    end.

  Definition finish_sum (s : lc_sum X.t) : lcons X.t :=
    LCons _ (lc_terms s) (if lc_equal s then REq else RLe)
      (fst (lc_sums s) - snd (lc_sums s))%Z.

  Definition combine (P : list (lcons X.t)) (ms : list Z) : option (lcons X.t) :=
    match combine_rows P ms with Some s => Some (finish_sum s) | None => None end.

  (** The original public result keeps zero occurrences in its term list. *)
  Definition combine_spec_value (P : list (lcons X.t)) (ms : list Z)
      : option (lcons X.t) :=
    match combine_rows_spec P ms with Some s => Some (finish_sum s) | None => None end.

  Definition insert_term (acc : PTrieCode.t (Z * Z)) (p : X.t * Z)
      : PTrieCode.t (Z * Z) :=
    let key := X.encode (fst p) in
    let previous := match PTrieCode.get key acc with
      | Some z => z | None => (0%Z, 0%Z) end in
    PTrieCode.set key (lc_add_signed (snd p) previous) acc.

  Definition gather (xs : list (X.t * Z)) : PTrieCode.t (Z * Z) :=
    fold_left insert_term xs PTrieCode.empty.

  Definition zero_entry (a : option (Z * Z)) (_ : option unit) : bool :=
    match a with None => true | Some z => (fst z =? snd z)%Z end.

  Definition linear_zero (xs : list (X.t * Z)) : bool :=
    PTrieCode.forall2b zero_entry (gather xs) (@PTrieCode.empty unit).

  Definition linear_equal (sc : Z) (xs ys : list (X.t * Z)) : bool :=
    linear_zero (xs ++ scale_terms (- sc)%Z ys).

  Definition empty_row (s : lcons X.t) : bool :=
    linear_zero (lhs s) &&
      match lrel s with
      | REq => negb (rhs s =? 0)%Z
      | RLe => (rhs s <? 0)%Z
      end.

  Definition check_empty (P : list (lcons X.t)) (ms : list Z) : bool :=
    match combine P ms with Some s => empty_row s | None => false end.

  Definition check_row (s c : lcons X.t) (k : cert) : bool :=
    (0 <? scale k)%Z && linear_equal (scale k) (lhs s) (lhs c) &&
      match lrel c, lrel s with
      | REq, REq => (rhs s =? scale k * rhs c)%Z
      | RLe, _ =>
        if cut k then (rhs s / scale k <=? rhs c)%Z
        else (rhs s <=? scale k * rhs c)%Z
      | REq, RLe => false
      end.

  (** The original checker is retained as the reference for cached gathering. *)
  Definition check_entails_spec (P : list (lcons X.t)) (c : lcons X.t) (k : cert) : bool :=
    match combine P (mults k) with
    | Some s => if empty_row s then true else check_row s c k
    | None => false
    end.

  (** A prepared coefficient trie avoids rebuilding the contradiction input. *)
  Definition empty_row_in (tr : PTrieCode.t (Z * Z)) (s : lcons X.t) : bool :=
    if PTrieCode.forall2b zero_entry tr (@PTrieCode.empty unit) then
      match lrel s with
      | REq => negb (rhs s =? 0)%Z
      | RLe => (rhs s <? 0)%Z
      end
    else false.

  (** Coefficient equality continues insertion from the already gathered source. *)
  Definition linear_equal_in (tr : PTrieCode.t (Z * Z)) (sc : Z)
      (ys : list (X.t * Z)) : bool :=
    PTrieCode.forall2b zero_entry
      (fold_left insert_term (scale_terms (-sc)%Z ys) tr) (@PTrieCode.empty unit).

  (** Scale and coefficient guards stop before the remaining row checks. *)
  Definition check_row_in (tr : PTrieCode.t (Z * Z)) (s c : lcons X.t) (k : cert) : bool :=
    if (0 <? scale k)%Z then
      if linear_equal_in tr (scale k) (lhs c) then
        match lrel c, lrel s with
        | REq, REq => (rhs s =? scale k * rhs c)%Z
        | RLe, _ =>
          if cut k then (rhs s / scale k <=? rhs c)%Z
          else (rhs s <=? scale k * rhs c)%Z
        | REq, RLe => false
        end
      else false
    else false.

  (** A successful combination shares one gather between both certificate checks. *)
  Definition check_entails_fast (P : list (lcons X.t)) (c : lcons X.t) (k : cert) : bool :=
    match combine P (mults k) with
    | Some s =>
      let tr := gather (lhs s) in
      if empty_row_in tr s then true else check_row_in tr s c k
    | None => false
    end.

  (** The public checker uses the shared coefficient trie. *)
  Definition check_entails (P : list (lcons X.t)) (c : lcons X.t) (k : cert) : bool :=
    check_entails_fast P c k.

End LinCertCode.

Module LinCert (X : KEY) <: LINCERT X.
  Include LinCertCode X.
  Include LINCERT_SPEC X.

  (** The cached contradiction check agrees with the original row test. *)
  Lemma empty_row_in_gather : forall s,
    empty_row_in (gather (lhs s)) s = empty_row s.
  Proof.
    intro s. unfold empty_row_in, empty_row, linear_zero.
    destruct (PTrieCode.forall2b zero_entry (gather (lhs s)) (@PTrieCode.empty unit));
      reflexivity.
  Qed.

  (** Continuing the fold equals gathering the concatenated occurrence list. *)
  Lemma linear_equal_in_gather : forall xs sc ys,
    linear_equal_in (gather xs) sc ys = linear_equal sc xs ys.
  Proof.
    intros xs sc ys. unfold linear_equal_in, linear_equal, linear_zero, gather.
    rewrite fold_left_app. reflexivity.
  Qed.

  (** The guarded row checker preserves the original Boolean result. *)
  Lemma check_row_in_gather : forall s c k,
    check_row_in (gather (lhs s)) s c k = check_row s c k.
  Proof.
    intros s c k. unfold check_row_in, check_row. rewrite linear_equal_in_gather.
    destruct (0 <? scale k)%Z, (linear_equal (scale k) (lhs s) (lhs c)); reflexivity.
  Qed.

  (** Sharing the gathered source preserves acceptance for every certificate. *)
  Lemma check_entails_fast_agrees : forall P c k,
    check_entails_fast P c k = check_entails_spec P c k.
  Proof.
    intros P c k. unfold check_entails_fast, check_entails_spec.
    destruct (combine P (mults k)) as [s|]; [|reflexivity].
    rewrite empty_row_in_gather, check_row_in_gather. reflexivity.
  Qed.

  (** The public checker preserves the retained reference computation. *)
  Lemma check_entails_agrees : forall P c k,
    check_entails P c k = check_entails_spec P c k.
  Proof.
    apply check_entails_fast_agrees.
  Qed.

  (** Omitting zero-weight rows never enlarges the certificate input measure. *)
  Lemma csize_nz_le : forall P ms, csize_nz P ms <= csize P ms.
  Proof.
    induction P as [|p ps IH]; intros [|m ns]; cbn [csize_nz csize]; try lia.
    specialize (IH ns). destruct (m =? 0)%Z; nia.
  Qed.
  (** Rational evaluation embeds each stored integer coefficient. *)
  Definition eval_coefQ (v : X.t -> Q) (xs : list (X.t * Z)) : Q :=
    fold_right (fun p q => (inject_Z (snd p) * v (fst p) + q)%Q) 0%Q xs.

  (** A head occurrence adds its coefficient exactly at its own key. *)
  Lemma coef_of_cons : forall x y a xs,
    coef_of x ((y, a) :: xs) =
      if X.eqb x y then (a + coef_of x xs)%Z else coef_of x xs.
  Proof.
    reflexivity.
  Qed.

  (** Concatenation adds the coefficients of both term lists. *)
  Lemma coef_of_app : forall x xs ys,
    coef_of x (xs ++ ys) = (coef_of x xs + coef_of x ys)%Z.
  Proof.
    intros x xs ys.
    induction xs as [|[y a] xs IH].
    - reflexivity.
    - cbn [app]. rewrite !coef_of_cons, IH.
      destruct (X.eqb x y); ring.
  Qed.

  (** Scaling every occurrence scales its total coefficient. *)
  Lemma coef_of_scale : forall x m xs,
    coef_of x (scale_terms m xs) = (m * coef_of x xs)%Z.
  Proof.
    intros x m xs.
    induction xs as [|[y a] xs IH].
    - change (0 = m * 0)%Z. ring.
    - change (coef_of x ((y, (m * a)%Z) :: scale_terms m xs) =
        (m * coef_of x ((y, a) :: xs))%Z).
      rewrite !coef_of_cons, IH. destruct (X.eqb x y); ring.
  Qed.

  (** Integer evaluation adds both sides of a concatenation. *)
  Lemma eval_coef_app : forall (v : X.t -> Z) xs ys,
    eval_coef v (xs ++ ys) = (eval_coef v xs + eval_coef v ys)%Z.
  Proof.
    intros v xs ys.
    induction xs as [|[x a] xs IH].
    - change (eval_coef v ys = 0 + eval_coef v ys)%Z. ring.
    - change (a * v x + eval_coef v (xs ++ ys) =
        (a * v x + eval_coef v xs) + eval_coef v ys)%Z.
      rewrite IH. ring.
  Qed.

  (** Integer evaluation commutes with scaling every coefficient. *)
  Lemma eval_coef_scale : forall m xs (v : X.t -> Z),
    eval_coef v (scale_terms m xs) = (m * eval_coef v xs)%Z.
  Proof.
    intros m xs v.
    induction xs as [|[x a] xs IH].
    - change (0 = m * 0)%Z. ring.
    - change ((m * a) * v x + eval_coef v (scale_terms m xs) =
        m * (a * v x + eval_coef v xs))%Z.
      rewrite IH. ring.
  Qed.

  (** Removing a key erases exactly that key's total coefficient. *)
  Lemma coef_of_filter : forall x y xs,
    coef_of y (filter (fun p => negb (X.eqb x (fst p))) xs) =
      if X.eqb y x then 0%Z else coef_of y xs.
  Proof.
    intros x y xs. induction xs as [|[z a] xs IH].
    - cbn [filter coef_of]. destruct (X.eqb y x); reflexivity.
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

  (** Separating one key preserves all of its repeated occurrences. *)
  Lemma eval_coef_split : forall x xs (v : X.t -> Z),
    eval_coef v xs =
      (coef_of x xs * v x +
       eval_coef v (filter (fun p => negb (X.eqb x (fst p))) xs))%Z.
  Proof.
    intros x xs v. induction xs as [|[y a] xs IH].
    - reflexivity.
    - rewrite coef_of_cons. cbn [filter fst].
      destruct (X.eqb_spec x y) as [Hxy|Hxy].
      + subst y.
        change (a * v x + eval_coef v xs = (a + coef_of x xs) * v x +
          eval_coef v (filter (fun p => negb (X.eqb x (fst p))) xs))%Z.
        rewrite IH. ring.
      + change (a * v y + eval_coef v xs = coef_of x xs * v x +
          (a * v y + eval_coef v (filter (fun p => negb (X.eqb x (fst p))) xs)))%Z.
        rewrite IH. ring.
  Qed.

  (** A term list with zero total coefficients evaluates to zero over integers. *)
  Lemma eval_coef_zero : forall xs (v : X.t -> Z),
    (forall x, coef_of x xs = 0%Z) -> eval_coef v xs = 0%Z.
  Proof.
    refine (well_founded_induction
      (well_founded_ltof _ (@length (X.t * Z))) _ _).
    intros xs IH v Hzero. destruct xs as [|[x a] xs].
    - reflexivity.
    - rewrite (eval_coef_split x ((x, a) :: xs) v), Hzero.
      rewrite Z.mul_0_l, Z.add_0_l. apply IH.
      + unfold ltof. cbn [filter fst length].
        destruct (X.eqb_spec x x) as [_|Hneq]; [|contradiction].
        cbn [negb]. pose proof
          (filter_length_le (fun p => negb (X.eqb x (fst p))) xs) as Hlength.
        lia.
      + intro y. rewrite coef_of_filter.
        destruct (X.eqb y x); [reflexivity|apply Hzero].
  Qed.

  (** Equal total coefficients give equal integer evaluations. *)
  Lemma eval_coef_ext : forall xs ys (v : X.t -> Z),
    (forall x, coef_of x xs = coef_of x ys) -> eval_coef v xs = eval_coef v ys.
  Proof.
    intros xs ys v Heq.
    assert (Hzero : forall x, coef_of x (xs ++ scale_terms (-1)%Z ys) = 0%Z).
    { intro x. rewrite coef_of_app, coef_of_scale, Heq. ring. }
    pose proof (eval_coef_zero _ v Hzero) as Heval.
    rewrite eval_coef_app, eval_coef_scale in Heval. lia.
  Qed.

  (** Rational evaluation adds both sides of a concatenation. *)
  Lemma eval_coef_app_Q : forall (v : X.t -> Q) xs ys,
    (fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 (xs ++ ys) ==
     fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 xs +
     fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 ys)%Q.
  Proof.
    intros v xs ys.
    change (eval_coefQ v (xs ++ ys) == eval_coefQ v xs + eval_coefQ v ys)%Q.
    induction xs as [|[x a] xs IH].
    - change (eval_coefQ v ys == 0 + eval_coefQ v ys)%Q. ring.
    - change (inject_Z a * v x + eval_coefQ v (xs ++ ys) ==
        (inject_Z a * v x + eval_coefQ v xs) + eval_coefQ v ys)%Q.
      setoid_rewrite IH. ring.
  Qed.

  (** Rational evaluation commutes with scaling every coefficient. *)
  Lemma eval_coef_scale_Q : forall m xs (v : X.t -> Q),
    (fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 (scale_terms m xs) ==
     inject_Z m * fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 xs)%Q.
  Proof.
    intros m xs v.
    change (eval_coefQ v (scale_terms m xs) == inject_Z m * eval_coefQ v xs)%Q.
    induction xs as [|[x a] xs IH].
    - change (0 == inject_Z m * 0)%Q. ring.
    - change (inject_Z (m * a) * v x + eval_coefQ v (scale_terms m xs) ==
        inject_Z m * (inject_Z a * v x + eval_coefQ v xs))%Q.
      rewrite inject_Z_mult. setoid_rewrite IH. ring.
  Qed.

  (** Separating one key also preserves rational evaluation. *)
  Lemma eval_coef_split_Q : forall x xs (v : X.t -> Q),
    (fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 xs ==
     inject_Z (coef_of x xs) * v x +
     fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0
       (filter (fun p => negb (X.eqb x (fst p))) xs))%Q.
  Proof.
    intros x xs v.
    change (eval_coefQ v xs == inject_Z (coef_of x xs) * v x +
      eval_coefQ v (filter (fun p => negb (X.eqb x (fst p))) xs))%Q.
    induction xs as [|[y a] xs IH].
    - change (0 == 0 * v x + 0)%Q. ring.
    - rewrite coef_of_cons. cbn [filter fst].
      destruct (X.eqb_spec x y) as [Hxy|Hxy].
      + subst y.
        change (inject_Z a * v x + eval_coefQ v xs ==
          inject_Z (a + coef_of x xs) * v x +
          eval_coefQ v (filter (fun p => negb (X.eqb x (fst p))) xs))%Q.
        rewrite inject_Z_plus. setoid_rewrite IH. ring.
      + change (inject_Z a * v y + eval_coefQ v xs ==
          inject_Z (coef_of x xs) * v x + (inject_Z a * v y +
          eval_coefQ v (filter (fun p => negb (X.eqb x (fst p))) xs)))%Q.
        setoid_rewrite IH. ring.
  Qed.

  (** A term list with zero total coefficients evaluates to zero over rationals. *)
  Lemma eval_coef_zero_Q : forall xs (v : X.t -> Q),
    (forall x, coef_of x xs = 0%Z) ->
    (fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 xs == 0)%Q.
  Proof.
    refine (well_founded_induction
      (well_founded_ltof _ (@length (X.t * Z))) _ _).
    intros xs IH v Hzero. destruct xs as [|[x a] xs].
    - reflexivity.
    - setoid_rewrite (eval_coef_split_Q x ((x, a) :: xs) v).
      rewrite Hzero.
      setoid_rewrite Qmult_0_l. setoid_rewrite Qplus_0_l. apply IH.
      + unfold ltof. cbn [filter fst length].
        destruct (X.eqb_spec x x) as [_|Hneq]; [|contradiction].
        cbn [negb]. pose proof
          (filter_length_le (fun p => negb (X.eqb x (fst p))) xs) as Hlength.
        lia.
      + intro y. rewrite coef_of_filter.
        destruct (X.eqb y x); [reflexivity|apply Hzero].
  Qed.

  (** Equal total coefficients give equal rational evaluations. *)
  Lemma eval_coef_ext_Q : forall xs ys (v : X.t -> Q),
    (forall x, coef_of x xs = coef_of x ys) ->
    (fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 xs ==
     fold_right (fun p q => inject_Z (snd p) * v (fst p) + q) 0 ys)%Q.
  Proof.
    intros xs ys v Heq.
    assert (Hzero : forall x, coef_of x (xs ++ scale_terms (-1)%Z ys) = 0%Z).
    { intro x. rewrite coef_of_app, coef_of_scale, Heq. ring. }
    pose proof (eval_coef_zero_Q _ v Hzero) as Heval.
    setoid_rewrite eval_coef_app_Q in Heval.
    setoid_rewrite eval_coef_scale_Q in Heval.
    change (eval_coefQ v xs + (-1) * eval_coefQ v ys == 0)%Q in Heval.
    change (eval_coefQ v xs == eval_coefQ v ys)%Q.
    apply (proj1 (Qplus_inj_r (eval_coefQ v xs) (eval_coefQ v ys)
      (- eval_coefQ v ys)%Q)).
    setoid_replace (eval_coefQ v ys + - eval_coefQ v ys)%Q with 0%Q by ring.
    setoid_replace (eval_coefQ v xs + - eval_coefQ v ys)%Q
      with (eval_coefQ v xs + (-1) * eval_coefQ v ys)%Q by ring.
    exact Heval.
  Qed.


  (** Separate signed sums still denote ordinary integer addition. *)
  Lemma add_signed_value : forall z s,
    (fst (lc_add_signed z s) - snd (lc_add_signed z s) = fst s - snd s + z)%Z.
  Proof.
    intros z [p n]. unfold lc_add_signed. cbn [fst snd].
    destruct (0 <=? z)%Z; cbn [fst snd]; ring.
  Qed.

  (** Only inequality rows restrict the sign of their weight. *)
  Lemma allowed_spec : forall p m,
    allowed p m = true <-> (lrel p = RLe -> (0 <= m)%Z).
  Proof.
    intros [xs r b] m. destruct r; cbn [allowed lrel].
    - split; [intros _ Hrel; discriminate|reflexivity].
    - rewrite Z.leb_le. tauto.
  Qed.

  (** Successful row traversal has exactly the required admissible weights. *)
  Lemma combine_rows_admissible : forall P ms s,
    combine_rows P ms = Some s -> admissible P ms.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hcombine;
      cbn [combine_rows] in Hcombine; try discriminate.
    - split; [reflexivity|constructor].
    - destruct (m =? 0)%Z eqn:Hzero.
      { apply Z.eqb_eq in Hzero. subst m.
        destruct (IH ns s Hcombine) as [Hlength Hweights].
        split; [cbn; congruence|constructor; [intros _; lia|exact Hweights]]. }
      destruct (allowed p m) eqn:Hallowed; [|discriminate].
      destruct (combine_rows ps ns) as [tail|] eqn:Htail; [|discriminate].
      destruct (IH ns tail Htail) as [Hlength Hweights].
      split; [cbn; congruence|constructor; [|exact Hweights]].
      now apply allowed_spec.
  Qed.

  (** Every admissible sequence produces a raw weighted sum. *)
  Lemma combine_rows_complete : forall P ms, admissible P ms ->
    exists s, combine_rows P ms = Some s.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] [Hlength Hweights];
      cbn in Hlength; try discriminate.
    - eexists. reflexivity.
    - inversion Hweights as [|p' m' ps' ns' Hallowed Htail]; subst.
      assert (Hallow : allowed p m = true) by (apply allowed_spec; exact Hallowed).
      destruct (IH ns) as [s Hsum]; [split; [lia|exact Htail]|].
      cbn [combine_rows]. destruct (m =? 0)%Z; rewrite ?Hallow, Hsum;
        eexists; reflexivity.
  Qed.

  (** The raw sum records the specified coefficients, bound and relation flag. *)
  Lemma combine_rows_values : forall P ms s, combine_rows P ms = Some s ->
    (forall x, coef_of x (lc_terms s) = comb_coef P ms x) /\
    (fst (lc_sums s) - snd (lc_sums s))%Z = comb_rhs P ms /\
    lc_equal s = comb_eq P ms.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hcombine;
      cbn [combine_rows] in Hcombine; try discriminate.
    - inversion Hcombine; subst. repeat split; reflexivity.
    - destruct (m =? 0)%Z eqn:Hzero.
      { apply Z.eqb_eq in Hzero. subst m.
        destruct (IH ns s Hcombine) as [Hcoef [Hrhs Hrel]].
        split.
        - intro x. rewrite Hcoef.
          change (comb_coef ps ns x = 0 * coef_of x (lhs p) + comb_coef ps ns x)%Z.
          ring.
        - split.
          + rewrite Hrhs.
            change (comb_rhs ps ns = 0 * rhs p + comb_rhs ps ns)%Z. ring.
          + rewrite Hrel. cbn [comb_eq List.combine forallb fst snd].
            destruct (lrel p); reflexivity. }
      destruct (allowed p m) eqn:Hallowed; [|discriminate].
      destruct (combine_rows ps ns) as [tail|] eqn:Htail; [|discriminate].
      inversion Hcombine; subst s.
      destruct (IH ns tail Htail) as [Hcoef [Hrhs Hrel]].
      cbn [lc_terms lc_sums lc_equal]. split.
      + intro x. rewrite coef_of_app, coef_of_scale, Hcoef. reflexivity.
      + split.
        * rewrite add_signed_value, Hrhs.
          change (comb_rhs ps ns + m * rhs p = m * rhs p + comb_rhs ps ns)%Z.
          ring.
        * rewrite Hrel. reflexivity.
  Qed.

  (** Skipping zero rows preserves failure, coefficients, sums and relation provenance. *)
  Lemma combine_rows_agrees : forall P ms,
    match combine_rows P ms, combine_rows_spec P ms with
    | Some s, Some original =>
      (forall x, coef_of x (lc_terms s) = coef_of x (lc_terms original)) /\
      lc_sums s = lc_sums original /\ lc_equal s = lc_equal original
    | None, None => True
    | _, _ => False
    end.
  Proof.
    induction P as [|p ps IH]; intros [|m ns]; cbn [combine_rows combine_rows_spec].
    - repeat split; reflexivity.
    - exact I.
    - exact I.
    - specialize (IH ns). destruct (m =? 0)%Z eqn:Hzero.
      + apply Z.eqb_eq in Hzero. subst m.
        assert (Hallowed : allowed p 0 = true) by (destruct p as [xs [] b]; reflexivity).
        assert (Hequal : equality_used p 0 = true)
          by (destruct p as [xs [] b]; reflexivity).
        rewrite Hallowed.
        destruct (combine_rows ps ns) as [s|], (combine_rows_spec ps ns) as [original|];
          try exact IH.
        destruct IH as [Hcoef [Hsums Hrel]].
        cbn [lc_terms lc_sums lc_equal]. split.
        * intro x. rewrite coef_of_app, coef_of_scale, Hcoef. ring.
        * split.
          -- rewrite Hsums, Z.mul_0_l. unfold lc_add_signed.
             destruct (lc_sums original) as [a b].
             change ((a, b) = (a + 0, b))%Z. now rewrite Z.add_0_r.
          -- rewrite Hequal, Hrel. reflexivity.
      + destruct (allowed p m); [|exact I].
        destruct (combine_rows ps ns) as [s|], (combine_rows_spec ps ns) as [original|];
          try exact IH.
        destruct IH as [Hcoef [Hsums Hrel]].
        cbn [lc_terms lc_sums lc_equal]. split.
        * intro x. rewrite !coef_of_app, Hcoef. reflexivity.
        * now rewrite Hsums, Hrel.
  Qed.

  (** The public result differs from its original only by zero-coefficient occurrences. *)
  Lemma combine_spec_value_agrees : forall P ms,
    match combine P ms, combine_spec_value P ms with
    | Some s, Some original =>
      (forall x, coef_of x (lhs s) = coef_of x (lhs original)) /\
      rhs s = rhs original /\ lrel s = lrel original
    | None, None => True
    | _, _ => False
    end.
  Proof.
    intros P ms. pose proof (combine_rows_agrees P ms) as Hagrees.
    unfold combine, combine_spec_value.
    destruct (combine_rows P ms) as [s|], (combine_rows_spec P ms) as [original|];
      try exact Hagrees.
    destruct Hagrees as [Hcoef [Hsums Hrel]].
    cbn [finish_sum lhs rhs lrel]. rewrite Hsums, Hrel. auto.
  Qed.

  (** A trie entry denotes its positive sum minus its negative sum. *)
  Definition sum_at (p : positive) (tr : PTrieCode.t (Z * Z)) : Z :=
    match PTrieCode.get p tr with Some z => (fst z - snd z)%Z | None => 0%Z end.

  (** Inserting a term changes only the coefficient of its own key. *)
  Lemma insert_term_value : forall x acc y a,
    sum_at (X.encode x) (insert_term acc (y, a)) =
      ((if X.eqb x y then a else 0) + sum_at (X.encode x) acc)%Z.
  Proof.
    intros x acc y a. destruct (X.eqb_spec x y) as [Heq|Hneq].
    - subst y. unfold insert_term, sum_at. cbn [fst snd].
      rewrite PTrie.get_set_same. rewrite add_signed_value.
      destruct (PTrieCode.get (X.encode x) acc) as [[p n]|]; cbn [fst snd]; ring.
    - unfold insert_term. cbn [fst snd]. unfold sum_at.
      rewrite PTrie.get_set_other; [ring|].
      intro Heq. apply Hneq. now apply X.encode_inj.
  Qed.

  (** Folding insertion adds every occurrence, including repeated keys. *)
  Lemma gather_value_from : forall xs acc x,
    sum_at (X.encode x) (fold_left insert_term xs acc) =
      (coef_of x xs + sum_at (X.encode x) acc)%Z.
  Proof.
    induction xs as [|[y a] xs IH]; intros acc x.
    - reflexivity.
    - cbn [fold_left]. rewrite IH, insert_term_value, coef_of_cons.
      destruct (X.eqb x y); ring.
  Qed.

  (** The gathered trie agrees with the total coefficient at each source key. *)
  Lemma gather_value : forall xs x, sum_at (X.encode x) (gather xs) = coef_of x xs.
  Proof.
    intros xs x. unfold gather. rewrite gather_value_from.
    unfold sum_at. rewrite PTrie.get_empty. ring.
  Qed.

  (** Insertion never creates a trie key outside the encoding image. *)
  Lemma insert_term_domain : forall acc y a,
    (forall p z, PTrieCode.get p acc = Some z -> exists x, X.encode x = p) ->
    forall p z, PTrieCode.get p (insert_term acc (y, a)) = Some z ->
      exists x, X.encode x = p.
  Proof.
    intros acc y a Hdomain p z Hget. unfold insert_term in Hget. cbn [fst snd] in Hget.
    destruct (Pos.eq_dec p (X.encode y)) as [Heq|Hneq].
    - exists y. symmetry. exact Heq.
    - rewrite PTrie.get_set_other in Hget by exact Hneq. now apply (Hdomain p z).
  Qed.

  (** Every present gathered key encodes a source variable. *)
  Lemma gather_domain : forall xs p z,
    PTrieCode.get p (gather xs) = Some z -> exists x, X.encode x = p.
  Proof.
    assert (Hfold : forall xs acc,
      (forall p z, PTrieCode.get p acc = Some z -> exists x, X.encode x = p) ->
      forall p z, PTrieCode.get p (fold_left insert_term xs acc) = Some z ->
        exists x, X.encode x = p).
    { induction xs as [|[y a] xs IH]; intros acc Hdomain; [exact Hdomain|].
      cbn [fold_left]. apply IH. now apply insert_term_domain. }
    intros xs. apply Hfold. intros p z Hget. rewrite PTrie.get_empty in Hget.
    discriminate.
  Qed.

  (** The zero test recognizes exactly the lists whose total coefficients vanish. *)
  Lemma linear_zero_spec : forall xs,
    linear_zero xs = true <-> forall x, coef_of x xs = 0%Z.
  Proof.
    intro xs. unfold linear_zero.
    rewrite PTrie.forall2b_spec by reflexivity. split.
    - intros Hzero x. specialize (Hzero (X.encode x)).
      rewrite <- gather_value. unfold sum_at.
      unfold zero_entry in Hzero.
      destruct (PTrieCode.get (X.encode x) (gather xs)) as [[p n]|]; [|reflexivity].
      cbn [fst snd] in *. apply Z.eqb_eq in Hzero. lia.
    - intros Hzero p. unfold zero_entry.
      destruct (PTrieCode.get p (gather xs)) as [[a b]|] eqn:Hget; [|reflexivity].
      destruct (gather_domain xs p (a, b) Hget) as [x Hencode].
      pose proof (gather_value xs x) as Hvalue.
      unfold sum_at in Hvalue. rewrite Hencode, Hget, Hzero in Hvalue.
      cbn [fst snd] in *. apply Z.eqb_eq. lia.
  Qed.

  (** Scaled coefficient comparison is exact even on unnormalized lists. *)
  Lemma linear_equal_spec : forall sc xs ys,
    linear_equal sc xs ys = true <->
      forall x, coef_of x xs = (sc * coef_of x ys)%Z.
  Proof.
    intros sc xs ys. unfold linear_equal. rewrite linear_zero_spec.
    split; intros H x; specialize (H x); rewrite coef_of_app, coef_of_scale in *; nia.
  Qed.

  (** One admissible weighted row preserves integer satisfaction of the partial sum. *)
  Lemma combine_cons_sat : forall p m s v,
    allowed p m = true -> sat v p -> sat v (finish_sum s) ->
    sat v (finish_sum (LCSum _ (scale_terms m (lhs p) ++ lc_terms s)
      (lc_add_signed (m * rhs p)%Z (lc_sums s)) (equality_used p m && lc_equal s))).
  Proof.
    intros p m s v Hallowed Hp Hs.
    unfold sat, finish_sum in *. cbn [lhs lrel rhs lc_terms lc_sums lc_equal] in *.
    rewrite eval_coef_app, eval_coef_scale, add_signed_value.
    unfold allowed, equality_used in *. destruct (lrel p); destruct (lc_equal s);
      cbn [andb] in *.
    - nia.
    - nia.
    - apply Z.leb_le in Hallowed. destruct (m =? 0)%Z eqn:Hzero; cbn [andb].
      + apply Z.eqb_eq in Hzero. nia.
      + nia.
    - apply Z.leb_le in Hallowed. destruct (m =? 0)%Z; cbn [andb]; nia.
  Qed.

  (** Successful combination of satisfied input rows is satisfied. *)
  Lemma combine_rows_sat : forall P ms s, combine_rows P ms = Some s ->
    forall v, Forall (sat v) P -> sat v (finish_sum s).
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hcombine v Hmodels;
      cbn [combine_rows] in Hcombine; try discriminate.
    - inversion Hcombine; subst. reflexivity.
    - destruct (m =? 0)%Z.
      { apply (IH ns s Hcombine v). now inversion Hmodels. }
      destruct (allowed p m) eqn:Hallowed; [|discriminate].
      destruct (combine_rows ps ns) as [tail|] eqn:Htail; [|discriminate].
      inversion Hcombine; subst s.
      inversion Hmodels as [|p' ps' Hp Hps]; subst.
      apply combine_cons_sat; [exact Hallowed|exact Hp|].
      exact (IH ns tail Htail v Hps).
  Qed.

  (** The exported combination retains every integer model of its input. *)
  Lemma combine_valid : forall P ms s, combine P ms = Some s ->
    forall v, Forall (sat v) P -> sat v s.
  Proof.
    intros P ms s Hcombine v Hmodels. unfold combine in Hcombine.
    destruct (combine_rows P ms) as [sum|] eqn:Hsum; [|discriminate].
    inversion Hcombine; subst s. exact (combine_rows_sat P ms sum Hsum v Hmodels).
  Qed.

  (** An accepted zero-left-hand-side contradiction has no integer model. *)
  Lemma empty_row_sound : forall s, empty_row s = true -> forall v, ~ sat v s.
  Proof.
    intros s Hempty v Hsat. unfold empty_row in Hempty.
    apply andb_true_iff in Hempty as [Hzero Hrhs].
    pose proof (proj1 (linear_zero_spec (lhs s)) Hzero) as Hcoef.
    pose proof (eval_coef_zero (lhs s) v Hcoef) as Hvalue.
    unfold sat in Hsat. destruct (lrel s).
    - apply negb_true_iff, Z.eqb_neq in Hrhs. congruence.
    - apply Z.ltb_lt in Hrhs. lia.
  Qed.

  (** Accepted scaled coefficients give the same scaled integer evaluation. *)
  Lemma linear_equal_eval : forall sc xs ys v, linear_equal sc xs ys = true ->
    eval_coef v xs = (sc * eval_coef v ys)%Z.
  Proof.
    intros sc xs ys v Heq.
    pose proof (proj1 (linear_equal_spec sc xs ys) Heq) as Hcoef.
    rewrite <- eval_coef_scale. apply eval_coef_ext.
    intro x. rewrite coef_of_scale. apply Hcoef.
  Qed.

  (** The checked bound follows from the weighted row, with floor division for integer cuts. *)
  Lemma check_row_sound : forall s c k, check_row s c k = true ->
    forall v, sat v s -> sat v c.
  Proof.
    intros s c k Hcheck v Hsat. unfold check_row in Hcheck.
    apply andb_true_iff in Hcheck as [Hleft Hrhs].
    apply andb_true_iff in Hleft as [Hscale Hcoef]. apply Z.ltb_lt in Hscale.
    pose proof (linear_equal_eval _ _ _ v Hcoef) as Heval.
    unfold sat in *. destruct (lrel c), (lrel s); try discriminate.
    - apply Z.eqb_eq in Hrhs. nia.
    - destruct (cut k).
      + apply Z.leb_le in Hrhs.
        pose proof (Z.div_mod (rhs s) (scale k) ltac:(lia)) as Hdiv.
        pose proof (Z.mod_pos_bound (rhs s) (scale k) Hscale) as Hmod. nia.
      + apply Z.leb_le in Hrhs. nia.
    - destruct (cut k).
      + apply Z.leb_le in Hrhs.
        pose proof (Z.div_mod (rhs s) (scale k) ltac:(lia)) as Hdiv.
        pose proof (Z.mod_pos_bound (rhs s) (scale k) Hscale) as Hmod. nia.
      + apply Z.leb_le in Hrhs. nia.
  Qed.

  (** Accepted certificates retain every integer model, including the contradiction case. *)
  Lemma check_entails_sound : forall P c k, check_entails P c k = true ->
    forall v, Forall (sat v) P -> sat v c.
  Proof.
    intros P c k Hcheck v Hmodels.
    rewrite check_entails_agrees in Hcheck. unfold check_entails_spec in Hcheck.
    destruct (combine P (mults k)) as [s|] eqn:Hsum; [|discriminate].
    pose proof (combine_valid P (mults k) s Hsum v Hmodels) as Hsat.
    destruct (empty_row s) eqn:Hempty.
    - exfalso. exact (empty_row_sound s Hempty v Hsat).
    - exact (check_row_sound s c k Hcheck v Hsat).
  Qed.
  (** One admissible weighted row preserves rational satisfaction of the partial sum. *)
  Lemma combine_cons_sat_Q : forall p m s v,
    allowed p m = true -> satQ v p -> satQ v (finish_sum s) ->
    satQ v (finish_sum (LCSum _ (scale_terms m (lhs p) ++ lc_terms s)
      (lc_add_signed (m * rhs p)%Z (lc_sums s)) (equality_used p m && lc_equal s))).
  Proof.
    intros p m s v Hallowed Hp Hs.
    pose proof (eval_coef_app_Q v (scale_terms m (lhs p)) (lc_terms s)) as Happ.
    pose proof (eval_coef_scale_Q m (lhs p) v) as Hscaled.
    unfold satQ, finish_sum in *.
    cbn [lhs lrel rhs lc_terms lc_sums lc_equal] in *.
    rewrite add_signed_value, inject_Z_plus, inject_Z_mult.
    unfold allowed, equality_used in *. destruct (lrel p); destruct (lc_equal s);
      cbn [andb] in *.
    - nra.
    - nra.
    - apply Z.leb_le in Hallowed. rewrite Zle_Qle in Hallowed.
      pose proof (Qmult_le_compat_r _ _ (inject_Z m) Hp Hallowed) as Hweighted.
      destruct (m =? 0)%Z eqn:Hzero; cbn [andb].
      + apply Z.eqb_eq in Hzero. subst m.
        change (eval_coefQ v (scale_terms 0 (lhs p) ++ lc_terms s) ==
          inject_Z (fst (lc_sums s) - snd (lc_sums s)) +
          inject_Z 0 * inject_Z (rhs p))%Q.
        change (eval_coefQ v (scale_terms 0 (lhs p)) ==
          inject_Z 0 * eval_coefQ v (lhs p))%Q in Hscaled.
        change (eval_coefQ v (scale_terms 0 (lhs p) ++ lc_terms s) ==
          eval_coefQ v (scale_terms 0 (lhs p)) + eval_coefQ v (lc_terms s))%Q in Happ.
        setoid_rewrite Happ. setoid_rewrite Hscaled. setoid_rewrite Hs. ring.
      + change (eval_coefQ v (scale_terms m (lhs p) ++ lc_terms s) <=
          inject_Z (fst (lc_sums s) - snd (lc_sums s)) +
          inject_Z m * inject_Z (rhs p))%Q.
        setoid_rewrite Happ. setoid_rewrite Hscaled. nra.
    - apply Z.leb_le in Hallowed. rewrite Zle_Qle in Hallowed.
      pose proof (Qmult_le_compat_r _ _ (inject_Z m) Hp Hallowed) as Hweighted.
      destruct (m =? 0)%Z; cbn [andb];
        change (eval_coefQ v (scale_terms m (lhs p) ++ lc_terms s) <=
          inject_Z (fst (lc_sums s) - snd (lc_sums s)) +
          inject_Z m * inject_Z (rhs p))%Q;
        setoid_rewrite Happ; setoid_rewrite Hscaled; nra.
  Qed.

  (** Successful combination of satisfied rows preserves every rational model. *)
  Lemma combine_rows_sat_Q : forall P ms s, combine_rows P ms = Some s ->
    forall v, Forall (satQ v) P -> satQ v (finish_sum s).
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hcombine v Hmodels;
      cbn [combine_rows] in Hcombine; try discriminate.
    - inversion Hcombine; subst. reflexivity.
    - destruct (m =? 0)%Z.
      { apply (IH ns s Hcombine v). now inversion Hmodels. }
      destruct (allowed p m) eqn:Hallowed; [|discriminate].
      destruct (combine_rows ps ns) as [tail|] eqn:Htail; [|discriminate].
      inversion Hcombine; subst s.
      inversion Hmodels as [|p' ps' Hp Hps]; subst.
      apply combine_cons_sat_Q; [exact Hallowed|exact Hp|].
      exact (IH ns tail Htail v Hps).
  Qed.

  (** The exported combination retains every rational model of its input. *)
  Lemma combine_valid_Q : forall P ms s, combine P ms = Some s ->
    forall v, Forall (satQ v) P -> satQ v s.
  Proof.
    intros P ms s Hcombine v Hmodels. unfold combine in Hcombine.
    destruct (combine_rows P ms) as [sum|] eqn:Hsum; [|discriminate].
    inversion Hcombine; subst s. exact (combine_rows_sat_Q P ms sum Hsum v Hmodels).
  Qed.

  (** An accepted zero-left-hand-side contradiction has no rational model. *)
  Lemma empty_row_sound_Q : forall s, empty_row s = true -> forall v, ~ satQ v s.
  Proof.
    intros s Hempty v Hsat. unfold empty_row in Hempty.
    apply andb_true_iff in Hempty as [Hzero Hrhs].
    pose proof (proj1 (linear_zero_spec (lhs s)) Hzero) as Hcoef.
    pose proof (eval_coef_zero_Q (lhs s) v Hcoef) as Hvalue.
    unfold satQ in Hsat. destruct (lrel s).
    - apply negb_true_iff, Z.eqb_neq in Hrhs.
      assert (Hz : (inject_Z (rhs s) == inject_Z 0)%Q).
      { transitivity (eval_coefQ v (lhs s)); [symmetry; exact Hsat|exact Hvalue]. }
      apply (proj1 (inject_Z_injective (rhs s) 0)) in Hz. contradiction.
    - apply Z.ltb_lt in Hrhs. rewrite Zlt_Qlt in Hrhs.
      setoid_rewrite Hvalue in Hsat. exact (Qlt_not_le _ _ Hrhs Hsat).
  Qed.

  (** Accepted scaled coefficients give the same scaled rational evaluation. *)
  Lemma linear_equal_eval_Q : forall sc xs ys (v : X.t -> Q),
    linear_equal sc xs ys = true ->
    (eval_coefQ v xs == inject_Z sc * eval_coefQ v ys)%Q.
  Proof.
    intros sc xs ys v Heq.
    pose proof (proj1 (linear_equal_spec sc xs ys) Heq) as Hcoef.
    transitivity (eval_coefQ v (scale_terms sc ys)).
    - apply eval_coef_ext_Q. intro x. rewrite coef_of_scale. apply Hcoef.
    - apply eval_coef_scale_Q.
  Qed.

  (** A cut-free checked bound follows over the rational numbers. *)
  Lemma check_row_sound_Q : forall s c k, check_row s c k = true -> cut k = false ->
    forall v, satQ v s -> satQ v c.
  Proof.
    intros s c k Hcheck Hcut v Hsat. unfold check_row in Hcheck.
    apply andb_true_iff in Hcheck as [Hleft Hrhs].
    apply andb_true_iff in Hleft as [Hscale Hcoef].
    apply Z.ltb_lt in Hscale. rewrite Zlt_Qlt in Hscale.
    change (0 < inject_Z (scale k))%Q in Hscale.
    assert (Hnonzero : ~ (inject_Z (scale k) == 0)%Q).
    { intro Hz. setoid_rewrite Hz in Hscale. exact (Qlt_irrefl _ Hscale). }
    pose proof (linear_equal_eval_Q _ _ _ v Hcoef) as Heval.
    unfold eval_coefQ in Heval. unfold satQ in *.
    destruct (lrel c), (lrel s); try discriminate.
    - apply Z.eqb_eq in Hrhs.
      apply (proj1 (Qmult_inj_l _ _ (inject_Z (scale k)) Hnonzero)).
      setoid_rewrite <- Heval. rewrite <- inject_Z_mult, <- Hrhs. exact Hsat.
    - rewrite Hcut in Hrhs. apply Z.leb_le in Hrhs.
      rewrite Zle_Qle, inject_Z_mult in Hrhs.
      apply (proj1 (Qmult_le_l _ _ (inject_Z (scale k)) Hscale)).
      setoid_rewrite <- Heval. setoid_rewrite Hsat. exact Hrhs.
    - rewrite Hcut in Hrhs. apply Z.leb_le in Hrhs.
      rewrite Zle_Qle, inject_Z_mult in Hrhs.
      apply (proj1 (Qmult_le_l _ _ (inject_Z (scale k)) Hscale)).
      setoid_rewrite <- Heval. exact (Qle_trans _ _ _ Hsat Hrhs).
  Qed.


  (** Certificates without integer cuts also entail their rational conclusion. *)
  Lemma check_entails_sound_rational : forall P c k,
    check_entails P c k = true -> cut k = false ->
    forall v, Forall (satQ v) P -> satQ v c.
  Proof.
    intros P c k Hcheck Hcut v Hmodels.
    rewrite check_entails_agrees in Hcheck. unfold check_entails_spec in Hcheck.
    destruct (combine P (mults k)) as [s|] eqn:Hsum; [|discriminate].
    pose proof (combine_valid_Q P (mults k) s Hsum v Hmodels) as Hsat.
    destruct (empty_row s) eqn:Hempty.
    - exfalso. exact (empty_row_sound_Q s Hempty v Hsat).
    - exact (check_row_sound_Q s c k Hcheck Hcut v Hsat).
  Qed.
  (** Accepted contradictions exclude every integer model. *)
  Lemma check_empty_sound : forall P ms, check_empty P ms = true ->
    forall v, ~ Forall (sat v) P.
  Proof.
    intros P ms Hempty v Hmodels. unfold check_empty in Hempty.
    destruct (combine P ms) as [s|] eqn:Hsum; [|discriminate].
    apply (empty_row_sound s Hempty v). exact (combine_valid P ms s Hsum v Hmodels).
  Qed.
  (** An accepted contradiction entails every conclusion. *)
  Lemma check_entails_empty : forall P c k,
    check_empty P (mults k) = true -> check_entails P c k = true.
  Proof.
    intros P c k Hempty.
    rewrite check_entails_agrees. unfold check_empty, check_entails_spec in *.
    destruct (combine P (mults k)) as [s|]; [now rewrite Hempty|discriminate].
  Qed.
  (** Admissible multipliers combine to the weighted sum of the rows. *)
  Lemma combine_spec : forall P ms, admissible P ms ->
    exists s, combine P ms = Some s /\
      (forall x, coef_of x (lhs s) = comb_coef P ms x) /\ rhs s = comb_rhs P ms /\
      lrel s = (if comb_eq P ms then REq else RLe).
  Proof.
    intros P ms Hadmissible.
    destruct (combine_rows_complete P ms Hadmissible) as [s Hsum].
    destruct (combine_rows_values P ms s Hsum) as [Hcoef [Hrhs Hrel]].
    exists (finish_sum s). split.
    - unfold combine. now rewrite Hsum.
    - cbn [finish_sum lhs rhs lrel]. split; [exact Hcoef|].
      split; [exact Hrhs|now rewrite Hrel].
  Qed.
  (** Combination succeeds only on admissible multipliers. *)
  Lemma combine_admissible : forall P ms s, combine P ms = Some s -> admissible P ms.
  Proof.
    intros P ms s Hcombine. unfold combine in Hcombine.
    destruct (combine_rows P ms) as [sum|] eqn:Hsum; [|discriminate].
    now apply (combine_rows_admissible P ms sum).
  Qed.
  (** Exact cut-free certificates are accepted. *)
  Lemma check_entails_complete : forall P c ms sc, admissible P ms -> (0 < sc)%Z ->
    (forall x, comb_coef P ms x = (sc * coef_of x (lhs c))%Z) ->
    match lrel c with
    | REq => comb_eq P ms = true /\ comb_rhs P ms = (sc * rhs c)%Z
    | RLe => (comb_rhs P ms <= sc * rhs c)%Z
    end ->
    check_entails P c (Cert ms sc false) = true.
  Proof.
    intros P c ms sc Hadmissible Hscale Hcoef Hbound.
    destruct (combine_spec P ms Hadmissible) as [s [Hsum [Hcoeff [Hrhs Hrel]]]].
    rewrite check_entails_agrees. unfold check_entails_spec. cbn [mults]. rewrite Hsum.
    destruct (empty_row s); [reflexivity|]. unfold check_row.
    cbn [scale cut]. apply andb_true_iff. split.
    - apply andb_true_iff. split; [now apply Z.ltb_lt|].
      apply linear_equal_spec. intro x. rewrite Hcoeff. apply Hcoef.
    - destruct (lrel c).
      + destruct Hbound as [Heq Hbound]. rewrite Heq in Hrel. rewrite Hrel.
        apply Z.eqb_eq. now rewrite Hrhs.
      + destruct (lrel s); apply Z.leb_le; now rewrite Hrhs.
  Qed.
  (** Rational contradictions are accepted. *)
  Lemma check_empty_complete : forall P ms, admissible P ms ->
    (forall x, comb_coef P ms x = 0%Z) ->
    (comb_rhs P ms < 0)%Z \/ (comb_eq P ms = true /\ comb_rhs P ms <> 0%Z) ->
    check_empty P ms = true.
  Proof.
    intros P ms Hadmissible Hcoef Hcontradiction.
    destruct (combine_spec P ms Hadmissible) as [s [Hsum [Hcoeff [Hrhs Hrel]]]].
    unfold check_empty. rewrite Hsum. unfold empty_row.
    apply andb_true_iff. split.
    - apply linear_zero_spec. intro x. rewrite Hcoeff. apply Hcoef.
    - rewrite Hrel, Hrhs. destruct (comb_eq P ms) eqn:Heq.
      + apply negb_true_iff, Z.eqb_neq. destruct Hcontradiction as [Hneg|[_ Hneq]]; lia.
      + apply Z.ltb_lt. destruct Hcontradiction as [Hneg|[Hfalse _]]; [exact Hneg|discriminate].
  Qed.
End LinCert.

Module LinCertT (X : KEY_T) <: LINCERT_ALL X.
  Include LinCert X.
  TimeFun coef_of.
  TimeFun comb_coef.
  TimeFun comb_rhs.
  TimeFun comb_eq.
  TimeFun scale_terms.
  TimeFun allowed.
  TimeFun equality_used.
  TimeFun combine_rows.
  TimeFun finish_sum.
  TimeFun combine.
  TimeFun insert_term.
  TimeFun gather.
  TimeFun zero_entry.
  TimeFun linear_zero.
  TimeFun linear_equal.
  TimeFun empty_row.
  TimeFun check_empty.
  TimeFun check_row.
  TimeFun empty_row_in.
  TimeFun linear_equal_in.
  TimeFun check_row_in.
  TimeFun check_entails_fast.
  TimeFun check_entails.
  (** The number of set bits pays for carry chains in nonnegative accumulation. *)
  Fixpoint lc_ones (p : positive) : N :=
    match p with
    | xI q => (lc_ones q + 1)%N
    | xO q => lc_ones q
    | xH => 1%N
    end.

  (** A positive integer has no more set bits than binary digits. *)
  Lemma lc_ones_le : forall p, (lc_ones p <= N.of_nat (Pos.size_nat p))%N.
  Proof.
    induction p as [p IH|p IH|]; time_cbn; lia.
  Qed.

  (** A successor pays for every carry by removing set bits. *)
  Lemma T_succ_ones : forall p,
    (Pos.T_succ p + lc_ones (Pos.succ p) <= lc_ones p + 2)%N.
  Proof.
    induction p as [p IH|p IH|]; time_unfold Pos.T_succ; time_cbn; lia.
  Qed.

  (** Addition charges the first operand's digits and the change of set-bit potential. *)
  Lemma T_add_ones_both : forall p q,
    (Pos.T_add p q + lc_ones (Pos.add p q) <=
      3 * N.of_nat (Pos.size_nat p) + lc_ones q + 3)%N /\
    (Pos.T_add_carry p q + lc_ones (Pos.add_carry p q) <=
      3 * N.of_nat (Pos.size_nat p) + lc_ones q + 3)%N.
  Proof.
    intro p. induction p as [p IH|p IH|]; intros [q|q|];
      time_unfold Pos.T_add; time_unfold Pos.T_add_carry; time_cbn;
      try specialize (IH q);
      try pose proof (T_succ_ones p); try pose proof (T_succ_ones q);
      try pose proof (lc_ones_le p); try pose proof (lc_ones_le q); lia.
  Qed.

  (** The two addition clocks are symmetric in their inputs. *)
  Lemma T_add_comm_both : forall p q,
    Pos.T_add p q = Pos.T_add q p /\
    Pos.T_add_carry p q = Pos.T_add_carry q p.
  Proof.
    intro p. induction p as [p IH|p IH|]; intros [q|q|];
      time_unfold Pos.T_add; time_unfold Pos.T_add_carry; time_cbn;
      try specialize (IH q); lia.
  Qed.

  (** The second operand can supply the charged digits of addition. *)
  Lemma T_add_ones_right : forall p q,
    (Pos.T_add p q + lc_ones (Pos.add p q) <=
      3 * N.of_nat (Pos.size_nat q) + lc_ones p + 3)%N.
  Proof.
    intros p q. rewrite (proj1 (T_add_comm_both p q)), (Pos.add_comm p q).
    exact (proj1 (T_add_ones_both q p)).
  Qed.

  (** Shift-and-add multiplication amortizes its internal carry chains. *)
  Lemma T_mul_ones : forall p q,
    (Pos.T_mul p q + lc_ones (Pos.mul p q) <=
      6 * N.of_nat (Pos.size_nat p) * (N.of_nat (Pos.size_nat q) + 1) + lc_ones q)%N.
  Proof.
    intro p. induction p as [p IH|p IH|]; intro q;
      time_unfold Pos.T_mul; time_cbn; try specialize (IH q).
    - pose proof (proj1 (T_add_ones_both q (xO (Pos.mul p q)))) as Hadd.
      time_cbn_all. nia.
    - nia.
    - nia.
  Qed.

  (** Positive multiplication is bilinear in operand bit lengths. *)
  Lemma T_pos_mul_bilinear : forall p q,
    (Pos.T_mul p q <=
      7 * N.of_nat (Pos.size_nat p) * (N.of_nat (Pos.size_nat q) + 1))%N.
  Proof.
    intros p q. pose proof (T_mul_ones p q) as Hmul.
    pose proof (lc_ones_le q) as Hones.
    pose proof (Pos.size_nat_pos p) as Hpositive. nia.
  Qed.

  (** Signed multiplication has the same bilinear bound with its sign dispatch. *)
  Lemma T_Z_mul_bilinear : forall x y,
    (Z.T_mul x y <=
      8 * N.of_nat (Z.size_nat x + 1) * N.of_nat (Z.size_nat y + 1))%N.
  Proof.
    intros [|p|p] [|q|q]; time_unfold Z.T_mul; time_cbn;
      try pose proof (T_pos_mul_bilinear p q); nia.
  Qed.


  (** The signed potential counts bits in the absolute value. *)
  Definition lc_ones_Z (z : Z) : N :=
    match z with
    | Z0 => 0%N
    | Zpos p => lc_ones p
    | Zneg p => lc_ones p
    end.

  (** The separate positive and negative sums carry separate potentials. *)
  Definition lc_pair_ones (s : Z * Z) : N :=
    (lc_ones_Z (fst s) + lc_ones_Z (snd s))%N.

  (** Adding a nonnegative operand charges its bits and the set-bit potential change. *)
  Lemma T_Z_add_nonnegative : forall x y, (0 <= x)%Z -> (0 <= y)%Z ->
    (Z.T_add x y + lc_ones_Z (x + y) <=
      4 * N.of_nat (Z.size_nat y + 1) + lc_ones_Z x)%N.
  Proof.
    intros [|p|p] [|q|q] Hx Hy; try lia;
      time_unfold Z.T_add; time_cbn;
      try pose proof (lc_ones_le q); try pose proof (T_add_ones_right p q); lia.
  Qed.

  (** Subtracting a nonpositive operand has the same amortized addition bound. *)
  Lemma T_Z_sub_nonpositive : forall x y, (0 <= x)%Z -> (y <= 0)%Z ->
    (Z.T_sub x y + lc_ones_Z (x - y) <=
      6 * N.of_nat (Z.size_nat y + 1) + lc_ones_Z x)%N.
  Proof.
    intros x y Hx Hy.
    pose proof (T_Z_add_nonnegative x (- y)%Z Hx ltac:(lia)) as Hadd.
    pose proof (Z.T_opp_le y) as Hopp.
    assert (Hsize : Z.size_nat (- y) = Z.size_nat y) by (destruct y; reflexivity).
    rewrite Hsize in Hadd. time_unfold Z.T_sub.
    change (lc_ones_Z (x - y)) with (lc_ones_Z (x + - y)). lia.
  Qed.

  (** Signed insertion preserves nonnegativity of the separate sums. *)
  Lemma lc_add_signed_nonnegative : forall z p n, (0 <= p)%Z -> (0 <= n)%Z ->
    (0 <= fst (lc_add_signed z (p, n)))%Z /\
    (0 <= snd (lc_add_signed z (p, n)))%Z.
  Proof.
    intros z p n Hp Hn. unfold lc_add_signed.
    destruct (0 <=? z)%Z eqn:Hz; cbn [fst snd].
    - apply Z.leb_le in Hz. lia.
    - apply Z.leb_gt in Hz. lia.
  Qed.

  (** Signed insertion pays only the new operand's bits after accounting for carries. *)
  Lemma T_lc_add_signed_ones : forall z p n, (0 <= p)%Z -> (0 <= n)%Z ->
    (T_lc_add_signed z (p, n) + lc_pair_ones (lc_add_signed z (p, n)) <=
      16 * N.of_nat (Z.size_nat z + 1) + lc_pair_ones (p, n))%N.
  Proof.
    intros z p n Hp Hn. pose proof (Z.T_leb_le 0 z) as Htest.
    destruct z as [|q|q].
    - pose proof (T_Z_add_nonnegative p 0 Hp ltac:(lia)) as Hadd.
      time_unfold T_lc_add_signed. unfold lc_pair_ones.
      time_simpl. time_cbn_all. lia.
    - pose proof (T_Z_add_nonnegative p (Zpos q) Hp ltac:(lia)) as Hadd.
      time_unfold T_lc_add_signed. unfold lc_pair_ones.
      time_simpl. time_cbn_all. lia.
    - pose proof (T_Z_sub_nonpositive n (Zneg q) Hn ltac:(lia)) as Hsub.
      time_unfold T_lc_add_signed. unfold lc_pair_ones.
      time_simpl. time_cbn_all. lia.
  Qed.


  (** Appending a one bit to a nonnegative double has constant cost. *)
  Lemma T_Z_add_double_one : forall q, (0 <= q)%Z ->
    (Z.T_add (2 * q) 1 <= 3)%N.
  Proof.
    intros [|p|p] Hq.
    - change (1 <= 3)%N. lia.
    - change (Z.T_add (Z.pos (xO p)) 1 <= 3)%N.
      time_unfold Z.T_add. time_unfold Pos.T_add. time_cbn. lia.
    - lia.
  Qed.

  (** Positive division charges numerator digits times denominator digits. *)
  Lemma T_Z_pos_div_bilinear : forall a b, (0 < b)%Z ->
    (Z.T_pos_div_eucl a b <=
      32 * N.of_nat (Pos.size_nat a) * (N.of_nat (Z.size_nat b) + 1))%N.
  Proof.
    intros a b Hb. induction a as [a IH|a IH|]; time_unfold Z.T_pos_div_eucl;
      cbn [Pos.size_nat].
    - destruct (Z.pos_div_eucl_sizes a b Hb) as (Hq0 & Hr0 & Hq & Hr).
      destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
      pose proof (Z.T_mul_two_le r). pose proof (Z.T_mul_two_le q).
      pose proof (T_Z_add_double_one r Hr0). pose proof (T_Z_add_double_one q Hq0).
      pose proof (Z.T_ltb_le (2 * r + 1) b). pose proof (Z.T_sub_le (2 * r + 1) b).
      pose proof (Z.size_nat_succ_double r Hr0).
      destruct (2 * r + 1 <? b)%Z; lia.
    - destruct (Z.pos_div_eucl_sizes a b Hb) as (Hq0 & Hr0 & Hq & Hr).
      destruct (Z.pos_div_eucl a b) as [q r]. cbn [fst snd] in *.
      pose proof (Z.T_mul_two_le r). pose proof (Z.T_mul_two_le q).
      pose proof (T_Z_add_double_one q Hq0).
      pose proof (Z.T_ltb_le (2 * r) b). pose proof (Z.T_sub_le (2 * r) b).
      pose proof (Z.size_nat_double r Hr0).
      destruct (2 * r <? b)%Z; lia.
    - pose proof (Z.T_leb_le 2 b). cbn [Z.size_nat Pos.size_nat] in *. lia.
  Qed.

  (** Correcting signs adds only a linear quotient/remainder cost. *)
  Lemma T_Z_div_eucl_bilinear : forall a b,
    (Z.T_div_eucl a b <=
      64 * (N.of_nat (Z.size_nat a) + 1) * (N.of_nat (Z.size_nat b) + 1))%N.
  Proof.
    intros [|a|a] [|b|b]; time_unfold Z.T_div_eucl; cbn [Z.size_nat];
      try lia;
      pose proof (T_Z_pos_div_bilinear a _ (eq_refl : (0 < Z.pos b)%Z));
      destruct (Z.pos_div_eucl_sizes a (Z.pos b) eq_refl) as (Hq0 & Hr0 & Hq & Hr);
      destruct (Z.pos_div_eucl a (Z.pos b)) as [q r]; cbn [fst snd Z.size_nat] in *;
      pose proof (Z.T_opp_le q); pose proof (Z.T_opp_le r);
      pose proof (Z.T_opp_le (q + 1)); pose proof (Z.T_add_le q 1);
      pose proof (Z.T_add_le (Z.pos b) r); pose proof (Z.T_add_le (Z.neg b) r);
      pose proof (Z.T_sub_le (Z.pos b) r);
      destruct r; cbn [Z.size_nat Pos.size_nat] in *; nia.
  Qed.

  (** Integer division has a bilinear bit-cost bound, including zero divisors. *)
  Lemma T_Z_div_bilinear : forall a b,
    (Z.T_div a b <=
      65 * N.of_nat (Z.size_nat a + 1) * N.of_nat (Z.size_nat b + 1))%N.
  Proof.
    intros a b. time_unfold Z.T_div.
    pose proof (T_Z_div_eucl_bilinear a b). time_cbn_all. nia.
  Qed.

  (** A positive sum uses at most the combined digits of its operands. *)
  Lemma lc_size_pos_add : forall p q,
    (Pos.size_nat (Pos.add p q) <= Pos.size_nat p + Pos.size_nat q)%nat.
  Proof.
    intros p q. apply Pos.size_nat_least.
    rewrite Pos2Nat.inj_add, Nat.pow_add_r.
    pose proof (Pos.size_nat_upper p). pose proof (Pos.size_nat_upper q).
    pose proof (Pos2Nat.is_pos p). pose proof (Pos2Nat.is_pos q). nia.
  Qed.

  (** Adding nonnegative integers uses at most the combined input digits. *)
  Lemma lc_size_add_nonnegative : forall x y, (0 <= x)%Z -> (0 <= y)%Z ->
    (Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y)%nat.
  Proof.
    intros [|p|p] [|q|q] Hx Hy; try lia; time_cbn; try lia.
    apply lc_size_pos_add.
  Qed.

  (** A product uses at most the combined digits of its two inputs. *)
  Lemma lc_size_mul : forall x y,
    (Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y)%nat.
  Proof.
    intros [|p|p] [|q|q]; time_cbn; try lia; apply Pos.size_nat_mul.
  Qed.

  (** Absolute value preserves the stored bit length. *)
  Lemma lc_size_abs : forall z, Z.size_nat (Z.abs z) = Z.size_nat z.
  Proof.
    intros [|p|p]; reflexivity.
  Qed.

  (** Subtracting two nonnegative sums uses at most their combined digits. *)
  Lemma lc_size_difference : forall p n, (0 <= p)%Z -> (0 <= n)%Z ->
    (Z.size_nat (p - n) <= Z.size_nat p + Z.size_nat n)%nat.
  Proof.
    intros p n Hp Hn.
    assert (Habs : (0 <= Z.abs (p - n) <= p + n)%Z).
    { split; [apply Z.abs_nonneg|apply Z.abs_le; lia]. }
    pose proof (Z.size_nat_mono _ _ Habs) as Hmono.
    rewrite lc_size_abs in Hmono.
    pose proof (lc_size_add_nonnegative p n Hp Hn). lia.
  Qed.

  (** Signed insertion increases combined accumulator digits by at most the new digits. *)
  Lemma lc_add_signed_size : forall z p n, (0 <= p)%Z -> (0 <= n)%Z ->
    (Z.size_nat (fst (lc_add_signed z (p, n))) +
     Z.size_nat (snd (lc_add_signed z (p, n))) <=
     Z.size_nat z + Z.size_nat p + Z.size_nat n)%nat.
  Proof.
    intros z p n Hp Hn. unfold lc_add_signed.
    destruct (0 <=? z)%Z eqn:Hz; cbn [fst snd].
    - apply Z.leb_le in Hz. pose proof (lc_size_add_nonnegative p z Hp Hz). lia.
    - apply Z.leb_gt in Hz.
      pose proof (lc_size_add_nonnegative n (-z)%Z Hn ltac:(lia)) as Hsize.
      assert (Hopp : Z.size_nat (-z) = Z.size_nat z) by (destruct z; reflexivity).
      rewrite Hopp in Hsize. change (Z.size_nat (n + -z)) with (Z.size_nat (n - z))
        in Hsize. lia.
  Qed.

  (** The row bit envelope includes its right-hand side. *)
  Lemma row_bits_rhs : forall p, (Z.size_nat (rhs p) <= row_bits p)%nat.
  Proof.
    intro p. unfold row_bits.
    induction (map (fun q : X.t * Z => Z.size_nat (snd q)) (lhs p)) as [|b bs IH].
    - reflexivity.
    - cbn [fold_right]. eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
  Qed.

  (** The row bit envelope includes every stored coefficient occurrence. *)
  Lemma row_bits_coefficient : forall p x a,
    In (x, a) (lhs p) -> (Z.size_nat a <= row_bits p)%nat.
  Proof.
    intros [xs r b] x a Hin. unfold row_bits. cbn [lhs rhs] in *.
    induction xs as [|[y c] xs IH]; [contradiction|].
    cbn [map fold_right snd] in *. destruct Hin as [Heq|Hin].
    - inversion Heq; subst. apply Nat.le_max_l.
    - eapply Nat.le_trans; [exact (IH Hin)|apply Nat.le_max_r].
  Qed.

  (** A list traversal needs callback bounds only on values that it visits. *)
  Lemma T_map_members : forall (A B : Type) (f : A -> B) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (ListDef.T_map f T_f xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold ListDef.T_map. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)).
      time_unfold ListDef.T_map. time_cbn. nia.
  Qed.

  (** Scaling visits each coefficient once and charges its multiplication. *)
  Lemma T_scale_terms_bounded : forall m xs b,
    (forall x a, In (x, a) xs -> (Z.size_nat a <= b)%nat) ->
    (T_scale_terms m xs <=
      16 * N.of_nat ((length xs + 1) * (Z.size_nat m + 1) * (b + 1)))%N.
  Proof.
    intros m xs b Hbits. time_unfold T_scale_terms.
    lazymatch goal with
    | |- context [ListDef.T_map ?f ?Tf xs] =>
      assert (Hmap : (ListDef.T_map f Tf xs <=
        (12 * N.of_nat ((Z.size_nat m + 1) * (b + 1)) + 1) *
        N.of_nat (length xs) + 1)%N);
      [ apply T_map_members; intros [x a] Hin;
        specialize (Hbits x a Hin); pose proof (T_Z_mul_bilinear m a);
        time_simpl; time_cbn_all; nia
      | nia ]
    end.
  Qed.

  (** A row's coefficient envelope bounds all of its scaling callbacks. *)
  Lemma T_scale_row : forall p m,
    (T_scale_terms m (lhs p) <=
      16 * N.of_nat ((length (lhs p) + 1) *
        (Z.size_nat m + 1) * (row_bits p + 1)))%N.
  Proof.
    intros p m. apply T_scale_terms_bounded. intros x a Hin.
    exact (row_bits_coefficient p x a Hin).
  Qed.

  (** Admissibility tests inspect only the multiplier's sign. *)
  Lemma T_allowed_le : forall p m, (T_allowed p m <= 6)%N.
  Proof.
    intros p m. time_unfold T_allowed. pose proof (Z.T_leb_le 0 m).
    destruct (lrel p); time_simpl; time_cbn_all; lia.
  Qed.

  (** Equality provenance tests charge at most the multiplier's digits. *)
  Lemma T_equality_used_le : forall p m,
    (T_equality_used p m <= N.of_nat (Z.size_nat m) + 3)%N.
  Proof.
    intros p m. time_unfold T_equality_used. pose proof (Z.T_eqb_le m 0).
    destruct (lrel p); time_simpl; time_cbn_all; lia.
  Qed.

  (** Every partial right-hand-side accumulator consists of two nonnegative sums. *)
  Lemma combine_rows_nonnegative : forall P ms s, combine_rows P ms = Some s ->
    (0 <= fst (lc_sums s))%Z /\ (0 <= snd (lc_sums s))%Z.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hsum;
      cbn [combine_rows] in Hsum; try discriminate.
    - inversion Hsum; cbn [lc_sums fst snd]; lia.
    - destruct (m =? 0)%Z; [exact (IH ns s Hsum)|].
      destruct (allowed p m); [|discriminate].
      destruct (combine_rows ps ns) as [u|] eqn:Hu; [|discriminate].
      inversion Hsum; subst s. cbn [lc_sums].
      specialize (IH ns u Hu). destruct (lc_sums u) as [a b].
      cbn [fst snd] in IH. apply lc_add_signed_nonnegative; tauto.
  Qed.

  (** Total input bit mass bounds both right-hand-side accumulators together. *)
  Lemma combine_rows_sums_size_nz : forall P ms s, combine_rows P ms = Some s ->
    (Z.size_nat (fst (lc_sums s)) + Z.size_nat (snd (lc_sums s)) <= csize_nz P ms)%nat.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hsum;
      cbn [combine_rows] in Hsum; try discriminate.
    - inversion Hsum. cbn [lc_sums fst snd csize_nz Z.size_nat]. lia.
    - cbn [csize_nz]. destruct (m =? 0)%Z.
      { specialize (IH ns s Hsum). lia. }
      destruct (allowed p m); [|discriminate].
      destruct (combine_rows ps ns) as [u|] eqn:Hu; [|discriminate].
      specialize (IH ns u Hu).
      pose proof (combine_rows_nonnegative ps ns u Hu) as [Ha Hb].
      inversion Hsum; subst s. cbn [lc_sums].
      destruct (lc_sums u) as [a b]. cbn [fst snd] in *.
      pose proof (lc_add_signed_size (m * rhs p) a b Ha Hb).
      pose proof (lc_size_mul m (rhs p)). pose proof (row_bits_rhs p). nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma combine_rows_sums_size : forall P ms s, combine_rows P ms = Some s ->
    (Z.size_nat (fst (lc_sums s)) + Z.size_nat (snd (lc_sums s)) <= csize P ms)%nat.
  Proof.
    intros P ms s Hsum.
    pose proof (combine_rows_sums_size_nz P ms s Hsum) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** Row combination carries the set-bit potential across its recursive sums. *)
  Lemma T_combine_rows_ones_nz : forall P ms,
    (T_combine_rows P ms +
      match combine_rows P ms with Some s => lc_pair_ones (lc_sums s) | None => 0 end <=
      96 * N.of_nat (csize_nz P ms + 1))%N.
  Proof.
    induction P as [|p ps IH]; intros [|m ns];
      time_unfold T_combine_rows; cbn [combine_rows csize_nz].
    - unfold lc_pair_ones, lc_ones_Z. time_cbn. lia.
    - time_cbn. lia.
    - time_cbn. lia.
    - specialize (IH ns). pose proof (Z.T_eqb_le m 0) as HzeroClock.
      destruct (m =? 0)%Z eqn:Hzero.
      { apply Z.eqb_eq in Hzero. subst m. time_cbn_all. lia. }
      pose proof (T_allowed_le p m) as Hallowed.
      destruct (allowed p m) eqn:Hallow; [|time_cbn; nia].
      destruct (combine_rows ps ns) as [s|] eqn:Hsum; [|time_cbn_all; nia].
      pose proof (combine_rows_nonnegative ps ns s Hsum) as [Ha Hb].
      pose proof (T_scale_row p m) as Hscale.
      pose proof (T_equality_used_le p m) as Hequal.
      pose proof (T_Z_mul_bilinear m (rhs p)) as Hmul.
      pose proof (lc_size_mul m (rhs p)) as Hbits.
      pose proof (row_bits_rhs p) as Hrhs.
      pose proof (Datatypes.T_app_le (scale_terms m (lhs p)) (lc_terms s)) as Happ.
      unfold scale_terms in Happ. rewrite length_map in Happ.
      destruct (lc_sums s) as [a b] eqn:Hsums.
      cbn [fst snd] in Ha, Hb.
      pose proof (T_lc_add_signed_ones (m * rhs p) a b Ha Hb) as Hadd.
      set (w := (length (lhs p) + 1) *
        (row_key_bits p + (Z.size_nat m + 1) * (row_bits p + 1))).
      assert (Hw : (1 <= w)%nat) by (unfold w; nia).
      assert (HzeroW : (Z.T_eqb m 0 <= N.of_nat w + 1)%N) by (unfold w; nia).
      assert (HscaleW : (T_scale_terms m (lhs p) <= 16 * N.of_nat w)%N)
        by (unfold w; nia).
      assert (HmulW : (Z.T_mul m (rhs p) <= 8 * N.of_nat w)%N)
        by (unfold w; nia).
      assert (HaddW : (T_lc_add_signed (m * rhs p) (a, b) +
        lc_pair_ones (lc_add_signed (m * rhs p) (a, b)) <=
        16 * N.of_nat w + lc_pair_ones (a, b))%N) by (unfold w; nia).
      assert (HequalW : (T_equality_used p m <= 4 * N.of_nat w)%N)
        by (unfold w; nia).
      assert (HappW : (Datatypes.T_app (scale_terms m (lhs p)) (lc_terms s) <=
        2 * N.of_nat w)%N) by (unfold w, scale_terms; nia).
      clear Hscale Hmul Hadd Hequal Happ Hbits Hrhs Ha Hb Hallow HzeroClock Hzero.
      cbn [lc_sums] in *. rewrite ?Hsums in *. clear Hsum Hsums.
      time_simpl. time_cbn_all. fold w. lia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma T_combine_rows_ones : forall P ms,
    (T_combine_rows P ms +
      match combine_rows P ms with Some s => lc_pair_ones (lc_sums s) | None => 0 end <=
      96 * N.of_nat (csize P ms + 1))%N.
  Proof.
    intros P ms.
    pose proof (T_combine_rows_ones_nz P ms) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** Finishing a combination subtracts its two stored right-hand-side sums once. *)
  Lemma T_finish_sum_le : forall s,
    (T_finish_sum s <= 3 * N.of_nat
      (Z.size_nat (fst (lc_sums s)) + Z.size_nat (snd (lc_sums s))) + 10)%N.
  Proof.
    intro s. time_unfold T_finish_sum.
    pose proof (Z.T_sub_le (fst (lc_sums s)) (snd (lc_sums s))).
    time_simpl. lia.
  Qed.

  (** Raw combination has linear cost in the certificate-weighted input size. *)
  Lemma T_combine_weighted_nz : forall P ms,
    (T_combine P ms <= 112 * N.of_nat (csize_nz P ms + 1))%N.
  Proof.
    intros P ms. pose proof (T_combine_rows_ones_nz P ms) as Hrows.
    time_unfold T_combine. destruct (combine_rows P ms) as [s|] eqn:Hsum.
    - pose proof (T_finish_sum_le s) as Hfinish.
      pose proof (combine_rows_sums_size_nz P ms s Hsum) as Hsize. nia.
    - nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma T_combine_weighted : forall P ms,
    (T_combine P ms <= 112 * N.of_nat (csize P ms + 1))%N.
  Proof.
    intros P ms.
    pose proof (T_combine_weighted_nz P ms) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** Magnitude is used only to prove binary-size bounds. *)
  Definition lc_magnitude (z : Z) : nat := Z.to_nat (Z.abs z).

  (** The magnitude of an integer is below its binary-size power of two. *)
  Lemma lc_magnitude_upper : forall z, lc_magnitude z < 2 ^ Z.size_nat z.
  Proof.
    intros [|p|p].
    - change (0 < 1). lia.
    - exact (Pos.size_nat_upper p).
    - exact (Pos.size_nat_upper p).
  Qed.

  (** A strict power-of-two bound bounds the number of binary digits. *)
  Lemma lc_size_least : forall z k, lc_magnitude z < 2 ^ k -> Z.size_nat z <= k.
  Proof.
    intros [|p|p] k Hbound; cbn [lc_magnitude Z.abs Z.to_nat Z.size_nat] in *;
      try lia; now apply Pos.size_nat_least.
  Qed.

  (** Magnitudes preserve multiplication. *)
  Lemma lc_magnitude_mul : forall x y,
    lc_magnitude (x * y) = lc_magnitude x * lc_magnitude y.
  Proof.
    intros x y. unfold lc_magnitude. rewrite Z.abs_mul.
    rewrite Z2Nat.inj_mul by apply Z.abs_nonneg. reflexivity.
  Qed.

  (** The magnitude of a sum is at most the sum of magnitudes. *)
  Lemma lc_magnitude_add : forall x y,
    lc_magnitude (x + y) <= lc_magnitude x + lc_magnitude y.
  Proof.
    intros x y. unfold lc_magnitude.
    rewrite <- Z2Nat.inj_add by apply Z.abs_nonneg.
    apply Z2Nat.inj_le; try apply Z.abs_nonneg; try lia.
  Qed.

  (** A product fits below the power for the sum of the operand widths. *)
  Lemma lc_product_upper : forall x y,
    lc_magnitude (x * y) < 2 ^ (Z.size_nat x + Z.size_nat y).
  Proof.
    intros x y. rewrite lc_magnitude_mul, Nat.pow_add_r.
    pose proof (lc_magnitude_upper x). pose proof (lc_magnitude_upper y). nia.
  Qed.

  (** A uniform magnitude bound charges a finite sum once per entry. *)
  Lemma lc_sum_magnitude : forall zs bound,
    Forall (fun z => lc_magnitude z <= bound) zs ->
    lc_magnitude (fold_right Z.add 0%Z zs) <= length zs * bound.
  Proof.
    intros zs bound Hbound. induction Hbound as [|z zs Hz Htail IH].
    - reflexivity.
    - cbn [fold_right length]. pose proof (lc_magnitude_add z (fold_right Z.add 0%Z zs)).
      nia.
  Qed.

  (** Every member is bounded by a maximum fold. *)
  Lemma lc_member_max : forall xs z, In z xs -> z <= fold_right Nat.max 0 xs.
  Proof.
    induction xs as [|x xs IH]; intros z Hin; cbn in Hin; [contradiction|].
    cbn [fold_right]. destruct Hin as [Heq|Hin]; [subst; apply Nat.le_max_l|].
    eapply Nat.le_trans; [exact (IH _ Hin)|apply Nat.le_max_r].
  Qed.

  (** Every natural number is strictly below its next binary logarithm power. *)
  Lemma lc_log_upper : forall n, n < 2 ^ (Nat.log2 n + 1).
  Proof.
    intros [|n]; [change (0 < 2); lia|].
    pose proof (Nat.log2_spec (S n) (Nat.lt_0_succ n)) as [_ Hupper].
    now replace (Nat.log2 (S n) + 1) with (S (Nat.log2 (S n))) by lia.
  Qed.

  (** Weighted right-hand sides fit the maximum product width and a row-count logarithm. *)
  Lemma comb_rhs_size : forall P ms, Z.size_nat (comb_rhs P ms) <= cbits P ms.
  Proof.
    intros P ms. unfold cbits.
    set (pairs := List.combine P ms).
    set (width := fold_right Nat.max 0
      (map (fun pm => Z.size_nat (snd pm) + row_bits (fst pm)) pairs)).
    apply lc_size_least. unfold comb_rhs.
    change (lc_magnitude (fold_right Z.add 0%Z
      (map (fun pm => (snd pm * rhs (fst pm))%Z) pairs)) <
      2 ^ (width + Nat.log2 (length P) + 1)).
    assert (Hrows : Forall (fun z => lc_magnitude z <= 2 ^ width)
      (map (fun pm => (snd pm * rhs (fst pm))%Z) pairs)).
    { apply Forall_forall. intros z Hin. apply in_map_iff in Hin as [[r m] [Heq Hin]].
      subst z. cbn [fst snd].
      pose proof (row_bits_rhs r) as Hbits.
      assert (Hwidth : Z.size_nat m + row_bits r <= width).
      { apply lc_member_max. apply in_map_iff. exists (r, m). auto. }
      eapply Nat.le_trans; [apply Nat.lt_le_incl, lc_product_upper|].
      apply Nat.pow_le_mono_r; lia. }
    pose proof (lc_sum_magnitude _ _ Hrows) as Hsum. rewrite length_map in Hsum.
    assert (Hlength : length pairs <= length P).
    { unfold pairs. rewrite length_combine. apply Nat.le_min_l. }
    pose proof (lc_log_upper (length P)) as Hlog.
    assert (Hpower : 0 < 2 ^ width) by (pose proof (Nat.pow_nonzero 2 width ltac:(lia)); lia).
    replace (width + Nat.log2 (length P) + 1) with
      (width + (Nat.log2 (length P) + 1)) by lia.
    rewrite Nat.pow_add_r. nia.
  Qed.

  (** A successful combination's right-hand side fits the declared certificate width. *)
  Lemma combine_rhs_size : forall P ms s, combine P ms = Some s ->
    Z.size_nat (rhs s) <= cbits P ms.
  Proof.
    intros P ms s Hcombine.
    pose proof (combine_admissible P ms s Hcombine) as Hadmissible.
    destruct (combine_spec P ms Hadmissible) as [r [Hr [_ [Hrhs _]]]].
    rewrite Hcombine in Hr. inversion Hr; subst r. rewrite Hrhs. apply comb_rhs_size.
  Qed.

  (** Each raw occurrence pays for its key, coefficient and list cell. *)
  Fixpoint lc_terms_weight (xs : list (X.t * Z)) : N :=
    match xs with
    | nil => 0
    | (x, a) :: ys => N.of_nat (Pos.size_nat (X.encode x) + Z.size_nat a + 1) +
        lc_terms_weight ys
    end%N.

  (** Concatenation preserves total occurrence weight. *)
  Lemma lc_terms_weight_app : forall xs ys,
    lc_terms_weight (xs ++ ys) = (lc_terms_weight xs + lc_terms_weight ys)%N.
  Proof.
    induction xs as [|[x a] xs IH]; intro ys;
      cbn [app lc_terms_weight]; rewrite ?IH; lia.
  Qed.

  (** A row's key envelope includes every stored key occurrence. *)
  Lemma row_key_bits_coefficient : forall p x a,
    In (x, a) (lhs p) -> (Pos.size_nat (X.encode x) <= row_key_bits p)%nat.
  Proof.
    intros [xs r b] x a Hin. unfold row_key_bits. cbn [lhs] in *.
    induction xs as [|[y c] xs IH]; [contradiction|].
    cbn [map fold_right fst] in *. destruct Hin as [Heq|Hin].
    - inversion Heq; subst. apply Nat.le_max_l.
    - eapply Nat.le_trans; [exact (IH Hin)|apply Nat.le_max_r].
  Qed.

  (** Coefficient scaling increases each occurrence only by the multiplier's bit length. *)
  Lemma lc_terms_weight_scale : forall m xs k b,
    (forall x a, In (x, a) xs ->
      (Pos.size_nat (X.encode x) <= k /\ Z.size_nat a <= b)%nat) ->
    (lc_terms_weight (scale_terms m xs) <=
      N.of_nat (length xs * (k + Z.size_nat m + b + 1)))%N.
  Proof.
    intros m xs. induction xs as [|[x a] xs IH]; intros k b Hbounds.
    - cbn [scale_terms map lc_terms_weight length]. lia.
    - destruct (Hbounds x a (or_introl eq_refl)) as [Hkey Hbits].
      specialize (IH k b ltac:(intros y z Hin; apply Hbounds; now right)).
      pose proof (lc_size_mul m a) as Hproduct.
      change (N.of_nat (Pos.size_nat (X.encode x) + Z.size_nat (m * a) + 1) +
        lc_terms_weight (scale_terms m xs) <=
        N.of_nat (S (length xs) * (k + Z.size_nat m + b + 1)))%N. nia.
  Qed.

  (** A scaled row's raw terms fit the row's contribution to certificate size. *)
  Lemma lc_terms_weight_scale_row : forall p m,
    (lc_terms_weight (scale_terms m (lhs p)) <=
      N.of_nat ((length (lhs p) + 1) *
        (row_key_bits p + (Z.size_nat m + 1) * (row_bits p + 1))))%N.
  Proof.
    intros p m.
    pose proof (lc_terms_weight_scale m (lhs p) (row_key_bits p) (row_bits p)
      ltac:(intros x a Hin; split; [now apply (row_key_bits_coefficient p x a)|
        now apply (row_bits_coefficient p x a)])) as Hscale. nia.
  Qed.

  (** Successful raw combinations retain at most the certificate's occurrence weight. *)
  Lemma combine_rows_terms_weight_nz : forall P ms s, combine_rows P ms = Some s ->
    (lc_terms_weight (lc_terms s) <= N.of_nat (csize_nz P ms))%N.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hsum;
      cbn [combine_rows] in Hsum; try discriminate.
    - inversion Hsum. cbn [lc_terms lc_terms_weight csize_nz]. lia.
    - cbn [csize_nz]. destruct (m =? 0)%Z.
      { specialize (IH ns s Hsum). nia. }
      destruct (allowed p m); [|discriminate].
      destruct (combine_rows ps ns) as [u|] eqn:Hu; [|discriminate].
      specialize (IH ns u Hu). inversion Hsum; subst s. cbn [lc_terms].
      rewrite lc_terms_weight_app. pose proof (lc_terms_weight_scale_row p m). nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma combine_rows_terms_weight : forall P ms s, combine_rows P ms = Some s ->
    (lc_terms_weight (lc_terms s) <= N.of_nat (csize P ms))%N.
  Proof.
    intros P ms s Hsum.
    pose proof (combine_rows_terms_weight_nz P ms s Hsum) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** The public combination retains the same raw occurrence weight. *)
  Lemma combine_terms_weight_nz : forall P ms s, combine P ms = Some s ->
    (lc_terms_weight (lhs s) <= N.of_nat (csize_nz P ms))%N.
  Proof.
    intros P ms s Hsum. unfold combine in Hsum.
    destruct (combine_rows P ms) as [u|] eqn:Hu; [|discriminate].
    inversion Hsum; subst s. cbn [finish_sum lhs].
    exact (combine_rows_terms_weight_nz P ms u Hu).
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma combine_terms_weight : forall P ms s, combine P ms = Some s ->
    (lc_terms_weight (lhs s) <= N.of_nat (csize P ms))%N.
  Proof.
    intros P ms s Hsum.
    pose proof (combine_terms_weight_nz P ms s Hsum) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** Total input bit mass also bounds the finished right-hand side. *)
  Lemma combine_rhs_coarse_size_nz : forall P ms s, combine P ms = Some s ->
    (Z.size_nat (rhs s) <= csize_nz P ms)%nat.
  Proof.
    intros P ms s Hsum. unfold combine in Hsum.
    destruct (combine_rows P ms) as [u|] eqn:Hu; [|discriminate].
    pose proof (combine_rows_nonnegative P ms u Hu) as [Ha Hb].
    pose proof (combine_rows_sums_size_nz P ms u Hu) as Hsize.
    inversion Hsum; subst s. cbn [finish_sum rhs].
    pose proof (lc_size_difference (fst (lc_sums u)) (snd (lc_sums u)) Ha Hb). lia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma combine_rhs_coarse_size : forall P ms s, combine P ms = Some s ->
    (Z.size_nat (rhs s) <= csize P ms)%nat.
  Proof.
    intros P ms s Hsum.
    pose proof (combine_rhs_coarse_size_nz P ms s Hsum) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** A proof-only sum accounts for every stored signed pair exactly once. *)
  Fixpoint lc_trie_sum_ne (f : Z * Z -> N) (n : trie_ne (Z * Z)) : N :=
    match n with
    | N001 r => lc_trie_sum_ne f r
    | N010 z => f z
    | N011 z r => f z + lc_trie_sum_ne f r
    | N100 l => lc_trie_sum_ne f l
    | N101 l r => lc_trie_sum_ne f l + lc_trie_sum_ne f r
    | N110 l z => lc_trie_sum_ne f l + f z
    | N111 l z r => lc_trie_sum_ne f l + f z + lc_trie_sum_ne f r
    end%N.

  (** The empty trie contributes zero to the stored-value sum. *)
  Definition lc_trie_sum (f : Z * Z -> N) (tr : PTrieCode.t (Z * Z)) : N :=
    match tr with
    | Empty => 0
    | Nodes n => lc_trie_sum_ne f n
    end%N.

  (** An absent binding contributes zero to the stored-value sum. *)
  Definition lc_option_sum (f : Z * Z -> N) (o : option (Z * Z)) : N :=
    match o with
    | None => 0
    | Some z => f z
    end%N.

  (** Rebuilding a canonical node preserves the sum of its three parts. *)
  Lemma lc_trie_sum_node : forall f l o r,
    lc_trie_sum f (PTrieCode.node l o r) =
      (lc_trie_sum f l + lc_option_sum f o + lc_trie_sum f r)%N.
  Proof.
    intros f [|l] [z|] [|r];
      cbn [PTrieCode.node lc_trie_sum lc_trie_sum_ne lc_option_sum]; lia.
  Qed.

  (** A trie sum decomposes into its left, root and right contributions. *)
  Lemma lc_trie_sum_parts : forall f tr,
    lc_trie_sum f tr =
      (lc_trie_sum f (PTrieCode.left tr) + lc_option_sum f (PTrieCode.value tr) +
        lc_trie_sum f (PTrieCode.right tr))%N.
  Proof.
    intros f [|n]; [reflexivity|]. destruct n;
      cbn [PTrieCode.left PTrieCode.value PTrieCode.right trie_left trie_value trie_right
        lc_trie_sum lc_trie_sum_ne lc_option_sum]; lia.
  Qed.

  (** Updating one key replaces precisely that key's contribution to the sum. *)
  Lemma lc_trie_sum_set : forall f key z tr,
    (lc_trie_sum f (PTrieCode.set key z tr) +
      lc_option_sum f (PTrieCode.get key tr) = lc_trie_sum f tr + f z)%N.
  Proof.
    intros f key. induction key as [key IH|key IH|]; intros z tr;
      pose proof (lc_trie_sum_parts f tr) as Hparts.
    - replace (PTrieCode.get (xI key) tr) with (PTrieCode.get key (PTrieCode.right tr))
        by exact (eq_sym (trie_get_xI key tr)).
      change (lc_trie_sum f (PTrieCode.node (PTrieCode.left tr) (PTrieCode.value tr)
        (PTrieCode.set key z (PTrieCode.right tr))) +
        lc_option_sum f (PTrieCode.get key (PTrieCode.right tr)) =
        lc_trie_sum f tr + f z)%N.
      rewrite lc_trie_sum_node. pose proof (IH z (PTrieCode.right tr)). lia.
    - replace (PTrieCode.get (xO key) tr) with (PTrieCode.get key (PTrieCode.left tr))
        by exact (eq_sym (trie_get_xO key tr)).
      change (lc_trie_sum f (PTrieCode.node (PTrieCode.set key z (PTrieCode.left tr))
        (PTrieCode.value tr) (PTrieCode.right tr)) +
        lc_option_sum f (PTrieCode.get key (PTrieCode.left tr)) =
        lc_trie_sum f tr + f z)%N.
      rewrite lc_trie_sum_node. pose proof (IH z (PTrieCode.left tr)). lia.
    - replace (PTrieCode.get xH tr) with (PTrieCode.value tr)
        by exact (eq_sym (trie_get_xH tr)).
      change (lc_trie_sum f (PTrieCode.node (PTrieCode.left tr) (Some z)
        (PTrieCode.right tr)) + lc_option_sum f (PTrieCode.value tr) =
        lc_trie_sum f tr + f z)%N.
      rewrite lc_trie_sum_node. change (lc_option_sum f (Some z)) with (f z). lia.
  Qed.

  (** A value fold adds the proof-only sum to its initial accumulator. *)
  Lemma lc_trie_sum_fold_ne : forall f n b,
    PTrieCode.fold_values_ne (fun acc z => (acc + f z)%N) n b =
      (b + lc_trie_sum_ne f n)%N.
  Proof.
    intros f n. induction n as
      [r IHr|z|z r IHr|l IHl|l IHl r IHr|l IHl z|l IHl z r IHr]; intro b;
      cbn [PTrieCode.fold_values_ne lc_trie_sum_ne]; rewrite ?IHl, ?IHr; lia.
  Qed.

  (** A value fold sums each stored contribution once. *)
  Lemma lc_trie_sum_fold : forall f tr b,
    PTrieCode.fold_values (fun acc z => (acc + f z)%N) tr b =
      (b + lc_trie_sum f tr)%N.
  Proof.
    intros f [|n] b; cbn [PTrieCode.fold_values lc_trie_sum]; [lia|].
    apply lc_trie_sum_fold_ne.
  Qed.

  (** Addition permits the list accumulator to be separated from its final sum. *)
  Lemma lc_sum_fold_left : forall f xs b,
    fold_left (fun acc p => (acc + f (snd p))%N) xs b =
      (b + fold_right N.add 0 (map (fun p : positive * (Z * Z) => f (snd p)) xs))%N.
  Proof.
    intros f xs. induction xs as [|p xs IH]; intro b;
      cbn [fold_left map fold_right]; rewrite ?IH; lia.
  Qed.

  (** Enumeration and the proof-only trie sum agree. *)
  Lemma lc_trie_sum_elements : forall f tr,
    lc_trie_sum f tr =
      fold_right N.add 0%N (map (fun p => f (snd p)) (PTrieCode.elements tr)).
  Proof.
    intros f tr.
    pose proof (PTrieT.fold_values_def (Z * Z) N
      (fun acc z => (acc + f z)%N) tr 0%N) as Hfold.
    rewrite lc_trie_sum_fold, lc_sum_fold_left in Hfold. lia.
  Qed.

  (** Every occupied signed accumulator has nonnegative components. *)
  Definition lc_trie_good (tr : PTrieCode.t (Z * Z)) : Prop :=
    forall key z, PTrieCode.get key tr = Some z ->
      (0 <= fst z)%Z /\ (0 <= snd z)%Z.

  (** Absent entries start from the nonnegative zero pair. *)
  Lemma lc_previous_nonnegative : forall tr key, lc_trie_good tr ->
    let previous := match PTrieCode.get key tr with Some z => z | None => (0%Z, 0%Z) end in
    (0 <= fst previous)%Z /\ (0 <= snd previous)%Z.
  Proof.
    intros tr key Hgood. destruct (PTrieCode.get key tr) as [z|] eqn:Hget.
    - exact (Hgood key z Hget).
    - cbn [fst snd]. lia.
  Qed.

  (** Inserting a coefficient preserves nonnegativity at every key. *)
  Lemma insert_term_good : forall tr p, lc_trie_good tr -> lc_trie_good (insert_term tr p).
  Proof.
    intros tr [x a] Hgood key z Hget. unfold insert_term in Hget. cbn [fst snd] in Hget.
    destruct (Pos.eq_dec key (X.encode x)) as [Heq|Hneq].
    - subst key. rewrite PTrie.get_set_same in Hget. inversion Hget; subst z.
      pose proof (lc_previous_nonnegative tr (X.encode x) Hgood) as Hprevious.
      destruct (match PTrieCode.get (X.encode x) tr with
        | Some w => w | None => (0%Z, 0%Z) end) as [p n].
      cbn [fst snd] in Hprevious. apply lc_add_signed_nonnegative; tauto.
    - rewrite PTrie.get_set_other in Hget by exact Hneq. exact (Hgood key z Hget).
  Qed.

  (** A stored value pays for both component widths and its occupied binding. *)
  Definition lc_pair_bits (z : Z * Z) : N :=
    N.of_nat (Z.size_nat (fst z) + Z.size_nat (snd z) + 1).

  (** A new contribution increases the stored width by at most its own width. *)
  Lemma lc_add_signed_bits : forall z s,
    (0 <= fst s)%Z -> (0 <= snd s)%Z ->
    (lc_pair_bits (lc_add_signed z s) <= N.of_nat (Z.size_nat z) + lc_pair_bits s)%N.
  Proof.
    intros z [p n] Hp Hn. cbn [fst snd] in Hp, Hn.
    pose proof (lc_add_signed_size z p n Hp Hn). unfold lc_pair_bits.
    cbn [fst snd]. lia.
  Qed.

  (** The signed accumulation clock accepts a pair-shaped invariant. *)
  Lemma T_lc_add_signed_pair : forall z s,
    (0 <= fst s)%Z -> (0 <= snd s)%Z ->
    (T_lc_add_signed z s + lc_pair_ones (lc_add_signed z s) <=
      16 * N.of_nat (Z.size_nat z + 1) + lc_pair_ones s)%N.
  Proof.
    intros z [p n] Hp Hn. exact (T_lc_add_signed_ones z p n Hp Hn).
  Qed.

  (** The zero default carries no set-bit potential. *)
  Lemma lc_previous_ones : forall tr key,
    lc_pair_ones (match PTrieCode.get key tr with Some z => z | None => (0%Z, 0%Z) end) =
      lc_option_sum lc_pair_ones (PTrieCode.get key tr).
  Proof.
    intros tr key. destruct (PTrieCode.get key tr); reflexivity.
  Qed.

  (** The zero default adds at most one new occupied binding. *)
  Lemma lc_previous_bits : forall tr key,
    (lc_pair_bits (match PTrieCode.get key tr with Some z => z | None => (0%Z, 0%Z) end) <=
      lc_option_sum lc_pair_bits (PTrieCode.get key tr) + 1)%N.
  Proof.
    intros tr key. destruct (PTrieCode.get key tr) as [z|].
    - change (lc_pair_bits z <= lc_pair_bits z + 1)%N. lia.
    - change (1 <= 0 + 1)%N. lia.
  Qed.

  (** Insertion increases total stored bit mass only by the incoming coefficient. *)
  Lemma insert_term_bits : forall tr x a, lc_trie_good tr ->
    (lc_trie_sum lc_pair_bits (insert_term tr (x, a)) <=
      lc_trie_sum lc_pair_bits tr + N.of_nat (Z.size_nat a + 1))%N.
  Proof.
    intros tr x a Hgood.
    pose proof (lc_previous_nonnegative tr (X.encode x) Hgood) as [Hp Hn].
    pose proof (lc_previous_bits tr (X.encode x)) as Hprevious.
    set (previous := match PTrieCode.get (X.encode x) tr with
      | Some z => z | None => (0%Z, 0%Z) end) in *.
    pose proof (lc_add_signed_bits a previous Hp Hn) as Hbits.
    pose proof (lc_trie_sum_set lc_pair_bits (X.encode x)
      (lc_add_signed a previous) tr) as Hset.
    change (lc_trie_sum lc_pair_bits (insert_term tr (x, a)) +
      lc_option_sum lc_pair_bits (PTrieCode.get (X.encode x) tr) =
      lc_trie_sum lc_pair_bits tr + lc_pair_bits (lc_add_signed a previous))%N in Hset.
    lia.
  Qed.

  (** Insertion charges newly allocated trie nodes and coefficient storage together. *)
  Lemma insert_term_storage : forall tr x a, lc_trie_good tr ->
    (N.of_nat (PTrie.nodes (insert_term tr (x, a))) +
      lc_trie_sum lc_pair_bits (insert_term tr (x, a)) <=
      N.of_nat (PTrie.nodes tr) + lc_trie_sum lc_pair_bits tr +
      N.of_nat (Pos.size_nat (X.encode x) + Z.size_nat a + 1))%N.
  Proof.
    intros tr x a Hgood. pose proof (insert_term_bits tr x a Hgood) as Hbits.
    pose proof (PTrie.nodes_set (Z * Z) (X.encode x)
      (lc_add_signed a (match PTrieCode.get (X.encode x) tr with
        | Some z => z | None => (0%Z, 0%Z) end)) tr) as Hnodes.
    change (PTrie.nodes (insert_term tr (x, a)) <=
      PTrie.nodes tr + Pos.size_nat (X.encode x))%nat in Hnodes. lia.
  Qed.

  (** Encoding and the two trie paths determine the per-occurrence insertion factor. *)
  Definition lc_insert_factor : N :=
    (2 * X.c_key + 4 * PTrieT.c_trie + 32)%N.

  (** A trie insertion pays for the new occurrence and the set-bit potential change. *)
  Lemma T_insert_term_ones : forall tr x a, lc_trie_good tr ->
    (T_insert_term tr (x, a) + lc_trie_sum lc_pair_ones (insert_term tr (x, a)) <=
      lc_insert_factor * N.of_nat (Pos.size_nat (X.encode x) + Z.size_nat a + 1) +
      lc_trie_sum lc_pair_ones tr)%N.
  Proof.
    intros tr x a Hgood.
    pose proof (lc_previous_nonnegative tr (X.encode x) Hgood) as [Hp Hn].
    pose proof (lc_previous_ones tr (X.encode x)) as Hprevious.
    set (previous := match PTrieCode.get (X.encode x) tr with
      | Some z => z | None => (0%Z, 0%Z) end) in *.
    pose proof (lc_trie_sum_set lc_pair_ones (X.encode x)
      (lc_add_signed a previous) tr) as Hset.
    change (lc_trie_sum lc_pair_ones (insert_term tr (x, a)) +
      lc_option_sum lc_pair_ones (PTrieCode.get (X.encode x) tr) =
      lc_trie_sum lc_pair_ones tr + lc_pair_ones (lc_add_signed a previous))%N in Hset.
    pose proof (X.T_encode_le x) as Hencode.
    pose proof (PTrieT.T_get_le (Z * Z) (X.encode x) tr) as Hget.
    pose proof (PTrieT.T_set_le (Z * Z) (X.encode x)
      (lc_add_signed a previous) tr) as Hput.
    pose proof (T_lc_add_signed_pair a previous Hp Hn) as Hadd.
    time_unfold T_insert_term. cbn [fst snd]. fold previous.
    unfold lc_insert_factor, X.bits in *. time_simpl. nia.
  Qed.

  (** Folding insertion preserves the signed-pair invariant. *)
  Lemma gather_from_good : forall xs tr, lc_trie_good tr ->
    lc_trie_good (fold_left insert_term xs tr).
  Proof.
    induction xs as [|p xs IH]; intros tr Hgood; cbn [fold_left].
    - exact Hgood.
    - apply IH, insert_term_good, Hgood.
  Qed.

  (** Folding insertion charges the total weight of raw occurrences. *)
  Lemma gather_from_storage : forall xs tr, lc_trie_good tr ->
    (N.of_nat (PTrie.nodes (fold_left insert_term xs tr)) +
      lc_trie_sum lc_pair_bits (fold_left insert_term xs tr) <=
      N.of_nat (PTrie.nodes tr) + lc_trie_sum lc_pair_bits tr + lc_terms_weight xs)%N.
  Proof.
    induction xs as [|[x a] xs IH]; intros tr Hgood; cbn [fold_left lc_terms_weight].
    - lia.
    - specialize (IH (insert_term tr (x, a)) (insert_term_good tr (x, a) Hgood)).
      pose proof (insert_term_storage tr x a Hgood). lia.
  Qed.

  (** The folding clock telescopes the set-bit potential across all insertions. *)
  Lemma T_gather_from_ones : forall xs tr, lc_trie_good tr ->
    (List.T_fold_left insert_term T_insert_term xs tr +
      lc_trie_sum lc_pair_ones (fold_left insert_term xs tr) <=
      (lc_insert_factor + 1) * lc_terms_weight xs + lc_trie_sum lc_pair_ones tr + 1)%N.
  Proof.
    induction xs as [|[x a] xs IH]; intros tr Hgood;
      time_unfold List.T_fold_left; cbn [fold_left lc_terms_weight].
    - lia.
    - specialize (IH (insert_term tr (x, a)) (insert_term_good tr (x, a) Hgood)).
      pose proof (T_insert_term_ones tr x a Hgood) as Hinsert. nia.
  Qed.

  (** The empty trie satisfies the signed-pair invariant. *)
  Lemma lc_empty_good : lc_trie_good (@PTrieCode.empty (Z * Z)).
  Proof.
    intros key z Hget. rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  (** Building the coefficient trie preserves nonnegative signed accumulators. *)
  Lemma gather_good : forall xs, lc_trie_good (gather xs).
  Proof.
    intro xs. apply gather_from_good, lc_empty_good.
  Qed.

  (** The final trie skeleton and stored widths fit the incoming occurrence weight. *)
  Lemma gather_storage : forall xs,
    (N.of_nat (PTrie.nodes (gather xs)) + lc_trie_sum lc_pair_bits (gather xs) <=
      lc_terms_weight xs)%N.
  Proof.
    intro xs. pose proof (gather_from_storage xs PTrieCode.empty lc_empty_good) as Hstorage.
    change (N.of_nat (PTrie.nodes (gather xs)) + lc_trie_sum lc_pair_bits (gather xs) <=
      N.of_nat 0 + 0 + lc_terms_weight xs)%N in Hstorage. lia.
  Qed.

  (** Trie construction has linear amortized cost in incoming occurrence weight. *)
  Lemma T_gather_weighted : forall xs,
    (T_gather xs <= (lc_insert_factor + 1) * lc_terms_weight xs + 3)%N.
  Proof.
    intro xs. pose proof (T_gather_from_ones xs PTrieCode.empty lc_empty_good) as Hfold.
    change (List.T_fold_left insert_term T_insert_term xs PTrieCode.empty +
      lc_trie_sum lc_pair_ones (gather xs) <=
      (lc_insert_factor + 1) * lc_terms_weight xs + 0 + 1)%N in Hfold.
    time_unfold T_gather.
    change (1 + List.T_fold_left insert_term T_insert_term xs PTrieCode.empty <=
      (lc_insert_factor + 1) * lc_terms_weight xs + 3)%N. lia.
  Qed.

  (** Comparing one occupied pair charges its stored bit mass. *)
  Lemma T_zero_entry_bits : forall z b,
    (T_zero_entry (Some z) b <= 4 * lc_pair_bits z)%N.
  Proof.
    intros z b. time_unfold T_zero_entry.
    pose proof (Z.T_eqb_le (fst z) (snd z)).
    unfold lc_pair_bits. time_simpl. lia.
  Qed.

  (** The zero-test callbacks together charge each stored value once. *)
  Lemma lc_zero_callbacks : forall tr,
    (fold_right N.add 0 (map (fun ka =>
      T_zero_entry (PTrieCode.get (fst ka) tr)
        (PTrieCode.get (fst ka) (@PTrieCode.empty unit))) (PTrieCode.elements tr)) <=
      4 * lc_trie_sum lc_pair_bits tr)%N.
  Proof.
    intro tr. rewrite lc_trie_sum_elements.
    assert (Hall : Forall (fun ka =>
      (T_zero_entry (PTrieCode.get (fst ka) tr)
        (PTrieCode.get (fst ka) (@PTrieCode.empty unit)) <=
        4 * lc_pair_bits (snd ka))%N) (PTrieCode.elements tr)).
    { apply Forall_forall. intros [key z] Hin. cbn [fst snd].
      apply PTrie.elements_spec in Hin. rewrite Hin. apply T_zero_entry_bits. }
    induction Hall as [|ka kas Hentry Htail IH]; cbn [map fold_right]; lia.
  Qed.

  (** The final trie comparison charges its skeleton and total stored bit mass. *)
  Lemma T_zero_trie : forall tr,
    (PTrieT.T_forall2b zero_entry T_zero_entry tr (@PTrieCode.empty unit) <=
      PTrieT.c_trie * (2 * N.of_nat (PTrie.nodes tr + 1) +
        4 * lc_trie_sum lc_pair_bits tr))%N.
  Proof.
    intro tr.
    pose proof (PTrieT.T_forall2b_sum_le (Z * Z) unit zero_entry T_zero_entry
      tr PTrieCode.empty) as Hcheck.
    change (PTrieT.elements (@PTrieCode.empty unit)) with
      (@nil (positive * unit)) in Hcheck.
    change (PTrieT.nodes (@PTrieCode.empty unit)) with 0%nat in Hcheck.
    change (T_zero_entry None None) with 1%N in Hcheck.
    cbn [map] in Hcheck. rewrite app_nil_r, map_map, Nat.add_0_r in Hcheck.
    pose proof (lc_zero_callbacks tr) as Hcallbacks. nia.
  Qed.

  (** The zero-check factor pays for construction and a single trie traversal. *)
  Definition lc_zero_factor : N := (lc_insert_factor + 4 * PTrieT.c_trie + 8)%N.

  (** Coefficient zero testing has linear cost in raw occurrence weight. *)
  Lemma T_linear_zero_weighted : forall xs,
    (T_linear_zero xs <= lc_zero_factor * (lc_terms_weight xs + 1))%N.
  Proof.
    intro xs. pose proof (T_gather_weighted xs) as Hbuild.
    pose proof (T_zero_trie (gather xs)) as Hcheck.
    pose proof (gather_storage xs) as Hstorage.
    time_unfold T_linear_zero.
    change (fun a b => T_zero_entry a b) with T_zero_entry.
    unfold lc_zero_factor. time_simpl. nia.
  Qed.

  (** Negation preserves an integer's stored bit length. *)
  Lemma lc_size_opp : forall z, Z.size_nat (-z) = Z.size_nat z.
  Proof.
    intros [|p|p]; reflexivity.
  Qed.

  (** Integer division adds at most one quotient digit under sign correction. *)
  Lemma lc_size_div : forall a b, (Z.size_nat (a / b) <= Z.size_nat a + 1)%nat.
  Proof.
    intros [|a|a] [|b|b]; unfold Z.div, Z.div_eucl; cbn beta iota zeta;
      try solve [cbn [Z.size_nat]; lia];
      destruct (Z.pos_div_eucl_sizes a (Z.pos b) eq_refl) as (Hq0 & Hr0 & Hq & Hr);
      destruct (Z.pos_div_eucl a (Z.pos b)) as [q r]; cbn [fst snd] in *;
      pose proof (lc_size_add_nonnegative q 1 Hq0 ltac:(lia)) as Hadd;
      destruct r; cbn [fst snd]; rewrite ?lc_size_opp;
      cbn [Z.size_nat Pos.size_nat] in *; lia.
  Qed.

  (** Every raw occurrence pays for its list cell. *)
  Lemma lc_terms_length : forall xs,
    (N.of_nat (length xs) <= lc_terms_weight xs)%N.
  Proof.
    induction xs as [|[x a] xs IH]; cbn [length lc_terms_weight]; lia.
  Qed.

  (** Row size includes the right-hand-side bit width and a constant unit. *)
  Lemma lsize_rhs : forall c, (Z.size_nat (rhs c) + 1 <= lsize c)%nat.
  Proof.
    intro c. pose proof (row_bits_rhs c). unfold lsize. nia.
  Qed.

  (** Scaling a conclusion charges its multiplier digits times the row size. *)
  Lemma T_scale_conclusion : forall sc c,
    (T_scale_terms sc (lhs c) <=
      16 * N.of_nat ((Z.size_nat sc + 1) * lsize c))%N.
  Proof.
    intros sc c. pose proof (T_scale_row c sc). unfold lsize. nia.
  Qed.

  (** Scaled conclusion occurrences fit the same multiplier-weighted row size. *)
  Lemma lc_terms_weight_conclusion : forall sc c,
    (lc_terms_weight (scale_terms sc (lhs c)) <=
      N.of_nat ((Z.size_nat sc + 1) * lsize c))%N.
  Proof.
    intros sc c. pose proof (lc_terms_weight_scale_row c sc). unfold lsize. nia.
  Qed.

  (** Linear equality charges both raw occurrence weights and conclusion scaling. *)
  Lemma T_linear_equal_weighted : forall sc xs c,
    (T_linear_equal sc xs (lhs c) <= (lc_zero_factor + 20) *
      (lc_terms_weight xs + N.of_nat ((Z.size_nat sc + 1) * lsize c) + 1))%N.
  Proof.
    intros sc xs c.
    pose proof (T_scale_conclusion (-sc)%Z c) as Hscale.
    pose proof (lc_terms_weight_conclusion (-sc)%Z c) as Hweight.
    rewrite lc_size_opp in Hscale, Hweight.
    pose proof (T_linear_zero_weighted (xs ++ scale_terms (-sc)%Z (lhs c))) as Hzero.
    rewrite lc_terms_weight_app in Hzero.
    assert (HzeroW : (T_linear_zero (xs ++ scale_terms (-sc)%Z (lhs c)) <=
      lc_zero_factor *
        (lc_terms_weight xs + N.of_nat ((Z.size_nat sc + 1) * lsize c) + 1))%N).
    { eapply N.le_trans; [exact Hzero|]. apply N.mul_le_mono_l. lia. }
    clear Hzero Hweight.
    pose proof (Datatypes.T_app_le xs (scale_terms (-sc)%Z (lhs c))) as Happ.
    pose proof (lc_terms_length xs) as Hlength. pose proof (Z.T_opp_le sc) as Hopp.
    time_unfold T_linear_equal. nia.
  Qed.

  (** Testing a row for contradiction charges its raw terms and right-hand-side width. *)
  Lemma T_empty_row_weighted : forall s,
    (T_empty_row s <= lc_zero_factor * (lc_terms_weight (lhs s) + 1) +
      N.of_nat (Z.size_nat (rhs s)) + 12)%N.
  Proof.
    intro s. pose proof (T_linear_zero_weighted (lhs s)) as Hzero.
    pose proof (Z.T_eqb_le (rhs s) 0) as Heq. pose proof (Z.T_ltb_le (rhs s) 0) as Hlt.
    time_unfold T_empty_row. destruct (lrel s); time_simpl; lia.
  Qed.

  (** A successful combination supplies a certificate-weighted contradiction test. *)
  Lemma T_empty_row_combined_nz : forall P ms s, combine P ms = Some s ->
    (T_empty_row s <= (lc_zero_factor + 13) * N.of_nat (csize_nz P ms + 1))%N.
  Proof.
    intros P ms s Hsum. pose proof (T_empty_row_weighted s) as Hrow.
    pose proof (combine_terms_weight_nz P ms s Hsum) as Hterms.
    assert (HtermsW : (lc_zero_factor * (lc_terms_weight (lhs s) + 1) <=
      lc_zero_factor * N.of_nat (csize_nz P ms + 1))%N).
    { apply N.mul_le_mono_l. lia. }
    pose proof (combine_rhs_coarse_size_nz P ms s Hsum) as Hrhs. nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma T_empty_row_combined : forall P ms s, combine P ms = Some s ->
    (T_empty_row s <= (lc_zero_factor + 13) * N.of_nat (csize P ms + 1))%N.
  Proof.
    intros P ms s Hsum.
    pose proof (T_empty_row_combined_nz P ms s Hsum) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.

  (** A checked row charges the conclusion and the incoming right-hand-side width. *)
  Lemma T_check_row_weighted : forall s c k b,
    (Z.size_nat (rhs s) <= b)%nat ->
    (T_check_row s c k <= (lc_zero_factor + 110) *
      (lc_terms_weight (lhs s) +
        N.of_nat ((Z.size_nat (scale k) + 1) * (lsize c + b + 1))))%N.
  Proof.
    intros s c k b Hbits.
    set (w := (lc_terms_weight (lhs s) +
      N.of_nat ((Z.size_nat (scale k) + 1) * (lsize c + b + 1)))%N).
    assert (Hw : (1 <= w)%N) by (unfold w; nia).
    pose proof (T_linear_equal_weighted (scale k) (lhs s) c) as Hequal.
    assert (HequalW : (T_linear_equal (scale k) (lhs s) (lhs c) <=
      (lc_zero_factor + 20) * w)%N).
    { eapply N.le_trans; [exact Hequal|]. apply N.mul_le_mono_l. unfold w. nia. }
    pose proof (T_Z_mul_bilinear (scale k) (rhs c)) as Hmul.
    pose proof (lsize_rhs c) as Hcsize.
    assert (HmulW : (Z.T_mul (scale k) (rhs c) <= 8 * w)%N)
      by (clear -Hmul Hcsize; unfold w; nia).
    pose proof (T_Z_div_bilinear (rhs s) (scale k)) as Hdiv.
    assert (HdivW : (Z.T_div (rhs s) (scale k) <= 65 * w)%N)
      by (clear -Hdiv Hbits; unfold w; nia).
    pose proof (lc_size_div (rhs s) (scale k)) as Hquotient.
    pose proof (Z.T_leb_le (rhs s / scale k) (rhs c)) as Hcut.
    assert (HcutW : (Z.T_leb (rhs s / scale k) (rhs c) <= 5 * w)%N)
      by (clear -Hcut Hquotient Hbits; unfold w; nia).
    pose proof (Z.T_eqb_le (rhs s) (scale k * rhs c)) as Heq.
    pose proof (Z.T_leb_le (rhs s) (scale k * rhs c)) as Hle.
    assert (HeqW : (Z.T_eqb (rhs s) (scale k * rhs c) <= 5 * w)%N)
      by (clear -Heq Hbits; unfold w; nia).
    assert (HleW : (Z.T_leb (rhs s) (scale k * rhs c) <= 5 * w)%N)
      by (clear -Hle Hbits; unfold w; nia).
    pose proof (Z.T_ltb_le 0 (scale k)) as Hpositive.
    change (Z.T_ltb 0 (scale k) <= 4)%N in Hpositive.
    clear Hequal Hmul Hcsize Hdiv Hquotient Hcut Heq Hle Hbits.
    time_unfold T_check_row. fold w. destruct (lrel c), (lrel s).
    - time_simpl. nia.
    - time_simpl. nia.
    - destruct (cut k); time_simpl; nia.
    - destruct (cut k); time_simpl; nia.
  Qed.

  (** The cached contradiction test charges one trie scan and the bound width. *)
  Lemma T_empty_row_in_weighted : forall s,
    (T_empty_row_in (gather (lhs s)) s <=
      4 * PTrieT.c_trie * (lc_terms_weight (lhs s) + 1) +
      N.of_nat (Z.size_nat (rhs s)) + 12)%N.
  Proof.
    intro s. pose proof (T_zero_trie (gather (lhs s))) as Hzero.
    pose proof (gather_storage (lhs s)) as Hstorage.
    pose proof (Z.T_eqb_le (rhs s) 0) as Heq.
    pose proof (Z.T_ltb_le (rhs s) 0) as Hlt.
    time_unfold T_empty_row_in.
    change (fun a b => T_zero_entry a b) with T_zero_entry.
    destruct (PTrieCode.forall2b zero_entry (gather (lhs s)) (@PTrieCode.empty unit));
      destruct (lrel s); time_simpl; nia.
  Qed.

  (** A combination supplies the nonzero certificate bound for its cached zero test. *)
  Lemma T_empty_row_in_combined_nz : forall P ms s, combine P ms = Some s ->
    (T_empty_row_in (gather (lhs s)) s <=
      (4 * PTrieT.c_trie + 13) * N.of_nat (csize_nz P ms + 1))%N.
  Proof.
    intros P ms s Hsum. pose proof (T_empty_row_in_weighted s) as Hrow.
    pose proof (combine_terms_weight_nz P ms s Hsum) as Hterms.
    pose proof (combine_rhs_coarse_size_nz P ms s Hsum) as Hrhs. nia.
  Qed.

  (** Initial gathering and continuation share the insertion potential. *)
  Lemma T_linear_equal_in_weighted : forall sc xs c,
    (T_gather xs + T_linear_equal_in (gather xs) sc (lhs c) <=
      (lc_zero_factor + 20) *
      (lc_terms_weight xs + N.of_nat ((Z.size_nat sc + 1) * lsize c) + 1))%N.
  Proof.
    intros sc xs c.
    pose proof (T_scale_conclusion (-sc)%Z c) as Hscale.
    pose proof (lc_terms_weight_conclusion (-sc)%Z c) as Hweight.
    rewrite lc_size_opp in Hscale, Hweight.
    pose proof (T_gather_from_ones xs PTrieCode.empty lc_empty_good) as Hfirst.
    change (List.T_fold_left insert_term T_insert_term xs PTrieCode.empty +
      lc_trie_sum lc_pair_ones (gather xs) <=
      (lc_insert_factor + 1) * lc_terms_weight xs + 0 + 1)%N in Hfirst.
    pose proof (T_gather_from_ones (scale_terms (-sc)%Z (lhs c))
      (gather xs) (gather_good xs)) as Hrest.
    pose proof (gather_from_storage (scale_terms (-sc)%Z (lhs c))
      (gather xs) (gather_good xs)) as Hrest_storage.
    pose proof (gather_storage xs) as Hfirst_storage.
    pose proof (T_zero_trie
      (fold_left insert_term (scale_terms (-sc)%Z (lhs c)) (gather xs))) as Hzero.
    assert (HfoldW :
      (List.T_fold_left insert_term T_insert_term xs PTrieCode.empty +
        List.T_fold_left insert_term T_insert_term (scale_terms (-sc)%Z (lhs c))
          (gather xs) <= (lc_insert_factor + 1) *
        (lc_terms_weight xs + N.of_nat ((Z.size_nat sc + 1) * lsize c)) + 2)%N) by nia.
    assert (HzeroW :
      (PTrieT.T_forall2b zero_entry T_zero_entry
        (fold_left insert_term (scale_terms (-sc)%Z (lhs c)) (gather xs))
        (@PTrieCode.empty unit) <= 4 * PTrieT.c_trie *
        (lc_terms_weight xs + N.of_nat ((Z.size_nat sc + 1) * lsize c) + 1))%N) by nia.
    clear Hfirst Hrest Hweight Hrest_storage Hfirst_storage Hzero.
    pose proof (Z.T_opp_le sc) as Hopp.
    time_unfold T_gather. time_unfold T_linear_equal_in.
    change (fun a b => T_insert_term a b) with T_insert_term.
    change (fun a b => T_zero_entry a b) with T_zero_entry.
    unfold lc_zero_factor. time_simpl. nia.
  Qed.

  (** The guarded row check includes the single initial gather in its weighted bound. *)
  Lemma T_check_row_in_weighted : forall s c k b,
    (Z.size_nat (rhs s) <= b)%nat ->
    (T_gather (lhs s) + T_check_row_in (gather (lhs s)) s c k <=
      (lc_zero_factor + 110) *
      (lc_terms_weight (lhs s) +
        N.of_nat ((Z.size_nat (scale k) + 1) * (lsize c + b + 1))))%N.
  Proof.
    intros s c k b Hbits.
    set (w := (lc_terms_weight (lhs s) +
      N.of_nat ((Z.size_nat (scale k) + 1) * (lsize c + b + 1)))%N).
    assert (Hw : (1 <= w)%N) by (unfold w; nia).
    pose proof (T_linear_equal_in_weighted (scale k) (lhs s) c) as Hequal.
    assert (HequalW : (T_gather (lhs s) +
      T_linear_equal_in (gather (lhs s)) (scale k) (lhs c) <=
      (lc_zero_factor + 20) * w)%N).
    { eapply N.le_trans; [exact Hequal|]. apply N.mul_le_mono_l. unfold w. nia. }
    pose proof (T_gather_weighted (lhs s)) as Hbuild.
    assert (HbuildW : (T_gather (lhs s) <= (lc_zero_factor + 3) * w)%N).
    { unfold lc_zero_factor. clear -Hbuild Hw. unfold w in *. nia. }
    pose proof (T_Z_mul_bilinear (scale k) (rhs c)) as Hmul.
    pose proof (lsize_rhs c) as Hcsize.
    assert (HmulW : (Z.T_mul (scale k) (rhs c) <= 8 * w)%N)
      by (clear -Hmul Hcsize; unfold w; nia).
    pose proof (T_Z_div_bilinear (rhs s) (scale k)) as Hdiv.
    assert (HdivW : (Z.T_div (rhs s) (scale k) <= 65 * w)%N)
      by (clear -Hdiv Hbits; unfold w; nia).
    pose proof (lc_size_div (rhs s) (scale k)) as Hquotient.
    pose proof (Z.T_leb_le (rhs s / scale k) (rhs c)) as Hcut.
    assert (HcutW : (Z.T_leb (rhs s / scale k) (rhs c) <= 5 * w)%N)
      by (clear -Hcut Hquotient Hbits; unfold w; nia).
    pose proof (Z.T_eqb_le (rhs s) (scale k * rhs c)) as Heq.
    pose proof (Z.T_leb_le (rhs s) (scale k * rhs c)) as Hle.
    assert (HeqW : (Z.T_eqb (rhs s) (scale k * rhs c) <= 5 * w)%N)
      by (clear -Heq Hbits; unfold w; nia).
    assert (HleW : (Z.T_leb (rhs s) (scale k * rhs c) <= 5 * w)%N)
      by (clear -Hle Hbits; unfold w; nia).
    pose proof (Z.T_ltb_le 0 (scale k)) as Hpositive.
    change (Z.T_ltb 0 (scale k) <= 4)%N in Hpositive.
    clear Hequal Hbuild Hmul Hcsize Hdiv Hquotient Hcut Heq Hle Hbits.
    time_unfold T_check_row_in. fold w.
    destruct (0 <? scale k)%Z;
      [destruct (linear_equal_in (gather (lhs s)) (scale k) (lhs c))|].
    - destruct (lrel c), (lrel s); try (destruct (cut k)); time_simpl; nia.
    - time_simpl. nia.
    - time_simpl. nia.
  Qed.

  (** A common constant covers combination, two trie scans and scaled bound checks. *)
  Definition c_lc : N := (512 + 4 * X.c_key + 16 * PTrieT.c_trie)%N.
  Lemma T_combine_le_nz : forall P ms, (T_combine P ms <= c_lc * N.of_nat ((csize_nz P ms +
    1)%nat))%N.
  Proof.
    intros P ms. pose proof (T_combine_weighted_nz P ms). unfold c_lc. nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma T_combine_le : forall P ms, (T_combine P ms <= c_lc * N.of_nat ((csize P ms +
    1)%nat))%N.
  Proof.
    intros P ms.
    pose proof (T_combine_le_nz P ms) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.
  (** Entailment checking charges the certificate and conclusion. *)
  Lemma T_check_entails_le_nz : forall P c k,
    (T_check_entails P c k <= c_lc * N.of_nat
      ((csize_nz P (mults k) + (Z.size_nat (scale k) + 1) *
        (lsize c + cbits P (mults k) + 1))%nat))%N.
  Proof.
    intros P c k.
    set (w := csize_nz P (mults k) + (Z.size_nat (scale k) + 1) *
      (lsize c + cbits P (mults k) + 1)).
    assert (Hw : (1 <= w)%nat) by (unfold w; nia).
    pose proof (T_combine_weighted_nz P (mults k)) as Hcombine.
    assert (HcombineW : (T_combine P (mults k) <= 112 * N.of_nat w)%N).
    { eapply N.le_trans; [exact Hcombine|]. apply N.mul_le_mono_l. unfold w. nia. }
    clear Hcombine. time_unfold T_check_entails. time_unfold T_check_entails_fast.
    destruct (combine P (mults k)) as [s|] eqn:Hsum.
    - pose proof (T_empty_row_in_combined_nz P (mults k) s Hsum) as Hempty.
      assert (HemptyW : (T_empty_row_in (gather (lhs s)) s <=
        (4 * PTrieT.c_trie + 13) * N.of_nat w)%N).
      { eapply N.le_trans; [exact Hempty|]. apply N.mul_le_mono_l. unfold w. nia. }
      pose proof (combine_rhs_size P (mults k) s Hsum) as Hrhs.
      pose proof (combine_terms_weight_nz P (mults k) s Hsum) as Hterms.
      pose proof (T_check_row_in_weighted s c k (cbits P (mults k)) Hrhs) as Hrow.
      assert (HrowW : (T_gather (lhs s) + T_check_row_in (gather (lhs s)) s c k <=
        (lc_zero_factor + 110) * N.of_nat w)%N).
      { eapply N.le_trans; [exact Hrow|]. apply N.mul_le_mono_l. unfold w. nia. }
      clear Hempty Hrhs Hterms Hrow Hsum.
      destruct (empty_row_in (gather (lhs s)) s); time_simpl;
        unfold c_lc, lc_zero_factor, lc_insert_factor in *; nia.
    - time_simpl. unfold c_lc. nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma T_check_entails_le : forall P c k,
    (T_check_entails P c k <= c_lc * N.of_nat
      ((csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (lsize c + cbits P (mults k) + 1))%nat))%N.
  Proof.
    intros P c k.
    pose proof (T_check_entails_le_nz P c k) as Hbound.
    pose proof (csize_nz_le P (mults k)) as Hsize. nia.
  Qed.
  (** Contradiction checking charges the certificate-weighted input. *)
  Lemma T_check_empty_le_nz : forall P ms,
    (T_check_empty P ms <= c_lc * N.of_nat ((csize_nz P ms + 1)%nat))%N.
  Proof.
    intros P ms. pose proof (T_combine_weighted_nz P ms) as Hcombine.
    time_unfold T_check_empty. destruct (combine P ms) as [s|] eqn:Hsum.
    - pose proof (T_empty_row_combined_nz P ms s Hsum) as Hrow.
      unfold c_lc, lc_zero_factor, lc_insert_factor in *. nia.
    - unfold c_lc. nia.
  Qed.

  (** The original input measure also bounds this nonzero-row estimate. *)
  Lemma T_check_empty_le : forall P ms,
    (T_check_empty P ms <= c_lc * N.of_nat ((csize P ms + 1)%nat))%N.
  Proof.
    intros P ms.
    pose proof (T_check_empty_le_nz P ms) as Hbound.
    pose proof (csize_nz_le P ms) as Hsize. nia.
  Qed.
  (** Combination charges the rows with a nonzero multiplier. *)
  Lemma combine_complexity : bigO (fun _ : list (lcons X.t) * list Z => True)
    (fun x => N.of_nat (csize_nz (fst x) (snd x)))
    (fun x => T_combine (fst x) (snd x)).
  Proof.
    apply bigO_intro with (c := c_lc). intros [P ms] _.
    pose proof (T_combine_le_nz P ms). cbn [fst snd]. nia.
  Qed.
  (** Entailment checking charges the nonzero rows, the certificate scale and the conclusion. *)
  Lemma check_entails_complexity :
    bigO (fun _ : list (lcons X.t) * lcons X.t * cert => True)
    (fun x => N.of_nat (csize_nz (fst (fst x)) (mults (snd x)) +
      (Z.size_nat (scale (snd x)) + 1) *
        (lsize (snd (fst x)) + cbits (fst (fst x)) (mults (snd x)) + 1)))
    (fun x => T_check_entails (fst (fst x)) (snd (fst x)) (snd x)).
  Proof.
    apply bigO_intro with (c := c_lc). intros [[P c] k] _.
    pose proof (T_check_entails_le_nz P c k). cbn [fst snd]. nia.
  Qed.
  (** Contradiction checking charges the nonzero rows. *)
  Lemma check_empty_complexity : bigO (fun _ : list (lcons X.t) * list Z => True)
    (fun x => N.of_nat (csize_nz (fst x) (snd x)))
    (fun x => T_check_empty (fst x) (snd x)).
  Proof.
    apply bigO_intro with (c := c_lc). intros [P ms] _.
    pose proof (T_check_empty_le_nz P ms). cbn [fst snd]. nia.
  Qed.
  Definition accumulate_term (m : Z) (acc : PTrieCode.t (Z * Z)) (p : X.t * Z)
      : PTrieCode.t (Z * Z) :=
    let key := X.encode (fst p) in
    let previous := match PTrieCode.get key acc with
      | Some z => z | None => (0%Z, 0%Z) end in
    let d := (snd p * m)%Z in
    PTrieCode.set key
      (if (0 <=? d)%Z then (fst previous + d, snd previous)%Z
       else (fst previous, snd previous - d)%Z) acc.
  Definition coefficient_trie (P : list (lcons X.t)) (ms : list Z) : PTrieCode.t (Z * Z) :=
    fold_left (fun acc pm => fold_left (accumulate_term (snd pm)) (lhs (fst pm)) acc)
      (List.combine P ms) PTrieCode.empty.
  (** The plan's insertion adds the same weighted term as the executable checker. *)
  Lemma accumulate_term_value : forall m acc x y a,
    sum_at (X.encode x) (accumulate_term m acc (y, a)) =
      (m * (if X.eqb x y then a else 0) + sum_at (X.encode x) acc)%Z.
  Proof.
    intros m acc x y a.
    change (sum_at (X.encode x) (insert_term acc (y, (a * m)%Z)) =
      (m * (if X.eqb x y then a else 0) + sum_at (X.encode x) acc)%Z).
    rewrite insert_term_value. destruct (X.eqb x y); ring.
  Qed.

  (** Folding one row adds its weighted total coefficient at every source key. *)
  Lemma accumulate_row_value : forall m xs acc x,
    sum_at (X.encode x) (fold_left (accumulate_term m) xs acc) =
      (m * coef_of x xs + sum_at (X.encode x) acc)%Z.
  Proof.
    intros m xs. induction xs as [|[y a] xs IH]; intros acc x.
    - change (sum_at (X.encode x) acc =
        m * 0 + sum_at (X.encode x) acc)%Z. ring.
    - cbn [fold_left]. rewrite IH, accumulate_term_value, coef_of_cons.
      destruct (X.eqb x y); ring.
  Qed.

  (** Folding all paired rows adds exactly their specified coefficient sum. *)
  Lemma coefficient_trie_value_from : forall P ms acc x,
    sum_at (X.encode x)
      (fold_left (fun tr pm =>
        fold_left (accumulate_term (snd pm)) (lhs (fst pm)) tr)
        (List.combine P ms) acc) =
      (comb_coef P ms x + sum_at (X.encode x) acc)%Z.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] acc x; try reflexivity.
    cbn [List.combine fold_left fst snd]. rewrite IH, accumulate_row_value.
    change (comb_coef ps ns x + (m * coef_of x (lhs p) + sum_at (X.encode x) acc) =
      (m * coef_of x (lhs p) + comb_coef ps ns x) + sum_at (X.encode x) acc)%Z.
    ring.
  Qed.

  (** Starting from the empty trie gives the specified coefficient sum. *)
  Lemma coefficient_trie_value : forall P ms x,
    sum_at (X.encode x) (coefficient_trie P ms) = comb_coef P ms x.
  Proof.
    intros P ms x. unfold coefficient_trie. rewrite coefficient_trie_value_from.
    unfold sum_at. rewrite PTrie.get_empty. ring.
  Qed.


  (** A successful combination agrees with the concrete trie accumulation at every key. *)
  Lemma combine_trie : forall P ms s, combine P ms = Some s -> forall x,
    (match PTrieCode.get (X.encode x) (coefficient_trie P ms) with
     | Some z => (fst z - snd z)%Z | None => 0%Z end) =
    fold_right (fun p z => if X.eqb x (fst p) then (snd p + z)%Z else z) 0%Z (lhs s).
  Proof.
    intros P ms s Hcombine x.
    change (sum_at (X.encode x) (coefficient_trie P ms) = coef_of x (lhs s)).
    rewrite coefficient_trie_value.
    destruct (combine_spec P ms (combine_admissible P ms s Hcombine))
      as [row [Hrow [Hcoef [_ _]]]].
    assert (Hsame : row = s) by congruence. subst row.
    symmetry. apply Hcoef.
  Qed.
  (** Successful combination retains the consequences of all input rows. *)
  Lemma combine_sound : forall P ms s, combine P ms = Some s ->
    forall v, Forall (sat v) P -> sat v s.
  Proof.
    exact combine_valid.
  Qed.
  (** Combination without cuts is valid over rational stores. *)
  Lemma combine_sound_rational : forall P ms s, combine P ms = Some s ->
    forall v, Forall (satQ v) P -> satQ v s.
  Proof.
    exact combine_valid_Q.
  Qed.
End LinCertT.
