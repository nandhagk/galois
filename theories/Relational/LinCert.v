(** * Linear certificate checking

    The checker combines admissible rows and compares their summed coefficients.
    For example, opposite occurrences of one variable cancel before comparison.
    Builds on: LinCertSig. *)

From Stdlib Require Import List ZArith QArith Lia Bool Psatz.
From Argent Require Import Time Tactics Std.
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

  Fixpoint combine_rows (P : list (lcons X.t)) (ms : list Z) : option (lc_sum X.t) :=
    match P, ms with
    | nil, nil => Some (LCSum _ nil (0%Z, 0%Z) true)
    | p :: ps, m :: ns =>
      if allowed p m then
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

  Definition check_entails (P : list (lcons X.t)) (c : lcons X.t) (k : cert) : bool :=
    match combine P (mults k) with
    | Some s => if empty_row s then true else check_row s c k
    | None => false
    end.
End LinCertCode.

Module LinCert (X : KEY) <: LINCERT X.
  Include LinCertCode X.
  Include LINCERT_SPEC X.
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
    - destruct (allowed p m) eqn:Hallowed; [|discriminate].
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
      cbn [combine_rows]. rewrite Hallow, Hsum. eexists. reflexivity.
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
    - destruct (allowed p m) eqn:Hallowed; [|discriminate].
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
    - destruct (allowed p m) eqn:Hallowed; [|discriminate].
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
    intros P c k Hcheck v Hmodels. unfold check_entails in Hcheck.
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
    - destruct (allowed p m) eqn:Hallowed; [|discriminate].
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
  Lemma check_entails_sound_Q : forall P c k,
    check_entails P c k = true -> cut k = false ->
    forall v, Forall (satQ v) P -> satQ v c.
  Proof.
    intros P c k Hcheck Hcut v Hmodels. unfold check_entails in Hcheck.
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
    intros P c k Hempty. unfold check_empty, check_entails in *.
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
    unfold check_entails. cbn [mults]. rewrite Hsum.
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
    - destruct (allowed p m); [|discriminate].
      destruct (combine_rows ps ns) as [u|] eqn:Hu; [|discriminate].
      inversion Hsum; subst s. cbn [lc_sums].
      specialize (IH ns u Hu). destruct (lc_sums u) as [a b].
      cbn [fst snd] in IH. apply lc_add_signed_nonnegative; tauto.
  Qed.

  (** Total input bit mass bounds both right-hand-side accumulators together. *)
  Lemma combine_rows_sums_size : forall P ms s, combine_rows P ms = Some s ->
    (Z.size_nat (fst (lc_sums s)) + Z.size_nat (snd (lc_sums s)) <= csize P ms)%nat.
  Proof.
    induction P as [|p ps IH]; intros [|m ns] s Hsum;
      cbn [combine_rows] in Hsum; try discriminate.
    - inversion Hsum. cbn [lc_sums fst snd csize Z.size_nat]. lia.
    - destruct (allowed p m); [|discriminate].
      destruct (combine_rows ps ns) as [u|] eqn:Hu; [|discriminate].
      specialize (IH ns u Hu).
      pose proof (combine_rows_nonnegative ps ns u Hu) as [Ha Hb].
      inversion Hsum; subst s. cbn [lc_sums csize].
      destruct (lc_sums u) as [a b]. cbn [fst snd] in *.
      pose proof (lc_add_signed_size (m * rhs p) a b Ha Hb).
      pose proof (lc_size_mul m (rhs p)). pose proof (row_bits_rhs p). nia.
  Qed.

  (** Row combination carries the set-bit potential across its recursive sums. *)
  Lemma T_combine_rows_ones : forall P ms,
    (T_combine_rows P ms +
      match combine_rows P ms with Some s => lc_pair_ones (lc_sums s) | None => 0 end <=
      96 * N.of_nat (csize P ms + 1))%N.
  Proof.
    induction P as [|p ps IH]; intros [|m ns];
      time_unfold T_combine_rows; cbn [combine_rows csize].
    - unfold lc_pair_ones, lc_ones_Z. time_cbn. lia.
    - time_cbn. lia.
    - time_cbn. lia.
    - specialize (IH ns). pose proof (T_allowed_le p m) as Hallowed.
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
      clear Hscale Hmul Hadd Hequal Happ Hbits Hrhs Ha Hb Hallow.
      cbn [lc_sums] in *. rewrite ?Hsums in *. clear Hsum Hsums.
      time_simpl. time_cbn_all. fold w. lia.
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
  Lemma T_combine_weighted : forall P ms,
    (T_combine P ms <= 112 * N.of_nat (csize P ms + 1))%N.
  Proof.
    intros P ms. pose proof (T_combine_rows_ones P ms) as Hrows.
    time_unfold T_combine. destruct (combine_rows P ms) as [s|] eqn:Hsum.
    - pose proof (T_finish_sum_le s) as Hfinish.
      pose proof (combine_rows_sums_size P ms s Hsum) as Hsize. nia.
    - nia.
  Qed.

  Definition c_lc : N := (512 + 4 * X.c_key + 16 * PTrieT.c_trie)%N.
  Lemma T_combine_le : forall P ms, (T_combine P ms <= c_lc * N.of_nat ((csize P ms +
    1)%nat))%N.
  Proof.
    intros P ms. pose proof (T_combine_weighted P ms). unfold c_lc. nia.
  Qed.
  (** Entailment checking charges the certificate and conclusion. *)
  Lemma T_check_entails_le : forall P c k,
    (T_check_entails P c k <= c_lc * N.of_nat
      ((csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (lsize c + cbits P (mults k) + 1))%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Contradiction checking charges the certificate-weighted input. *)
  Lemma T_check_empty_le : forall P ms,
    (T_check_empty P ms <= c_lc * N.of_nat ((csize P ms + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
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
  Lemma combine_sound_Q : forall P ms s, combine P ms = Some s ->
    forall v, Forall (satQ v) P -> satQ v s.
  Proof.
    exact combine_valid_Q.
  Qed.
End LinCertT.
