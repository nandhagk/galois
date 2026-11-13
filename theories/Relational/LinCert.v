(** * Linear certificate checking

    The checker combines admissible rows and compares their summed coefficients.
    For example, opposite occurrences of one variable cancel before comparison.
    Builds on: LinCertSig. *)

From Stdlib Require Import List ZArith QArith Lia Bool.
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
  Lemma check_entails_sound : forall P c k, check_entails P c k = true ->
    forall v, Forall (sat v) P -> sat v c.
  Proof. Admitted. (* STUB *)
  (** Certificates without integer cuts also entail their rational conclusion. *)
  Lemma check_entails_sound_Q : forall P c k,
    check_entails P c k = true -> cut k = false ->
    forall v, Forall (satQ v) P -> satQ v c.
  Proof. Admitted. (* STUB *)
  (** Accepted contradictions exclude every integer model. *)
  Lemma check_empty_sound : forall P ms, check_empty P ms = true ->
    forall v, ~ Forall (sat v) P.
  Proof. Admitted. (* STUB *)
  (** An accepted contradiction entails every conclusion. *)
  Lemma check_entails_empty : forall P c k,
    check_empty P (mults k) = true -> check_entails P c k = true.
  Proof. Admitted. (* STUB *)
  (** Admissible multipliers combine to the weighted sum of the rows. *)
  Lemma combine_spec : forall P ms, admissible P ms ->
    exists s, combine P ms = Some s /\
      (forall x, coef_of x (lhs s) = comb_coef P ms x) /\ rhs s = comb_rhs P ms /\
      lrel s = (if comb_eq P ms then REq else RLe).
  Proof. Admitted. (* STUB *)
  (** Combination succeeds only on admissible multipliers. *)
  Lemma combine_admissible : forall P ms s, combine P ms = Some s -> admissible P ms.
  Proof. Admitted. (* STUB *)
  (** Exact cut-free certificates are accepted. *)
  Lemma check_entails_complete : forall P c ms sc, admissible P ms -> (0 < sc)%Z ->
    (forall x, comb_coef P ms x = (sc * coef_of x (lhs c))%Z) ->
    match lrel c with
    | REq => comb_eq P ms = true /\ comb_rhs P ms = (sc * rhs c)%Z
    | RLe => (comb_rhs P ms <= sc * rhs c)%Z
    end ->
    check_entails P c (Cert ms sc false) = true.
  Proof. Admitted. (* STUB *)
  (** Rational contradictions are accepted. *)
  Lemma check_empty_complete : forall P ms, admissible P ms ->
    (forall x, comb_coef P ms x = 0%Z) ->
    (comb_rhs P ms < 0)%Z \/ (comb_eq P ms = true /\ comb_rhs P ms <> 0%Z) ->
    check_empty P ms = true.
  Proof. Admitted. (* STUB *)
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
  Definition c_lc : N := 1. (* STUB *)
  Lemma T_combine_le : forall P ms, (T_combine P ms <= c_lc * N.of_nat ((csize P ms +
    1)%nat))%N.
  Proof. Admitted. (* STUB *)
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
  (** A successful combination agrees with the concrete trie accumulation at every key. *)
  Lemma combine_trie : forall P ms s, combine P ms = Some s -> forall x,
    (match PTrieCode.get (X.encode x) (coefficient_trie P ms) with
     | Some z => (fst z - snd z)%Z | None => 0%Z end) =
    fold_right (fun p z => if X.eqb x (fst p) then (snd p + z)%Z else z) 0%Z (lhs s).
  Proof. Admitted. (* STUB *)
  (** Successful combination retains the consequences of all input rows. *)
  Lemma combine_sound : forall P ms s, combine P ms = Some s ->
    forall v, Forall (sat v) P -> sat v s.
  Proof. Admitted. (* STUB *)
  (** Combination without cuts is valid over rational stores. *)
  Lemma combine_sound_Q : forall P ms s, combine P ms = Some s ->
    forall v, Forall (satQ v) P -> satQ v s.
  Proof. Admitted. (* STUB *)
End LinCertT.
