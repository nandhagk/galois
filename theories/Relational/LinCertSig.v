(** * Linear certificate checking

    Certificates combine input constraints to justify an output constraint.
    For example, nonnegative multipliers combine two upper bounds.
    Builds on: KeySig and LinForm. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Trie.
From Galois.Relational Require Import LinForm.
Local Open Scope nat_scope.

Record cert := Cert {
  mults : list Z;
  scale : Z;
  cut : bool
}.

TimeFun mults.
TimeFun scale.
TimeFun cut.

Module Type LINCERT_OPS (X : KEY_OPS).
  Parameter combine : list (lcons X.t) -> list Z -> option (lcons X.t).
  Parameter check_entails : list (lcons X.t) -> lcons X.t -> cert -> bool.
  Parameter check_empty : list (lcons X.t) -> list Z -> bool.
End LINCERT_OPS.

Module Type LINCERT_LAWS (X : KEY) (Import C : LINCERT_OPS X).
  (** Accepted certificates entail their integer conclusion. *)
  Parameter check_entails_sound : forall P c k, check_entails P c k = true ->
    forall v, Forall (sat v) P -> sat v c.
  (** Certificates without integer cuts also entail their rational conclusion. *)
  Parameter check_entails_sound_Q : forall P c k,
    check_entails P c k = true -> cut k = false ->
    forall v, Forall (satQ v) P -> satQ v c.
  (** Accepted contradictions exclude every integer model. *)
  Parameter check_empty_sound : forall P ms, check_empty P ms = true ->
    forall v, ~ Forall (sat v) P.
  (** An accepted contradiction entails every conclusion. *)
  Parameter check_entails_empty : forall P c k,
    check_empty P (mults k) = true -> check_entails P c k = true.
End LINCERT_LAWS.

Module Type LINCERT (X : KEY) := LINCERT_OPS X <+ LINCERT_LAWS X.

Module Type LINCERT_SPEC (X : KEY_OPS).
  Definition row_bits (c : lcons X.t) : nat :=
    fold_right Nat.max (Z.size_nat (rhs c)) (map (fun p => Z.size_nat (snd p)) (lhs c)).
  Definition row_key_bits (c : lcons X.t) : nat :=
    fold_right Nat.max 0 (map (fun p => Pos.size_nat (X.encode (fst p))) (lhs c)).
  Definition lsize (c : lcons X.t) : nat :=
    (length (lhs c) + 1) * (row_key_bits c + row_bits c + 1).
  Fixpoint csize (P : list (lcons X.t)) (ms : list Z) : nat :=
    match P, ms with
    | p :: ps, m :: ns =>
      (length (lhs p) + 1) * (row_key_bits p + (Z.size_nat m + 1) * (row_bits p + 1)) +
      csize ps ns
    | _, _ => length P + length ms
    end.
  Definition cbits (P : list (lcons X.t)) (ms : list Z) : nat :=
    fold_right Nat.max 0
      (map (fun pm => Z.size_nat (snd pm) + row_bits (fst pm)) (List.combine P ms)) +
    Nat.log2 (length P) + 1.
End LINCERT_SPEC.

Module Type LINCERT_TIME (X : KEY_T) (Import C : LINCERT X).
  Include LINCERT_SPEC X.
  Parameter T_combine : list (lcons X.t) -> list Z -> N.
  Parameter T_check_entails : list (lcons X.t) -> lcons X.t -> cert -> N.
  Parameter T_check_empty : list (lcons X.t) -> list Z -> N.
  Parameter c_lc : N.
  (** Combination charges certificate-weighted row sizes. *)
  Parameter T_combine_le : forall P ms, (T_combine P ms <= c_lc * N.of_nat ((csize P ms +
    1)%nat))%N.
  (** Entailment checking charges the certificate and conclusion. *)
  Parameter T_check_entails_le : forall P c k,
    (T_check_entails P c k <= c_lc * N.of_nat
      ((csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (lsize c + cbits P (mults k) + 1))%nat))%N.
  (** Contradiction checking charges the certificate-weighted input. *)
  Parameter T_check_empty_le : forall P ms,
    (T_check_empty P ms <= c_lc * N.of_nat ((csize P ms + 1)%nat))%N.
End LINCERT_TIME.

Module Type LINCERT_T (X : KEY_T) := LINCERT X <+ LINCERT_TIME X.

Module Type LINCERT_PLAN (X : KEY_T) (Import C : LINCERT_T X).
  (* Coefficients accumulate in the concrete PTrieCode keyed by X.encode.
     The final comparison looks up each scaled conclusion coefficient. *)
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
  Parameter combine_trie : forall P ms s, combine P ms = Some s -> forall x,
    (match PTrieCode.get (X.encode x) (coefficient_trie P ms) with
     | Some z => (fst z - snd z)%Z | None => 0%Z end) =
    fold_right (fun p z => if X.eqb x (fst p) then (snd p + z)%Z else z) 0%Z (lhs s).
  (** Successful combination retains the consequences of all input rows. *)
  Parameter combine_sound : forall P ms s, combine P ms = Some s ->
    forall v, Forall (sat v) P -> sat v s.
  (** Combination without cuts is valid over rational stores. *)
  Parameter combine_sound_Q : forall P ms s, combine P ms = Some s ->
    forall v, Forall (satQ v) P -> satQ v s.
  (** Combination rejects multiplier vectors of the wrong length. *)
  Parameter combine_length : forall P ms s,
    combine P ms = Some s -> length P = length ms.
  (** Inequality rows require nonnegative multipliers. *)
  Parameter combine_nonnegative : forall P ms s,
    combine P ms = Some s ->
    Forall2 (fun p m => lrel p = RLe -> (0 <= m)%Z) P ms.
End LINCERT_PLAN.

Module Type LINCERT_ALL (X : KEY_T) := LINCERT_T X <+ LINCERT_PLAN X.
