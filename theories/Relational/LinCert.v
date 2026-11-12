(** * Linear certificate placeholders

    These modules provide the certificate checker interface.
    For example, a placeholder combination returns no row.
    Builds on: LinCertSig. *)

From Stdlib Require Import List ZArith QArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Trie.
From Galois.Relational Require Import LinForm LinCertSig.
Local Open Scope nat_scope.

Module LinCertCode (X : KEY_OPS) <: LINCERT_OPS X.
  (* STUB-CODE *)
  Definition combine (_ : list (lcons X.t)) (_ : list Z) : option (lcons X.t) := None.
  (* STUB-CODE *)
  Definition check_entails (_ : list (lcons X.t)) (_ : lcons X.t) (_ : cert) : bool := false.
  (* STUB-CODE *)
  Definition check_empty (_ : list (lcons X.t)) (_ : list Z) : bool := false.
End LinCertCode.

Module LinCert (X : KEY) <: LINCERT X.
  Include LinCertCode X.
  Lemma check_entails_sound : forall P c k, check_entails P c k = true ->
    forall v, Forall (sat v) P -> sat v c.
  Proof. Admitted.
  (** Certificates without integer cuts also entail their rational conclusion. *)
  Lemma check_entails_sound_Q : forall P c k,
    check_entails P c k = true -> cut k = false ->
    forall v, Forall (satQ v) P -> satQ v c.
  Proof. Admitted.
  (** Accepted contradictions exclude every integer model. *)
  Lemma check_empty_sound : forall P ms, check_empty P ms = true ->
    forall v, ~ Forall (sat v) P.
  Proof. Admitted.
  (** An accepted contradiction entails every conclusion. *)
  Lemma check_entails_empty : forall P c k,
    check_empty P (mults k) = true -> check_entails P c k = true.
  Proof. Admitted.
End LinCert.

Module LinCertT (X : KEY_T) <: LINCERT_ALL X.
  Include LinCert X.
  Include LINCERT_SPEC X.
  TimeFun combine.
  TimeFun check_entails.
  TimeFun check_empty.
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
  Definition accumulate_term (m : Z) (acc : PTrieCode.t Z) (p : X.t * Z)
      : PTrieCode.t Z :=
    let key := X.encode (fst p) in
    let previous := match PTrieCode.get key acc with Some z => z | None => 0%Z end in
    PTrieCode.set key (previous + m * snd p)%Z acc.
  Definition coefficient_trie (P : list (lcons X.t)) (ms : list Z) : PTrieCode.t Z :=
    fold_left (fun acc pm => fold_left (accumulate_term (snd pm)) (lhs (fst pm)) acc)
      (List.combine P ms) PTrieCode.empty.
  (** A successful combination agrees with the concrete trie accumulation at every key. *)
  Lemma combine_trie : forall P ms s, combine P ms = Some s -> forall x,
    (match PTrieCode.get (X.encode x) (coefficient_trie P ms) with
     | Some z => z | None => 0%Z end) =
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
  (** Combination rejects multiplier vectors of the wrong length. *)
  Lemma combine_length : forall P ms s,
    combine P ms = Some s -> length P = length ms.
  Proof. Admitted. (* STUB *)
  (** Inequality rows require nonnegative multipliers. *)
  Lemma combine_nonnegative : forall P ms s,
    combine P ms = Some s ->
    Forall2 (fun p m => lrel p = RLe -> (0 <= m)%Z) P ms.
  Proof. Admitted. (* STUB *)
End LinCertT.
