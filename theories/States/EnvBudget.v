(** * Canonical word environment budget instance

    The budget bounds stored payloads at their declared variable widths.
    For example, a congruence payload uses its polynomial representation envelope.
    Builds on: EnvBudgetSig and the operational environment and system links. *)

From Stdlib Require Import List PArith Arith ZArith Bool Lia.
From Galois.Base Require Import KeySig MapSig.
From Galois.Bits Require Import Word.
From Galois.Domains Require Import LangSig ValueSig WordSig BitsLang SignSig CongruenceSig.
From Galois.States Require Import EnvSig EnvBudgetSig.
From Galois.Fixpoint Require Import SystemSig.

Local Open Scope nat_scope.

(** Every three-flag sign payload has a canonical representation. *)
Module SignEnvelope (L : WORD_LANGUAGE_T) (S : SIGN_ALL L)
    <: WORD_PAYLOAD_ENVELOPE L S.
  Definition canonical (_ : positive) (_ : S.p) : Prop := True.
  Definition payload_size_bound := Pos.to_nat.
  Definition payload_rank_bound (_ : S.pwparam) (_ : positive) : nat := 3.
  (** Canonical payload sizes fit the concrete width envelope. *)
  Lemma canonical_size : forall w p,
    canonical w p -> S.psize w p <= payload_size_bound w.
  Proof.
    intros w p _. unfold payload_size_bound. rewrite S.psize_width. reflexivity.
  Qed.
  (** Canonical payload ranks fit the concrete rank envelope. *)
  Lemma canonical_rank : forall q w p,
    canonical w p -> S.pwrank q w p <= payload_rank_bound q w.
  Proof.
    intros q w p _. unfold payload_rank_bound. rewrite S.F_pwrank. lia.
  Qed.
  (** The concrete bottom payload is canonical. *)
  Lemma canonical_bot : forall w, canonical w (S.pbot w).
  Proof.
    intros. constructor.
  Qed.
  (** The concrete top payload is canonical. *)
  Lemma canonical_top : forall w, canonical w (S.ptop w).
  Proof.
    intros. constructor.
  Qed.
  (** Literal abstraction returns a canonical payload. *)
  Lemma canonical_const : forall w z, canonical w (S.pconst w z).
  Proof.
    intros. constructor.
  Qed.
  (** Concrete join keeps canonical payloads canonical. *)
  Lemma canonical_join : forall w a b,
    canonical w a -> canonical w b -> canonical w (S.pjoin w a b).
  Proof.
    intros. constructor.
  Qed.
  (** Concrete meet keeps canonical payloads canonical. *)
  Lemma canonical_meet : forall w a b,
    canonical w a -> canonical w b -> canonical w (S.pmeet w a b).
  Proof.
    intros. constructor.
  Qed.
  (** Concrete widening keeps canonical payloads canonical. *)
  Lemma canonical_widen : forall q w a b,
    canonical w a -> canonical w b -> canonical w (S.pwiden q w a b).
  Proof.
    intros. constructor.
  Qed.
  (** Concrete narrowing keeps canonical payloads canonical. *)
  Lemma canonical_narrow : forall w a b,
    canonical w a -> canonical w b -> canonical w (S.pnarrow w a b).
  Proof.
    intros. constructor.
  Qed.
End SignEnvelope.

(** Concrete normalized congruences fit a quadratic width envelope. *)
Module CongruenceEnvelope (L : WORD_LANGUAGE_T) (W : CONGRUENCE_ALL L)
    (R : CONGRUENCE_BUDGET_CODE_LINK L W) <: WORD_PAYLOAD_ENVELOPE L W.
  Definition canonical (w : positive) (p : W.p) : Prop :=
    CongruenceBudgetCode.congr_norm w p = p.
  Definition payload_size_bound (w : positive) : nat := (3 * Pos.to_nat w + 1)^2.
  Definition payload_rank_bound (_ : W.pwparam) (w : positive) : nat := Pos.to_nat w + 2.
  (** Fixed points of concrete normalization have at most two width-sized stored integers. *)
  Lemma canonical_size : forall w p,
    canonical w p -> W.psize w p <= payload_size_bound w.
  Proof.
    intros w p Hcanonical. unfold canonical in Hcanonical.
    rewrite <- R.norm_code in Hcanonical.
    pose proof (W.congr_norm_bits w p) as Hbits. rewrite Hcanonical in Hbits.
    rewrite W.psize_congr. unfold payload_size_bound. apply Nat.pow_le_mono_l. lia.
  Qed.
  (** Congruence ranks fit the width-plus-two envelope. *)
  Lemma canonical_rank : forall q w p,
    canonical w p -> W.pwrank q w p <= payload_rank_bound q w.
  Proof.
    intros q w p _. unfold payload_rank_bound. rewrite W.F14_pwrank.
    apply W.F13_wrank_le.
  Qed.
  (** The concrete bottom payload is canonical. *)
  Lemma canonical_bot : forall w, canonical w (W.pbot w).
  Proof.
    intro w. rewrite R.bot_code. reflexivity.
  Qed.
  (** The concrete top payload is canonical. *)
  Lemma canonical_top : forall w, canonical w (W.ptop w).
  Proof.
    intro w. rewrite R.top_code. unfold canonical, CongruenceBudgetCode.ptop.
    assert (Hwidth : (modulus w <=? 1)%Z = false).
    { apply Z.leb_gt. exact (proj2 (one_is_word w)). }
    cbn [CongruenceBudgetCode.congr_norm Z.abs Z.eqb].
    now rewrite Hwidth.
  Qed.
  (** Literal abstraction returns a canonical payload. *)
  Lemma canonical_const : forall w z, canonical w (W.pconst w z).
  Proof.
    intros w z. rewrite R.const_code. unfold canonical.
    change ((if CongruenceBudgetCode.wordb w (wrap w z)
      then C 0 (wrap w z) else CBot) = C 0 (wrap w z)).
    assert (Hword : CongruenceBudgetCode.wordb w (wrap w z) = true).
    { unfold CongruenceBudgetCode.wordb. apply andb_true_iff. split.
      - apply Z.leb_le. exact (proj1 (wrap_is_word w z)).
      - apply Z.ltb_lt. exact (proj2 (wrap_is_word w z)). }
    now rewrite Hword.
  Qed.
  (** Concrete join keeps canonical payloads canonical. *)
  Lemma canonical_join : forall w a b,
    canonical w a -> canonical w b -> canonical w (W.pjoin w a b).
  Proof.
    intros w a b Ha Hb. rewrite R.join_code. unfold CongruenceBudgetCode.pjoin.
    unfold canonical in Ha, Hb. rewrite Ha, Hb.
    destruct a as [|m r], b as [|n s]; try assumption; try reflexivity.
    unfold canonical. rewrite <- R.norm_code. apply W.F4_norm_idempotent.
  Qed.
  (** Concrete meet keeps canonical payloads canonical. *)
  Lemma canonical_meet : forall w a b,
    canonical w a -> canonical w b -> canonical w (W.pmeet w a b).
  Proof.
    intros w a b Ha Hb. rewrite R.meet_code. unfold CongruenceBudgetCode.pmeet.
    unfold canonical in Ha, Hb. rewrite Ha, Hb.
    destruct a as [|m r], b as [|n s]; try reflexivity.
    destruct (Z.eqb (r mod Z.gcd m n) (s mod Z.gcd m n)); [|reflexivity].
    unfold canonical. rewrite <- R.norm_code. apply W.F4_norm_idempotent.
  Qed.
  (** Concrete widening keeps canonical payloads canonical. *)
  Lemma canonical_widen : forall q w a b,
    canonical w a -> canonical w b -> canonical w (W.pwiden q w a b).
  Proof.
    intros q w a b Ha Hb. rewrite R.widen_code.
    destruct (W.pleb w b a); [exact Ha|now apply canonical_join].
  Qed.
  (** Concrete narrowing keeps canonical payloads canonical. *)
  Lemma canonical_narrow : forall w a b,
    canonical w a -> canonical w b -> canonical w (W.pnarrow w a b).
  Proof.
    intros w a b Ha Hb. rewrite R.narrow_code. now apply canonical_meet.
  Qed.
End CongruenceEnvelope.

Module EnvBudget (X : KEY_T) (M : MAP_T X) (L : WORD_LANGUAGE_T)
    (W : WORD_PAYLOAD_T L) (T : WORD_TABLE_T L W) (C : WORD_PAYLOAD_ENVELOPE L W)
    (CT : WORD_TABLE_ENVELOPE L W T C)
    (B : LANG_T with Definition op := bop with Definition val := word)
    (V : VALUE_DOMAIN_T B with Definition t := tagged W.p
      with Definition wparam := W.pwparam)
    (D : WORD_VALUE_BUDGET_LINK L W T C B V)
    (E : ENV_ALL X M B V) (S : SYSTEM_T E) (P : ENV_WORD_PROGRAM X M L W B V E S)
    <: BUDGET E S.
  Include ENV_BUDGET_SPEC X M L W C B V E S P.

  (** Unreachable environments satisfy the representation invariant. *)
  Lemma inv_bot : forall p, inv p E.bot.
  Proof. Admitted. (* STUB *)

  (** Pointwise join keeps declared widths and canonical payloads. *)
  Lemma inv_join : forall p a b, inv p a -> inv p b -> inv p (E.join a b).
  Proof. Admitted. (* STUB *)

  (** Pointwise narrowing keeps declared widths and canonical payloads. *)
  Lemma inv_narrow : forall p a b, inv p a -> inv p b -> inv p (E.narrow a b).
  Proof. Admitted. (* STUB *)

  (** Payload widening keeps the representation invariant for every widening parameter. *)
  Lemma inv_widen : forall p w a b,
    inv p a -> inv p b -> inv p (E.widen w a b).
  Proof. Admitted. (* STUB *)

  (** Typed operational rows preserve the representation invariant on every contribution. *)
  Lemma inv_rows : forall p r look a ss, S.wf p -> In r (S.rows p) ->
    (forall x, inv p (look x)) -> S.eval p r look = Some (a, ss) ->
    inv p a /\ Forall (fun xa => inv p (snd xa)) ss.
  Proof. Admitted. (* STUB *)

  (** Canonical representation sizes fit the program's sum of width-dependent envelopes. *)
  Lemma size_le : forall p a, inv p a -> E.size a <= vsize p.
  Proof. Admitted. (* STUB *)

  (** Canonical environments store at most one binding per declared variable. *)
  Lemma wunits_le : forall p a, inv p a -> E.wunits a <= wunits p.
  Proof. Admitted. (* STUB *)

  (** Canonical payload ranks fit the program's sum of parameter-dependent rank envelopes. *)
  Lemma wrank_le : forall p w a, inv p a -> E.wrank w a <= wmax p w.
  Proof. Admitted. (* STUB *)
End EnvBudget.
