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

  (** Optional bindings retain their declared variable and canonical value. *)
  Definition binding_inv (p : S.prog) (x : X.t) (a : option V.t) : Prop :=
    match a with
    | None => True
    | Some v => In x (P.variables p) /\ value_inv p x v
    end.

  (** Every stored binding in an invariant map has its declared width. *)
  Lemma inv_get : forall p m x, inv p (Reached m) -> binding_inv p x (M.get x m).
  Proof.
    intros p m x [Hwf Hvalues]. rewrite Forall_forall in Hvalues.
    unfold binding_inv. destruct (M.get x m) as [a|] eqn:Hget; [|constructor].
    apply (Hvalues (x, a)). apply (proj2 (M.elements_spec V.t m x a Hwf)). exact Hget.
  Qed.

  (** Pointwise binding invariants suffice for a consistent reached map. *)
  Lemma inv_of_get : forall p m, M.wf m ->
    (forall x, binding_inv p x (M.get x m)) -> inv p (Reached m).
  Proof.
    intros p m Hwf Hget. split; [exact Hwf|]. apply Forall_forall.
    intros [x a] Hin. specialize (Hget x). unfold binding_inv in Hget.
    rewrite (proj1 (M.elements_spec V.t m x a Hwf) Hin) in Hget. exact Hget.
  Qed.

  (** Merging invariant bindings preserves the environment representation. *)
  Lemma inv_merge : forall p ma mb (f : option V.t -> option V.t -> option V.t),
    inv p (Reached ma) -> inv p (Reached mb) -> f None None = None ->
    (forall x a b, binding_inv p x a -> binding_inv p x b -> binding_inv p x (f a b)) ->
    inv p (Reached (M.merge f ma mb)).
  Proof.
    intros p ma mb f Ha Hb Hnone Hf. apply inv_of_get.
    - apply M.wf_merge; [exact (proj1 Ha)|exact (proj1 Hb)].
    - intro x. rewrite (M.get_merge V.t V.t V.t f ma mb x Hnone).
      apply Hf; now apply inv_get.
  Qed.

  (** Updating a declared variable keeps support and canonical values. *)
  Lemma inv_set : forall p m x a, inv p (Reached m) -> In x (P.variables p) ->
    value_inv p x a -> inv p (Reached (M.set x a m)).
  Proof.
    intros p m x a Hinv Hdeclared Ha. apply inv_of_get.
    - apply M.wf_set. exact (proj1 Hinv).
    - intro y. destruct (X.eqb_spec y x) as [Heq|Hneq].
      + subst y. rewrite M.get_set_same. split; assumption.
      + rewrite M.get_set_other by exact Hneq. now apply inv_get.
  Qed.

  (** Tagged top is permitted at every declared width. *)
  Lemma value_inv_top : forall p x, value_inv p x V.top.
  Proof.
    intros p x. rewrite D.top_tag. constructor.
  Qed.

  (** Tagged bottom is permitted at every declared width. *)
  Lemma value_inv_bot : forall p x, value_inv p x V.bot.
  Proof.
    intros p x. rewrite D.bot_tag. constructor.
  Qed.

  (** A payload operation preserving canonical values also preserves its common width. *)
  Lemma value_inv_binary : forall p x f a b,
    (forall w r s, C.canonical w r -> C.canonical w s -> C.canonical w (f w r s)) ->
    value_inv p x a -> value_inv p x b ->
    value_inv p x (budget_binary W.pis_bot f a b).
  Proof.
    intros p x f a b Hf Ha Hb.
    destruct a as [|wa ra|], b as [|wb rb|]; cbn [budget_binary];
      try exact Ha; try exact Hb; try exact Logic.I.
    destruct Ha as [Hwa Hra], Hb as [Hwb Hrb]. subst wa wb.
    rewrite Pos.eqb_refl. unfold budget_norm.
    destruct (W.pis_bot (P.width_of p x) (f (P.width_of p x) ra rb)); [constructor|].
    split; [reflexivity|now apply Hf].
  Qed.

  (** Tagged join retains the declared operand width. *)
  Lemma value_inv_join : forall p x a b,
    value_inv p x a -> value_inv p x b -> value_inv p x (V.join a b).
  Proof.
    intros p x a b Ha Hb. rewrite D.join_tag.
    apply value_inv_binary; [exact C.canonical_join|exact Ha|exact Hb].
  Qed.

  (** Tagged widening retains the declared operand width. *)
  Lemma value_inv_widen : forall p x q a b,
    value_inv p x a -> value_inv p x b -> value_inv p x (V.widen q a b).
  Proof.
    intros p x q a b Ha Hb. rewrite D.widen_tag. destruct (V.leb b a); [exact Ha|].
    apply value_inv_binary; [exact (C.canonical_widen q)|exact Ha|exact Hb].
  Qed.

  (** Tagged narrowing retains the declared operand width. *)
  Lemma value_inv_narrow : forall p x a b,
    value_inv p x a -> value_inv p x b -> value_inv p x (V.narrow a b).
  Proof.
    intros p x a b Ha Hb. apply D.narrow_width; assumption.
  Qed.

  (** Tagged intersection retains the declared operand width. *)
  Lemma value_inv_meet : forall p x a b,
    value_inv p x a -> value_inv p x b -> value_inv p x (V.meet a b).
  Proof.
    intros p x a b Ha Hb. apply D.meet_width; assumption.
  Qed.

  (** Empty reached maps satisfy every program's representation invariant. *)
  Lemma inv_top : forall p, inv p E.top.
  Proof.
    intro p. rewrite E.F_top. apply inv_of_get; [apply M.wf_empty|].
    intro x. rewrite M.get_empty. constructor.
  Qed.

  (** Reading a consistent environment returns a canonical value at the declared width. *)
  Lemma read_width : forall p m x, inv p (Reached m) ->
    D.at_width (P.width_of p x) (E.read m x).
  Proof.
    intros p m x Hinv. rewrite E.read_spec.
    pose proof (inv_get p m x Hinv) as Hget.
    destruct (M.get x m) as [a|]; [exact (proj2 Hget)|apply value_inv_top].
  Qed.

  (** Unreachable environments satisfy the representation invariant. *)
  Lemma inv_bot : forall p, inv p E.bot.
  Proof.
    intro p. rewrite E.F_bot. constructor.
  Qed.

  (** Pointwise join keeps declared widths and canonical payloads. *)
  Lemma inv_join : forall p a b, inv p a -> inv p b -> inv p (E.join a b).
  Proof.
    intros p a b Ha Hb. rewrite E.F_join.
    destruct a as [|ma], b as [|mb]; try assumption.
    rewrite E.F_join_map. apply inv_merge; try assumption; [reflexivity|].
    intros x [va|] [vb|] Hx Hy; try exact Logic.I.
    destruct Hx as [Hdeclared Hva], Hy as [_ Hvb].
    cbn [binding_inv].
    destruct (V.is_bot (V.join va vb)); [constructor|].
    split; [exact Hdeclared|now apply value_inv_join].
  Qed.

  (** Pointwise narrowing keeps declared widths and canonical payloads. *)
  Lemma inv_narrow : forall p a b, inv p a -> inv p b -> inv p (E.narrow a b).
  Proof.
    intros p a b Ha Hb. rewrite E.F_narrow. destruct (E.is_bot b); [exact Hb|].
    destruct a as [|ma], b as [|mb]; try assumption.
    apply inv_merge; try assumption; [reflexivity|].
    intros x [va|] [vb|] Hx Hy; try exact Hx; try exact Hy; try exact Logic.I.
    destruct Hx as [Hdeclared Hva], Hy as [_ Hvb].
    split; [exact Hdeclared|now apply value_inv_narrow].
  Qed.

  (** Payload widening keeps the representation invariant for every widening parameter. *)
  Lemma inv_widen : forall p w a b,
    inv p a -> inv p b -> inv p (E.widen w a b).
  Proof.
    intros p q a b Ha Hb. rewrite E.F_widen. destruct (E.leb b a); [exact Ha|].
    destruct a as [|ma], b as [|mb]; try assumption.
    apply inv_merge; try assumption; [reflexivity|].
    intros x [va|] [vb|] Hx Hy; try exact Logic.I.
    destruct Hx as [Hdeclared Hva], Hy as [_ Hvb].
    cbn [binding_inv].
    destruct (V.is_bot (V.widen q va vb)); [constructor|].
    split; [exact Hdeclared|now apply value_inv_widen].
  Qed.

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
