(** * Canonical word environment budget instance

    The budget bounds stored payloads at their declared variable widths.
    For example, a congruence payload uses its polynomial representation envelope.
    Builds on: EnvBudgetSig and the operational environment and system links. *)

From Stdlib Require Import List PArith Arith ZArith Bool Lia.
From Stdlib.Sorting Require Import Permutation.
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

  (** Untagging typed operands exposes their declared widths and canonical payloads. *)
  Lemma untag_width : forall ws xs wps,
    Forall2 D.at_width ws xs -> budget_untag xs = Some wps ->
    map fst wps = ws /\ Forall (fun wp => C.canonical (fst wp) (snd wp)) wps.
  Proof.
    intros ws xs wps Hwidth. revert wps.
    induction Hwidth as [|w a ws xs Ha Htail IH]; intros wps Htag.
    - cbn [budget_untag] in Htag. inversion Htag; subst. split; constructor.
    - destruct a as [|u q|]; cbn [budget_untag] in Htag; try discriminate.
      destruct (budget_untag xs) as [ps|] eqn:Hrest; [|discriminate].
      injection Htag as <-. destruct Ha as [Hu Hq]. subst u.
      destruct (IH ps eq_refl) as [Hws Hcanonical].
      split; [cbn; now rewrite Hws|constructor; assumption].
  Qed.

  (** A typed operator's tagged result has its declared width and a canonical payload. *)
  Lemma forward_width : forall o xs ws rw,
    D.operator_width o ws rw -> Forall2 D.at_width ws xs ->
    D.at_width rw (V.forward o xs).
  Proof.
    intros o xs ws rw Hoperator Hwidth.
    destruct (V.forward o xs) as [|w q|] eqn:Hforward; try exact Logic.I.
    destruct (D.forward_tag o xs w q Hforward) as
      [[z [Hop [Hxs Hq]]]|[op [wps [Hop [Htag [Hresult Hq]]]]]].
    - subst o xs q. destruct Hoperator as [_ Hrw]. subst rw.
      split; [reflexivity|apply C.canonical_const].
    - subst o. destruct (untag_width ws xs wps Hwidth Htag) as [Hws Hcanonical].
      rewrite Hws in Hresult. change (Op.result_width op ws = Some rw) in Hoperator.
      assert (Hw : w = rw) by congruence. subst w. split; [reflexivity|].
      destruct Hq as [Htop|[Hentry|[z Hconst]]].
      + subst q. apply C.canonical_top.
      + eapply CT.wfwd_canonical; eassumption.
      + subst q. apply C.canonical_const.
  Qed.

  (** Typed annotations place every forward result at its declared width. *)
  Lemma annotate_width : forall p e w m, inv p (Reached m) ->
    word_term_typed (P.variables p) (P.width_of p) e w ->
    D.at_width w (E.root (E.annotate m e)).
  Proof.
    intros p e. induction e as [x|o es IH]; intros w m Hinv Htyped.
    - inversion Htyped; subst. rewrite E.annotate_leaf, E.root_leaf. now apply read_width.
    - inversion Htyped as [|w' z|op es' ws w' Hchildren Hresult]; subst.
      + rewrite E.annotate_node, E.root_node. cbn [map].
        apply (forward_width _ _ nil); [split; reflexivity|constructor].
      + rewrite E.annotate_node, E.root_node. apply (forward_width _ _ ws); [exact Hresult|].
        clear Htyped Hresult. revert IH.
        induction Hchildren as [|e es cw cws Hhead Hrest IHrest]; intro IH.
        * constructor.
        * inversion IH as [|e' IHe es' IHtail]; subst. constructor.
          -- now apply IHe.
          -- now apply IHrest.
  Qed.

  (** Lists of typed terms retain their ordered list of declared widths. *)
  Lemma annotations_width : forall p m es ws, inv p (Reached m) ->
    word_terms_typed (P.variables p) (P.width_of p) es ws ->
    Forall2 D.at_width ws (map (fun e => E.root (E.annotate m e)) es).
  Proof.
    intros p m es ws Hinv Htyped.
    induction Htyped as [|e es w ws Hhead Htail IH].
    - constructor.
    - constructor; [eapply annotate_width; eassumption|exact IH].
  Qed.

  (** Summing concatenated lists adds their separate sums. *)
  Lemma budget_sum_app : forall {A} (f : A -> nat) xs ys,
    fold_right Nat.add 0 (map f (xs ++ ys)) =
      fold_right Nat.add 0 (map f xs) + fold_right Nat.add 0 (map f ys).
  Proof.
    intros A f xs ys. induction xs; cbn; lia.
  Qed.

  (** Permutation preserves a nonnegative list sum. *)
  Lemma budget_sum_permutation : forall {A} (f : A -> nat) xs ys,
    Permutation xs ys ->
    fold_right Nat.add 0 (map f xs) = fold_right Nat.add 0 (map f ys).
  Proof.
    intros A f xs ys Hperm. induction Hperm; cbn [map fold_right]; lia.
  Qed.

  (** Pointwise bounds give a bound on their list sums. *)
  Lemma budget_sum_mono : forall {A} (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) ->
    fold_right Nat.add 0 (map f xs) <= fold_right Nat.add 0 (map g xs).
  Proof.
    intros A f g xs. induction xs as [|x xs IH]; intros H; cbn; [lia|].
    pose proof (H x (or_introl eq_refl)).
    assert (Htail : forall y, In y xs -> f y <= g y).
    { intros y Hy. apply H. now right. }
    specialize (IH Htail). lia.
  Qed.

  (** A list without duplicates contributes no more than any list containing it. *)
  Lemma budget_sum_incl : forall {A} (f : A -> nat) xs ys,
    NoDup xs -> incl xs ys ->
    fold_right Nat.add 0 (map f xs) <= fold_right Nat.add 0 (map f ys).
  Proof.
    intros A f xs. induction xs as [|x xs IH]; intros ys Hnd Hincl; [cbn; lia|].
    inversion Hnd as [|x1 xs1 Hnot Hndtail]; subst x1 xs1.
    destruct (in_split x ys (Hincl x (or_introl eq_refl))) as [ys1 [ys2 Hys]].
    subst ys.
    assert (Htail : incl xs (ys1 ++ ys2)).
    { intros y Hy. specialize (Hincl y (or_intror Hy)).
      apply in_app_iff in Hincl. apply in_app_iff.
      destruct Hincl as [Hin|[Heq|Hin]]; [now left| |now right].
      subst y. contradiction. }
    specialize (IH (ys1 ++ ys2) Hndtail Htail).
    rewrite budget_sum_app in IH. rewrite budget_sum_app. cbn. lia.
  Qed.

  (** The initial accumulator contributes one to the sum. *)
  Lemma budget_sum_seed : forall xs,
    fold_right Nat.add 1 xs = fold_right Nat.add 0 xs + 1.
  Proof.
    induction xs; cbn; lia.
  Qed.

  (** Summing pointwise additions separates the two contributions. *)
  Lemma budget_sum_pair : forall {A} (f g : A -> nat) xs,
    fold_right Nat.add 0 (map (fun x => f x + g x) xs) =
      fold_right Nat.add 0 (map f xs) + fold_right Nat.add 0 (map g xs).
  Proof.
    intros A f g xs. induction xs; cbn; lia.
  Qed.

  (** Injective key encoding preserves the absence of duplicate keys. *)
  Lemma budget_encode_nodup : forall xs,
    NoDup xs -> NoDup (map X.encode xs).
  Proof.
    intros xs Hnd. induction Hnd; cbn; constructor; [|assumption].
    intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hy]].
    apply X.encode_inj in Heq. subst y. contradiction.
  Qed.

  (** Stored codes permute the encodings of the enumerated consistent bindings. *)
  Lemma budget_codes_elements : forall (m : M.t V.t), M.wf m ->
    Permutation (M.codes m) (map (fun xa => X.encode (fst xa)) (M.elements m)).
  Proof.
    intros m Hwf. apply NoDup_Permutation.
    - apply M.codes_nodup.
    - rewrite <- map_map. apply budget_encode_nodup. now apply M.elements_nodup.
    - intro code. rewrite M.codes_spec, in_map_iff. split.
      + intros Hbound. destruct (M.find code m) as [a|] eqn:Hfind; [|contradiction].
        destruct (M.wf_find V.t m code a Hwf Hfind) as [x Hcode].
        exists (x, a). split; [exact Hcode|].
        apply (proj2 (M.elements_spec V.t m x a Hwf)).
        rewrite M.get_find, Hcode. exact Hfind.
      + intros [[x a] [Hcode Hin]]. cbn in Hcode.
        rewrite <- Hcode, <- M.get_find.
        rewrite (proj1 (M.elements_spec V.t m x a Hwf) Hin). discriminate.
  Qed.

  (** Summing successful code lookups agrees with summing enumerated values. *)
  Lemma budget_codes_sum : forall (m : M.t V.t) (f : V.t -> nat), M.wf m ->
    fold_right Nat.add 0 (map (fun code =>
      match M.find code m with Some a => f a | None => 0 end) (M.codes m)) =
    fold_right Nat.add 0 (map (fun xa => f (snd xa)) (M.elements m)).
  Proof.
    intros m f Hwf.
    rewrite (budget_sum_permutation _ _ _ (budget_codes_elements m Hwf)), map_map.
    f_equal. apply map_ext_in. intros [x a] Hin. cbn.
    rewrite <- M.get_find, (proj1 (M.elements_spec V.t m x a Hwf) Hin). reflexivity.
  Qed.

  (** Distinct stored variables fit the program sum even when declarations repeat. *)
  Lemma budget_declared_sum : forall p m (f : X.t * V.t -> nat) (g : X.t -> nat),
    inv p (Reached m) ->
    (forall x a, In (x, a) (M.elements m) -> f (x, a) <= g x) ->
    fold_right Nat.add 0 (map f (M.elements m)) <=
      fold_right Nat.add 0 (map g (P.variables p)).
  Proof.
    intros p m f g [Hwf Hinv] Hbound.
    eapply Nat.le_trans with
      (m := fold_right Nat.add 0 (map (fun xa => g (fst xa)) (M.elements m))).
    - apply budget_sum_mono. intros [x a] Hin. now apply Hbound.
    - rewrite <- map_map. apply budget_sum_incl.
      + now apply M.elements_nodup.
      + intros x Hx. apply in_map_iff in Hx. destruct Hx as [[y a] [Heq Hin]].
        cbn in Heq. subst y. rewrite Forall_forall in Hinv.
        exact (proj1 (Hinv (x, a) Hin)).
  Qed.

  (** A canonical value fits the envelope of its declared variable. *)
  Lemma budget_value_size : forall p x a, value_inv p x a ->
    V.size a <= Pos.to_nat (P.width_of p x) +
      C.payload_size_bound (P.width_of p x) + 1.
  Proof.
    intros p x a Hinv. rewrite D.size_tag.
    destruct a as [|w q|]; cbn; try lia.
    destruct Hinv as [Hw Hcanon]. subst w.
    pose proof (C.canonical_size _ _ Hcanon). lia.
  Qed.

  (** A canonical value rank fits the envelope of its declared variable. *)
  Lemma budget_value_rank : forall p w x a, value_inv p x a ->
    V.wrank w a <= 1 + C.payload_rank_bound w (P.width_of p x).
  Proof.
    intros p w x a Hinv. rewrite D.rank_tag.
    destruct a as [|u q|]; cbn; try lia.
    destruct Hinv as [Hu Hcanon]. subst u.
    pose proof (C.canonical_rank w _ _ Hcanon). lia.
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

  (** Refinement of a typed cached annotation preserves every stored variable's width. *)
  Lemma refine_checked_inv : forall p e w cached current q,
    word_term_typed (P.variables p) (P.width_of p) e w ->
    inv p (Reached cached) -> inv p (Reached current) -> D.at_width w q ->
    inv p (Reached (fst (E.refine_checked q (E.annotate cached e) current))).
  Proof.
    intros p e. induction e as [x|o es IH];
      intros w cached current q Htyped Hcached Hcurrent Hq.
    - inversion Htyped as [x' Hdeclared| |]; subst.
      rewrite E.annotate_leaf, E.F_refine_leaf. cbn [fst].
      apply inv_set; [exact Hcurrent|exact Hdeclared|].
      apply D.meet_width; [now apply read_width|exact Hq].
    - inversion Htyped as [|w' z|op es' ws w' Hchildren Hresult]; subst.
      + rewrite E.annotate_node, E.F_refine_node. cbn [map fst]. exact Hcurrent.
      + pose proof (D.backward_width (BOp op) q
          (map (fun e => E.root (E.annotate cached e)) es) ws w Hresult Hq
          (annotations_width p cached es ws Hcached Hchildren)) as Hrequests.
        rewrite E.annotate_node, E.F_refine_node, map_map.
        remember (V.backward (BOp op) q
          (map (fun e => E.root (E.annotate cached e)) es)) as requests.
        clear Heqrequests Htyped Hresult Hq.
        revert IH current Hcurrent requests Hrequests.
        generalize false as bad.
        induction Hchildren as [|e es child_width widths Hhead Htail IHtail];
          intros bad IH current Hcurrent requests Hrequests.
        * cbn [map fst]. exact Hcurrent.
        * inversion IH as [|e' IHe es' IHrest]; subst.
          inversion Hrequests as [|w' request ws' requests' Hrequest Hrest]; subst.
          cbn [map fst]. apply IHtail; [exact IHrest| |exact Hrest].
          eapply IHe; eassumption.
  Qed.

  (** Existentially typed guard operands admit a common ordered width list. *)
  Lemma typed_terms_widths : forall p es,
    Forall (fun e => exists w, word_term_typed (P.variables p) (P.width_of p) e w) es ->
    exists ws, word_terms_typed (P.variables p) (P.width_of p) es ws.
  Proof.
    intros p es Htyped. induction Htyped as [|e es [w He] Htail [ws Hrest]].
    - exists nil. constructor.
    - exists (w :: ws). constructor; assumption.
  Qed.

  (** Typed assignment writes a canonical result at the destination's declared width. *)
  Lemma inv_assign : forall p x e s, inv p s -> In x (P.variables p) ->
    word_term_typed (P.variables p) (P.width_of p) e (P.width_of p x) ->
    inv p (E.assign x e s).
  Proof.
    intros p x e [|m] Hinv Hdeclared Htyped; rewrite E.F_assign; [constructor|].
    apply inv_set; [exact Hinv|exact Hdeclared|].
    rewrite E.F_eval. eapply annotate_width; eassumption.
  Qed.

  (** Havoc writes top only at a declared variable. *)
  Lemma inv_havoc : forall p x s,
    inv p s -> In x (P.variables p) -> inv p (E.havoc x s).
  Proof.
    intros p x [|m] Hinv Hdeclared; rewrite E.F_havoc; [constructor|].
    apply inv_set; [exact Hinv|exact Hdeclared|apply value_inv_top].
  Qed.

  (** Sequential guard requests preserve the invariant while retaining the cached annotations. *)
  Lemma refine_fold_inv : forall p cached es ws requests current bad,
    inv p (Reached cached) -> inv p (Reached current) ->
    word_terms_typed (P.variables p) (P.width_of p) es ws ->
    Forall2 D.at_width ws requests ->
    inv p (Reached (fst (fold_left (fun result nq =>
      let next := E.refine_checked (snd nq) (fst nq) (fst result) in
      (fst next, orb (snd result) (snd next)))
      (combine (map (E.annotate cached) es) requests) (current, bad)))).
  Proof.
    intros p cached es ws requests current bad Hcached Hcurrent Htyped.
    revert requests current bad Hcurrent.
    induction Htyped as [|e es w ws Hhead Htail IH];
      intros requests current bad Hcurrent Hrequests.
    - cbn [map combine fold_left fst]. exact Hcurrent.
    - inversion Hrequests as [|w' request ws' requests' Hrequest Hrest]; subst.
      cbn [map combine fold_left fst snd]. apply IH; [|exact Hrest].
      eapply refine_checked_inv; eassumption.
  Qed.

  (** Typed guard refinement keeps every cached request at its declared operand width. *)
  Lemma inv_assume : forall p g es s, inv p s ->
    Forall (fun e => exists w, word_term_typed (P.variables p) (P.width_of p) e w) es ->
    inv p (E.assume g es s).
  Proof.
    intros p g es [|m] Hinv Htyped; rewrite E.F_assume; [constructor|].
    cbn iota zeta. rewrite map_map.
    destruct (typed_terms_widths p es Htyped) as [ws Hwidths].
    pose proof (D.guard_width g (map (fun e => E.root (E.annotate m e)) es) ws
      (annotations_width p m es ws Hinv Hwidths)) as Hrequests.
    pose proof (refine_fold_inv p m es ws
      (V.guard g (map (fun e => E.root (E.annotate m e)) es)) m false
      Hinv Hinv Hwidths Hrequests) as Hrefined.
    match goal with
    | |- inv _ (if ?bad then _ else _) => destruct bad
    end; [constructor|exact Hrefined].
  Qed.

  (** Each well-typed instruction preserves the canonical environment invariant. *)
  Lemma inv_instruction : forall p i s,
    P.typed_instruction p i -> inv p s -> inv p (P.apply_instruction i s).
  Proof.
    intros p [x e|x|g es|] s Htyped Hinv; cbn [P.apply_instruction].
    - destruct Htyped as [Hdeclared Hterm]. now apply inv_assign.
    - now apply inv_havoc.
    - now apply inv_assume.
    - exact Hinv.
  Qed.

  (** Ordered well-typed instructions preserve the invariant from their actual source state. *)
  Lemma inv_instructions : forall p instructions s,
    Forall (P.typed_instruction p) instructions -> inv p s ->
    inv p (fold_left (fun s i => P.apply_instruction i s) instructions s).
  Proof.
    intros p instructions s Htyped. revert s.
    induction Htyped as [|i instructions Hi Hrest IH]; intros s Hinv.
    - exact Hinv.
    - cbn [fold_left]. apply IH. now apply inv_instruction.
  Qed.

  (** Typed operational rows preserve the representation invariant on every contribution. *)
  Lemma inv_rows : forall p r look a ss, S.wf p -> In r (S.rows p) ->
    (forall x, inv p (look x)) -> S.eval p r look = Some (a, ss) ->
    inv p a /\ Forall (fun xa => inv p (snd xa)) ss.
  Proof.
    intros p r look a ss Hwf Hrow Hlook Heval.
    rewrite (P.row_execution p r look Hwf Hrow) in Heval.
    injection Heval as <- <-. split; [|constructor].
    pose proof (P.instruction_typed p r Hwf Hrow) as Htyped.
    destruct (P.row_plan p r) as [[source instructions]|] in Htyped |- *.
    - now apply inv_instructions.
    - apply inv_top.
  Qed.

  (** Canonical representation sizes fit the program's sum of width-dependent envelopes. *)
  Lemma size_le : forall p a, inv p a -> E.size a <= vsize p.
  Proof.
    intros p [|m] Hinv.
    - rewrite P.size_unreached. lia.
    - destruct Hinv as [Hwf Hvalues]. rewrite P.size_environment, budget_sum_seed.
      rewrite (budget_codes_sum m (fun a => V.size a + 1) Hwf).
      pose proof (M.nodes_le_weight V.t m Hwf) as Hnodes.
      unfold M.weight in Hnodes.
      assert (Hsum : fold_right Nat.add 0
        (map (fun xa => (X.bits (fst xa) + 1) + (V.size (snd xa) + 1)) (M.elements m)) <=
        fold_right Nat.add 0
          (map (fun x => X.bits x + Pos.to_nat (P.width_of p x) +
            C.payload_size_bound (P.width_of p x) + 3) (P.variables p))).
      { apply budget_declared_sum; [split; assumption|].
        intros x a Hin. rewrite Forall_forall in Hvalues.
        pose proof (budget_value_size p x a (proj2 (Hvalues (x, a) Hin))). cbn. lia. }
      rewrite budget_sum_pair in Hsum.
      unfold vsize. rewrite budget_sum_seed. unfold X.bits in *. lia.
  Qed.

  (** Canonical environments store at most one binding per declared variable. *)
  Lemma wunits_le : forall p a, inv p a -> E.wunits a <= wunits p.
  Proof.
    intros p [|m] Hinv.
    - rewrite E.F_wunits_unreached. lia.
    - rewrite E.F_wunits_reached. unfold wunits.
      destruct Hinv as [Hwf Hvalues].
      pose proof (Permutation_length (budget_codes_elements m Hwf)) as Hlength.
      rewrite length_map in Hlength. rewrite Hlength.
      rewrite <- (length_map fst (M.elements m)). apply NoDup_incl_length.
      + now apply M.elements_nodup.
      + intros x Hx. apply in_map_iff in Hx. destruct Hx as [[y a] [Heq Hin]].
        cbn in Heq. subst y. rewrite Forall_forall in Hvalues.
        exact (proj1 (Hvalues (x, a) Hin)).
  Qed.

  (** Canonical payload ranks fit the program's sum of parameter-dependent rank envelopes. *)
  Lemma wrank_le : forall p w a, inv p a -> E.wrank w a <= wmax p w.
  Proof.
    intros p w [|m] Hinv.
    - rewrite P.rank_unreached. lia.
    - rewrite E.wrank_env by exact (proj1 Hinv). unfold wmax.
      apply budget_declared_sum; [exact Hinv|].
      intros x a Hin. destruct Hinv as [_ Hvalues]. rewrite Forall_forall in Hvalues.
      exact (budget_value_rank p w x a (proj2 (Hvalues (x, a) Hin))).
  Qed.
End EnvBudget.
