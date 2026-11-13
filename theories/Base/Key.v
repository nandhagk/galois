(** * Key implementations

    Scalar keys use positive encodings and reflected equality.
    For example, the positive key uses its value as its encoding.
    Builds on: Stdlib binary arithmetic and Argent time interfaces. *)

From Stdlib Require Import Bool NArith PArith ZArith Lia.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Stdlib Require Import List.
From Galois.Base Require Import Code.

Module Pos.
  TimeFun Pos.of_succ_nat.
End Pos.

Module Bool.
  TimeFun Bool.eqb.
End Bool.

Module PosKeyCode <: KEY_OPS.
  Definition t := positive.
  Definition encode (x : t) := x.
  Definition eqb := Pos.eqb.
End PosKeyCode.

Module NKeyCode <: KEY_OPS.
  Definition t := N.
  Definition encode := N.succ_pos.
  Definition eqb := N.eqb.
End NKeyCode.

Module ZKeyCode <: KEY_OPS.
  Definition t := Z.
  Definition encode (z : t) := match z with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
  Definition eqb := Z.eqb.
End ZKeyCode.

Module NatKeyCode <: KEY_OPS.
  Definition t := nat.
  Definition encode := Pos.of_succ_nat.
  Definition eqb := Nat.eqb.
End NatKeyCode.

Module BoolKeyCode <: KEY_OPS.
  Definition t := bool.
  Definition encode (b : t) := if b then xO xH else xH.
  Definition eqb := Bool.eqb.
End BoolKeyCode.

Module UnitKeyCode <: KEY_OPS.
  Definition t := unit.
  Definition encode (_ : t) := xH.
  Definition eqb (_ _ : t) := true.
End UnitKeyCode.

Module PairKeyCode (A B : KEY_OPS) <: KEY_OPS.
  Definition t := (A.t * B.t)%type.
  Definition encode := pair_code A.encode B.encode.
  Definition eqb (x y : t) := andb (A.eqb (fst x) (fst y)) (B.eqb (snd x) (snd y)).
End PairKeyCode.

Module SumKeyCode (A B : KEY_OPS) <: KEY_OPS.
  Definition t := (A.t + B.t)%type.
  Definition encode := sum_code A.encode B.encode.
  Definition eqb (x y : t) :=
    match x, y with
    | inl a, inl b => A.eqb a b
    | inr a, inr b => B.eqb a b
    | _, _ => false
    end.
End SumKeyCode.

Module OptionKeyCode (K : KEY_OPS) <: KEY_OPS.
  Definition t := option K.t.
  Definition encode := option_code K.encode.
  Definition eqb (x y : t) :=
    match x, y with
    | None, None => true
    | Some a, Some b => K.eqb a b
    | _, _ => false
    end.
End OptionKeyCode.

Module ListKeyCode (K : KEY_OPS) <: KEY_OPS.
  Definition t := list K.t.
  Definition encode := list_code K.encode.
  Fixpoint eqb (x y : t) : bool :=
    match x, y with
    | nil, nil => true
    | a :: x, b :: y => andb (K.eqb a b) (eqb x y)
    | _, _ => false
    end.
End ListKeyCode.

Module PosKey <: KEY.
  Include PosKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. intros a b Hcode. exact Hcode. Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. exact Pos.eqb_spec. Qed.
End PosKey.

Module NKey <: KEY.
  Include NKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros a b Hcode.
    apply (f_equal (fun p => N.pred (N.pos p))) in Hcode.
    now rewrite !N.succ_pos_spec, !N.pred_succ in Hcode.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. exact N.eqb_spec. Qed.
End NKey.

Module ZKey <: KEY.
  Include ZKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. intros [|a|a] [|b|b] Hcode; cbn in Hcode; congruence. Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. exact Z.eqb_spec. Qed.
End ZKey.

Module NatKey <: KEY.
  Include NatKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros a b Hcode.
    apply (f_equal (fun p => Nat.pred (Pos.to_nat p))) in Hcode.
    now rewrite !SuccNat2Pos.id_succ in Hcode.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. exact Nat.eqb_spec. Qed.
End NatKey.

Module BoolKey <: KEY.
  Include BoolKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. intros [] [] Hcode; cbn in Hcode; congruence. Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. exact Bool.eqb_spec. Qed.
End BoolKey.

Module UnitKey <: KEY.
  Include UnitKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. intros [] [] Hcode; reflexivity. Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. intros [] []; constructor; reflexivity. Qed.
End UnitKey.

Module PairKey (A B : KEY) <: KEY.
  Include PairKeyCode A B.
  Include KEY_SPEC.
  (** Equal pair codes identify each component. *)
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [a b] [a' b'] Hcode. apply glue_inj in Hcode as [Ha Hb].
    f_equal; [now apply A.encode_inj | now apply B.encode_inj].
  Qed.
  (** Component equality tests decide equality of pairs. *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [a b] [a' b']; unfold eqb; cbn [fst snd].
    destruct (A.eqb_spec a a') as [Ha | Ha];
      destruct (B.eqb_spec b b') as [Hb | Hb]; cbn; constructor; congruence.
  Qed.
End PairKey.

Module SumKey (A B : KEY) <: KEY.
  Include SumKeyCode A B.
  Include KEY_SPEC.
  (** Tags and component injectivity identify encoded sum values. *)
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [a | b] [a' | b'] Hcode; cbn [encode sum_code] in Hcode;
      try discriminate.
    - injection Hcode as Ha. f_equal. now apply A.encode_inj.
    - injection Hcode as Hb. f_equal. now apply B.encode_inj.
  Qed.
  (** Sum equality checks matching alternatives with the component test. *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [a | b] [a' | b']; cbn [eqb]; try (constructor; discriminate).
    - destruct (A.eqb_spec a a') as [Ha | Ha]; constructor; congruence.
    - destruct (B.eqb_spec b b') as [Hb | Hb]; constructor; congruence.
  Qed.
End SumKey.

Module OptionKey (K : KEY) <: KEY.
  Include OptionKeyCode K.
  Include KEY_SPEC.
  (** Option tags separate absence and preserve component injectivity. *)
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [a |] [b |] Hcode; cbn [encode option_code] in Hcode;
      try discriminate; [|reflexivity].
    injection Hcode as Hab. f_equal. now apply K.encode_inj.
  Qed.
  (** Option equality checks presence and then the component test. *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [a |] [b |]; cbn [eqb]; try (constructor; congruence).
    destruct (K.eqb_spec a b) as [Hab | Hab]; constructor; congruence.
  Qed.
End OptionKey.

Module ListKey (K : KEY) <: KEY.
  Include ListKeyCode K.
  Include KEY_SPEC.
  (** Delimited component codes identify a list and each of its elements. *)
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intro a; induction a as [|x xs IH]; intros [|y ys] Hcode;
      cbn [encode list_code] in Hcode.
    - reflexivity.
    - destruct (K.encode y); discriminate.
    - destruct (K.encode x); discriminate.
    - apply glue_inj in Hcode as [Hhead Htail].
      apply K.encode_inj in Hhead. apply IH in Htail. congruence.
  Qed.
  (** Recursive component equality decides list equality. *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intro a; induction a as [|x xs IH]; intros [|y ys]; cbn [eqb].
    - constructor; reflexivity.
    - constructor; discriminate.
    - constructor; discriminate.
    - destruct (K.eqb_spec x y) as [Hhead | Hhead];
        destruct (IH ys) as [Htail | Htail]; cbn; constructor; congruence.
  Qed.
End ListKey.

Module PosKeyT <: KEY_T.
  Include PosKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End PosKeyT.

Module NKeyT <: KEY_T.
  Include NKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End NKeyT.

Module ZKeyT <: KEY_T.
  Include ZKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End ZKeyT.

Module BoolKeyT <: KEY_T.
  Include BoolKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End BoolKeyT.

Module UnitKeyT <: KEY_T.
  Include UnitKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End UnitKeyT.

Module PairKeyT (A B : KEY_T) <: KEY_T.
  Include PairKey A B.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End PairKeyT.

Module SumKeyT (A B : KEY_T) <: KEY_T.
  Include SumKey A B.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End SumKeyT.

Module OptionKeyT (K : KEY_T) <: KEY_T.
  Include OptionKey K.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End OptionKeyT.

Module ListKeyT (K : KEY_T) <: KEY_T.
  Include ListKey K.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End ListKeyT.
