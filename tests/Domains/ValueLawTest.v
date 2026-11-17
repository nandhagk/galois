(** * Value semantic law clients

    These clients instantiate product and translated domain laws over integer intervals.
    For example, a product forward result describes each concrete evaluation result.

    Groups:
    - [ProductTests] The forward and guard laws of a product of two interval domains.
    - [TranslationTests] The translated forward law under the identity language.

    Builds on: Product, Translate and Interval. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import LangSig ValueSig Product Translate Interval Thresholds ZLang.
Import List.ListNotations.

(** * Fixtures *)

(** Interval values over integer operators. *)
Module IntValues := Interval ZLang Thresholds.
(** Pairs of interval values over integer operators. *)
Module PairValues := Product ZLang IntValues IntValues.

(** Translation laws for any source language, morphism and value domain. *)
Module TranslationClients (L1 L2 : LANG) (F : LANG_MORPHISM L1 L2)
    (D : VALUE_DOMAIN L2).
  (** The translated domain. *)
  Module Renamed := Translate L1 L2 F D.
  (** The forward law of the translated domain. *)
  Definition renamed_forward_law := Renamed.forward_sound.
  (** The backward law of the translated domain. *)
  Definition renamed_backward_law := Renamed.backward_sound.
  (** The guard law of the translated domain. *)
  Definition renamed_guard_law := Renamed.guard_sound.
End TranslationClients.

(** The morphism from integer operators to themselves. *)
Module IdentityLanguage.
  (** Operators map to themselves. *)
  Definition op (o : ZLang.op) := o.
  (** Guards map to themselves. *)
  Definition guard (g : ZLang.guard) := g.
  (** Values map to themselves. *)
  Definition value (z : ZLang.val) := z.
  (** Translating the operands first gives the translated evaluation result. *)
  Lemma eval_commutes : forall o cs,
    ZLang.eval (op o) (map value cs) = option_map value (ZLang.eval o cs).
  Proof.
    intros o cs. unfold op, value. rewrite map_id.
    destruct (ZLang.eval o cs); reflexivity.
  Qed.
  (** A guard that holds still holds after translation. *)
  Lemma guard_preserves : forall g cs,
    ZLang.holds g cs -> ZLang.holds (guard g) (map value cs).
  Proof. intros g cs H. unfold guard, value. now rewrite map_id. Qed.
End IdentityLanguage.

(** Translation clients instantiated with the identity language over intervals. *)
Module ConcreteTranslation := TranslationClients ZLang ZLang IdentityLanguage IntValues.

(** * Product *)

Module ProductTests.

  (** The forward result of a product describes each concrete evaluation result. *)
  Example forward_describes_concrete_result : forall o xs cs c,
    Forall2 PairValues.gamma xs cs -> ZLang.eval o cs = Some c ->
    PairValues.gamma (PairValues.forward o xs) c.
  Proof. exact PairValues.forward_sound. Qed.

  (** The guard of a product keeps every operand described by the concrete operands. *)
  Example guard_keeps_operands_described : forall g xs cs,
    Forall2 PairValues.gamma xs cs -> ZLang.holds g cs ->
    Forall2 PairValues.gamma (PairValues.guard g xs) cs.
  Proof. exact PairValues.guard_sound. Qed.

End ProductTests.

(** * Translation *)

Module TranslationTests.

  (** The translated forward result describes each concrete evaluation result. *)
  Example translated_forward_describes_concrete_result : forall o xs cs c,
    Forall2 ConcreteTranslation.Renamed.gamma xs cs -> ZLang.eval o cs = Some c ->
    ConcreteTranslation.Renamed.gamma (ConcreteTranslation.Renamed.forward o xs) c.
  Proof. exact ConcreteTranslation.renamed_forward_law. Qed.

End TranslationTests.
