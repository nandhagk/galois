(** * Value semantic law clients

    These clients instantiate product and translated domain laws over integer intervals.
    For example, a product forward result describes each concrete evaluation result.
    Builds on: Product, Translate and Interval. *)

From Stdlib Require Import List ZArith.
From Galois.Domains Require Import LangSig ValueSig Product Translate Interval Thresholds ZLang.
Import List.ListNotations.

Module IntValues := Interval ZLang Thresholds.
Module PairValues := Product ZLang IntValues IntValues.

Example product_forward_law : forall o xs cs c,
  Forall2 PairValues.gamma xs cs -> ZLang.eval o cs = Some c ->
  PairValues.gamma (PairValues.forward o xs) c.
Proof. exact PairValues.forward_sound. Qed.

Example product_guard_law : forall g xs cs,
  Forall2 PairValues.gamma xs cs -> ZLang.holds g cs ->
  Forall2 PairValues.gamma (PairValues.guard g xs) cs.
Proof. exact PairValues.guard_sound. Qed.

Module TranslationClients (L1 L2 : LANG) (F : LANG_MORPHISM L1 L2)
    (D : VALUE_DOMAIN L2).
  Module Renamed := Translate L1 L2 F D.
  Definition renamed_forward_law := Renamed.forward_sound.
  Definition renamed_backward_law := Renamed.backward_sound.
  Definition renamed_guard_law := Renamed.guard_sound.
End TranslationClients.

Module IdentityLanguage.
  Definition op (o : ZLang.op) := o.
  Definition guard (g : ZLang.guard) := g.
  Definition value (z : ZLang.val) := z.
  Lemma eval_commutes : forall o cs,
    ZLang.eval (op o) (map value cs) = option_map value (ZLang.eval o cs).
  Proof.
    intros o cs. unfold op, value. rewrite map_id.
    destruct (ZLang.eval o cs); reflexivity.
  Qed.
  Lemma guard_preserves : forall g cs,
    ZLang.holds g cs -> ZLang.holds (guard g) (map value cs).
  Proof. intros g cs H. unfold guard, value. now rewrite map_id. Qed.
End IdentityLanguage.

Module ConcreteTranslation := TranslationClients ZLang ZLang IdentityLanguage IntValues.

Example translated_forward_law : forall o xs cs c,
  Forall2 ConcreteTranslation.Renamed.gamma xs cs -> ZLang.eval o cs = Some c ->
  ConcreteTranslation.Renamed.gamma (ConcreteTranslation.Renamed.forward o xs) c.
Proof. exact ConcreteTranslation.renamed_forward_law. Qed.
