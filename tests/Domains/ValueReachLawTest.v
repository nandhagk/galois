(** * Reachability semantic interface clients

    The old Boolean reachability transfers can be supplied to current product laws.
    For example, product forward soundness follows from the current product interface.
    Builds on: ValueOpenTest, Product and Translate. *)

From Stdlib Require Import List Bool.
From Galois.Lattice Require Import Simple.
From Galois.Domains Require Import LangSig ValueSig Product Translate.
From Galois.Tests.Domains Require Import ValueOpenTest TranslateTest.
Import List.ListNotations.

Module Type REACH_EXTRA.
  Parameter wrank : unit -> bool -> nat.
  Parameter widen_ub_l : forall p a b, ReachCode.leb a (ReachCode.widen p a b) = true.
  Parameter widen_ub_r : forall p a b, ReachCode.leb b (ReachCode.widen p a b) = true.
  Parameter widen_stable : forall p a b, ReachCode.leb b a = true -> ReachCode.widen p a b = a.
  Parameter wrank_widen : forall p a b, ReachCode.is_bot a = false -> ReachCode.leb b a = false ->
    (wrank p (ReachCode.widen p a b) < wrank p a)%nat.
  Parameter wrank_widen_le : forall p a b, ReachCode.is_bot a = false ->
    (wrank p (ReachCode.widen p a b) <= wrank p a)%nat.
  Parameter narrow_between : forall a b, ReachCode.leb b a = true ->
    ReachCode.leb b (ReachCode.narrow a b) = true /\
    ReachCode.leb (ReachCode.narrow a b) a = true.
  Parameter gamma_meet : forall a b c,
    ReachCode.gamma a c -> ReachCode.gamma b c -> ReachCode.gamma (ReachCode.meet a b) c.
  Parameter is_bot_sound : forall a c, ReachCode.is_bot a = true -> ~ ReachCode.gamma a c.
  Parameter is_bot_below : forall a b,
    ReachCode.leb a b = true -> ReachCode.is_bot b = true -> ReachCode.is_bot a = true.
End REACH_EXTRA.

Module ReachCertified (Extra : REACH_EXTRA) <: VALUE_DOMAIN UnitLanguage.
  Include ReachCode.
  Definition leb_refl := BoolLat.leb_refl.
  Definition leb_trans := BoolLat.leb_trans.
  Definition bot_least := BoolLat.bot_least.
  Definition is_bot_bot := BoolLat.is_bot_bot.
  Definition is_bot_least := BoolLat.is_bot_least.
  Definition join_ub_l := BoolLat.join_ub_l.
  Definition join_ub_r := BoolLat.join_ub_r.
  Definition top_greatest := BoolLat.top_greatest.
  Definition meet_lb_l := BoolLat.meet_lb_l.
  Definition wrank := Extra.wrank.
  Definition widen_ub_l := Extra.widen_ub_l.
  Definition widen_ub_r := Extra.widen_ub_r.
  Definition widen_stable := Extra.widen_stable.
  Definition wrank_widen := Extra.wrank_widen.
  Definition wrank_widen_le := Extra.wrank_widen_le.
  Definition narrow_between := Extra.narrow_between.
  Definition gamma_mono := reach_gamma_mono.
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof. intros c Hbot. discriminate Hbot. Qed.
  Lemma gamma_top : forall c, gamma top c.
  Proof. intros c. reflexivity. Qed.
  Definition gamma_meet := Extra.gamma_meet.
  Definition is_bot_sound := Extra.is_bot_sound.
  Definition is_bot_below := Extra.is_bot_below.
  Definition forward_sound := reach_forward_sound.
  Definition backward_sound := reach_backward_sound.
  Definition backward_refines := reach_backward_refines.
  Definition guard_sound := reach_guard_sound.
  Definition guard_refines := reach_guard_refines.
End ReachCertified.

Module ReachProductClients (Extra : REACH_EXTRA).
  Module D := ReachCertified Extra.
  Module P := Product UnitLanguage D D.
  Module Renamed := Translate SourceLanguage UnitLanguage FixtureMorphism D.
  Definition identity_product_forward_law := P.forward_sound.
  Definition identity_product_backward_law := P.backward_sound.
  Definition identity_product_guard_law := P.guard_sound.
  Definition renamed_forward_law := Renamed.forward_sound.
  Definition renamed_backward_law := Renamed.backward_sound.
  Definition renamed_guard_law := Renamed.guard_sound.
End ReachProductClients.
