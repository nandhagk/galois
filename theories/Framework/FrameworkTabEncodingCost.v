(** * Primitive costs of tabulation keys

    Composite-key budgets retain every component callback and every serialized bit.
    For example, an incoming key contains a caller vertex and an exploded arc occurrence.
    Builds on: FrameworkUtil, FrameworkTabulate and the public BaseCode cost contracts. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkTabulate.
Import Cost.Notations.

Module TabEncodingCost.

(** A local budget bounds one genuine encoding callback and its resulting positive width. *)
Definition bounded {K} (E : encoding K) x e w : Prop :=
  (Cost.ticks (encode_c E x) <= e)%N /\ (key_bits E x <= w)%N.

Definition pair_width a b := (7 + 2 * a + 2 * b)%N.
Definition pair_charge ea eb wa wb :=
  (9 + ea + eb + encode_k * pair_width wa wb)%N.
Definition option_width w := (8 + 2 * w)%N.
Definition option_charge e w := (9 + e + encode_k * option_width w)%N.

(** Framework pairs retain both component widths and every serialization tag. *)
Theorem pair_bits {X Y} (EX : encoding X) (EY : encoding Y) x y :
  key_bits (FrameworkKey.pair EX EY) (x, y) =
    pair_width (key_bits EX x) (key_bits EY y).
Proof.
  unfold FrameworkKey.pair, key_bits at 1; rewrite encoding_comap_equation.
  change (key_bits (codec_enc (pair_codec positive_codec positive_codec))
    (encode EX x, encode EY y) = pair_width (key_bits EX x) (key_bits EY y)).
  rewrite pair_codec_bits, !positive_encoding_bits; reflexivity.
Qed.

(** Pair construction pays component conversion before the public binary serializer. *)
Theorem pair_cost {X Y} (EX : encoding X) (EY : encoding Y) x y :
  (Cost.ticks (encode_c (FrameworkKey.pair EX EY) (x, y)) <=
    pair_charge (Cost.ticks (encode_c EX x)) (Cost.ticks (encode_c EY y))
      (key_bits EX x) (key_bits EY y))%N.
Proof.
  unfold FrameworkKey.pair; rewrite encoding_comap_cost.
  pose proof (pair_codec_cost positive_codec positive_codec (encode EX x) (encode EY y))
    as Hserialize.
  rewrite !positive_encoding_cost, pair_codec_bits, !positive_encoding_bits in Hserialize.
  fold (key_bits EX x) (key_bits EY y) in Hserialize.
  cbn [FrameworkKey.pair_c fst snd]; autorewrite with galois_cost.
  unfold pair_charge, pair_width; change
    (2 + (1 + (Cost.ticks (encode_c EX x) + (1 + (Cost.ticks (encode_c EY y) + 0)))) +
      Cost.ticks (encode_c (codec_enc (pair_codec positive_codec positive_codec))
        (encode EX x, encode EY y)) <=
      9 + Cost.ticks (encode_c EX x) + Cost.ticks (encode_c EY y) +
        encode_k * (7 + 2 * key_bits EX x + 2 * key_bits EY y))%N.
  lia.
Qed.

(** Local primitive budgets compose without a law or finiteness premise on their carriers. *)
Theorem pair_bounded {X Y} (EX : encoding X) (EY : encoding Y) x y ex ey wx wy :
  bounded EX x ex wx -> bounded EY y ey wy ->
  bounded (FrameworkKey.pair EX EY) (x, y)
    (pair_charge ex ey wx wy) (pair_width wx wy).
Proof.
  intros [Hex Hwx] [Hey Hwy]; split.
  - pose proof (pair_cost EX EY x y) as Hcost.
    unfold pair_charge, pair_width in *; nia.
  - rewrite pair_bits; unfold pair_width; lia.
Qed.

(** Tagged sums retain the selected component width and its actual serialization tags. *)
Theorem sum_bits {X Y} (EX : encoding X) (EY : encoding Y) v :
  key_bits (FrameworkKey.sum EX EY) v =
    match v with
    | inl x => (5 + 2 * key_bits EX x)%N
    | inr y => (8 + 2 * key_bits EY y)%N
    end.
Proof.
  unfold FrameworkKey.sum, key_bits at 1; rewrite encoding_comap_equation.
  destruct v as [x|y].
  - change (key_bits (codec_enc (sum_codec positive_codec positive_codec))
      (inl (encode EX x)) = (5 + 2 * key_bits EX x)%N).
    rewrite sum_codec_bits, positive_encoding_bits; reflexivity.
  - change (key_bits (codec_enc (sum_codec positive_codec positive_codec))
      (inr (encode EY y)) = (8 + 2 * key_bits EY y)%N).
    rewrite sum_codec_bits, positive_encoding_bits; reflexivity.
Qed.

(** Tagged sums price only their selected original component callback and emitted binary code. *)
Theorem sum_cost {X Y} (EX : encoding X) (EY : encoding Y) v :
  (Cost.ticks (encode_c (FrameworkKey.sum EX EY) v) <=
    6 + match v with
        | inl x => Cost.ticks (encode_c EX x)
        | inr y => Cost.ticks (encode_c EY y)
        end + encode_k * key_bits (FrameworkKey.sum EX EY) v)%N.
Proof.
  destruct v as [x|y]; rewrite sum_bits;
    unfold FrameworkKey.sum; rewrite encoding_comap_cost;
    cbn [FrameworkKey.sum_c]; autorewrite with galois_cost.
  - pose proof (sum_codec_cost positive_codec positive_codec (inl (encode EX x)))
      as Hserialize.
    cbn beta iota zeta in Hserialize.
    rewrite positive_encoding_cost, sum_codec_bits in Hserialize.
    cbn beta iota zeta in Hserialize; rewrite positive_encoding_bits in Hserialize.
    fold (key_bits EX x) in Hserialize.
    change (2 + (1 + Cost.ticks (encode_c EX x)) +
      Cost.ticks (encode_c (codec_enc (sum_codec positive_codec positive_codec))
        (inl (encode EX x))) <=
      6 + Cost.ticks (encode_c EX x) + encode_k * (5 + 2 * key_bits EX x))%N.
    lia.
  - pose proof (sum_codec_cost positive_codec positive_codec (inr (encode EY y)))
      as Hserialize.
    cbn beta iota zeta in Hserialize.
    rewrite positive_encoding_cost, sum_codec_bits in Hserialize.
    cbn beta iota zeta in Hserialize; rewrite positive_encoding_bits in Hserialize.
    fold (key_bits EY y) in Hserialize.
    change (2 + (1 + Cost.ticks (encode_c EY y)) +
      Cost.ticks (encode_c (codec_enc (sum_codec positive_codec positive_codec))
        (inr (encode EY y))) <=
      6 + Cost.ticks (encode_c EY y) + encode_k * (8 + 2 * key_bits EY y))%N.
    lia.
Qed.

Definition sum_width w := (8 + 2 * w)%N.
Definition sum_charge e w := (6 + e + encode_k * sum_width w)%N.

(** A selected alternative satisfies a uniform budget from that component's primitive bound. *)
Theorem sum_bounded {X Y} (EX : encoding X) (EY : encoding Y) v e w :
  (match v with
   | inl x => bounded EX x e w
   | inr y => bounded EY y e w
   end) ->
  bounded (FrameworkKey.sum EX EY) v (sum_charge e w) (sum_width w).
Proof.
  intro Hbound; pose proof (sum_cost EX EY v) as Hcost.
  split.
  - rewrite sum_bits in Hcost; destruct v as [x|y]; destruct Hbound as [He Hw];
      unfold sum_charge, sum_width; nia.
  - rewrite sum_bits; destruct v as [x|y]; destruct Hbound as [He Hw];
      unfold sum_width; lia.
Qed.

(** Optional facts retain the zero tag and the selected fact code. *)
Theorem option_bits {D} (ED : encoding D) d :
  key_bits (FrameworkKey.option ED) d =
    match d with
    | None => 7%N
    | Some x => option_width (key_bits ED x)
    end.
Proof.
  unfold FrameworkKey.option, key_bits at 1; rewrite encoding_comap_equation.
  destruct d as [x|].
  - change (key_bits (FrameworkKey.sum unit_encoding ED) (inr x) =
      option_width (key_bits ED x)).
    rewrite sum_bits; reflexivity.
  - change (key_bits (FrameworkKey.sum unit_encoding ED) (inl tt) = 7%N).
    rewrite sum_bits, unit_encoding_bits; reflexivity.
Qed.

(** Optional encoding budgets concern the selected fact alone, including the zero boundary. *)
Theorem option_bounded {D} (ED : encoding D) d e w :
  (match d with Some x => bounded ED x e w | None => True end) ->
  bounded (FrameworkKey.option ED) d (option_charge e w) (option_width w).
Proof.
  intro Hd; split.
  - unfold FrameworkKey.option; rewrite encoding_comap_cost, Cost.ticks_ret.
    pose proof (sum_cost unit_encoding ED
      (match d with None => inl tt | Some x => inr x end)) as Hcost.
    destruct d as [x|]; rewrite sum_bits in Hcost.
    + change (2 + 0 + Cost.ticks (encode_c (FrameworkKey.sum unit_encoding ED) (inr x)) <=
        option_charge e w)%N.
      change (Cost.ticks (encode_c (FrameworkKey.sum unit_encoding ED) (inr x)) <=
        6 + Cost.ticks (encode_c ED x) + encode_k * (8 + 2 * key_bits ED x))%N in Hcost.
      destruct Hd as [He Hw]; unfold option_charge, option_width in *; nia.
    + rewrite unit_encoding_cost, unit_encoding_bits in Hcost.
      change (2 + 0 + Cost.ticks (encode_c (FrameworkKey.sum unit_encoding ED) (inl tt)) <=
        option_charge e w)%N.
      unfold option_charge, option_width; nia.
  - rewrite option_bits; destruct d as [x|].
    + destruct Hd as [He Hw]; unfold option_width; lia.
    + unfold option_width; lia.
Qed.

(** A vertex uses the actual node and optional-fact callbacks. *)
Theorem vertex_bounded {N E P D A F} (I : Ide.t N E P D A F) n d en ed wn wd :
  bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) n en wn ->
  (match d with Some x => bounded (Ifds.fact_enc (Ide.ifds I)) x ed wd | None => True end) ->
  bounded (IdeValue.key_enc I) (n, d)
    (pair_charge en (option_charge ed wd) wn (option_width wd))
    (pair_width wn (option_width wd)).
Proof.
  intros Hn Hd; apply pair_bounded; [exact Hn|apply option_bounded; exact Hd].
Qed.

(** Jump encoding pays the two complete vertex constructions before pairing their codes. *)
Theorem jump_bounded {N E P D A F} (I : Ide.t N E P D A F) root dst e w :
  bounded (IdeValue.key_enc I) root e w -> bounded (IdeValue.key_enc I) dst e w ->
  bounded (Jump.enc I) (root, dst) (pair_charge e e w w) (pair_width w w).
Proof.
  destruct root as [r x], dst as [n y]; apply pair_bounded.
Qed.

(** Exploded occurrence codes retain the edge and both optional-fact encodings. *)
Theorem arc_bounded {N E P D A F} (I : Ide.t N E P D A F)
    (a : Jump.arc N E P D F) ee ed we wd :
  bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) (Jump.edge a) ee we ->
  (match snd (Jump.source a) with
   | Some x => bounded (Ifds.fact_enc (Ide.ifds I)) x ed wd
   | None => True
   end) ->
  (match snd (Jump.target a) with
   | Some y => bounded (Ifds.fact_enc (Ide.ifds I)) y ed wd
   | None => True
   end) ->
  let ow := option_width wd in
  let oe := option_charge ed wd in
  bounded (Tab.arc_enc I) (Tab.arc_key a)
    (pair_charge ee (pair_charge oe oe ow ow) we (pair_width ow ow))
    (pair_width we (pair_width ow ow)).
Proof.
  intros He Hx Hy; apply pair_bounded; [exact He|].
  apply pair_bounded; apply option_bounded; assumption.
Qed.

(** Incoming encoding retains its own caller vertex and actual exploded occurrence construction. *)
Theorem incoming_bounded {N E P D A F} (I : Ide.t N E P D A F) root
    (a : Jump.arc N E P D F) ev ea wv wa :
  bounded (IdeValue.key_enc I) root ev wv ->
  bounded (Tab.arc_enc I) (Tab.arc_key a) ea wa ->
  bounded (Tab.incoming_enc I) (root, Tab.arc_key a)
    (pair_charge ev ea wv wa) (pair_width wv wa).
Proof.
  apply pair_bounded.
Qed.

End TabEncodingCost.
