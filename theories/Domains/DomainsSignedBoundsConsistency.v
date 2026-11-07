(** * Ordinary range consistency checks

    Backward consistency keeps the legacy ordinary endpoint cover before modular refinement.
    For example, an overflowing unsigned rectangle is top even when signed multiplication is narrow.
    Builds on: DomainsSignedBoundsForward and DomainsSignedBoundsMod. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsArith BitsTestbit.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsSignedBounds
  DomainsSignedBoundsRange DomainsSignedBoundsArith DomainsSignedBoundsMod
  DomainsSignedBoundsForward.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition sb_udiv_bound (w : width) (a b : sb_range) : sb_range :=
  hd (0, modulus w - 1) (sb_range_udiv w a b).

Lemma sb_udiv_one_range : forall w a b, sb_range_udiv w a b = [sb_udiv_bound w a b].
Proof.
  intros w [la ua] [lb ub]. unfold sb_udiv_bound, sb_range_udiv.
  destruct ((0 <=? la) && (0 <? lb)); [rewrite sb_checked_ranges_pair; reflexivity|].
  destruct ((0 <=? la) && (lb =? 0) && (0 <? ub));
    [rewrite sb_checked_ranges_pair; reflexivity|].
  destruct ((lb =? 0) && (ub =? 0)); reflexivity.
Qed.

Lemma sb_udiv_bound_sound : forall w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_udiv_bound w a b) (wudiv w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (sb_range_udiv_sound w a b x y Hx Hy Ha Hb) as H.
  rewrite sb_udiv_one_range in H. now apply sb_single_range_gamma in H.
Qed.

Definition sb_signed_ordinary_bound (division : bool) (w : width) (a b : sb_range)
    : sb_range :=
  match sb_range_sign w a, sb_range_sign w b with
  | Some sa, Some sb =>
    let aa := sb_range_magnitude w sa a in
    let bb := sb_range_magnitude w sb b in
    let r := if division then sb_udiv_bound w aa bb else sb_urem_bound w aa bb in
    if (if division then xorb sa sb else sa) then sb_neg_bound w r else r
  | _, _ => (0, modulus w - 1)
  end.

Lemma sb_signed_ordinary_bound_sound : forall division w a b x y,
  is_word w x -> is_word w y -> sb_range_gamma a x -> sb_range_gamma b y ->
  sb_range_gamma (sb_signed_ordinary_bound division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  intros division w a b x y Hx Hy Ha Hb.
  assert (Hresult : is_word w (if division then wsdiv w x y else wsrem w x y))
    by (destruct division; [apply wsdiv_is_word|apply wsrem_is_word]).
  unfold sb_signed_ordinary_bound.
  destruct (sb_range_sign w a) as [sa|] eqn:Hsa;
    destruct (sb_range_sign w b) as [sb|] eqn:Hsb.
  2,3,4: unfold sb_range_gamma, is_word in *; cbn [fst snd]; lia.
  pose proof (sb_range_sign_sound w a x sa Hx Ha Hsa) as Hsignx.
  pose proof (sb_range_sign_sound w b y sb Hy Hb Hsb) as Hsigny.
  pose proof (sb_range_magnitude_sound w a x sa Hx Ha Hsa) as Hmagx.
  pose proof (sb_range_magnitude_sound w b y sb Hy Hb Hsb) as Hmagy.
  assert (Hnx : is_word w (wneg w x)) by (rewrite wneg_value; apply wrap_is_word).
  assert (Hny : is_word w (wneg w y)) by (rewrite wneg_value; apply wrap_is_word).
  destruct division; destruct sa, sb; cbn [xorb];
    rewrite ?wsdiv_value, ?wsrem_value, Hsignx, Hsigny;
    try (apply sb_neg_bound_sound;
      [first [apply wudiv_is_word|apply wurem_is_word]|]);
    first [apply sb_udiv_bound_sound|apply sb_urem_bound_sound]; assumption.
Qed.

Definition sb_consistency_raw_c (o : op) (wa wb : width) (a b : sb_range) (rw : width)
    : Cost.t (list sb_range) :=
  match o with
  | bvmul => Cost.ret
    (sb_checked_ranges rw (sb_product_lower a b) (sb_product_upper a b))
  | bvsdiv => Cost.ret [sb_signed_ordinary_bound true rw a b]
  | bvsrem => Cost.ret [sb_signed_ordinary_bound false rw a b]
  | _ => sb_range_forward_c o [(wa, a); (wb, b)] rw
  end.

Lemma sb_consistency_raw_sound : forall o wa wb a b rw x y z,
  is_word wa x -> is_word wb y -> sb_range_gamma a x -> sb_range_gamma b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  sb_ranges_gamma rw (Cost.value (sb_consistency_raw_c o wa wb a b rw)) z.
Proof.
  intros o wa wb a b rw x y z Hx Hy Ha Hb Heval.
  assert (Hbase : sb_ranges_gamma rw (sb_range_forward o [(wa, a); (wb, b)] rw) z).
  { eapply sb_range_forward_sound; [|exact Heval].
    constructor; [split; [reflexivity|split; assumption]|].
    constructor; [split; [reflexivity|split; assumption]|constructor]. }
  destruct o; try exact Hbase.
  - pose proof (eval_op_fun2_width bvmul wmul wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvmul wb x y wmul eq_refl) in Heval.
    injection Heval as <- <-. rewrite wmul_value.
    apply sb_checked_ranges_wrapped_sound. now apply sb_product_bounds.
  - pose proof (eval_op_fun2_width bvsdiv wsdiv wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsdiv wb x y wsdiv eq_refl) in Heval.
    injection Heval as <- <-. split; [apply wsdiv_is_word|].
    eexists. split; [now left|]. now apply (sb_signed_ordinary_bound_sound true).
  - pose proof (eval_op_fun2_width bvsrem wsrem wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsrem wb x y wsrem eq_refl) in Heval.
    injection Heval as <- <-. split; [apply wsrem_is_word|].
    eexists. split; [now left|]. now apply (sb_signed_ordinary_bound_sound false).
Qed.

(** Binary consistency retains the ordinary singleton fast path, including signed division. *)
Definition sb_consistency_c (o : op) (wa wb : width) (a b : sb_range) (rw : width)
    : Cost.t (list sb_range) :=
  Cost.step ;;
  if (fst a =? snd a) && (fst b =? snd b) then
    let* result := known_bits_eval_c o [(wa, fst a); (wb, fst b)] in
    Cost.ret (match result with Some (_, z) => [(z, z)] | None => [] end)
  else sb_consistency_raw_c o wa wb a b rw.

Definition sb_consistency (o : op) (wa wb : width) (a b : sb_range) (rw : width)
    : list sb_range := Cost.value (sb_consistency_c o wa wb a b rw).

(** Ordinary consistency contains every successful result at its generated result width. *)
Theorem sb_consistency_sound : forall o wa wb a b rw x y z,
  is_word wa x -> is_word wb y -> sb_range_gamma a x -> sb_range_gamma b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  sb_ranges_gamma rw (sb_consistency o wa wb a b rw) z.
Proof.
  intros o wa wb [la ua] [lb ub] rw x y z Hx Hy Ha Hb Heval.
  unfold sb_consistency, sb_consistency_c. autorewrite with galois_cost.
  cbn [fst snd]. destruct ((la =? ua) && (lb =? ub)) eqn:Hpoint.
  - apply andb_true_iff in Hpoint as [Ha' Hb']. apply Z.eqb_eq in Ha', Hb'.
    assert (Hax : la = x) by (unfold sb_range_gamma in Ha; cbn [fst snd] in Ha; lia).
    assert (Hby : lb = y) by (unfold sb_range_gamma in Hb; cbn [fst snd] in Hb; lia).
    autorewrite with galois_cost. rewrite known_bits_eval_equation.
    cbn [fst snd]. rewrite Hax, Hby, Heval.
    split; [exact (eval_op_is_word _ _ (rw, z) Heval)|].
    exists (z, z). split; [now left|]. unfold sb_range_gamma. cbn [fst snd]. lia.
  - now apply (sb_consistency_raw_sound o wa wb (la, ua) (lb, ub) rw x y).
Qed.
