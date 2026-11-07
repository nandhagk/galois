(** * Circular word transfer dictionary

    The circular domain uses the shared point and empty paths and costed piece callbacks.
    Backward payloads retain the widths of their individual operands.
    For example, an eight-bit comparison operand remains eight-bit under a one-bit result fact.
    Builds on: DomainsWrappedTransfer, DomainsWrappedRefine and DomainsTagged. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTagged DomainsTransfer DomainsWrapped
  DomainsWrappedParts DomainsWrappedTransfer DomainsWrappedRefine.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition wrapped_point w a : option Z :=
  match wrapped_norm w a with
  | WItv lo hi => if Z.eqb lo hi then Some lo else None
  | _ => None
  end.

(** A successful singleton observation identifies every represented circular word. *)
Theorem wrapped_point_sound w a x z :
  wrapped_gamma w a x -> wrapped_point w a = Some z -> x = z.
Proof.
  intros Ha Hpoint. unfold wrapped_point in Hpoint.
  pose proof (proj2 (wrapped_norm_gamma w a x) Ha) as Hnormal.
  destruct (wrapped_norm w a) as [| |lo hi] eqn:Hnorm; try discriminate.
  pose proof (wrapped_norm_endpoints w a lo hi Hnorm) as [Hlo Hhi].
  destruct (Z.eqb lo hi) eqn:Heq; [|discriminate].
  apply Z.eqb_eq in Heq. subst hi. inversion Hpoint; subst z.
  destruct Hnormal as [Hx Hoffset]. rewrite wrapped_offset_self in Hoffset.
  rewrite (wrapped_offset_word_cases w lo x Hlo Hx) in Hoffset.
  destruct (lo <=? x) eqn:Horder;
    [apply Z.leb_le in Horder|apply Z.leb_gt in Horder]; destruct Hlo, Hx; lia.
Qed.

Definition wrapped_shape : Transfer.shape (width * wrapped) wrapped op width word :=
  {| Transfer.eval_c := fun o xs => Cost.step ;; Cost.ret (eval_op o xs);
     Transfer.point_c := fun wp =>
       Cost.step ;; Cost.ret
         (match wrapped_point (fst wp) (snd wp) with
          | Some z => Some (fst wp, z) | None => None end);
     Transfer.is_empty_c := fun wp =>
       Cost.step ;; Cost.ret (match snd wp with WBot => true | _ => false end);
     Transfer.inj_c := fun _ c => Cost.step ;; Cost.ret (WItv (snd c) (snd c));
     Transfer.bot_out := fun _ => WBot;
     Transfer.top_out := fun _ => WFull;
     Transfer.keep_c := fun wp => Cost.step ;; Cost.ret (wrapped_norm (fst wp) (snd wp)) |}.

(** The circular shape respects normalized result contexts and operand-specific payload meanings. *)
Theorem wrapped_shape_laws :
  transfer_sem wrapped_shape (payload_sound wrapped_gamma)
    (word_output wrapped_gamma) word_context.
Proof.
  constructor.
  - intros [w a] c [v x] Hp [Hwidth [_ Ha]].
    change (w = v) in Hwidth. subst v.
    change (match wrapped_point w a with
      | Some z => Some (w, z) | None => None end = Some c) in Hp.
    destruct (wrapped_point w a) as [z|] eqn:Hpoint; [|discriminate].
    inversion Hp; subst c. pose proof (wrapped_point_sound w a x z Ha Hpoint). congruence.
  - intros [w a] [v x] Hempty [_ [_ Ha]].
    destruct a; try discriminate. exact Ha.
  - intros rw [w z] [Hcontext Hword]. split; [exact Hword|lia].
  - intros rw c Hempty. exact Hempty.
  - intros rw c [_ Hword]. exact Hword.
  - intros rw [w a] [v z] [Hwidth [_ Ha]].
    change (w = v) in Hwidth. subst v. exact (proj2 (wrapped_norm_gamma w a z) Ha).
Qed.

Definition wrapped_bwd1_c o rw q (xs : list (width * wrapped)) : Cost.t (list wrapped) :=
  match xs with
  | [(w, a)] => Cost.step ;; Cost.ret [wrapped_assume_unary o w a rw q]
  | _ => Cost.ret []
  end.

Definition wrapped_bwd2_c o rw q (xs : list (width * wrapped)) : Cost.t (list wrapped) :=
  match xs with
  | [(wa, a); (wb, b)] =>
    Cost.map (fun refined => [fst refined; snd refined])
      (wrapped_assume_binary_c o wa wb a b rw q)
  | _ => Cost.ret []
  end.

Definition wrapped_bwd_entry o n :
    option (width -> wrapped -> list (width * wrapped) -> Cost.t (list wrapped)) :=
  match n with
  | 1%nat => Some (wrapped_bwd1_c o)
  | 2%nat => Some (wrapped_bwd2_c o)
  | _ => None
  end.

Definition wrapped_table : Transfer.table (width * wrapped) wrapped op width :=
  {| Transfer.fwd := fun o n => Cost.step ;; Cost.ret (wrapped_fwd_entry o n);
     Transfer.bwd := fun o n => Cost.step ;; Cost.ret (wrapped_bwd_entry o n) |}.

Local Lemma wrapped_bwd1_sound o rw q xs cs z :
  length xs = 1%nat -> Forall2 (payload_sound wrapped_gamma) xs cs ->
  eval_op o cs = Some (rw, z) -> wrapped_gamma rw q z ->
  Forall2 (word_output wrapped_gamma rw) (Cost.value (wrapped_bwd1_c o rw q xs)) cs.
Proof.
  intros Hlength Hxs Heval Hq.
  destruct xs as [|[w a] [|surplus rest]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [v x] tail values Ha Htail]; subst.
  inversion Htail; subst. destruct Ha as [Hwidth [_ Ha]].
  change (w = v) in Hwidth. subst v.
  constructor; [|constructor]. eapply wrapped_assume_unary_sound; eassumption.
Qed.

Local Lemma wrapped_bwd2_sound o rw q xs cs z :
  length xs = 2%nat -> Forall2 (payload_sound wrapped_gamma) xs cs ->
  eval_op o cs = Some (rw, z) -> wrapped_gamma rw q z ->
  Forall2 (word_output wrapped_gamma rw) (Cost.value (wrapped_bwd2_c o rw q xs)) cs.
Proof.
  intros Hlength Hxs Heval Hq.
  destruct xs as [|[wa a] [|[wb b] [|surplus rest]]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [wx x] tail values Ha Htail]; subst.
  inversion Htail as [|wp [wy y] tail' values' Hb Hlast]; subst.
  inversion Hlast; subst.
  destruct Ha as [Hwa [_ Ha]], Hb as [Hwb [_ Hb]].
  change (wa = wx) in Hwa. change (wb = wy) in Hwb. subst wx wy.
  pose proof (wrapped_assume_binary_sound o wa wb a b rw q x y z Ha Hb Hq Heval)
    as [Hleft Hright].
  constructor; [exact Hleft|constructor; [exact Hright|constructor]].
Qed.

(** Circular forward and backward callbacks satisfy all harness semantic and length premises. *)
Theorem wrapped_table_laws :
  table_laws wrapped_table wrapped_shape (payload_sound wrapped_gamma)
    (word_output wrapped_gamma) word_context.
Proof.
  constructor.
  - intros o n f rw xs cs [v z] Hentry Hlength Hxs Heval [Hcontext Hword].
    change (v = rw) in Hcontext. subst v.
    change (wrapped_fwd_entry o n = Some f) in Hentry.
    eapply wrapped_fwd_entry_sound; eassumption.
  - intros o n f rw q xs cs [v z] Hentry Hlength Hxs Heval [Hcontext Hword] Hq.
    change (v = rw) in Hcontext. subst v.
    change (wrapped_bwd_entry o n = Some f) in Hentry.
    destruct n as [|[|[|n]]]; cbn [wrapped_bwd_entry] in Hentry; try discriminate;
      inversion Hentry; subst;
      first [eapply wrapped_bwd1_sound; eassumption|eapply wrapped_bwd2_sound; eassumption].
  - intros o n f rw q xs Hentry Hlength.
    change (wrapped_bwd_entry o n = Some f) in Hentry.
    destruct n as [|[|[|n]]]; cbn [wrapped_bwd_entry] in Hentry; try discriminate;
      inversion Hentry; subst;
      destruct xs as [|[wa a] [|[wb b] [|surplus rest]]];
      cbn in Hlength; try discriminate; reflexivity.
Qed.

(** Every circular backward callback is structurally reductive without concrete witnesses. *)
Theorem wrapped_table_refines :
  table_refines wrapped_table wrapped_shape
    (fun wp p => wrapped_leb (fst wp) p (snd wp) = true).
Proof.
  constructor.
  - intros [w a]. exact (proj2 (wrapped_norm_leb w a)).
  - intros o n f rw q xs Hentry Hlength.
    change (wrapped_bwd_entry o n = Some f) in Hentry.
    destruct n as [|[|[|n]]]; cbn [wrapped_bwd_entry] in Hentry; try discriminate;
      inversion Hentry; subst.
    + destruct xs as [|[w a] [|surplus rest]]; cbn in Hlength; try discriminate.
      constructor; [apply wrapped_assume_unary_lower|constructor].
    + destruct xs as [|[wa a] [|[wb b] [|surplus rest]]]; cbn in Hlength; try discriminate.
      destruct (wrapped_assume_binary_lower o wa wb a b rw q) as [Hleft Hright].
      constructor; [exact Hleft|constructor; [exact Hright|constructor]].
Qed.

Definition wrapped_word_domain : word_domain wrapped :=
  word_of_table wrapped_table wrapped_shape wrapped_lattice (fun _ => WFull)
    (fun w z => Cost.step ;; Cost.ret (WItv (wrap w z) (wrap w z)))
    (fun w a b => Cost.step ;; Cost.ret (wrapped_meet w a b)).

(** Circular word transfer preserves all concrete words and both refinement directions. *)
Theorem wrapped_word_laws : word_laws wrapped_word_domain wrapped_gamma.
Proof.
  apply word_of_table_laws.
  - intros. reflexivity.
  - exact wrapped_shape_laws.
  - exact wrapped_table_laws.
  - apply wrapped_laws.
  - intros w a b z Hle Hz. exact (proj1 (wrapped_leb_spec w a b) Hle z Hz).
  - intros w z Hempty. exact Hempty.
  - intros w z Hz. exact Hz.
  - intros w z. split; [apply wrap_is_word|lia].
  - exact wrapped_table_refines.
  - apply wrapped_meet_sound.
  - apply wrapped_meet_lower_left.
Qed.

Definition wrapped_domain := tagged_domain wrapped_word_domain.

(** Tagging circular payloads derives the full numeric laws. *)
Theorem wrapped_numeric_laws :
  numeric_laws wrapped_domain (tagged_gamma wrapped_gamma).
Proof.
  apply tagged_numeric_laws. exact wrapped_word_laws.
Qed.
