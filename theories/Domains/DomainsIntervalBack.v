(** * Interval backward entries and word dictionaries

    Result assumptions refine comparisons and invert nonwrapping arithmetic.
    Each returned payload is interpreted at its own operand width.
    For example, a one-bit comparison result can refine an eight-bit operand.
    Builds on: DomainsIntervalTransfer, DomainsIntervalRefine and DomainsTagged. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsFun BitsArith BitsOp BitsTactics.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalArith DomainsIntervalSigned DomainsIntervalRefine DomainsIntervalTransfer
  DomainsNumeric DomainsTagged DomainsTransfer.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition interval_is_point (i : interval) (z : Z) : bool :=
  match interval_finite i with
  | Some (lo, hi) => Z.eqb lo z && Z.eqb hi z
  | None => false
  end.

(** A successful point test identifies the value of every represented concrete word. *)
Theorem interval_is_point_sound w i z value :
  interval_pgamma w i value -> interval_is_point i z = true -> value = z.
Proof.
  intros Hi Hpoint. unfold interval_is_point in Hpoint.
  destruct (interval_finite i) as [[lo hi]|] eqn:Hfinite; [|discriminate].
  apply andb_true_iff in Hpoint as [Hlo Hhi]. apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
  pose proof (interval_finite_sound w i lo hi value Hi Hfinite). lia.
Qed.

Definition interval_assume_pair (o : op) (w : width) (a b q : interval) : interval * interval :=
  match o with
  | bveq => if interval_is_point q 1 then interval_assume_equal a b
            else if interval_is_point q 0 then interval_assume_neq a b else (a, b)
  | bvne => if interval_is_point q 0 then interval_assume_equal a b
            else if interval_is_point q 1 then interval_assume_neq a b else (a, b)
  | bvult => if interval_is_point q 1 then interval_assume_ult a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ule b a)
             else (a, b)
  | bvule => if interval_is_point q 1 then interval_assume_ule a b
             else if interval_is_point q 0 then interval_swap (interval_assume_ult b a)
             else (a, b)
  | bvslt => if interval_is_point q 1 then interval_assume_signed w true true a b
             else if interval_is_point q 0 then interval_assume_signed w true false a b
             else (a, b)
  | bvsle => if interval_is_point q 1 then interval_assume_signed w false true a b
             else if interval_is_point q 0 then interval_assume_signed w false false a b
             else (a, b)
  | bvadd => interval_assume_add w a b q
  | bvsub => interval_assume_sub a b q
  | _ => (a, b)
  end.

(** Binary result refinement retains every concrete operand pair satisfying the result fact. *)
Theorem interval_assume_pair_sound o w v a b q x y rw z :
  interval_pgamma w a x -> interval_pgamma v b y -> interval_pgamma rw q z ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  interval_pgamma w (fst (interval_assume_pair o w a b q)) x /\
  interval_pgamma v (snd (interval_assume_pair o w a b q)) y.
Proof.
  intros Ha Hb Hq Heval. op_cases o by (split; assumption).
  all: assert (Hwv : w = v) by
    (match type of Heval with
     | eval_op ?o _ = _ =>
       first
         [ eapply (eval_op_fun2_width o); [reflexivity|exact Heval]
         | eapply (eval_op_cmp_width o); [reflexivity|exact Heval] ]
     end); subst v.
  - rewrite (eval_op_fun2 bvadd w x y wadd eq_refl) in Heval.
    inversion Heval; subst rw z. rewrite wadd_value in Hq.
    now apply interval_assume_add_sound.
  - rewrite (eval_op_fun2 bvsub w x y wsub eq_refl) in Heval.
    inversion Heval; subst rw z. rewrite wsub_value in Hq.
    now apply interval_assume_sub_sound.
  - unfold interval_assume_pair.
    rewrite (eval_op_cmp bveq w x y
      (fun w' x' y' => Z.eqb (wrap w' x') (wrap w' y')) eq_refl) in Heval.
    cbn beta in Heval. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
      apply Z.eqb_eq in Heq. subst y. now apply interval_assume_equal_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate|].
      apply Z.eqb_neq in Heq. now apply interval_assume_neq_sound.
  - unfold interval_assume_pair.
    rewrite (eval_op_cmp bvne w x y
      (fun w' x' y' => negb (Z.eqb (wrap w' x') (wrap w' y'))) eq_refl) in Heval.
    cbn beta in Heval. rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
    destruct (interval_is_point q 0) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 0 z Hq Hpoint) as Hz.
      inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [|discriminate].
      apply Z.eqb_eq in Heq. subst y. now apply interval_assume_equal_sound.
    + destruct (interval_is_point q 1) eqn:Hpoint1; [|split; assumption].
      pose proof (interval_is_point_sound rw q 1 z Hq Hpoint1) as Hz.
      inversion Heval; subst rw z. destruct (Z.eqb x y) eqn:Heq; [discriminate|].
      apply Z.eqb_neq in Heq. now apply interval_assume_neq_sound.
  - unfold interval_assume_pair.
    rewrite (eval_op_cmp bvult w x y wult eq_refl), wult_value in Heval.
    rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Heval; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [|discriminate].
      apply Z.ltb_lt in Hlt. now apply interval_assume_ult_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Heval; subst rw z. destruct (Z.ltb x y) eqn:Hlt; [discriminate|].
      apply Z.ltb_ge in Hlt.
      destruct (interval_assume_ule_sound w w b a y x Hb Ha Hlt) as [Hfirst Hsecond].
      split; assumption.
  - unfold interval_assume_pair.
    rewrite (eval_op_cmp bvule w x y wule eq_refl), wule_value in Heval.
    rewrite (wrap_id w x (proj1 Ha)), (wrap_id w y (proj1 Hb)) in Heval.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Heval; subst rw z. destruct (Z.leb x y) eqn:Hle; [|discriminate].
      apply Z.leb_le in Hle. now apply interval_assume_ule_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Heval; subst rw z. destruct (Z.leb x y) eqn:Hle; [discriminate|].
      apply Z.leb_gt in Hle.
      destruct (interval_assume_ult_sound w w b a y x Hb Ha Hle) as [Hfirst Hsecond].
      split; assumption.
  - unfold interval_assume_pair.
    rewrite (eval_op_cmp bvslt w x y wslt eq_refl), wslt_value in Heval.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Heval; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
        [|discriminate]. now apply interval_assume_signed_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Heval; subst rw z. destruct (Z.ltb (signed w x) (signed w y)) eqn:Hlt;
        [discriminate|]. now apply interval_assume_signed_sound.
  - unfold interval_assume_pair.
    rewrite (eval_op_cmp bvsle w x y wsle eq_refl), wsle_value in Heval.
    destruct (interval_is_point q 1) eqn:Hpoint.
    + pose proof (interval_is_point_sound rw q 1 z Hq Hpoint) as Hz.
      inversion Heval; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
        [|discriminate]. now apply interval_assume_signed_sound.
    + destruct (interval_is_point q 0) eqn:Hpoint0; [|split; assumption].
      pose proof (interval_is_point_sound rw q 0 z Hq Hpoint0) as Hz.
      inversion Heval; subst rw z. destruct (Z.leb (signed w x) (signed w y)) eqn:Hle;
        [discriminate|]. now apply interval_assume_signed_sound.
Qed.

(** Binary refinement lies below each original operand for every operator and result payload. *)
Theorem interval_assume_pair_lower ts o w a b q :
  leb (interval_lattice ts) (fst (interval_assume_pair o w a b q)) a = true /\
  leb (interval_lattice ts) (snd (interval_assume_pair o w a b q)) b = true.
Proof.
  op_cases o by (split; apply (leb_refl (interval_laws ts))).
  - apply interval_assume_add_lower.
  - apply interval_assume_sub_lower.
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_equal_lower|].
    destruct (interval_is_point q 0); [apply interval_assume_neq_lower|].
    split; apply (leb_refl (interval_laws ts)).
  - unfold interval_assume_pair. destruct (interval_is_point q 0);
      [apply interval_assume_equal_lower|].
    destruct (interval_is_point q 1); [apply interval_assume_neq_lower|].
    split; apply (leb_refl (interval_laws ts)).
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_ult_lower|].
    destruct (interval_is_point q 0); [|split; apply (leb_refl (interval_laws ts))].
    destruct (interval_assume_ule_lower ts b a) as [Hfirst Hsecond]. split; assumption.
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_ule_lower|].
    destruct (interval_is_point q 0); [|split; apply (leb_refl (interval_laws ts))].
    destruct (interval_assume_ult_lower ts b a) as [Hfirst Hsecond]. split; assumption.
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_signed_lower|].
    destruct (interval_is_point q 0); [apply interval_assume_signed_lower|].
    split; apply (leb_refl (interval_laws ts)).
  - unfold interval_assume_pair. destruct (interval_is_point q 1);
      [apply interval_assume_signed_lower|].
    destruct (interval_is_point q 0); [apply interval_assume_signed_lower|].
    split; apply (leb_refl (interval_laws ts)).
Qed.

Definition interval_bwd1_c rw q (xs : list (width * interval)) : Cost.t (list interval) :=
  match xs with
  | [(w, a)] =>
    Cost.step ;;
    let* ca := Cost.step ;; Cost.ret (interval_clip w a) in
    Cost.step ;; Cost.step ;; Cost.ret [interval_assume_rewrap rw ca q]
  | _ => Cost.ret []
  end.

Definition interval_bwd2_c o (rw : width) q (xs : list (width * interval))
    : Cost.t (list interval) :=
  match xs with
  | [(wa, a); (wb, b)] =>
    Cost.step ;;
    let* ca := Cost.step ;; Cost.ret (interval_clip wa a) in
    Cost.step ;;
    let* cb := Cost.step ;; Cost.ret (interval_clip wb b) in
    Cost.step ;; Cost.step ;;
    let refined := interval_assume_pair o wa ca cb q in
    Cost.ret [fst refined; snd refined]
  | _ => Cost.ret []
  end.

Definition interval_bwd_entry (o : op) (n : nat) :
    option (width -> interval -> list (width * interval) -> Cost.t (list interval)) :=
  match o, n with
  | (bvzext _ | bvtrunc _), 1%nat => Some interval_bwd1_c
  | (bveq | bvne | bvult | bvule | bvslt | bvsle | bvadd | bvsub), 2%nat =>
    Some (interval_bwd2_c o)
  | _, _ => None
  end.

(** Forward and backward dispatch share the same harness and prepared threshold tree. *)
Definition interval_table ts : Transfer.table (width * interval) interval op width :=
  {| Transfer.fwd := fun o n => Cost.step ;; Cost.ret (interval_fwd_entry ts o n);
     Transfer.bwd := fun o n => Cost.step ;; Cost.ret (interval_bwd_entry o n) |}.

Local Lemma interval_bwd1_sound o rw q xs cs z :
  (exists extra, o = bvzext extra) \/ (exists target, o = bvtrunc target) ->
  length xs = 1%nat -> Forall2 (payload_sound interval_pgamma) xs cs ->
  eval_op o cs = Some (rw, z) -> interval_pgamma rw q z ->
  Forall2 (word_output interval_pgamma rw) (Cost.value (interval_bwd1_c rw q xs)) cs.
Proof.
  intros Hkind Hlength Hxs Heval Hq.
  destruct xs as [|[w a] [|extra rest]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [v x] tail values Ha Htail]; subst.
  inversion Htail; subst. destruct Ha as [Hwidth [_ Ha]].
  change (w = v) in Hwidth. subst v.
  change (Forall2 (word_output interval_pgamma rw)
    [interval_assume_rewrap rw (interval_clip w a) q] [(w, x)]).
  constructor; [|constructor].
  change (interval_pgamma w (interval_assume_rewrap rw (interval_clip w a) q) x).
  apply interval_assume_rewrap_sound; [now apply interval_clip_sound|].
  destruct Hkind as [[extra ->]|[target ->]].
  - rewrite eval_op_zext, (wrap_id w x (proj1 Ha)) in Heval.
    inversion Heval; subst. exact Hq.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    rewrite (wrap_id w x (proj1 Ha)) in Heval. inversion Heval; subst. exact Hq.
Qed.

Local Lemma interval_bwd2_sound o rw q xs cs z :
  length xs = 2%nat -> Forall2 (payload_sound interval_pgamma) xs cs ->
  eval_op o cs = Some (rw, z) -> interval_pgamma rw q z ->
  Forall2 (word_output interval_pgamma rw) (Cost.value (interval_bwd2_c o rw q xs)) cs.
Proof.
  intros Hlength Hxs Heval Hq.
  destruct xs as [|[wa a] [|[wb b] [|extra rest]]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [wx x] tail values Ha Htail]; subst.
  inversion Htail as [|wp [wy y] tail' values' Hb Hlast]; subst.
  inversion Hlast; subst.
  destruct Ha as [Hwa [_ Ha]], Hb as [Hwb [_ Hb]].
  change (wa = wx) in Hwa. change (wb = wy) in Hwb. subst wx wy.
  pose proof (interval_assume_pair_sound o wa wb
    (interval_clip wa a) (interval_clip wb b) q x y rw z
    (interval_clip_sound wa a x Ha) (interval_clip_sound wb b y Hb) Hq Heval)
    as [Hleft Hright].
  constructor; [exact Hleft|constructor; [exact Hright|constructor]].
Qed.

Local Lemma interval_bwd_entry_sound o n f rw q xs cs z :
  interval_bwd_entry o n = Some f -> length xs = n ->
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  interval_pgamma rw q z ->
  Forall2 (word_output interval_pgamma rw) (Cost.value (f rw q xs)) cs.
Proof.
  intros Hentry Hlength Hxs Heval Hq.
  destruct n as [|[|[|n]]]; op_cases o; cbn [interval_bwd_entry] in Hentry;
    try discriminate; inversion Hentry; subst f.
  all: try (eapply interval_bwd2_sound; eassumption).
  - eapply interval_bwd1_sound; [left; eexists; reflexivity|exact Hlength|exact Hxs|
      exact Heval|exact Hq].
  - eapply interval_bwd1_sound; [right; eexists; reflexivity|exact Hlength|exact Hxs|
      exact Heval|exact Hq].
Qed.

(** Every supplied table callback preserves its declared concrete semantics and operand count. *)
Theorem interval_table_laws ts :
  table_laws (interval_table ts) interval_shape
    (payload_sound interval_pgamma) (word_output interval_pgamma) word_context.
Proof.
  constructor.
  - intros o n f rw xs cs [v z] Hentry Hlength Hxs Heval [Hcontext Hword].
    change (v = rw) in Hcontext. subst v.
    change (interval_fwd_entry ts o n = Some f) in Hentry.
    eapply interval_fwd_entry_sound; eassumption.
  - intros o n f rw q xs cs [v z] Hentry Hlength Hxs Heval [Hcontext Hword] Hq.
    change (v = rw) in Hcontext. subst v.
    change (interval_bwd_entry o n = Some f) in Hentry.
    eapply interval_bwd_entry_sound; eassumption.
  - intros o n f rw q xs Hentry Hlength.
    change (interval_bwd_entry o n = Some f) in Hentry.
    destruct n as [|[|[|n]]]; op_cases o; cbn [interval_bwd_entry] in Hentry;
      try discriminate; inversion Hentry; subst f.
    all: destruct xs as [|[wa a] [|[wb b] [|surplus rest]]];
      cbn in Hlength; try discriminate; reflexivity.
Qed.

Local Lemma interval_bwd1_refines ts rw q xs :
  length xs = 1%nat ->
  Forall2 (fun wp p => leb (interval_lattice ts) p (snd wp) = true)
    xs (Cost.value (interval_bwd1_c rw q xs)).
Proof.
  intro Hlength.
  destruct xs as [|[w a] [|extra rest]]; cbn in Hlength; try discriminate.
  constructor; [|constructor].
  eapply (leb_trans (interval_laws ts)); [apply interval_assume_rewrap_lower|].
  apply interval_meet_lower_left.
Qed.

Local Lemma interval_bwd2_refines ts o rw q xs :
  length xs = 2%nat ->
  Forall2 (fun wp p => leb (interval_lattice ts) p (snd wp) = true)
    xs (Cost.value (interval_bwd2_c o rw q xs)).
Proof.
  intro Hlength.
  destruct xs as [|[wa a] [|[wb b] [|extra rest]]]; cbn in Hlength; try discriminate.
  destruct (interval_assume_pair_lower ts o wa (interval_clip wa a) (interval_clip wb b) q)
    as [Hleft Hright].
  constructor.
  - eapply (leb_trans (interval_laws ts)); [exact Hleft|apply interval_meet_lower_left].
  - constructor; [|constructor].
    eapply (leb_trans (interval_laws ts)); [exact Hright|apply interval_meet_lower_left].
Qed.

(** Backward entries and the clipping default are reductive without semantic premises. *)
Theorem interval_table_refines ts :
  table_refines (interval_table ts) interval_shape
    (fun wp p => leb (interval_lattice ts) p (snd wp) = true).
Proof.
  constructor.
  - intros [w a]. apply interval_meet_lower_left.
  - intros o n f rw q xs Hentry Hlength.
    change (interval_bwd_entry o n = Some f) in Hentry.
    destruct n as [|[|[|n]]]; op_cases o; cbn [interval_bwd_entry] in Hentry;
      try discriminate; inversion Hentry; subst f;
      first [now apply interval_bwd1_refines|now apply interval_bwd2_refines].
Qed.

(** The word dictionary supplies lattice and meet separately from the transfer harness. *)
Definition interval_word_domain ts : word_domain interval :=
  word_of_table (interval_table ts) interval_shape (fun _ => interval_lattice ts) interval_top
    (fun w z => Cost.step ;; Cost.ret (interval_const w z))
    (fun _ a b => Cost.step ;; Cost.ret (interval_meet a b)).

(** Interval words retain concrete evaluation and assumptions at every operand width. *)
Theorem interval_word_laws ts : word_laws (interval_word_domain ts) interval_pgamma.
Proof.
  apply word_of_table_laws.
  - intros. reflexivity.
  - exact interval_shape_laws.
  - apply interval_table_laws.
  - intros. apply interval_laws.
  - intros w a b z Hle [Hword Hz]. split; [exact Hword|].
    eapply (gamma_monotone (interval_gamma_laws ts)); eassumption.
  - intros w z [_ Hempty]. exact Hempty.
  - apply interval_top_sound.
  - apply interval_const_sound.
  - apply interval_table_refines.
  - apply interval_meet_sound.
  - intros. apply interval_meet_lower_left.
Qed.

Definition interval_domain ts := tagged_domain (interval_word_domain ts).

(** Width tagging derives the complete numeric interval laws from the word laws. *)
Theorem interval_numeric_laws ts :
  numeric_laws (interval_domain ts) (tagged_gamma interval_pgamma).
Proof.
  apply tagged_numeric_laws. apply interval_word_laws.
Qed.

Definition interval_forward_c ts o xs rw := pforward_c (interval_word_domain ts) o xs rw.
Definition interval_forward ts o xs rw := Cost.value (interval_forward_c ts o xs rw).
Definition interval_assume_c ts o xs rw q := passume_c (interval_word_domain ts) o xs rw q.
Definition interval_assume ts o xs rw q := Cost.value (interval_assume_c ts o xs rw q).

(** The forward accessor retains every successful concrete operator result. *)
Theorem interval_forward_sound ts o xs cs rw z :
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  interval_pgamma rw (interval_forward ts o xs rw) z.
Proof.
  apply (pforward_sound (interval_word_laws ts)).
Qed.

(** The backward accessor retains every satisfying operand at that operand's width. *)
Theorem interval_assume_sound ts o xs cs rw z q :
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  interval_pgamma rw q z ->
  Forall2 (fun p y => interval_pgamma (fst p) (snd p) (snd y))
    (combine (map fst xs) (interval_assume ts o xs rw q)) cs.
Proof.
  apply (passume_sound (interval_word_laws ts)).
Qed.
