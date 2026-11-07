(** * Charged circular forward entries

    Pole-aware entries retain all charges from their delegated interval transfers.
    For example, a binary fallback covers each unsigned and signed-pole piece pair.
    Builds on: DomainsWrappedArith and the interval transfer harness. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsArith BitsOp BitsTactics.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalBack DomainsNumeric DomainsTransfer DomainsWrapped DomainsWrappedParts
  DomainsWrappedArith.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition wrapped_union_c w (a b : Cost.t wrapped) : Cost.t wrapped :=
  let* a := a in
  let* b := b in
  Cost.step ;; join_c (wrapped_lattice w) a b.

Definition wrapped_union_four_c w (a b c d : Cost.t wrapped) : Cost.t wrapped :=
  wrapped_union_c w (wrapped_union_c w a b) (wrapped_union_c w c d).

(** Charged union retains both computations and has the usual circular join value. *)
Theorem wrapped_union_value w a b :
  Cost.value (wrapped_union_c w a b) = wrapped_join w (Cost.value a) (Cost.value b).
Proof.
  reflexivity.
Qed.

(** Charged union retains both input costs and charges the join and its call overhead. *)
Theorem wrapped_union_cost w a b :
  Cost.ticks (wrapped_union_c w a b) = (Cost.ticks a + Cost.ticks b + 2)%N.
Proof.
  unfold wrapped_union_c, wrapped_lattice. autorewrite with galois_cost.
  rewrite ticks_join_of_pure. lia.
Qed.

(** Four-way charged union retains all four computations and their circular join value. *)
Theorem wrapped_union_four_value w a b c d :
  Cost.value (wrapped_union_four_c w a b c d) =
  wrapped_join_four w (Cost.value a) (Cost.value b) (Cost.value c) (Cost.value d).
Proof.
  reflexivity.
Qed.

Definition wrapped_piece_forward_c o xs rw : Cost.t wrapped :=
  Cost.step ;;
  let* result := interval_forward_c ThresholdEmpty o xs rw in
  Cost.step ;; Cost.ret (wrapped_of_interval rw result).

Definition wrapped_piece_forward o xs rw := Cost.value (wrapped_piece_forward_c o xs rw).

(** Piece conversion retains the delegated interval cost and both local call charges. *)
Theorem wrapped_piece_forward_cost o xs rw :
  Cost.ticks (wrapped_piece_forward_c o xs rw) =
    (Cost.ticks (interval_forward_c ThresholdEmpty o xs rw) + 2)%N.
Proof.
  unfold wrapped_piece_forward_c. autorewrite with galois_cost. lia.
Qed.

(** Delegated interval forward evaluation retains each successful result after projection. *)
Theorem wrapped_piece_forward_sound o xs cs rw z :
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  wrapped_gamma rw (wrapped_piece_forward o xs rw) z.
Proof.
  intros Hxs Heval. unfold wrapped_piece_forward, wrapped_piece_forward_c.
  autorewrite with galois_cost.
  apply wrapped_interval_value_sound. now apply interval_forward_sound with (cs := cs).
Qed.

Definition wrapped_forward_unary_c o w a rw : Cost.t wrapped :=
  Cost.step ;;
  let pieces := wrapped_parts w a in
  wrapped_union_c rw
    (wrapped_piece_forward_c o [(w, fst pieces)] rw)
    (wrapped_piece_forward_c o [(w, snd pieces)] rw).

Definition wrapped_forward_unary o w a rw := Cost.value (wrapped_forward_unary_c o w a rw).

(** Unary piece evaluation retains every concrete unary result. *)
Theorem wrapped_forward_unary_sound o w a x rw z :
  wrapped_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward_unary o w a rw) z.
Proof.
  intros Ha Heval. apply wrapped_parts_spec in Ha.
  unfold wrapped_forward_unary, wrapped_forward_unary_c.
  autorewrite with galois_cost. rewrite wrapped_union_value.
  apply wrapped_join_sound. destruct Ha as [Ha|Ha].
  - left. eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [|constructor]. split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
  - right. eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [|constructor]. split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
Qed.

Definition wrapped_piece_forward_binary_c o wa wb a b rw : Cost.t wrapped :=
  match o with
  | bvsdiv => Cost.step ;; Cost.ret (wrapped_signed_piece true rw a b)
  | bvsrem => Cost.step ;; Cost.ret (wrapped_signed_piece false rw a b)
  | _ => wrapped_piece_forward_c o [(wa, a); (wb, b)] rw
  end.

Definition wrapped_piece_forward_cut_c o wa wb a b rw : Cost.t wrapped :=
  Cost.step ;;
  let pa := wrapped_pole_cut wa a in
  Cost.step ;;
  let pb := wrapped_pole_cut wb b in
  wrapped_union_four_c rw
    (wrapped_piece_forward_binary_c o wa wb (fst pa) (fst pb) rw)
    (wrapped_piece_forward_binary_c o wa wb (fst pa) (snd pb) rw)
    (wrapped_piece_forward_binary_c o wa wb (snd pa) (fst pb) rw)
    (wrapped_piece_forward_binary_c o wa wb (snd pa) (snd pb) rw).

Definition wrapped_forward_binary_c o wa wb a b rw : Cost.t wrapped :=
  Cost.step ;;
  let pa := wrapped_parts wa a in
  Cost.step ;;
  let pb := wrapped_parts wb b in
  wrapped_union_four_c rw
    (wrapped_piece_forward_cut_c o wa wb (fst pa) (fst pb) rw)
    (wrapped_piece_forward_cut_c o wa wb (fst pa) (snd pb) rw)
    (wrapped_piece_forward_cut_c o wa wb (snd pa) (fst pb) rw)
    (wrapped_piece_forward_cut_c o wa wb (snd pa) (snd pb) rw).

Local Lemma wrapped_piece_binary_sound o wa wb a b x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (wrapped_piece_forward_binary_c o wa wb a b rw)) z.
Proof.
  intros Ha Hb Heval.
  assert (Hbase : wrapped_gamma rw (wrapped_piece_forward o [(wa, a); (wb, b)] rw) z).
  { eapply wrapped_piece_forward_sound; [|exact Heval]. constructor.
    - split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
    - constructor; [|constructor].
      split; [reflexivity|]. split; [exact (proj1 Hb)|exact Hb]. }
  op_cases o by exact Hbase.
  - pose proof (eval_op_fun2_width bvsdiv wsdiv wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsdiv wb x y wsdiv eq_refl) in Heval.
    inversion Heval; subst rw z. apply (wrapped_signed_piece_sound true); assumption.
  - pose proof (eval_op_fun2_width bvsrem wsrem wa wb x y (rw, z) eq_refl Heval) as ->.
    rewrite (eval_op_fun2 bvsrem wb x y wsrem eq_refl) in Heval.
    inversion Heval; subst rw z. apply (wrapped_signed_piece_sound false); assumption.
Qed.

Local Lemma wrapped_piece_forward_cut_sound o wa wb a b x y rw z :
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (wrapped_piece_forward_cut_c o wa wb a b rw)) z.
Proof.
  intros Ha Hb Heval.
  apply wrapped_pole_cut_sound in Ha. apply wrapped_pole_cut_sound in Hb.
  unfold wrapped_piece_forward_cut_c. autorewrite with galois_cost.
  rewrite wrapped_union_four_value. apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. eapply wrapped_piece_binary_sound; eassumption.
  - right; left. eapply wrapped_piece_binary_sound; eassumption.
  - right; right; left. eapply wrapped_piece_binary_sound; eassumption.
  - right; right; right. eapply wrapped_piece_binary_sound; eassumption.
Qed.

(** Binary pole-piece evaluation retains every successful concrete result. *)
Theorem wrapped_forward_binary_sound o wa wb a b x y rw z :
  wrapped_gamma wa a x -> wrapped_gamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (wrapped_forward_binary_c o wa wb a b rw)) z.
Proof.
  intros Ha Hb Heval. apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hb.
  unfold wrapped_forward_binary_c. autorewrite with galois_cost.
  rewrite wrapped_union_four_value. apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; right; left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; right; right. eapply wrapped_piece_forward_cut_sound; eassumption.
Qed.

Definition wrapped_fwd1_c o rw (xs : list (width * wrapped)) : Cost.t wrapped :=
  match xs with
  | [(w, a)] =>
    match o with
    | bvneg => Cost.step ;; Cost.ret (wrapped_neg rw a)
    | bvzext _ | bvtrunc _ => Cost.step ;; Cost.ret (wrapped_project rw w a)
    | _ => wrapped_forward_unary_c o w a rw
    end
  | _ => Cost.step ;; Cost.ret WFull
  end.

Definition wrapped_fwd2_c o rw (xs : list (width * wrapped)) : Cost.t wrapped :=
  match xs with
  | [(wa, a); (wb, b)] =>
    match o with
    | bvadd => Cost.step ;; Cost.ret (wrapped_add rw a b)
    | bvsub => Cost.step ;; Cost.ret (wrapped_sub rw a b)
    | bvmul => Cost.step ;; Cost.ret (wrapped_mul rw a b)
    | _ => wrapped_forward_binary_c o wa wb a b rw
    end
  | _ => Cost.step ;; Cost.ret WFull
  end.

Definition wrapped_fwd3_c rw (xs : list (width * wrapped)) : Cost.t wrapped :=
  match xs with
  | [_; (_, a); (_, b)] => Cost.step ;; join_c (wrapped_lattice rw) a b
  | _ => Cost.step ;; Cost.ret WFull
  end.

Definition wrapped_fwd_entry o n :
    option (width -> list (width * wrapped) -> Cost.t wrapped) :=
  match n with
  | 1%nat => Some (wrapped_fwd1_c o)
  | 2%nat => Some (wrapped_fwd2_c o)
  | 3%nat => match o with bvite => Some wrapped_fwd3_c | _ => None end
  | _ => None
  end.

Local Lemma wrapped_fwd1_sound o rw xs cs z :
  length xs = 1%nat -> Forall2 (payload_sound wrapped_gamma) xs cs ->
  eval_op o cs = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (wrapped_fwd1_c o rw xs)) z.
Proof.
  intros Hlength Hxs Heval.
  destruct xs as [|[w a] [|surplus rest]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [v x] tail values Ha Htail]; subst.
  inversion Htail; subst. destruct Ha as [Hwidth [_ Ha]].
  change (w = v) in Hwidth. subst v.
  op_cases o by (eapply wrapped_forward_unary_sound; eassumption).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. rewrite wneg_value. now apply wrapped_neg_sound.
  - rewrite eval_op_zext, (wrap_id w x (wrapped_gamma_word w a x Ha)) in Heval.
    inversion Heval; subst rw z. now apply wrapped_project_sound.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    rewrite (wrap_id w x (wrapped_gamma_word w a x Ha)) in Heval.
    inversion Heval; subst rw z. now apply wrapped_project_sound.
Qed.

Local Lemma wrapped_fwd2_sound o rw xs cs z :
  length xs = 2%nat -> Forall2 (payload_sound wrapped_gamma) xs cs ->
  eval_op o cs = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (wrapped_fwd2_c o rw xs)) z.
Proof.
  intros Hlength Hxs Heval.
  destruct xs as [|[wa a] [|[wb b] [|surplus rest]]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [wx x] tail values Ha Htail]; subst.
  inversion Htail as [|wp [wy y] tail' values' Hb Hlast]; subst.
  inversion Hlast; subst.
  destruct Ha as [Hwa [_ Ha]], Hb as [Hwb [_ Hb]].
  change (wa = wx) in Hwa. change (wb = wy) in Hwb. subst wx wy.
  op_cases o by (eapply wrapped_forward_binary_sound; eassumption).
  - pose proof (eval_op_fun2_width bvadd wadd wa wb x y (rw, z) eq_refl Heval) as ->.
    pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd wb x y wadd eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. rewrite wadd_value. now apply wrapped_add_sound.
  - pose proof (eval_op_fun2_width bvsub wsub wa wb x y (rw, z) eq_refl Heval) as ->.
    pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub wb x y wsub eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. rewrite wsub_value. now apply wrapped_sub_sound.
  - pose proof (eval_op_fun2_width bvmul wmul wa wb x y (rw, z) eq_refl Heval) as ->.
    pose proof (eq_trans (eq_sym (eval_op_fun2 bvmul wb x y wmul eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply wrapped_mul_sound.
Qed.

Local Lemma wrapped_fwd3_sound rw xs cs z :
  length xs = 3%nat -> Forall2 (payload_sound wrapped_gamma) xs cs ->
  eval_op bvite cs = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (wrapped_fwd3_c rw xs)) z.
Proof.
  intros Hlength Hxs Heval.
  destruct xs as [|[wc c] [|[wa a] [|[wb b] [|surplus rest]]]];
    cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [vc t] tail values Hc Htail]; subst.
  inversion Htail as [|wp [va x] tail' values' Ha Hlast]; subst.
  inversion Hlast as [|wp [vb y] tail'' values'' Hb Hnil]; subst.
  inversion Hnil; subst.
  destruct Hc as [Hwc [_ Hc]], Ha as [Hwa [_ Ha]], Hb as [Hwb [_ Hb]].
  change (wc = vc) in Hwc. change (wa = va) in Hwa. change (wb = vb) in Hwb.
  subst vc va vb.
  destruct (eval_op_ite_width wc wa wb t x y (rw, z) Heval) as [Hcondition Harms].
  subst wc wb. rewrite eval_op_ite in Heval.
  rewrite (wrap_id wa x (wrapped_gamma_word _ _ _ Ha)),
    (wrap_id wa y (wrapped_gamma_word _ _ _ Hb)) in Heval.
  destruct (wrap 1%positive t =? 1); inversion Heval; subst rw z;
    apply wrapped_join_sound; tauto.
Qed.

(** Every selected circular forward entry satisfies the harness forward premise. *)
Theorem wrapped_fwd_entry_sound o n f rw xs cs z :
  wrapped_fwd_entry o n = Some f -> length xs = n ->
  Forall2 (payload_sound wrapped_gamma) xs cs -> eval_op o cs = Some (rw, z) ->
  wrapped_gamma rw (Cost.value (f rw xs)) z.
Proof.
  intros Hentry Hlength Hxs Heval.
  destruct n as [|[|[|[|n]]]]; cbn [wrapped_fwd_entry] in Hentry; try discriminate.
  - inversion Hentry; subst. eapply wrapped_fwd1_sound; eassumption.
  - inversion Hentry; subst. eapply wrapped_fwd2_sound; eassumption.
  - op_cases o by discriminate. inversion Hentry; subst.
    eapply wrapped_fwd3_sound; eassumption.
Qed.
