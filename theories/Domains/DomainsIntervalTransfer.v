(** * Interval forward transfer entries

    The shared harness handles empty operands and points before selecting a scalar entry.
    Each entry clips operands to their own widths and retains the clipping and call charges.
    For example, a singleton population count uses the harness point path.
    Builds on: DomainsTransfer and the interval scalar family. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsOp BitsTactics.
From Galois.Domains Require Import DomainsBound DomainsThreshold DomainsInterval
  DomainsIntervalArith DomainsIntervalBitwise DomainsIntervalCompare DomainsIntervalShift
  DomainsIntervalSigned DomainsNumeric DomainsTransfer.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition interval_shape : Transfer.shape (width * interval) interval op width word :=
  {| Transfer.eval_c := fun o xs => Cost.step ;; Cost.ret (eval_op o xs);
     Transfer.point_c := fun wp =>
       Cost.step ;; Cost.ret
         (match interval_singleton (interval_clip (fst wp) (snd wp)) with
          | Some z => Some (fst wp, z)
          | None => None
          end);
     Transfer.is_empty_c := fun wp =>
       Cost.step ;; Cost.ret
         (match interval_clip (fst wp) (snd wp) with IBot => true | _ => false end);
     Transfer.inj_c := fun _ c =>
       Cost.step ;; Cost.ret (Itv (Fin (snd c)) (Fin (snd c)));
     Transfer.bot_out := fun _ => IBot;
     Transfer.top_out := interval_top;
     Transfer.keep_c := fun wp => Cost.step ;; Cost.ret (interval_clip (fst wp) (snd wp)) |}.

(** Shape callbacks preserve operand meanings and normalized result contexts. *)
Theorem interval_shape_laws :
  transfer_sem interval_shape (payload_sound interval_pgamma)
    (word_output interval_pgamma) word_context.
Proof.
  constructor.
  - intros [w a] c [v x] Hp [Hwidth [_ Ha]].
    change (w = v) in Hwidth. subst v.
    change (match interval_singleton (interval_clip w a) with
      | Some z => Some (w, z) | None => None end = Some c) in Hp.
    destruct (interval_singleton (interval_clip w a)) as [z|] eqn:Hsingle; [|discriminate].
    inversion Hp; subst c.
    pose proof (interval_singleton_sound w (interval_clip w a) x z
      (interval_clip_sound w a x Ha) Hsingle). congruence.
  - intros [w a] [v x] Hempty [Hwidth [_ Ha]].
    change (w = v) in Hwidth. subst v.
    change (match interval_clip w a with IBot => true | _ => false end = true) in Hempty.
    pose proof (interval_clip_sound w a x Ha) as Hclip.
    destruct (interval_clip w a); [exact (proj2 Hclip)|discriminate].
  - intros rw [w z] [Hwidth Hword].
    change (w = rw) in Hwidth. cbn in Hword. subst rw.
    split; [exact Hword|]. cbn. now rewrite Z.leb_refl.
  - intros rw [w z] Hbot. exact (proj2 Hbot).
  - intros rw [w z] [Hwidth Hword].
    change (w = rw) in Hwidth. cbn in Hword. subst rw. now apply interval_top_sound.
  - intros rw [w a] [v z] [Hwidth [_ Ha]].
    change (w = v) in Hwidth. subst v. now apply interval_clip_sound.
Qed.

Definition interval_entry1_c
    (f : width -> width -> interval -> interval) rw (xs : list (width * interval))
    : Cost.t interval :=
  match xs with
  | [(w, a)] =>
    Cost.step ;;
    let* clipped := Cost.step ;; Cost.ret (interval_clip w a) in
    Cost.step ;; Cost.step ;; Cost.ret (f rw w clipped)
  | _ => Cost.step ;; Cost.ret (interval_top rw)
  end.

Definition interval_entry2_c
    (f : width -> width -> width -> interval -> interval -> interval)
    rw (xs : list (width * interval)) : Cost.t interval :=
  match xs with
  | [(wa, a); (wb, b)] =>
    Cost.step ;;
    let* ca := Cost.step ;; Cost.ret (interval_clip wa a) in
    Cost.step ;;
    let* cb := Cost.step ;; Cost.ret (interval_clip wb b) in
    Cost.step ;; Cost.step ;; Cost.ret (f rw wa wb ca cb)
  | _ => Cost.step ;; Cost.ret (interval_top rw)
  end.

Definition interval_ite_entry_c ts rw (xs : list (width * interval)) : Cost.t interval :=
  match xs with
  | [_; (wa, a); (wb, b)] =>
    Cost.step ;;
    let* ca := Cost.step ;; Cost.ret (interval_clip wa a) in
    Cost.step ;;
    let* cb := Cost.step ;; Cost.ret (interval_clip wb b) in
    Cost.step ;; join_c (interval_lattice ts) ca cb
  | _ => Cost.step ;; Cost.ret (interval_top rw)
  end.

(** The entry index contains only modeled operators at their supported arities. *)
Definition interval_fwd_entry ts (o : op) (n : nat) :
    option (width -> list (width * interval) -> Cost.t interval) :=
  match o, n with
  | bvnot, 1%nat => Some (interval_entry1_c (fun rw _ => interval_not rw))
  | bvneg, 1%nat => Some (interval_entry1_c (fun rw _ => interval_neg rw))
  | (bvclz | bvctz | bvpopcnt), 1%nat =>
    Some (interval_entry1_c (fun rw _ _ => interval_counts rw))
  | (bvzext _ | bvtrunc _), 1%nat =>
    Some (interval_entry1_c (fun rw _ => interval_rewrap rw))
  | bvsext _, 1%nat => Some (interval_entry1_c interval_sext)
  | bvadd, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_add rw))
  | bvsub, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_sub rw))
  | bvmul, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_mul rw))
  | bvudiv, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_udiv rw))
  | bvurem, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_urem rw))
  | bvsdiv, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_sdiv rw))
  | bvsrem, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_srem rw))
  | bvsmod, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_smod rw))
  | bvand, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_and rw))
  | (bvor | bvxor), 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_or_xor rw))
  | bvshl, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_shl rw))
  | bvlshr, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_lshr rw))
  | bvashr, 2%nat => Some (interval_entry2_c (fun rw _ _ => interval_ashr rw))
  | bveq, 2%nat => Some (interval_entry2_c (fun _ _ _ => interval_eq))
  | bvne, 2%nat => Some (interval_entry2_c (fun _ _ _ a b => interval_bool_not (interval_eq a b)))
  | bvult, 2%nat => Some (interval_entry2_c (fun _ _ _ => interval_ult))
  | bvule, 2%nat => Some (interval_entry2_c (fun _ _ _ => interval_ule))
  | bvslt, 2%nat => Some (interval_entry2_c (fun _ w _ => interval_signed_compare w true))
  | bvsle, 2%nat => Some (interval_entry2_c (fun _ w _ => interval_signed_compare w false))
  | bvconcat, 2%nat => Some (interval_entry2_c (fun rw _ w => interval_concat rw w))
  | bvite, 3%nat => Some (interval_ite_entry_c ts)
  | _, _ => None
  end.

Local Lemma interval_entry1_sound o f rw xs cs z :
  length xs = 1%nat ->
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  (forall w a x, interval_pgamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
    interval_pgamma rw (f rw w a) z) ->
  interval_pgamma rw (Cost.value (interval_entry1_c f rw xs)) z.
Proof.
  intros Hlength Hxs Heval Hf.
  destruct xs as [|[w a] [|extra rest]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [v x] tail values Ha Htail]; subst.
  inversion Htail; subst. destruct Ha as [Hwidth [_ Ha]].
  change (w = v) in Hwidth. subst v.
  change (interval_pgamma rw (f rw w (interval_clip w a)) z).
  apply (Hf w (interval_clip w a) x); [now apply interval_clip_sound|exact Heval].
Qed.

Local Lemma interval_entry2_sound o f rw xs cs z :
  length xs = 2%nat ->
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  (forall wa wb a b x y, interval_pgamma wa a x -> interval_pgamma wb b y ->
    eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
    interval_pgamma rw (f rw wa wb a b) z) ->
  interval_pgamma rw (Cost.value (interval_entry2_c f rw xs)) z.
Proof.
  intros Hlength Hxs Heval Hf.
  destruct xs as [|[wa a] [|[wb b] [|extra rest]]]; cbn in Hlength; try discriminate.
  inversion Hxs as [|wp [wx x] tail values Ha Htail]; subst.
  inversion Htail as [|wp [wy y] tail' values' Hb Hlast]; subst.
  inversion Hlast; subst.
  destruct Ha as [Hwa [_ Ha]], Hb as [Hwb [_ Hb]].
  change (wa = wx) in Hwa. change (wb = wy) in Hwb. subst wx wy.
  change (interval_pgamma rw (f rw wa wb (interval_clip wa a) (interval_clip wb b)) z).
  apply (Hf wa wb (interval_clip wa a) (interval_clip wb b) x y);
    try now apply interval_clip_sound.
  exact Heval.
Qed.

Local Lemma interval_binary_semantics o g f :
  word_fun2 o = Some g ->
  (forall w a b x y, interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma w (f w a b) (g w x y)) ->
  forall rw wa wb a b x y z, interval_pgamma wa a x -> interval_pgamma wb b y ->
    eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
    interval_pgamma rw (f rw a b) z.
Proof.
  intros Hkind Hscalar rw wa wb a b x y z Ha Hb Heval.
  pose proof (eval_op_fun2_width o g wa wb x y (rw, z) Hkind Heval) as ->.
  rewrite (eval_op_fun2 o wb x y g Hkind) in Heval.
  inversion Heval; subst. now apply Hscalar.
Qed.

Local Lemma interval_unary_semantics o g f :
  word_fun1 o = Some g ->
  (forall w a x, interval_pgamma w a x -> interval_pgamma w (f w a) (g w x)) ->
  forall rw w a x z, interval_pgamma w a x ->
    eval_op o [(w, x)] = Some (rw, z) -> interval_pgamma rw (f rw a) z.
Proof.
  intros Hkind Hscalar rw w a x z Ha Heval.
  rewrite (eval_op_fun1 o w x g Hkind) in Heval.
  inversion Heval; subst. now apply Hscalar.
Qed.

Local Lemma interval_comparison_semantics o g f :
  word_cmp o = Some g ->
  (forall w a b x y, interval_pgamma w a x -> interval_pgamma w b y ->
    interval_pgamma 1%positive (f w a b) (if g w x y then 1 else 0)) ->
  forall rw wa wb a b x y z, interval_pgamma wa a x -> interval_pgamma wb b y ->
    eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
    interval_pgamma rw (f wa a b) z.
Proof.
  intros Hkind Hscalar rw wa wb a b x y z Ha Hb Heval.
  pose proof (eval_op_cmp_width o g wa wb x y (rw, z) Hkind Heval) as Hwidth.
  subst wb. rewrite (eval_op_cmp o wa x y g Hkind) in Heval.
  inversion Heval; subst. now apply Hscalar.
Qed.

Local Lemma interval_ite_entry_sound ts rw xs cs z :
  length xs = 3%nat -> Forall2 (payload_sound interval_pgamma) xs cs ->
  eval_op bvite cs = Some (rw, z) ->
  interval_pgamma rw (Cost.value (interval_ite_entry_c ts rw xs)) z.
Proof.
  intros Hlength Hxs Heval.
  destruct xs as [|[wc c] [|[wa a] [|[wb b] [|extra rest]]]];
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
  rewrite (wrap_id wa x (proj1 Ha)), (wrap_id wa y (proj1 Hb)) in Heval.
  destruct (wrap 1%positive t =? 1) eqn:Hdecision; inversion Heval; subst rw z;
    apply (interval_join_sound ts).
  - left. now apply interval_clip_sound.
  - right. now apply interval_clip_sound.
Qed.

(** Each selected forward callback satisfies the harness's forward entry premise. *)
Theorem interval_fwd_entry_sound ts o n f rw xs cs z :
  interval_fwd_entry ts o n = Some f -> length xs = n ->
  Forall2 (payload_sound interval_pgamma) xs cs -> eval_op o cs = Some (rw, z) ->
  interval_pgamma rw (Cost.value (f rw xs)) z.
Proof.
  intros Hentry Hlength Hxs Heval.
  destruct n as [|[|[|[|n]]]]; op_cases o; cbn [interval_fwd_entry] in Hentry;
    try discriminate; inversion Hentry; subst f.
  all: first
    [ eapply interval_entry1_sound; [exact Hlength|exact Hxs|exact Heval|]
    | eapply interval_entry2_sound; [exact Hlength|exact Hxs|exact Heval|]
    | exact (interval_ite_entry_sound ts rw xs cs z Hlength Hxs Heval) ].
  - intros w a x Ha Hr.
    eapply (interval_unary_semantics bvnot wnot (fun w => interval_not w));
      [reflexivity|exact interval_not_sound|exact Ha|exact Hr].
  - intros w a x Ha Hr.
    eapply (interval_unary_semantics bvneg wneg (fun w => interval_neg w));
      [reflexivity| |exact Ha|exact Hr].
    intros. rewrite wneg_value. now apply interval_neg_sound.
  - intros w a x Ha Hr.
    eapply (interval_unary_semantics bvclz wclz (fun w _ => interval_counts w));
      [reflexivity|intros; apply interval_clz_sound|exact Ha|exact Hr].
  - intros w a x Ha Hr.
    eapply (interval_unary_semantics bvctz wctz (fun w _ => interval_counts w));
      [reflexivity|intros; apply interval_ctz_sound|exact Ha|exact Hr].
  - intros w a x Ha Hr.
    eapply (interval_unary_semantics bvpopcnt wpopcnt (fun w _ => interval_counts w));
      [reflexivity|intros; apply interval_popcnt_sound|exact Ha|exact Hr].
  - intros w a x Ha Hr. rewrite eval_op_zext, (wrap_id w x (proj1 Ha)) in Hr.
    inversion Hr; subst. now apply (interval_rewrap_sound _ w).
  - intros w a x Ha Hr. rewrite eval_op_sext in Hr.
    inversion Hr; subst. now apply interval_sext_sound.
  - intros w a x Ha Hr. rewrite eval_op_trunc in Hr.
    destruct (Pos.leb target w); [|discriminate].
    rewrite (wrap_id w x (proj1 Ha)) in Hr.
    inversion Hr; subst. now apply (interval_rewrap_sound _ w).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_binary_semantics bvadd wadd interval_add);
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy. rewrite wadd_value.
    exact (interval_add_sound w w w a' b' x' y' Hx Hy).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_binary_semantics bvsub wsub interval_sub);
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy. rewrite wsub_value.
    exact (interval_sub_sound w w w a' b' x' y' Hx Hy).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_binary_semantics bvmul wmul interval_mul);
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy. rewrite wmul_value.
    exact (interval_mul_sound w w w a' b' x' y' Hx Hy).
  - intros. eapply (interval_binary_semantics bvudiv wudiv interval_udiv);
      [reflexivity|exact interval_udiv_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvurem wurem interval_urem);
      [reflexivity|exact interval_urem_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvsdiv wsdiv interval_sdiv);
      [reflexivity|exact interval_sdiv_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvsrem wsrem interval_srem);
      [reflexivity|exact interval_srem_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvsmod wsmod interval_smod);
      [reflexivity|exact interval_smod_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvand wand interval_and);
      [reflexivity|exact interval_and_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvor wor interval_or_xor);
      [reflexivity| |eassumption|eassumption|eassumption].
    intros w a' b' x' y' Hx Hy.
    exact (proj1 (interval_or_xor_sound w a' b' x' y' Hx Hy)).
  - intros. eapply (interval_binary_semantics bvxor wxor interval_or_xor);
      [reflexivity| |eassumption|eassumption|eassumption].
    intros w a' b' x' y' Hx Hy.
    exact (proj2 (interval_or_xor_sound w a' b' x' y' Hx Hy)).
  - intros. eapply (interval_binary_semantics bvshl wshl interval_shl);
      [reflexivity|exact interval_shl_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvlshr wlshr interval_lshr);
      [reflexivity|exact interval_lshr_sound|eassumption|eassumption|eassumption].
  - intros. eapply (interval_binary_semantics bvashr washr interval_ashr);
      [reflexivity|exact interval_ashr_sound|eassumption|eassumption|eassumption].
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_comparison_semantics bveq
      (fun w x y => Z.eqb (wrap w x) (wrap w y)) (fun _ => interval_eq));
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy.
    rewrite (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
    now apply (interval_eq_sound w w).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_comparison_semantics bvne
      (fun w x y => negb (Z.eqb (wrap w x) (wrap w y)))
      (fun _ a b => interval_bool_not (interval_eq a b)));
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy.
    rewrite (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
    apply interval_bool_not_sound. now apply (interval_eq_sound w w).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_comparison_semantics bvult wult (fun _ => interval_ult));
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy.
    rewrite wult_value, (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
    now apply (interval_ult_sound w w).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_comparison_semantics bvule wule (fun _ => interval_ule));
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros w a' b' x' y' Hx Hy.
    rewrite wule_value, (wrap_id w x' (proj1 Hx)), (wrap_id w y' (proj1 Hy)).
    now apply (interval_ule_sound w w).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_comparison_semantics bvslt wslt
      (fun w => interval_signed_compare w true));
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros. rewrite wslt_value. now apply (interval_signed_compare_sound _ _ _ _ _ _ true).
  - intros wa wb a b x y Ha Hb Hr.
    eapply (interval_comparison_semantics bvsle wsle
      (fun w => interval_signed_compare w false));
      [reflexivity| |exact Ha|exact Hb|exact Hr].
    intros. rewrite wsle_value. now apply (interval_signed_compare_sound _ _ _ _ _ _ false).
  - intros wa wb a b x y Ha Hb Hr.
    rewrite eval_op_concat, (wrap_id wa x (proj1 Ha)), (wrap_id wb y (proj1 Hb)) in Hr.
    inversion Hr; subst. now apply (interval_concat_sound _ wa wb).
Qed.
