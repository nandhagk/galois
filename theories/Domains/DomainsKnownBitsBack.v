(** * Known-bit backward entries

    Backward entries project result facts and intersect each result with its original operand.
    For example, addition result seven with a second operand one refines the first to six.
    Builds on: DomainsTnumBack and the public Bits evaluation inversions. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit.
From Galois.Domains Require Import DomainsNumeric DomainsTnum DomainsTnumArith
  DomainsTnumShift DomainsTnumExpand DomainsTnumCompare DomainsTnumBack.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Definition tnum_backward_raw_c (o : op) (wps : list (width * tnum))
    (rw : width) (q : tnum) : Cost.t (list tnum) :=
  match o, wps with
  | bvnot, [(w, _)] => Cost.ret [tnum_not w q]
  | (bvzext _ | bvtrunc _), [(w, _)] => Cost.ret [tnum_project w rw (fun m => m) q]
  | bvsext _, [(w, _)] => Cost.ret [tnum_back_sext w rw q]
  | bvextract _ lo, [(w, _)] =>
    Cost.ret [tnum_project w rw (fun m => Z.shiftl m (Z.of_nat lo)) q]
  | bvand, [(w, a); (v, b)] => Cost.ret [tnum_and_back w q b; tnum_and_back v q a]
  | bvor, [(w, a); (v, b)] => Cost.ret [tnum_or_back w q b; tnum_or_back v q a]
  | bvxor, [(w, a); (v, b)] => Cost.ret [tnum_xor w q b; tnum_xor v q a]
  | bvadd, [(w, a); (v, b)] => Cost.ret [tnum_sub w q b; tnum_sub v q a]
  | bvsub, [(w, a); (v, b)] => Cost.ret [tnum_add w q b; tnum_sub v a q]
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(w, _); (v, b)] =>
    match tnum_constant v b with
    | Some k => Cost.ret [tnum_back_shift o w k q; b]
    | None => Cost.map (fun p => [p; b]) (tnum_back_variable_shift_c o w b q)
    end
  | bveq, [(_, a); (_, b)] =>
    Cost.ret (if Z.testbit (ones q) 0 then [b; a] else [a; b])
  | bvult, [(w, a); (_, b)] =>
    let p := tnum_order_back true w q a b in Cost.ret [fst p; snd p]
  | bvule, [(w, a); (_, b)] =>
    let p := tnum_order_back false w q a b in Cost.ret [fst p; snd p]
  | bvconcat, [(w, _); (v, _)] =>
    Cost.ret [tnum_project w rw (fun m => Z.shiftr m (Zpos v)) q;
      tnum_project v rw (fun m => m) q]
  | _, _ => map_c (fun wp => Cost.ret (snd wp)) wps
  end.

Definition tnum_backward_raw (o : op) (wps : list (width * tnum))
    (rw : width) (q : tnum) : list tnum := Cost.value (tnum_backward_raw_c o wps rw q).

Lemma tnum_backward_one_sound : forall o w a x rw z q,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun p v => tnum_gamma w p v) (tnum_backward_raw o [(w, a)] rw q) [x].
Proof.
  intros o w a x rw z q Hx Ha Heval Hq. destruct o.
  all: unfold tnum_backward_raw, tnum_backward_raw_c;
    autorewrite with galois_cost; try rewrite value_map_c;
    constructor; [|constructor].
  all: try exact Ha.
  - rewrite (eval_op_fun1 bvnot w x wnot eq_refl) in Heval. injection Heval as <- <-.
    rewrite <- (wnot_involutive w x Hx). now apply tnum_not_sound.
  - rewrite eval_op_zext in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_resize|exact Hx|exact Hq].
  - rewrite eval_op_sext in Heval. injection Heval as <- <-. now apply tnum_back_sext_sound.
  - rewrite eval_op_trunc in Heval. destruct (Pos.leb target w); [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_resize|exact Hx|exact Hq].
  - rewrite eval_op_extract in Heval.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)); [|discriminate].
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_extract; lia|exact Hx|exact Hq].
Qed.

Lemma tnum_backward_shift_sound : forall o w f a b x y q,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w q (f w x y) ->
  Forall2 (fun p v => tnum_gamma w p v) (tnum_backward_raw o [(w, a); (w, b)] w q) [x; y].
Proof.
  intros o w f a b x y q Ho Hf Hx Hy Ha Hb Hq.
  assert (Hknown : forall k, tnum_constant w b = Some k ->
    tnum_gamma w (tnum_back_shift o w k q) x).
  { intros k Hconstant. pose proof (tnum_constant_value w b y k Hy Hb Hconstant) as Hyk.
    subst k. now apply (tnum_back_shift_sound o w f). }
  assert (Hvariable : tnum_gamma w (tnum_back_variable_shift o w b q) x).
  { now apply (tnum_back_variable_shift_sound o w f b q x y). }
  destruct Ho as [Ho|[Ho|[Ho|[Ho|Ho]]]]; subst o;
    unfold tnum_backward_raw, tnum_backward_raw_c;
    destruct (tnum_constant w b) as [k|] eqn:Hconstant;
    autorewrite with galois_cost.
  all: constructor; [first [now apply Hknown|exact Hvariable]|
    constructor; [exact Hb|constructor]].
Qed.

Lemma tnum_backward_fun2_sound : forall o w f a b x y q,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w q (f w x y) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] w q) [x; y].
Proof.
  intros o w f a b x y q Hf Hx Hy Ha Hb Hq. destruct o;
    try discriminate Hf; injection Hf as <-;
    try (change (Forall2 (fun p v => tnum_gamma w p v) [a; b] [x; y]);
      constructor; [exact Ha|constructor; [exact Hb|constructor]]);
    try solve [eapply tnum_backward_shift_sound; try eassumption; try reflexivity;
      unfold tnum_shift_op; tauto].
  - destruct (tnum_add_back_sound w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - destruct (tnum_sub_back_sound w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - constructor; [now apply (tnum_and_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wand_comm in Hq.
    now apply (tnum_and_back_sound w q a y x).
  - constructor; [now apply (tnum_or_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wor_comm in Hq.
    now apply (tnum_or_back_sound w q a y x).
  - constructor; [now apply (tnum_xor_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wxor_comm in Hq.
    now apply (tnum_xor_back_sound w q a y x).
Qed.

Lemma tnum_backward_cmp_sound : forall o w f a b x y q,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive q (if f w x y then 1 else 0) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] 1%positive q) [x; y].
Proof.
  intros o w f a b x y q Hf Hx Hy Ha Hb Hq.
  destruct o; try discriminate Hf; injection Hf as <-.
  - unfold tnum_backward_raw, tnum_backward_raw_c.
    destruct (Z.testbit (ones q) 0) eqn:Htrue.
    + apply tnum_boolean_sound in Hq. destruct Hq as [Hq _]. specialize (Hq Htrue).
      apply Z.eqb_eq in Hq. rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
      subst y. constructor; [exact Hb|constructor; [exact Ha|constructor]].
    + constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - rewrite wult_value, (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
    destruct (tnum_order_back_sound true w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - rewrite wule_value, (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
    destruct (tnum_order_back_sound false w q a b x y Hx Hy Ha Hb Hq) as [Hl Hr].
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
Qed.

Lemma tnum_backward_two_sound : forall o w v a b x y rw z q,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) -> tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine [(w, a); (v, b)] [(w, x); (v, y)])
    (tnum_backward_raw o [(w, a); (v, b)] rw q).
Proof.
  intros o w v a b x y rw z q Hx Hy Ha Hb Heval Hq.
  destruct (word_fun2 o) as [f|] eqn:Hf.
  - pose proof (eval_op_fun2_width o f w v x y (rw, z) Hf Heval) as ->.
    rewrite (eval_op_fun2 o v x y f Hf) in Heval. injection Heval as <- <-.
    pose proof (tnum_backward_fun2_sound o v f a b x y q Hf Hx Hy Ha Hb Hq) as Hback.
    inversion Hback as [|p x' ps xs Hl Htail]; subst.
    inversion Htail as [|p' y' ps' xs' Hr Hnil]; subst.
    inversion Hnil; subst.
    constructor; [exact Hl|constructor; [exact Hr|constructor]].
  - destruct (word_cmp o) as [f|] eqn:Hcmp.
    + pose proof (eval_op_cmp_width o f w v x y (rw, z) Hcmp Heval) as ->.
      rewrite (eval_op_cmp o v x y f Hcmp) in Heval. injection Heval as <- <-.
      pose proof (tnum_backward_cmp_sound o v f a b x y q Hcmp Hx Hy Ha Hb Hq) as Hback.
      inversion Hback as [|p x' ps xs Hl Htail]; subst.
      inversion Htail as [|p' y' ps' xs' Hr Hnil]; subst.
      inversion Hnil; subst.
      constructor; [exact Hl|constructor; [exact Hr|constructor]].
    + destruct o; try discriminate Hf; try discriminate Hcmp;
        try (constructor; [exact Ha|constructor; [exact Hb|constructor]]).
      rewrite eval_op_concat in Heval. injection Heval as <- <-.
      rewrite (wrap_id w x Hx), (wrap_id v y Hy) in Hq.
      apply (proj1 (tnum_gamma_wrap (w + v)%positive q (x * modulus v + y))) in Hq.
      destruct (tnum_concat_back_sound w v q x y Hx Hy Hq) as [Hl Hr].
      constructor; [exact Hl|constructor; [exact Hr|constructor]].
Qed.

Lemma tnum_backward_identity_sound : forall wps ys,
  Forall2 (payload_sound tnum_gamma) wps ys ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (map snd wps).
Proof.
  intros wps ys Hgamma.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; cbn; constructor.
  - exact (proj2 (proj2 Hhead)).
  - exact IH.
Qed.

(** Backward entry soundness interprets every result payload at its own original operand width. *)
Theorem tnum_backward_raw_sound : forall o wps ys rw z q,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (tnum_backward_raw o wps rw q).
Proof.
  intros o wps ys rw z q Hgamma Heval Hq.
  destruct wps as [|[w a] [|[v b] [|wp rest]]].
  - destruct o; constructor.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    pose proof (tnum_backward_one_sound o w a x rw z q Hx Ha Heval Hq) as Hback.
    inversion Hback as [|p x' ps xs Hl Hnil]; subst. inversion Hnil; subst.
    constructor; [exact Hl|constructor].
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (tnum_backward_two_sound o w v a b x y rw z q Hx Hy Ha Hb Heval Hq).
  - destruct o; unfold tnum_backward_raw, tnum_backward_raw_c;
      rewrite value_map_c; apply tnum_backward_identity_sound; exact Hgamma.
Qed.

Fixpoint tnum_refine_c (wps : list (width * tnum)) (qs : list tnum) : Cost.t (list tnum) :=
  match wps, qs with
  | [], _ => Cost.ret []
  | (w, a) :: rest, q :: tail =>
    Cost.step ;; Cost.map (cons (tnum_meet w a q)) (tnum_refine_c rest tail)
  | (_, a) :: rest, [] => Cost.step ;; Cost.map (cons a) (tnum_refine_c rest [])
  end.

Definition tnum_refine (wps : list (width * tnum)) (qs : list tnum) : list tnum :=
  Cost.value (tnum_refine_c wps qs).

(** Refinement charges each operand and keeps the legacy short-result fallback. *)
Theorem tnum_refine_equation : forall wps qs,
  tnum_refine wps qs =
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => tnum_meet w a q :: tnum_refine rest tail
  | (_, a) :: rest, [] => a :: tnum_refine rest []
  end.
Proof.
  intros [|[w a] rest] [|q tail]; unfold tnum_refine; cbn [tnum_refine_c];
    autorewrite with galois_cost; reflexivity.
Qed.

(** Refinement always returns one fact per input, without any semantic-witness premise. *)
Theorem tnum_refine_length : forall wps qs, length (tnum_refine wps qs) = length wps.
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q tail];
    rewrite tnum_refine_equation; cbn [length]; [reflexivity|reflexivity| |];
    f_equal; apply IH.
Qed.

(** Refinement is reductive for all raw operands and all result lists. *)
Theorem tnum_refine_refines : forall wps qs,
  Forall2 (fun wp q => leb (tnum_lattice (fst wp)) q (snd wp) = true)
    wps (tnum_refine wps qs).
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q tail];
    rewrite tnum_refine_equation; constructor;
    first [apply (leb_refl (tnum_laws w))|apply tnum_meet_lower_left|apply IH].
Qed.

(** Meeting projected facts with the original facts preserves each concrete operand. *)
Theorem tnum_refine_sound : forall wps ys qs,
  Forall2 (payload_sound tnum_gamma) wps ys ->
  Forall2 (fun wp_y q => tnum_gamma (fst (fst wp_y)) q (snd (snd wp_y)))
    (combine wps ys) qs ->
  Forall2 (fun p y => tnum_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (tnum_refine wps qs)) ys.
Proof.
  intros wps ys qs Hgamma. revert qs.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; intros qs Hqs.
  - destruct qs; constructor.
  - inversion Hqs as [|wp_y q rest' qs' Hq Hrest]; subst qs.
    destruct Hhead as [Hwv [Hx Ha]]. cbn in Hwv, Hx, Ha, Hq. subst v.
    rewrite tnum_refine_equation. cbn [combine map fst snd]. constructor.
    + now apply tnum_meet_sound.
    + now apply IH.
Qed.
