(** * Open values from word domains

    Bridges interpret client operations as word expressions and preserve partial conversion.
    For example, a disabled truth capability keeps nonword operands unchanged.
    Builds on: DomainsNumeric, DomainsTactics and BitsTestbit. *)

From Stdlib Require Import List ZArith Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsExpr BitsTestbit.
From Galois.Domains Require Import DomainsValue DomainsNumeric DomainsTactics.
Import List.ListNotations Cost.Notations Expr.

(** Bridge capabilities are computational data and their promises live in separate laws. *)
Record op_bridge (K C : Type) : Type := OpBridge {
  op_expr_c : K -> Cost.t (option expr);
  to_word_c : C -> Cost.t (option word);
  truth_words : bool;
  differ_words_c : C -> Cost.t bool
}.

Arguments op_expr_c {K C}.
Arguments to_word_c {K C}.
Arguments truth_words {K C}.
Arguments differ_words_c {K C}.

Definition op_expr {K C} (br : op_bridge K C) k := Cost.value (op_expr_c br k).
Definition to_word {K C} (br : op_bridge K C) c := Cost.value (to_word_c br c).
Definition differ_words {K C} (br : op_bridge K C) c := Cost.value (differ_words_c br c).

(** Bridge laws preserve defined operators, normalized conversion and enabled guard capabilities. *)
Record op_bridge_laws {K C} (br : op_bridge K C)
    (ev : K -> list C -> option C) (truth : C -> bool) : Prop := {
  bridge_word : forall c w, to_word br c = Some w -> is_word (fst w) (snd w);
  bridge_eq : forall k cs c e, ev k cs = Some c -> op_expr br k = Some e ->
    exists ws wr, Forall2 (fun c w => to_word br c = Some w) cs ws /\
      eval eval_op (fun i => nth i ws (1%positive, 0%Z)) e = Some wr /\
      to_word br c = Some wr;
  bridge_truth : forall c w, to_word br c = Some w ->
    truth c = negb (Z.eqb (snd w) 0);
  truth_total : truth_words br = true -> forall c, exists w, to_word br c = Some w;
  differ_total : forall d, differ_words br d = true ->
    forall c, exists w, to_word br c = Some w;
  differ_width : forall d c wc wd, differ_words br d = true ->
    to_word br c = Some wc -> to_word br d = Some wd -> fst wc = fst wd;
  differ_injective : forall d c w, differ_words br d = true ->
    to_word br c = Some w -> to_word br d = Some w -> c = d
}.

Arguments bridge_word {K C br ev truth}.
Arguments bridge_eq {K C br ev truth}.
Arguments bridge_truth {K C br ev truth}.
Arguments truth_total {K C br ev truth}.
Arguments differ_total {K C br ev truth}.
Arguments differ_width {K C br ev truth}.
Arguments differ_injective {K C br ev truth}.

(** Truth, equality and disequality inspect one value while explicit tests inspect operand lists. *)
Inductive bits_guard (C : Type) : Type :=
  | Truth (b : bool)
  | Equal (c : C)
  | Differ (c : C)
  | Test (e : expr) (b : bool).

Arguments Truth {C}.
Arguments Equal {C}.
Arguments Differ {C}.
Arguments Test {C}.

(** Nonword values are retained at exactly the facts that are not below bottom. *)
Definition numeric_conc {A K C} (D : numeric_domain A) (G : concretisation A word)
    (br : op_bridge K C) : concretisation A C :=
  {| gamma := fun a c =>
       match to_word br c with
       | Some w => gamma G a w
       | None => leb (lat D) a (bot (lat D)) = false
       end |}.

(** The truth expression compares a value with its zero-valued self-xor. *)
Definition numeric_truth_expr (e : expr) : expr := App bvne [e; App bvxor [e; e]].

(** Guard semantics retains ordinary concrete equality and disequality. *)
Definition bits_sem {K C} (br : op_bridge K C)
    (ev : K -> list C -> option C) (truth : C -> bool) : ValueSem.t C K (bits_guard C) :=
  {| ValueSem.eval := ev;
     ValueSem.holds := fun g cs =>
       match g, cs with
       | Truth b, [c] => truth c = b
       | Equal d, [c] => c = d
       | Differ d, [c] => c <> d
       | Test e b, _ =>
         exists ws w z, Forall2 (fun c w => to_word br c = Some w) cs ws /\
           eval eval_op (fun i => nth i ws (1%positive, 0%Z)) e = Some (w, z) /\
           negb (Z.eqb z 0) = b
       | _, _ => False
       end |}.

(** Indexed list lookup charges every visited cell. *)
Fixpoint nth_c {A} (xs : list A) (d : A) (i : nat) : Cost.t A :=
  match xs, i with
  | [], _ => Cost.ret d
  | x :: _, O => Cost.step ;; Cost.ret x
  | _ :: xs, S i => Cost.step ;; nth_c xs d i
  end.

Local Lemma nth_equation {A} (xs : list A) d i : Cost.value (nth_c xs d i) = nth i xs d.
Proof.
  revert i. induction xs as [|x xs IH]; intros [|i]; cbn; auto.
Qed.

(** Readback traverses the original support and retains the charged lookup at every position. *)
Fixpoint readback_c {A B} (env : nat -> Cost.t A) (start : nat) (xs : list B)
    : Cost.t (list A) :=
  match xs with
  | [] => Cost.ret []
  | _ :: xs =>
    Cost.step ;;
    let* a := Cost.step ;; env start in
    Cost.map (cons a) (readback_c env (S start) xs)
  end.

Local Lemma readback_length {A B} (env : nat -> Cost.t A) start (xs : list B) :
  length (Cost.value (readback_c env start xs)) = length xs.
Proof.
  revert start. induction xs; intro start; cbn [readback_c];
    autorewrite with galois_cost; cbn; auto.
Qed.

(** Refinement shares the numeric assumption engine and reads back exactly the original operands. *)
Definition numeric_refine_c {A} (D : numeric_domain A) top xs e a :=
  let* result := num_eval_c D (nth_c xs top) e in
  let* common := Cost.step ;; meet_c D result a in
  let* empty := Cost.step ;; leb_c (lat D) common (bot (lat D)) in
  if empty then map_c (fun _ => Cost.ret (bot (lat D))) xs else
  let* env := num_assume_c D (nth_c xs top) e a in readback_c env 0 xs.

(** Guard transfer checks capabilities before applying operator-independent refinements. *)
Definition bits_guard_c {A K C} (D : numeric_domain A) (br : op_bridge K C) top
    (g : bits_guard C) (xs : list A) : Cost.t (list A) :=
  match g, xs with
  | Truth b, [_] =>
    if truth_words br then
      let* a := Cost.step ;; of_const_c D 1%positive (if b then 1%Z else 0%Z) in
      numeric_refine_c D top xs (numeric_truth_expr (Var 0)) a
    else Cost.ret xs
  | Equal d, [a] =>
    let* w := Cost.step ;; to_word_c br d in
    match w with
    | Some (w, z) =>
      let* c := Cost.step ;; of_const_c D w z in
      Cost.map (fun a => [a]) (Cost.step ;; meet_c D a c)
    | None => Cost.ret xs
    end
  | Differ d, [_] =>
    let* enabled := Cost.step ;; differ_words_c br d in
    if enabled then
      let* w := Cost.step ;; to_word_c br d in
      match w with
      | Some (w, z) =>
        let* a := Cost.step ;; of_const_c D 1%positive 1%Z in
        numeric_refine_c D top xs (App bvne [Var 0; Const w z]) a
      | None => Cost.ret xs
      end
    else Cost.ret xs
  | Test e b, _ =>
    let* a := Cost.step ;; of_const_c D 1%positive (if b then 1%Z else 0%Z) in
    numeric_refine_c D top xs (numeric_truth_expr e) a
  | _, _ => Cost.ret xs
  end.

(** The Bits builder interprets supported operators and retains safe defaults elsewhere. *)
Definition bits_values {A K C} (D : numeric_domain A) (br : op_bridge K C) (top : A)
    : ValueAbs.t A K (bits_guard C) :=
  {| ValueAbs.lat := lat D;
     ValueAbs.top := top;
     ValueAbs.op_c := fun k xs =>
       let* e := Cost.step ;; op_expr_c br k in
       match e with
       | Some e => num_eval_c D (nth_c xs top) e
       | None => Cost.ret top
       end;
     ValueAbs.back_c := fun k a xs =>
       let* e := Cost.step ;; op_expr_c br k in
       match e with
       | Some e => numeric_refine_c D top xs e a
       | None => Cost.ret xs
       end;
     ValueAbs.guard_c := bits_guard_c D br top |}.

Local Lemma numeric_truth_eval env e w z :
  eval eval_op env e = Some (w, z) ->
  eval eval_op env (numeric_truth_expr e) =
    Some (1%positive, if negb (Z.eqb z 0) then 1%Z else 0%Z).
Proof.
  intro He.
  pose proof (eval_is_word eval_op eval_op_is_word (w, z) env e He) as Hw.
  assert (Hxor : eval eval_op env (App bvxor [e; e]) = Some (w, 0%Z)).
  { rewrite eval_app, !eval_args_cons, He, eval_args_nil.
    change (eval_op bvxor [(w, z); (w, z)] = Some (w, 0%Z)).
    now rewrite (eval_op_fun2 bvxor w z z wxor eq_refl), wxor_self. }
  unfold numeric_truth_expr.
  rewrite eval_app, !eval_args_cons, He, Hxor, eval_args_nil.
  change (eval_op bvne [(w, z); (w, 0%Z)] =
    Some (1%positive, if negb (Z.eqb z 0) then 1%Z else 0%Z)).
  rewrite (eval_op_cmp bvne w z 0
    (fun w x y => negb (Z.eqb (wrap w x) (wrap w y))) eq_refl).
  rewrite wrap_0, wrap_id by exact Hw. reflexivity.
Qed.

Local Lemma numeric_words {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    xs cs ws :
  Forall2 (gamma (numeric_conc D G br)) xs cs ->
  Forall2 (fun c w => to_word br c = Some w) cs ws -> Forall2 (gamma G) xs ws.
Proof.
  intros Hxs Hws. revert xs Hxs.
  induction Hws as [|c w cs ws Hw Hws IH]; intros xs Hxs;
    inversion Hxs as [|a c' xs' cs' Ha Htail]; subst; constructor.
  - cbn [numeric_conc gamma] in Ha. now rewrite Hw in Ha.
  - now apply IH.
Qed.

Local Lemma nth_words {K C} (br : op_bridge K C) ev truth :
  op_bridge_laws br ev truth -> forall cs ws,
  Forall2 (fun c w => to_word br c = Some w) cs ws ->
  env_ok (fun i => nth i ws (1%positive, 0%Z)).
Proof.
  intros H cs ws Hws. induction Hws as [|c w cs ws Hw Hws IH]; intros [|i]; cbn.
  - apply zero_is_word.
  - apply zero_is_word.
  - exact (bridge_word H c w Hw).
  - apply IH.
Qed.

Local Lemma nth_facts {A} (G : concretisation A word) top xs ws :
  gamma G top (1%positive, 0%Z) -> Forall2 (gamma G) xs ws ->
  forall i, gamma G (Cost.value (nth_c xs top i)) (nth i ws (1%positive, 0%Z)).
Proof.
  intros Htop Hxs i. rewrite nth_equation. revert i.
  induction Hxs; intros [|i]; cbn; auto.
Qed.

Local Lemma nth_conversion {K C} (br : op_bridge K C) cs ws :
  Forall2 (fun c w => to_word br c = Some w) cs ws ->
  forall i c, nth_error cs i = Some c -> to_word br c = Some (nth i ws (1%positive, 0%Z)).
Proof.
  intro H. induction H as [|c w cs ws Hw Hws IH]; intros [|i] d Hd;
    cbn in Hd |- *; try discriminate.
  - inversion Hd; subst d. exact Hw.
  - now apply IH.
Qed.

Local Lemma readback_sound {A B C} (R : A -> C -> Prop) (env : nat -> Cost.t A)
    (xs : list B) (cs : list C) start :
  length xs = length cs ->
  (forall i c, nth_error cs i = Some c -> R (Cost.value (env (start + i)%nat)) c) ->
  Forall2 R (Cost.value (readback_c env start xs)) cs.
Proof.
  revert cs start. induction xs as [|x xs IH]; intros [|c cs] start Hlen Henv;
    cbn in Hlen; try discriminate; [constructor|].
  cbn [readback_c]. autorewrite with galois_cost. constructor.
  - specialize (Henv O c eq_refl). now rewrite Nat.add_0_r in Henv.
  - apply IH; [now injection Hlen|].
    intros i d Hd. specialize (Henv (S i) d Hd).
    rewrite Nat.add_succ_r in Henv. exact Henv.
Qed.

Local Lemma numeric_refine_sound {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    ev truth top xs cs ws e a r :
  numeric_laws D G -> op_bridge_laws br ev truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  Forall2 (gamma (numeric_conc D G br)) xs cs ->
  Forall2 (fun c w => to_word br c = Some w) cs ws ->
  eval eval_op (fun i => nth i ws (1%positive, 0%Z)) e = Some r -> gamma G a r ->
  Forall2 (gamma (numeric_conc D G br)) (Cost.value (numeric_refine_c D top xs e a)) cs.
Proof.
  intros HN HB Htop Hxs Hws He Ha.
  assert (Henv : forall i, gamma G (Cost.value (nth_c xs top i))
    (nth i ws (1%positive, 0%Z))).
  { apply nth_facts; [apply Htop, zero_is_word|].
    exact (numeric_words D G br xs cs ws Hxs Hws). }
  pose proof (nth_words br ev truth HB cs ws Hws) as Hok.
  pose proof (num_eval_c_sound D G _ _ e r HN Hok Henv He) as Hresult.
  pose proof (meet_sound HN _ a r Hresult Ha) as Hcommon.
  unfold numeric_refine_c. autorewrite with galois_cost.
  destruct (Cost.value (leb_c (lat D)
    (Cost.value (meet_c D (Cost.value (num_eval_c D (nth_c xs top) e)) a))
    (bot (lat D)))) eqn:Hempty.
  - exfalso. apply (gamma_bot_empty (bot_empty HN) r).
    exact (gamma_monotone (gamma_laws HN) _ _ r Hempty Hcommon).
  - autorewrite with galois_cost.
  apply readback_sound; [exact (Forall2_length Hxs)|].
  intros i c Hnth. cbn [Nat.add].
  cbn [numeric_conc gamma]. rewrite (nth_conversion br cs ws Hws i c Hnth).
  exact (num_assume_c_sound D G (nth_c xs top)
    (fun i => nth i ws (1%positive, 0%Z)) e a r HN Hok Henv He Ha i).
Qed.

Local Lemma numeric_top_sound {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    ev truth top :
  op_bridge_laws br ev truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  leb (lat D) top (bot (lat D)) = false -> forall c, gamma (numeric_conc D G br) top c.
Proof.
  intros H Htop Hnot c. cbn. destruct (to_word br c) as [[w z]|] eqn:Hw.
  - apply Htop. exact (bridge_word H c (w, z) Hw).
  - exact Hnot.
Qed.

Local Lemma bits_op_sound {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    ev truth top :
  numeric_laws D G -> op_bridge_laws br ev truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  leb (lat D) top (bot (lat D)) = false ->
  forall k xs cs c, Forall2 (gamma (numeric_conc D G br)) xs cs -> ev k cs = Some c ->
  gamma (numeric_conc D G br) (ValueAbs.op (bits_values D br top) k xs) c.
Proof.
  intros HN HB Htop Hnot k xs cs c Hxs He.
  unfold ValueAbs.op. cbn [bits_values ValueAbs.op_c]. autorewrite with galois_cost.
  change (Cost.value (op_expr_c br k)) with (op_expr br k).
  destruct (op_expr br k) as [e|] eqn:Hex.
  - destruct (bridge_eq HB k cs c e He Hex) as [ws [wr [Hws [Hr Hw]]]].
    cbn [numeric_conc gamma]. rewrite Hw.
    autorewrite with galois_cost. rewrite ?Hex.
    eapply (num_eval_c_sound D G (nth_c xs top)
      (fun i => nth i ws (1%positive, 0%Z)) e wr HN).
    + exact (nth_words br ev truth HB cs ws Hws).
    + apply nth_facts; [apply Htop, zero_is_word|].
      exact (numeric_words D G br xs cs ws Hxs Hws).
    + exact Hr.
  - exact (numeric_top_sound D G br ev truth top HB Htop Hnot c).
Qed.

Local Lemma bits_back_sound {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    ev truth top :
  numeric_laws D G -> op_bridge_laws br ev truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  forall k a xs cs c, Forall2 (gamma (numeric_conc D G br)) xs cs -> ev k cs = Some c ->
  gamma (numeric_conc D G br) a c ->
  Forall2 (gamma (numeric_conc D G br)) (ValueAbs.back (bits_values D br top) k a xs) cs.
Proof.
  intros HN HB Htop k a xs cs c Hxs He Ha.
  unfold ValueAbs.back. cbn [bits_values ValueAbs.back_c]. autorewrite with galois_cost.
  change (Cost.value (op_expr_c br k)) with (op_expr br k).
  destruct (op_expr br k) as [e|] eqn:Hex; [|exact Hxs].
  destruct (bridge_eq HB k cs c e He Hex) as [ws [wr [Hws [Hr Hw]]]].
  cbn [numeric_conc gamma] in Ha. rewrite Hw in Ha.
  exact (numeric_refine_sound D G br ev truth top xs cs ws e a wr
    HN HB Htop Hxs Hws Hr Ha).
Qed.

Local Lemma bool_constant {A} (D : numeric_domain A) G :
  numeric_laws D G -> forall b : bool,
  gamma G (of_const D 1%positive (if b then 1%Z else 0%Z))
    (1%positive, if b then 1%Z else 0%Z).
Proof.
  intros H [|].
  - pose proof (of_const_sound H 1%positive 1%Z) as Hc. now rewrite wrap_1 in Hc.
  - pose proof (of_const_sound H 1%positive 0%Z) as Hc. now rewrite wrap_0 in Hc.
Qed.

Local Lemma bits_guard_sound {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    ev truth top :
  numeric_laws D G -> op_bridge_laws br ev truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  forall g xs cs, Forall2 (gamma (numeric_conc D G br)) xs cs ->
  ValueSem.holds (bits_sem br ev truth) g cs ->
  Forall2 (gamma (numeric_conc D G br)) (Cost.value (bits_guard_c D br top g xs)) cs.
Proof.
  intros HN HB Htop [b|d|d|e b] xs cs Hxs Hg.
  - destruct xs as [|a [|a' xs]]; try exact Hxs.
    inversion Hxs as [|a0 c xs0 cs0 Ha Htail]; subst.
    inversion Htail; subst. cbn [bits_sem ValueSem.holds] in Hg.
    cbn [bits_guard_c]. destruct (truth_words br) eqn:Hcap; [|exact Hxs].
    autorewrite with galois_cost.
    destruct (truth_total HB Hcap c) as [[w z] Hw].
    assert (Hwords : Forall2 (fun c w => to_word br c = Some w) [c] [(w, z)]).
    { constructor; [exact Hw|constructor]. }
    assert (He : eval eval_op (fun i => nth i [(w, z)] (1%positive, 0%Z))
      (Var 0) = Some (w, z)).
    { rewrite eval_var. cbn [nth]. rewrite normalize_word_id; [reflexivity|].
      exact (bridge_word HB c (w, z) Hw). }
    pose proof (numeric_truth_eval _ _ _ _ He) as Htruth.
    pose proof (bridge_truth HB c (w, z) Hw) as Hbool. cbn in Hbool.
    rewrite <- Hbool, Hg in Htruth.
    eapply numeric_refine_sound; eauto. apply bool_constant, HN.
  - destruct xs as [|a [|a' xs]]; try exact Hxs.
    inversion Hxs as [|a0 c xs0 cs0 Ha Htail]; subst.
    inversion Htail; subst. cbn [bits_sem ValueSem.holds] in Hg. subst c.
    cbn [bits_guard_c]. autorewrite with galois_cost.
    change (Cost.value (to_word_c br d)) with (to_word br d).
    destruct (to_word br d) as [[w z]|] eqn:Hw; [|exact Hxs].
    autorewrite with galois_cost. constructor; [|constructor].
    cbn [numeric_conc gamma] in Ha |- *. rewrite Hw in Ha |- *.
    apply (meet_sound HN); [exact Ha|].
    pose proof (of_const_sound HN w z) as Hc.
    rewrite (wrap_id w z (bridge_word HB d (w, z) Hw)) in Hc. exact Hc.
  - destruct xs as [|a [|a' xs]]; try exact Hxs.
    inversion Hxs as [|a0 c xs0 cs0 Ha Htail]; subst.
    inversion Htail; subst. cbn [bits_sem ValueSem.holds] in Hg.
    cbn [bits_guard_c]. autorewrite with galois_cost.
    change (Cost.value (differ_words_c br d)) with (differ_words br d).
    destruct (differ_words br d) eqn:Hcap; [|exact Hxs].
    autorewrite with galois_cost.
    change (Cost.value (to_word_c br d)) with (to_word br d).
    destruct (to_word br d) as [[wd zd]|] eqn:Hd; [|exact Hxs].
    autorewrite with galois_cost.
    destruct (differ_total HB d Hcap c) as [[wc zc] Hc].
    pose proof (differ_width HB d c (wc, zc) (wd, zd) Hcap Hc Hd) as Hwidth.
    cbn in Hwidth. subst wc.
    assert (Hne : zc <> zd).
    { intro Heq. subst zc. apply Hg.
      exact (differ_injective HB d c (wd, zd) Hcap Hc Hd). }
    assert (Hew : eval eval_op
      (fun i => nth i [(wd, zc)] (1%positive, 0%Z))
      (App bvne [Var 0; Const wd zd]) = Some (1%positive, 1%Z)).
    { rewrite eval_app, !eval_args_cons, eval_var, eval_const, eval_args_nil.
      cbn [nth]. rewrite normalize_word_id by exact (bridge_word HB c _ Hc).
      rewrite wrap_id by exact (bridge_word HB d _ Hd).
      change (eval_op bvne [(wd, zc); (wd, zd)] = Some (1%positive, 1%Z)).
      rewrite (eval_op_cmp bvne wd zc zd
        (fun w x y => negb (Z.eqb (wrap w x) (wrap w y))) eq_refl).
      rewrite !wrap_id by (first [exact (bridge_word HB c _ Hc)|exact (bridge_word HB d _ Hd)]).
      apply Z.eqb_neq in Hne. rewrite Hne. reflexivity. }
    refine (numeric_refine_sound D G br ev truth top [a] [c] [(wd, zc)]
      (App bvne [Var 0; Const wd zd]) (of_const D 1%positive 1%Z)
      (1%positive, 1%Z) HN HB Htop Hxs _ Hew _).
    + constructor; [exact Hc|constructor].
    + exact (bool_constant D G HN true).
  - destruct Hg as [ws [w [z [Hws [He Hb]]]]].
    cbn [bits_guard_c]. autorewrite with galois_cost.
    pose proof (numeric_truth_eval _ _ _ _ He) as Htruth. rewrite Hb in Htruth.
    eapply numeric_refine_sound; eauto. apply bool_constant, HN.
Qed.

Local Lemma refine_length {A} (D : numeric_domain A) top xs e a :
  length (Cost.value (numeric_refine_c D top xs e a)) = length xs.
Proof.
  unfold numeric_refine_c. autorewrite with galois_cost.
  destruct (Cost.value (leb_c (lat D)
    (Cost.value (meet_c D (Cost.value (num_eval_c D (nth_c xs top) e)) a))
    (bot (lat D)))); autorewrite with galois_cost.
  - apply length_map.
  - apply readback_length.
Qed.

Local Lemma bits_guard_length {A K C} (D : numeric_domain A) (br : op_bridge K C)
    top g xs :
  length (Cost.value (bits_guard_c D br top g xs)) = length xs.
Proof.
  destruct g as [b|d|d|e b].
  - destruct xs as [|a [|a' xs]]; try reflexivity. cbn [bits_guard_c].
    destruct (truth_words br); [|reflexivity]. autorewrite with galois_cost.
    apply refine_length.
  - destruct xs as [|a [|a' xs]]; try reflexivity. cbn [bits_guard_c].
    autorewrite with galois_cost.
    destruct (Cost.value (to_word_c br d)) as [[w z]|]; [|reflexivity].
    autorewrite with galois_cost. reflexivity.
  - destruct xs as [|a [|a' xs]]; try reflexivity. cbn [bits_guard_c].
    autorewrite with galois_cost.
    destruct (Cost.value (differ_words_c br d)); [|reflexivity].
    autorewrite with galois_cost.
    destruct (Cost.value (to_word_c br d)) as [[w z]|]; [|reflexivity].
    autorewrite with galois_cost. apply refine_length.
  - cbn [bits_guard_c]. autorewrite with galois_cost. apply refine_length.
Qed.

(** Lawful numeric dictionaries and capability-respecting bridges yield lawful open values. *)
Theorem bits_values_laws {A K C} (D : numeric_domain A) G (br : op_bridge K C)
    top ev truth :
  numeric_laws D G -> op_bridge_laws br ev truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) ->
  leb (lat D) top (bot (lat D)) = false ->
  value_laws (bits_values D br top) (bits_sem br ev truth) (numeric_conc D G br).
Proof.
  intros HN HB Htop Hnot. constructor.
  - exact (lat_laws HN).
  - constructor. intros a b c Hab Ha. cbn in Ha |- *.
    destruct (to_word br c) as [w|].
    + exact (gamma_monotone (gamma_laws HN) a b w Hab Ha).
    + destruct (leb (lat D) b (bot (lat D))) eqn:Hb; [|reflexivity].
      pose proof (leb_trans (lat_laws HN) a b _ Hab Hb). congruence.
  - intro c. cbn. destruct (to_word br c) as [w|].
    + exact (gamma_bot_empty (bot_empty HN) w).
    + rewrite (leb_refl (lat_laws HN)). discriminate.
  - intro c. pose proof (numeric_top_sound D G br ev truth top HB Htop Hnot c).
    gamma_solver.
  - exact (bits_op_sound D G br ev truth top HN HB Htop Hnot).
  - exact (bits_back_sound D G br ev truth top HN HB Htop).
  - exact (bits_guard_sound D G br ev truth top HN HB Htop).
  - intros k a xs. unfold ValueAbs.back. cbn [bits_values ValueAbs.back_c].
    autorewrite with galois_cost.
    destruct (Cost.value (op_expr_c br k)); [apply refine_length|reflexivity].
  - exact (bits_guard_length D br top).
Qed.

#[export] Hint Resolve bits_values_laws num_eval_sound num_assume_sound : galois_gamma.

Arguments numeric_refine_c : simpl never.
Arguments bits_guard_c : simpl never.
Arguments nth_c : simpl never.
Arguments readback_c : simpl never.
