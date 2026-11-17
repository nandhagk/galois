(** * Linear word evaluation

    Bitwise, additive, comparison and resizing operators have linear derived clocks.
    For example, addition has linear cost in the operand widths and raw integer sizes.

    Main results
    - [linear_value_time_le] Value evaluation of a linear operator fits the metadata and operand
      widths in time and size, with [linear_value_size_le], [linear_result_width_size_le],
      [linear_result_width_time_le] and [normalize_words_time_le].
    - [eval_op_linear_time_le] Evaluating a linear operator charges width checks, normalisation and
      wrapping linearly in the metadata widths and raw operand sizes.
    - [eval_op_linear_complexity] Linear operator evaluation is linear in metadata widths and
      raw operand sizes,
      O(op widths + total operand size).

    Builds on: Word, Fun and Op. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Bits Require Import Word Fun Testbit Arith Op.
Import List.ListNotations.
Import ComplexityNotations.

Local Open Scope Z_scope.

(** These operators use no multiplication or division of two word-sized values. *)
Definition linear_op (o : op) : bool :=
  match o with
  | bvnot | bvneg | bvadd | bvsub | bvand | bvor | bvxor
  | bveq | bvne | bvult | bvule | bvslt | bvsle | bvite
  | bvzext _ | bvsext _ | bvtrunc _ => true
  | _ => false
  end.

(** * Dispatch costs *)

(** Linear unary tags add only a constant to their selected operation. *)
Lemma linear_unary_time_le tag w x : (tag = UNot \/ tag = UNeg) ->
  (T_eval_unary_tag tag w x <=
    256 * N.of_nat (Pos.to_nat w + Z.size_nat x + 1))%N.
Proof.
  intros [-> | ->].
  - pose proof (wnot_time_le w x) as Htime.
    time_unfold T_eval_unary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  - pose proof (wneg_time_le w x) as Htime.
    time_unfold T_eval_unary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** Linear binary tags add only a constant to their selected operation. *)
Lemma linear_binary_time_le tag w x y :
  (tag = BAdd \/ tag = BSub \/ tag = BAnd \/ tag = BOr \/ tag = BXor) ->
  (T_eval_binary_tag tag w x y <=
    256 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  intros [-> | [-> | [-> | [-> | ->]]]].
  - pose proof (wadd_time_le w x y) as Htime.
    time_unfold T_eval_binary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  - pose proof (wsub_time_le w x y) as Htime.
    time_unfold T_eval_binary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  - pose proof (wand_time_le w x y) as Htime.
    time_unfold T_eval_binary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  - pose proof (wor_time_le w x y) as Htime.
    time_unfold T_eval_binary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  - pose proof (wxor_time_le w x y) as Htime.
    time_unfold T_eval_binary_tag. rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** Comparisons charge two linear unsigned or signed interpretations. *)
Lemma comparison_time_le tag w x y :
  (T_eval_comparison_tag tag w x y <=
    512 * N.of_nat (Pos.to_nat w + Z.size_nat x + Z.size_nat y + 1))%N.
Proof.
  pose proof (wrap_time_le w x) as Hx.
  pose proof (wrap_time_le w y) as Hy.
  pose proof (signed_time_le w x) as Hsignedx.
  pose proof (signed_time_le w y) as Hsignedy.
  pose proof (time_of_nat_le _ _ (wrap_size_le w x)) as Hsx.
  pose proof (time_of_nat_le _ _ (signed_size_le w x)) as Hssx.
  pose proof (Z.T_eqb_le (wrap w x) (wrap w y)) as Heq.
  pose proof (Z.T_ltb_le (wrap w x) (wrap w y)) as Hult.
  pose proof (Z.T_leb_le (wrap w x) (wrap w y)) as Hule.
  pose proof (Z.T_ltb_le (signed w x) (signed w y)) as Hslt.
  pose proof (Z.T_leb_le (signed w x) (signed w y)) as Hsle.
  destruct tag; time_unfold T_eval_comparison_tag;
    try time_unfold T_wult; try time_unfold T_wule;
    try time_unfold T_wslt; try time_unfold T_wsle;
    time_simpl; rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** A selected linear unary operator is complement or negation. *)
Lemma linear_unary_tag o tag : linear_op o = true -> word_fun1 o = Some tag ->
  tag = UNot \/ tag = UNeg.
Proof.
  destruct o; cbn [linear_op word_fun1]; intros Hlinear Htag; try discriminate;
    inversion Htag; auto.
Qed.

(** A selected linear binary operator is additive or bitwise. *)
Lemma linear_binary_tag o tag : linear_op o = true -> word_fun2 o = Some tag ->
  tag = BAdd \/ tag = BSub \/ tag = BAnd \/ tag = BOr \/ tag = BXor.
Proof.
  destruct o; cbn [linear_op word_fun2]; intros Hlinear Htag; try discriminate;
    inversion Htag; auto.
Qed.

(** Unary value dispatch fits a linear budget in its normalized operand width. *)
Lemma linear_value_unary_time_le o tag w x : linear_op o = true ->
  word_fun1 o = Some tag ->
  (T_op_value o [(w, wrap w x)] <= 1024 * N.of_nat (Pos.to_nat w + 1))%N.
Proof.
  intros Hlinear Htag.
  pose proof (linear_unary_time_le tag w (wrap w x)
    (linear_unary_tag o tag Hlinear Htag)) as Htime.
  pose proof (time_of_nat_le _ _ (wrap_size_le w x)) as Hsize.
  time_unfold T_op_value. rewrite Htag. destruct (word_fun2 o), (word_cmp o);
    time_simpl; rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** Binary value dispatch fits both normalized operand widths, even when they differ. *)
Lemma linear_value_binary_time_le o tag wa wb x y : linear_op o = true ->
  word_fun2 o = Some tag ->
  (T_op_value o [(wa, wrap wa x); (wb, wrap wb y)] <=
    2048 * N.of_nat (Pos.to_nat wa + Pos.to_nat wb + 1))%N.
Proof.
  intros Hlinear Htag.
  pose proof (linear_binary_time_le tag wa (wrap wa x) (wrap wb y)
    (linear_binary_tag o tag Hlinear Htag)) as Htime.
  pose proof (time_of_nat_le _ _ (wrap_size_le wa x)) as Hsx.
  pose proof (time_of_nat_le _ _ (wrap_size_le wb y)) as Hsy.
  time_unfold T_op_value. rewrite Htag. destruct (word_fun1 o), (word_cmp o);
    time_simpl; rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** Comparison dispatch fits both normalized operand widths. *)
Lemma value_comparison_time_le o tag wa wb x y : word_cmp o = Some tag ->
  (T_op_value o [(wa, wrap wa x); (wb, wrap wb y)] <=
    2048 * N.of_nat (Pos.to_nat wa + Pos.to_nat wb + 1))%N.
Proof.
  intros Htag.
  pose proof (comparison_time_le tag wa (wrap wa x) (wrap wb y)) as Htime.
  pose proof (time_of_nat_le _ _ (wrap_size_le wa x)) as Hsx.
  pose proof (time_of_nat_le _ _ (wrap_size_le wb y)) as Hsy.
  assert (Hbinary : word_fun2 o = None) by (destruct o; cbn in *; congruence).
  time_unfold T_op_value. rewrite Htag, Hbinary. destruct (word_fun1 o);
    time_simpl; rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** Increasing a coefficient and an input budget preserves a linear clock bound. *)
Lemma time_linear_subsumes t c d a b : (t <= c * N.of_nat a)%N ->
  (c <= d)%N -> (a <= b)%nat -> (t <= d * N.of_nat b)%N.
Proof.
  intros Htime Hcoefficient Hsize. eapply N.le_trans; [exact Htime|].
  apply N.mul_le_mono; [exact Hcoefficient|apply time_of_nat_le; exact Hsize].
Qed.

(** Value evaluation for a linear operator fits the metadata and normalized widths. *)
Theorem linear_value_time_le o xs : linear_op o = true ->
  (T_op_value o (map normalize_word xs) <= 4096 * N.of_nat (op_widths o +
    fold_right Nat.add 0%nat (map (fun c => Pos.to_nat (fst c)) xs) + 1))%N.
Proof.
  intros Hlinear. destruct o; cbn [linear_op] in Hlinear; try discriminate;
    destruct xs as [|[a x] [|[b y] [|[c z] [|d rest]]]];
    cbn [map normalize_word fst snd op_widths fold_right].
  all: unfold normalize_word; cbn [fst snd].
  all: try (eapply time_linear_subsumes;
    [eapply linear_value_unary_time_le; [reflexivity|reflexivity]|lia|lia]).
  all: try (eapply time_linear_subsumes;
    [eapply linear_value_binary_time_le; [reflexivity|reflexivity]|lia|lia]).
  all: try (eapply time_linear_subsumes;
    [eapply value_comparison_time_le; [reflexivity]|lia|lia]).
  all: try (time_unfold T_op_value; time_simpl;
    rewrite ?Nat2N.inj_add in *; time_cbn_all; lia).
  - pose proof (Z.T_eqb_le (wrap a x) 1) as Heq.
    pose proof (time_of_nat_le _ _ (wrap_size_le a x)) as Hsize.
    time_unfold T_op_value. time_simpl.
    rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
  - pose proof (signed_time_le a (wrap a x)) as Hsigned.
    pose proof (time_of_nat_le _ _ (wrap_size_le a x)) as Hsize.
    time_unfold T_op_value. time_simpl.
    rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** * Result sizes and width checking *)

(** A unary value has at most its declared width many bits. *)
Lemma unary_value_size_le tag w x :
  (Z.size_nat (eval_unary_tag tag w x) <= Pos.to_nat w)%nat.
Proof.
  apply word_size_le. destruct tag; cbn [eval_unary_tag];
    first [apply wnot_is_word|apply wrap_is_word|apply wclz_is_word|
      apply wctz_is_word|apply wpopcnt_is_word].
Qed.

(** A binary value has at most its declared width many bits. *)
Lemma binary_value_size_le tag w x y :
  (Z.size_nat (eval_binary_tag tag w x y) <= Pos.to_nat w)%nat.
Proof.
  apply word_size_le. destruct tag; cbn [eval_binary_tag];
    first [apply wrap_is_word|apply wudiv_is_word|apply wurem_is_word|
      apply wsdiv_is_word|apply wsrem_is_word|apply wsmod_is_word|
      apply wand_is_word|apply wor_is_word|apply wxor_is_word|apply wshl_is_word|
      apply wlshr_is_word|apply washr_is_word|
      unfold wrotr, wrotl; apply wrap_is_word|unfold wrotl; apply wrap_is_word].
Qed.

(** Linear intermediate values fit the metadata and normalized operand widths. *)
Theorem linear_value_size_le o xs : linear_op o = true ->
  (Z.size_nat (op_value o (map normalize_word xs)) <=
    op_widths o + fold_right Nat.add 0%nat (map (fun c => Pos.to_nat (fst c)) xs) + 1)%nat.
Proof.
  intros Hlinear. destruct o; cbn [linear_op] in Hlinear; try discriminate;
    destruct xs as [|[a x] [|[b y] [|[c z] [|d rest]]]];
    cbn [op_value word_fun1 word_fun2 word_cmp map normalize_word fst snd
      op_widths fold_right];
    try (eapply Nat.le_trans; [apply unary_value_size_le|lia]);
    try (eapply Nat.le_trans; [apply binary_value_size_le|lia]);
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    end;
    try (eapply Nat.le_trans; [apply wrap_size_le|lia]);
    try (eapply Nat.le_trans; [apply signed_size_le|lia]);
    cbn [Z.size_nat Pos.size_nat]; lia.
Qed.

(** A checked linear operator returns a width covered by its metadata and operands. *)
Theorem linear_result_width_size_le o ws rw : linear_op o = true ->
  result_width o ws = Some rw ->
  (Pos.to_nat rw <= op_widths o + fold_right Nat.add 0%nat (map Pos.to_nat ws) + 1)%nat.
Proof.
  intros Hlinear. destruct o; cbn [linear_op] in Hlinear; try discriminate;
    destruct ws as [|a [|b [|c [|d rest]]]];
    cbn [result_width op_widths map fold_right]; try discriminate;
    repeat match goal with
    | |- (if ?test then _ else _) = _ -> _ => destruct test; try discriminate
    end; intros Hwidth; inversion Hwidth; subst;
    rewrite ?Pos2Nat.inj_add; cbn [Pos.to_nat]; lia.
Qed.

(** Linear operator metadata uses only linear positive arithmetic and comparisons. *)
Theorem linear_result_width_time_le o ws : linear_op o = true ->
  (T_result_width o ws <= 128 * N.of_nat (op_widths o +
    fold_right Nat.add 0%nat (map Pos.to_nat ws) + 1))%N.
Proof.
  intros Hlinear. destruct o; cbn [linear_op] in Hlinear; try discriminate;
    destruct ws as [|a [|b [|c [|d rest]]]].
  all: time_unfold T_result_width; cbn [op_widths map fold_right]; time_simpl.
  all: try pose proof (time_of_nat_le _ _ (positive_size_value a)) as Hsizea;
    try pose proof (time_of_nat_le _ _ (positive_size_value b)) as Hsizeb;
    try pose proof (time_of_nat_le _ _ (positive_size_value c)) as Hsizec;
    try pose proof (time_of_nat_le _ _ (positive_size_value extra)) as Hsizeextra;
    try pose proof (time_of_nat_le _ _ (positive_size_value target)) as Hsizetarget.
  all: try time_unfold Pos.T_leb; time_pose.
  all: repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    end; rewrite ?Nat2N.inj_add in *; time_cbn_all; lia.
Qed.

(** * Operand normalization and evaluation *)

(** Operand widths are bounded by widths plus raw magnitude sizes. *)
Lemma operand_widths_le xs :
  (fold_right Nat.add 0%nat (map (fun c => Pos.to_nat (fst c)) xs) <=
    fold_right Nat.add 0%nat
      (map (fun c => (Pos.to_nat (fst c) + Z.size_nat (snd c))%nat) xs))%nat.
Proof.
  induction xs as [|[w z] xs IH]; cbn [map fold_right fst snd]; lia.
Qed.

(** Every positive operand width pays for its list entry. *)
Lemma operand_length_le xs :
  (length xs <= fold_right Nat.add 0%nat
    (map (fun c => (Pos.to_nat (fst c) + Z.size_nat (snd c))%nat) xs))%nat.
Proof.
  induction xs as [|[w z] xs IH]; cbn [length map fold_right fst snd];
    [lia|pose proof (Pos2Nat.is_pos w); lia].
Qed.

(** Normalizing an operand list is linear in its total raw bit budget. *)
Theorem normalize_words_time_le xs :
  (ListDef.T_map normalize_word (fun c => T_normalize_word c) xs <=
    96 * N.of_nat (fold_right Nat.add 0%nat
      (map (fun c => (Pos.to_nat (fst c) + Z.size_nat (snd c))%nat) xs) + 1))%N.
Proof.
  induction xs as [|[w z] xs IH].
  - time_unfold (@ListDef.T_map). cbn. lia.
  - time_unfold (@ListDef.T_map). unfold T_normalize_word at 1.
    cbn [map fold_right fst snd] in *. time_simpl.
    pose proof (wrap_time_le w z) as Hwrap.
    pose proof (time_of_nat_le _ _ (Pos2Nat.is_pos w)) as Hpositive.
    rewrite ?Nat2N.inj_add in *; time_cbn_all;
      rewrite ?Nat2N.inj_add in *; lia.
Qed.

(** Evaluation of a linear operator charges width checks, normalization and wrapping. *)
Theorem eval_op_linear_time_le o xs : linear_op o = true ->
  (T_eval_op o xs <= 8192 * N.of_nat (op_widths o +
    fold_right Nat.add 0%nat
      (map (fun c => (Pos.to_nat (fst c) + Z.size_nat (snd c))%nat) xs) + 1))%N.
Proof.
  intros Hlinear. pose proof (operand_widths_le xs) as Hwidths.
  set (raw := fold_right Nat.add 0%nat
    (map (fun c => (Pos.to_nat (fst c) + Z.size_nat (snd c))%nat) xs)) in *.
  set (budget := N.of_nat (op_widths o + raw + 1)).
  assert (Hprojection : (ListDef.T_map (@fst width Z)
    (fun c => @Datatypes.T_fst width Z c) xs <= 4 * budget)%N).
  { pose proof (ListDef.T_map_le (@fst width Z) (fun c => @Datatypes.T_fst width Z c)
      1 xs ltac:(intros [w z]; time_step)) as Hmap.
    pose proof (time_of_nat_le _ _ (operand_length_le xs)) as Hlength.
    fold raw in Hlength. unfold budget, word, width in *.
    rewrite ?Nat2N.inj_add in *; time_cbn_all; lia. }
  assert (Hmetadata : (T_result_width o (map fst xs) <= 128 * budget)%N).
  { unfold budget. eapply time_linear_subsumes;
      [apply linear_result_width_time_le; exact Hlinear|lia|].
    rewrite map_map. unfold word, width in *. lia. }
  assert (Hnormalize : (ListDef.T_map normalize_word (fun c => T_normalize_word c) xs <=
    96 * budget)%N).
  { unfold budget. eapply time_linear_subsumes;
      [apply normalize_words_time_le|lia|unfold raw; lia]. }
  assert (Hvalue : (T_op_value o (map normalize_word xs) <= 4096 * budget)%N).
  { unfold budget. eapply time_linear_subsumes;
      [apply linear_value_time_le; exact Hlinear|lia|lia]. }
  time_unfold T_eval_op. destruct (result_width o (map fst xs)) as [rw|] eqn:Hwidth.
  - assert (Hwrap : (T_wrap rw (op_value o (map normalize_word xs)) <= 96 * budget)%N).
    { pose proof (wrap_time_le rw (op_value o (map normalize_word xs))) as Htime.
      pose proof (linear_result_width_size_le o (map fst xs) rw Hlinear Hwidth) as Hresult.
      rewrite map_map in Hresult.
      pose proof (linear_value_size_le o xs Hlinear) as Hsize.
      apply time_of_nat_le in Hresult. apply time_of_nat_le in Hsize.
      apply time_of_nat_le in Hwidths. unfold budget, word, width in *.
      rewrite ?Nat2N.inj_add in *; time_cbn_all; lia. }
    assert (Hpositive : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. time_cbn. lia. }
    clearbody budget raw. unfold word, width in *. time_cbn_all. lia.
  - assert (Hpositive : (1 <= budget)%N).
    { unfold budget. rewrite Nat2N.inj_add. time_cbn. lia. }
    clearbody budget raw. unfold word, width in *. time_cbn_all. lia.
Qed.

(** Linear operator evaluation is linear in metadata widths and raw operand sizes. *)
Theorem eval_op_linear_complexity :
  T_eval_op o xs ∈ 𝑂(N.of_nat (op_widths o +
    fold_right Nat.add 0%nat
      (map (fun c => (Pos.to_nat (fst c) + Z.size_nat (snd c))%nat) xs)))
  for (o, xs) | linear_op o = true.
Proof.
  apply (bigO_intro _ _ _ 8192). intros [o xs] Hlinear. cbn [fst snd] in *.
  pose proof (eval_op_linear_time_le o xs Hlinear) as Htime.
  rewrite Nat2N.inj_add in Htime. time_cbn_all. lia.
Qed.
