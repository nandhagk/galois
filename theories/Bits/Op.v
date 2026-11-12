(** * First-order bitvector operators

    Operator tags select width checks, arithmetic and metadata.
    For example, binary addition checks that both operand widths agree.
    Builds on: Word, Fun, Testbit, Arith and Base code. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time Std.
From Galois.Base Require Import Code KeySig.
From Galois.Bits Require Import Word Fun Testbit Arith Tactics.
Import List.ListNotations.

Open Scope Z_scope.

(** The closed operator vocabulary retains the legacy constructors and parameters. *)
Inductive op : Type :=
  | bvnot
  | bvneg
  | bvclz
  | bvctz
  | bvpopcnt
  | bvadd
  | bvsub
  | bvmul
  | bvudiv
  | bvurem
  | bvsdiv
  | bvsrem
  | bvsmod
  | bvand
  | bvor
  | bvxor
  | bvshl
  | bvlshr
  | bvashr
  | bvrotl
  | bvrotr
  | bveq
  | bvne
  | bvult
  | bvule
  | bvslt
  | bvsle
  | bvite
  | bvzext (extra : positive)
  | bvsext (extra : positive)
  | bvtrunc (target : width)
  | bvextract (hi lo : nat)
  | bvconcat.


(** Operator metadata charges each carried width or extraction index. *)
Definition op_widths (o : op) : nat :=
  match o with
  | bvzext w | bvsext w | bvtrunc w => Pos.to_nat w
  | bvextract hi lo => (hi + lo)%nat
  | _ => 0%nat
  end.

(** Tags select an operation without storing an executable closure. *)
Inductive unary_tag := UNot | UNeg | UClz | UCtz | UPopcnt.
Inductive binary_tag :=
  | BAdd | BSub | BMul | BUdiv | BUrem | BSdiv | BSrem | BSmod
  | BAnd | BOr | BXor | BShl | BLshr | BAshr | BRotl | BRotr.
Inductive comparison_tag := CEq | CNe | CUlt | CUle | CSlt | CSle.

Definition eval_unary_tag tag w x :=
  match tag with
  | UNot => wnot w x | UNeg => wneg w x | UClz => wclz w x
  | UCtz => wctz w x | UPopcnt => wpopcnt w x
  end.
Definition eval_binary_tag tag w x y :=
  match tag with
  | BAdd => wadd w x y | BSub => wsub w x y | BMul => wmul w x y
  | BUdiv => wudiv w x y | BUrem => wurem w x y | BSdiv => wsdiv w x y
  | BSrem => wsrem w x y | BSmod => wsmod w x y | BAnd => wand w x y
  | BOr => wor w x y | BXor => wxor w x y | BShl => wshl w x y
  | BLshr => wlshr w x y | BAshr => washr w x y | BRotl => wrotl w x y
  | BRotr => wrotr w x y
  end.
Definition eval_comparison_tag tag w x y :=
  match tag with
  | CEq => wrap w x =? wrap w y | CNe => negb (wrap w x =? wrap w y)
  | CUlt => wult w x y | CUle => wule w x y
  | CSlt => wslt w x y | CSle => wsle w x y
  end.
Definition word_fun1 o :=
  match o with
  | bvnot => Some UNot | bvneg => Some UNeg | bvclz => Some UClz
  | bvctz => Some UCtz | bvpopcnt => Some UPopcnt | _ => None
  end.
Definition word_fun2 o :=
  match o with
  | bvadd => Some BAdd | bvsub => Some BSub | bvmul => Some BMul
  | bvudiv => Some BUdiv | bvurem => Some BUrem | bvsdiv => Some BSdiv
  | bvsrem => Some BSrem | bvsmod => Some BSmod | bvand => Some BAnd
  | bvor => Some BOr | bvxor => Some BXor | bvshl => Some BShl
  | bvlshr => Some BLshr | bvashr => Some BAshr | bvrotl => Some BRotl
  | bvrotr => Some BRotr | _ => None
  end.
Definition word_cmp o :=
  match o with
  | bveq => Some CEq | bvne => Some CNe | bvult => Some CUlt
  | bvule => Some CUle | bvslt => Some CSlt | bvsle => Some CSle | _ => None
  end.

Definition arity o : nat :=
  match o with
  | bvnot | bvneg | bvclz | bvctz | bvpopcnt | bvzext _ | bvsext _
  | bvtrunc _ | bvextract _ _ => 1%nat
  | bvite => 3%nat
  | _ => 2%nat
  end.
Definition commutative o :=
  match o with bvadd | bvmul | bvand | bvor | bvxor | bveq | bvne => true
  | _ => false end.
Definition result_width o ws :=
  match o, ws with
  | (bvnot | bvneg | bvclz | bvctz | bvpopcnt), [w] => Some w
  | (bvzext n | bvsext n), [w] => Some (w + n)%positive
  | bvtrunc t, [w] => if Pos.leb t w then Some t else None
  | bvextract hi lo, [w] =>
      if (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w))%bool
      then Some (Pos.of_nat (S (hi - lo))) else None
  | bvconcat, [a; b] => Some (a + b)%positive
  | bvite, [c; a; b] => if Pos.eqb c 1 && Pos.eqb a b then Some a else None
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [a; b] =>
      if Pos.eqb a b then Some 1%positive else None
  | (bvadd | bvsub | bvmul | bvudiv | bvurem | bvsdiv | bvsrem | bvsmod |
      bvand | bvor | bvxor | bvshl | bvlshr | bvashr | bvrotl | bvrotr), [a; b] =>
      if Pos.eqb a b then Some a else None
  | _, _ => None
  end.
Definition op_value o xs : Z :=
  match word_fun1 o, word_fun2 o, word_cmp o, xs with
  | Some t, _, _, [(w, x)] => eval_unary_tag t w x
  | _, Some t, _, [(w, x); (_, y)] => eval_binary_tag t w x y
  | _, _, Some t, [(w, x); (_, y)] => if eval_comparison_tag t w x y then 1 else 0
  | _, _, _, [(_, c); (_, x); (_, y)] =>
      match o with bvite => if c =? 1 then x else y | _ => 0 end
  | _, _, _, [(w, x)] =>
      match o with
      | bvzext _ | bvtrunc _ => x
      | bvsext _ => signed w x
      | bvextract _ lo => x / 2 ^ Z.of_nat lo
      | _ => 0
      end
  | _, _, _, [(_, x); (w, y)] =>
      match o with bvconcat => x * modulus w + y | _ => 0 end
  | _, _, _, _ => 0
  end.
Local Open Scope nat_scope.
Definition op_code o : nat * (positive * positive) :=
  match o with
  | bvnot => (0, (1%positive, 1%positive)) | bvneg => (1, (1%positive, 1%positive))
  | bvclz => (2, (1%positive, 1%positive)) | bvctz => (3, (1%positive, 1%positive))
  | bvpopcnt => (4, (1%positive, 1%positive)) | bvadd => (5, (1%positive, 1%positive))
  | bvsub => (6, (1%positive, 1%positive)) | bvmul => (7, (1%positive, 1%positive))
  | bvudiv => (8, (1%positive, 1%positive)) | bvurem => (9, (1%positive, 1%positive))
  | bvsdiv => (10, (1%positive, 1%positive)) | bvsrem => (11, (1%positive, 1%positive))
  | bvsmod => (12, (1%positive, 1%positive)) | bvand => (13, (1%positive, 1%positive))
  | bvor => (14, (1%positive, 1%positive)) | bvxor => (15, (1%positive, 1%positive))
  | bvshl => (16, (1%positive, 1%positive)) | bvlshr => (17, (1%positive, 1%positive))
  | bvashr => (18, (1%positive, 1%positive)) | bvrotl => (19, (1%positive, 1%positive))
  | bvrotr => (20, (1%positive, 1%positive)) | bveq => (21, (1%positive, 1%positive))
  | bvne => (22, (1%positive, 1%positive)) | bvult => (23, (1%positive, 1%positive))
  | bvule => (24, (1%positive, 1%positive)) | bvslt => (25, (1%positive, 1%positive))
  | bvsle => (26, (1%positive, 1%positive)) | bvite => (27, (1%positive, 1%positive))
  | bvzext n => (28, (n, 1%positive)) | bvsext n => (29, (n, 1%positive))
  | bvtrunc n => (30, (n, 1%positive))
  | bvextract hi lo => (31, (Pos.of_succ_nat hi, Pos.of_succ_nat lo))
  | bvconcat => (32, (1%positive, 1%positive))
  end.
Local Open Scope Z_scope.
Definition normalize_word (x : word) : word := (fst x, wrap (fst x) (snd x)).
Definition eval_op (o : op) (xs : list word) : option word :=
  match result_width o (map fst xs) with
  | Some rw => Some (rw, wrap rw (op_value o (map normalize_word xs)))
  | None => None
  end.
Theorem eval_op_total : forall o xs,
  eval_op o xs = None <-> result_width o (map fst xs) = None.
Proof.
  intros o xs. unfold eval_op. destruct (result_width o (map fst xs));
    split; intro H; try discriminate; reflexivity.
Qed.

(** A successful evaluation returns the width chosen by width checking. *)
Theorem eval_op_width : forall o xs r, eval_op o xs = Some r ->
  result_width o (map fst xs) = Some (fst r).
Proof.
  intros o xs r. unfold eval_op. destruct (result_width o (map fst xs)) eqn:Hwidth;
    intro Hresult; [inversion Hresult; reflexivity|discriminate].
Qed.

(** Successful same-width binary dispatch requires equal operand widths. *)
(** A successful binary operation has equal operand widths. *)
Theorem eval_op_fun2_width : forall o t wa wb x y r,
  word_fun2 o = Some t -> eval_op o [(wa, x); (wb, y)] = Some r -> wa = wb.
Proof.
  intros o t wa wb x y r Hfun Hresult.
  op_cases o; cbn [word_fun2] in Hfun; try discriminate;
    unfold eval_op in Hresult; cbn [result_width map fst] in Hresult;
    destruct (Pos.eqb wa wb) eqn:Hwidth; try discriminate;
    now apply Pos.eqb_eq.
Qed.

(** A successful comparison has equal operand widths. *)
Theorem eval_op_cmp_width : forall o t wa wb x y r,
  word_cmp o = Some t -> eval_op o [(wa, x); (wb, y)] = Some r -> wa = wb.
Proof.
  intros o t wa wb x y r Hfun Hresult.
  op_cases o; cbn [word_cmp] in Hfun; try discriminate;
    unfold eval_op in Hresult; cbn [result_width map fst] in Hresult;
    destruct (Pos.eqb wa wb) eqn:Hwidth; try discriminate;
    now apply Pos.eqb_eq.
Qed.
Theorem eval_op_ite_width : forall wc wa wb c x y r,
  eval_op bvite [(wc, c); (wa, x); (wb, y)] = Some r ->
  wc = 1%positive /\ wa = wb.
Proof.
  intros wc wa wb c x y r Hresult.
  apply eval_op_width in Hresult.
  change ((if Pos.eqb wc 1 && Pos.eqb wa wb then Some wa else None) =
    Some (fst r)) in Hresult.
  destruct (Pos.eqb wc 1 && Pos.eqb wa wb) eqn:Hwidth; [|discriminate].
  apply andb_true_iff in Hwidth as [Hcondition Hbranches].
  split; now apply Pos.eqb_eq.
Qed.

(** A successful width check implies the operator's arity. *)
(** A successful width check implies the operator's arity. *)
Theorem result_width_arity : forall o ws w,
  result_width o ws = Some w -> length ws = arity o.
Proof.
  intros o ws w. op_cases o; destruct ws as [|a [|b [|c [|d rest]]]];
    cbn [result_width arity]; try discriminate;
    repeat match goal with
    | |- (if ?test then _ else _) = _ -> _ => destruct test; try discriminate
    end; intros; reflexivity.
Qed.
Theorem eval_op_arity : forall o xs r, eval_op o xs = Some r -> length xs = arity o.
Proof.
  intros o xs r Hresult. apply eval_op_width in Hresult.
  apply result_width_arity in Hresult. now rewrite length_map in Hresult.
Qed.

(** Every successful result is an unsigned word. *)
Theorem eval_op_is_word : forall o xs r,
  eval_op o xs = Some r -> is_word (fst r) (snd r).
Proof.
  intros o xs r. unfold eval_op. destruct (result_width o (map fst xs));
    intro Hresult; [inversion Hresult; apply wrap_is_word|discriminate].
Qed.

(** Normalization is idempotent. *)
Theorem normalize_word_idempotent : forall x,
  normalize_word (normalize_word x) = normalize_word x.
Proof.
  intros [w x]. unfold normalize_word. cbn. now rewrite wrap_wrap.
Qed.

(** Normalization fixes every input that already satisfies the unsigned word range. *)
Theorem normalize_word_id : forall x,
  is_word (fst x) (snd x) -> normalize_word x = x.
Proof.
  intros [w x] Hword. unfold normalize_word. cbn.
  now rewrite (wrap_id w x Hword).
Qed.

(** Pre-normalizing operands leaves evaluation unchanged. *)
Theorem eval_op_normalised : forall o xs,
  eval_op o xs = eval_op o (map (fun x => (fst x, wrap (fst x) (snd x))) xs).
Proof.
  intros o xs. change (eval_op o xs = eval_op o (map normalize_word xs)).
  unfold eval_op. rewrite !map_map.
  assert (Hwidths : map (fun x => fst (normalize_word x)) xs = map fst xs).
  { apply map_ext. intros [w x]. reflexivity. }
  rewrite Hwidths. f_equal.
  assert (Hvalues : map (fun x => normalize_word (normalize_word x)) xs =
    map normalize_word xs).
  { apply map_ext. apply normalize_word_idempotent. }
  now rewrite Hvalues.
Qed.

(** Unary selection returns a word at the supplied width. *)
Theorem word_fun1_is_word : forall o t w x,
  word_fun1 o = Some t -> is_word w (eval_unary_tag t w x).
Proof.
  intros o t w x Hf. op_cases o; cbn [word_fun1] in Hf; try discriminate;
    injection Hf as <-; cbn [eval_unary_tag];
    first [apply wnot_is_word|apply wrap_is_word|apply wclz_is_word|
      apply wctz_is_word|apply wpopcnt_is_word].
Qed.

(** Binary selection returns a word at the supplied width. *)
Theorem word_fun2_is_word : forall o t w x y,
  word_fun2 o = Some t -> is_word w (eval_binary_tag t w x y).
Proof.
  intros o t w x y Hf. op_cases o; cbn [word_fun2] in Hf; try discriminate;
    injection Hf as <-; cbn [eval_binary_tag];
    first [apply wrap_is_word|apply wudiv_is_word|apply wurem_is_word|
      apply wsdiv_is_word|apply wsrem_is_word|apply wsmod_is_word|
      apply wand_is_word|apply wor_is_word|apply wxor_is_word|apply wshl_is_word|
      apply wlshr_is_word|apply washr_is_word|
      unfold wrotr, wrotl; apply wrap_is_word|unfold wrotl; apply wrap_is_word].
Qed.
(** Unary selection is insensitive to normalization. *)
Theorem word_fun1_normalised : forall o t w x,
  word_fun1 o = Some t -> eval_unary_tag t w (wrap w x) = eval_unary_tag t w x.
Proof.
  intros o t w x Hf. op_cases o; cbn [word_fun1] in Hf; try discriminate;
    injection Hf as <-; cbn [eval_unary_tag];
    unfold wnot, wneg, wclz, wctz, wpopcnt;
    now rewrite ?wrap_wrap, ?wrap_opp.
Qed.

(** Binary selection is insensitive to normalization. *)
Theorem word_fun2_normalised : forall o t w x y,
  word_fun2 o = Some t ->
  eval_binary_tag t w (wrap w x) (wrap w y) = eval_binary_tag t w x y.
Proof.
  intros o t w x y Hf. op_cases o; cbn [word_fun2] in Hf; try discriminate;
    injection Hf as <-; cbn [eval_binary_tag];
    unfold wadd, wsub, wmul, wsdiv, wsrem, wsmod, wudiv, wurem, wneg,
      wand, wor, wxor, wshl, wlshr, washr, wrotr, wrotl, msb, signed;
    repeat rewrite wrap_wrap;
    try rewrite <- wrap_add; try rewrite <- wrap_sub; try rewrite <- wrap_mul;
    repeat rewrite wrap_opp; try reflexivity.
  unfold wadd, wrap. repeat rewrite Z.add_mod_idemp_r by apply modulus_nonzero.
  reflexivity.
Qed.

(** Comparison selection is insensitive to normalization. *)
Theorem word_cmp_normalised : forall o t w x y,
  word_cmp o = Some t ->
  eval_comparison_tag t w (wrap w x) (wrap w y) = eval_comparison_tag t w x y.
Proof.
  intros o t w x y Hf. op_cases o; cbn [word_cmp] in Hf; try discriminate;
    injection Hf as <-; cbn [eval_comparison_tag];
    unfold wult, wule, wslt, wsle, signed; now rewrite !wrap_wrap.
Qed.
(** Unary dispatch agrees with its selected tag. *)
Theorem eval_op_fun1 : forall o w z t,
  word_fun1 o = Some t -> eval_op o [(w, z)] = Some (w, eval_unary_tag t w z).
Proof.
  intros o w z t Hf.
  pose proof (word_fun1_normalised o t w z Hf) as Hnorm.
  pose proof (word_fun1_is_word o t w z Hf) as Hrange.
  op_cases o; cbn [word_fun1] in Hf; try discriminate; injection Hf as <-;
    cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
      normalize_word map fst snd eval_unary_tag] in *;
    cbn [eval_binary_tag] in Hnorm, Hrange; rewrite Hnorm, wrap_id by exact Hrange; reflexivity.
Qed.

(** Binary dispatch agrees with its selected tag. *)
Theorem eval_op_fun2 : forall o w x y t, word_fun2 o = Some t ->
  eval_op o [(w, x); (w, y)] = Some (w, eval_binary_tag t w x y).
Proof.
  intros o w x y t Hf.
  pose proof (word_fun2_normalised o t w x y Hf) as Hnorm.
  pose proof (word_fun2_is_word o t w x y Hf) as Hrange.
  op_cases o; cbn [word_fun2] in Hf; try discriminate; injection Hf as <-;
    unfold eval_op; cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
      normalize_word map fst snd] in *;
    rewrite ?Pos.eqb_refl; cbn [op_value word_fun1 word_fun2 word_cmp normalize_word map fst snd];
    rewrite Hnorm, wrap_id by exact Hrange; reflexivity.
Qed.

(** Comparison dispatch returns the one-bit Boolean value of its selected tag. *)
Theorem eval_op_cmp : forall o w x y t, word_cmp o = Some t ->
  eval_op o [(w, x); (w, y)] =
    Some (1%positive, if eval_comparison_tag t w x y then 1 else 0).
Proof.
  intros o w x y t Hf.
  pose proof (word_cmp_normalised o t w x y Hf) as Hnorm.
  op_cases o; cbn [word_cmp] in Hf; try discriminate; injection Hf as <-;
    unfold eval_op; cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
      normalize_word map fst snd eval_comparison_tag] in *;
    rewrite ?Pos.eqb_refl; cbn [op_value word_fun1 word_fun2 word_cmp normalize_word map fst snd eval_comparison_tag]; rewrite ?Hnorm;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    end; reflexivity.
Qed.

(** Conditional selection reads its normalized one-bit condition. *)
Theorem eval_op_ite : forall w x y c,
  eval_op bvite [(1%positive, c); (w, x); (w, y)] =
    Some (w, if wrap 1%positive c =? 1 then wrap w x else wrap w y).
Proof.
  intros w x y c. unfold eval_op.
  cbn [result_width map fst]. rewrite Pos.eqb_refl.
  cbn [op_value word_fun1 word_fun2 word_cmp normalize_word map fst snd].
  rewrite Pos.eqb_refl. cbn. destruct (wrap 1%positive c =? 1); now rewrite wrap_wrap.
Qed.

(** Equal constructor-and-parameter codes identify operators. *)
Theorem op_code_injective : forall o1 o2, op_code o1 = op_code o2 -> o1 = o2.
Proof.
  intros o1 o2. op_cases o1; op_cases o2;
    cbn [op_code]; intro Hcode; try discriminate; try congruence.
  injection Hcode as Hhi Hlo.
  apply (f_equal Pos.to_nat) in Hhi. apply (f_equal Pos.to_nat) in Hlo.
  rewrite !SuccNat2Pos.id_succ in Hhi, Hlo. congruence.
Qed.
(** Zero extension normalizes the input before wrapping at the larger width. *)
Theorem eval_op_zext : forall extra w x,
  eval_op (bvzext extra) [(w, x)] =
    Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)).
Proof.
  intros extra w x.
  reflexivity.
Qed.

(** Sign extension uses the signed interpretation of the normalized input. *)
Theorem eval_op_sext : forall extra w x,
  eval_op (bvsext extra) [(w, x)] =
    Some ((w + extra)%positive, wrap (w + extra)%positive (signed w x)).
Proof.
  intros extra w x.
  cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
    op_value  map normalize_word fst snd].
  now rewrite signed_wrap.
Qed.

(** Truncation normalizes the input and rejects targets wider than the input. *)
Theorem eval_op_trunc : forall target w x,
  eval_op (bvtrunc target) [(w, x)] =
    if Pos.leb target w then Some (target, wrap target (wrap w x)) else None.
Proof.
  intros target w x.
  unfold eval_op.
  cbn [result_width op_value word_fun1 word_fun2 word_cmp
    op_value  map normalize_word fst snd].
  destruct (Pos.leb target w); reflexivity.
Qed.

(** Extraction rejects invalid slices and reads the normalized input at the slice offset. *)
Theorem eval_op_extract : forall hi lo w x,
  eval_op (bvextract hi lo) [(w, x)] =
    if (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w))%bool then
      Some (Pos.of_nat (S (hi - lo)),
        wrap (Pos.of_nat (S (hi - lo))) (wrap w x / 2 ^ Z.of_nat lo))
    else None.
Proof.
  intros hi lo w x. unfold eval_op.
  cbn [result_width op_value word_fun1 word_fun2 word_cmp
    op_value  map normalize_word fst snd].
  destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w))%bool; reflexivity.
Qed.

(** Concatenation normalizes both inputs before joining their high and low bits. *)
Theorem eval_op_concat : forall wa wb x y,
  eval_op bvconcat [(wa, x); (wb, y)] =
    Some ((wa + wb)%positive,
      wrap (wa + wb)%positive (wrap wa x * modulus wb + wrap wb y)).
Proof.
  intros wa wb x y.
  reflexivity.
Qed.

(** Zero extension preserves the normalized unsigned value. *)
Theorem eval_zext_value : forall w n x,
  eval_op (bvzext n) [(w, x)] = Some ((w + n)%positive, wrap w x).
Proof.
  intros w n x. cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
    op_value  map normalize_word fst snd].
  rewrite wrap_id; [reflexivity|].
  eapply word_widen; [apply width_add_le|apply wrap_is_word].
Qed.

(** Sign extension wraps the original signed interpretation at the larger width. *)
Theorem eval_sext_value : forall w n x,
  eval_op (bvsext n) [(w, x)] =
    Some ((w + n)%positive, wrap (w + n)%positive (signed w x)).
Proof.
  intros w n x. cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
    op_value  map normalize_word fst snd].
  now rewrite signed_wrap.
Qed.

(** Truncation keeps the target width's low bits when the target is no wider. *)
Theorem eval_trunc_value : forall w t x, (t <= w)%positive ->
  eval_op (bvtrunc t) [(w, x)] = Some (t, wrap t x).
Proof.
  intros w t x Hle.
  assert (Hwidth : result_width (bvtrunc t) [w] = Some t).
  { change ((if Pos.leb t w then Some t else None) = Some t).
    now rewrite (proj2 (Pos.leb_le t w) Hle). }
  unfold eval_op. change ((match result_width (bvtrunc t) [w] with
    | Some rw => Some (rw, wrap rw (wrap w x))
    | None => None
    end) = Some (t, wrap t x)).
  rewrite Hwidth. now rewrite wrap_narrow by exact Hle.
Qed.

(** Concatenation places the first operand above the second operand's bits. *)
Theorem eval_concat_value : forall w w2 x y,
  eval_op bvconcat [(w, x); (w2, y)] =
    Some ((w + w2)%positive, wrap w x * modulus w2 + wrap w2 y).
Proof.
  intros w w2 x y.
  cbn [eval_op result_width op_value word_fun1 word_fun2 word_cmp
    op_value  map normalize_word fst snd].
  rewrite wrap_id by apply concat_is_word. reflexivity.
Qed.

(** The marked operators evaluate symmetrically on every pair of dynamic words. *)
Theorem commutative_sound : forall o, commutative o = true -> forall a b : word,
  eval_op o [a; b] = eval_op o [b; a].
Proof.
  intros o Hcomm [w x] [w2 y].
  op_cases o by (cbn [commutative] in Hcomm; discriminate).
  all: unfold eval_op;
    cbn [result_width map fst snd]; rewrite (Pos.eqb_sym w2 w);
    destruct (Pos.eqb w w2) eqn:Hwidth; try reflexivity;
    apply Pos.eqb_eq in Hwidth; subst w2;
    cbn [op_value word_fun1 word_fun2 word_cmp eval_binary_tag eval_comparison_tag
      normalize_word map fst snd];
    repeat rewrite wrap_wrap;
    first [now rewrite wadd_comm|now rewrite wmul_comm|now rewrite wand_comm|
      now rewrite wor_comm|now rewrite wxor_comm|now rewrite (Z.eqb_sym (wrap w y))].
Qed.

Module Desc.
  Inductive kind_tag := Bitwise | Additive | Multiplicative | Division | Shift | Rotate |
    Count | Compare | Select | Resize.
  Definition wf (arity : nat) (check : list width -> option width) : Prop :=
    forall ws w, check ws = Some w -> length ws = arity.
  Definition word_valued (check : list width -> option width) (value : list word -> Z) : Prop :=
    forall xs w, Forall (fun x => is_word (fst x) (snd x)) xs ->
      check (map fst xs) = Some w -> is_word w (value xs).
End Desc.

Definition unary_width (ws : list width) := match ws with [w] => Some w | _ => None end.
Definition binary_width (ws : list width) :=
  match ws with [a; b] => if Pos.eqb a b then Some a else None | _ => None end.
Definition compare_width (ws : list width) :=
  match ws with [a; b] => if Pos.eqb a b then Some 1%positive else None | _ => None end.
Definition select_width (ws : list width) :=
  match ws with [c; a; b] => if Pos.eqb c 1 && Pos.eqb a b then Some a else None | _ => None end.
Definition resize_width (check : width -> option width) (ws : list width) :=
  match ws with [w] => check w | _ => None end.
Definition concat_width (ws : list width) := match ws with [a; b] => Some (a + b)%positive | _ => None end.
Definition unary_value (f : width -> Z -> Z) (xs : list word) :=
  match xs with [(w, x)] => f w x | _ => 0 end.
Definition binary_value (f : width -> Z -> Z -> Z) (xs : list word) :=
  match xs with [(w, x); (_, y)] => f w x y | _ => 0 end.
Definition compare_value (f : width -> Z -> Z -> bool) (xs : list word) :=
  match xs with [(w, x); (_, y)] => if f w x y then 1 else 0 | _ => 0 end.
Definition select_value (xs : list word) :=
  match xs with [(_, c); (_, x); (_, y)] => if c =? 1 then x else y | _ => 0 end.
Definition concat_value (xs : list word) :=
  match xs with [(_, x); (w, y)] => x * modulus w + y | _ => 0 end.

(** A unary width check accepts one operand. *)
Theorem unary_wf : forall (_ : Desc.kind_tag) (_ : nat) (_ : width -> Z -> Z),
  Desc.wf 1 unary_width.
Proof. intros. unfold Desc.wf. intros ws w Hwidth. destruct ws as [|a [|b rest]]; cbn in *; congruence. Qed.
(** A binary width check accepts two operands. *)
Theorem binary_wf : forall (_ : Desc.kind_tag) (_ : nat) (_ : bool)
    (_ : width -> Z -> Z -> Z), Desc.wf 2 binary_width.
Proof.
  intros. unfold Desc.wf. intros ws w Hwidth. destruct ws as [|a [|b [|c rest]]]; cbn in *; try discriminate.
  destruct (Pos.eqb a b); congruence.
Qed.
(** A comparison width check accepts two operands. *)
Theorem compare_wf : forall (_ : nat) (_ : bool) (_ : width -> Z -> Z -> bool),
  Desc.wf 2 compare_width.
Proof.
  intros. unfold Desc.wf. intros ws w Hwidth. destruct ws as [|a [|b [|c rest]]]; cbn in *; try discriminate.
  destruct (Pos.eqb a b); congruence.
Qed.
(** A selection width check accepts three operands. *)
Theorem select_wf : forall (_ : nat), Desc.wf 3 select_width.
Proof.
  intros. unfold Desc.wf. intros ws w Hwidth. destruct ws as [|a [|b [|c [|d rest]]]]; cbn in *; try discriminate.
  destruct (Pos.eqb a 1 && Pos.eqb b c); congruence.
Qed.
(** A resize width check accepts one operand. *)
Theorem resize_wf : forall (_ : nat) (_ : positive * positive) check
    (_ : width -> Z -> Z), Desc.wf 1 (resize_width check).
Proof. intros. unfold Desc.wf. intros ws w Hwidth. destruct ws as [|a [|b rest]]; cbn in *; congruence. Qed.
(** A concatenation width check accepts two operands. *)
Theorem concat_wf : forall (_ : nat), Desc.wf 2 concat_width.
Proof. intros. unfold Desc.wf. intros ws w Hwidth. destruct ws as [|a [|b [|c rest]]]; cbn in *; congruence. Qed.

(** A unary word-valued function gives a word-valued unary helper. *)
Theorem unary_word_valued : forall (_ : Desc.kind_tag) (_ : nat) f,
  (forall w x, is_word w (f w x)) -> Desc.word_valued unary_width (unary_value f).
Proof.
  intros k n f Hf xs w Hwords Hwidth.
  destruct xs as [|[a x] [|b rest]]; cbn [unary_width map fst] in Hwidth; try discriminate.
  inversion Hwidth; subst. apply Hf.
Qed.
(** A binary word-valued function gives a word-valued binary helper. *)
Theorem binary_word_valued : forall (_ : Desc.kind_tag) (_ : nat) (_ : bool) f,
  (forall w x y, is_word w (f w x y)) -> Desc.word_valued binary_width (binary_value f).
Proof.
  intros k n c f Hf xs w Hwords Hwidth.
  destruct xs as [|[a x] [|[b y] [|d rest]]]; cbn [binary_width map fst] in Hwidth;
    try discriminate.
  destruct (Pos.eqb a b); inversion Hwidth; subst. apply Hf.
Qed.
(** Comparisons give one-bit words. *)
Theorem compare_word_valued : forall (_ : nat) (_ : bool) f,
  Desc.word_valued compare_width (compare_value f).
Proof.
  intros n c f xs w Hwords Hwidth.
  destruct xs as [|[a x] [|[b y] [|d rest]]]; cbn [compare_width map fst] in Hwidth;
    try discriminate.
  destruct (Pos.eqb a b); inversion Hwidth; subst.
  cbn [compare_value]. destruct (f a x y); [apply one_is_word|apply zero_is_word].
Qed.
(** Selection returns a normalized branch. *)
Theorem select_word_valued : forall (_ : nat), Desc.word_valued select_width select_value.
Proof.
  intros n xs w Hwords Hwidth.
  destruct xs as [|[c z] [|[a x] [|[b y] [|d rest]]]];
    cbn [select_width map fst] in Hwidth; try discriminate.
  destruct (Pos.eqb c 1 && Pos.eqb a b) eqn:Hcheck; inversion Hwidth; subst w.
  apply andb_true_iff in Hcheck as [_ Hab]. apply Pos.eqb_eq in Hab. subst b.
  inversion Hwords as [|? ? Hc Htail]; subst.
  inversion Htail as [|? ? Hx Hlast]; subst.
  inversion Hlast as [|? ? Hy Hnil]; subst.
  cbn [select_value]. destruct (z =? 1); assumption.
Qed.
(** Resizing is word-valued when its callback respects the accepted width. *)
Theorem resize_word_valued : forall (_ : nat) (_ : positive * positive) check f,
  (forall w t x, is_word w x -> check w = Some t -> is_word t (f w x)) ->
  Desc.word_valued (resize_width check) (unary_value f).
Proof.
  intros n p check f Hf xs w Hwords Hwidth.
  destruct xs as [|[a x] [|b rest]]; cbn [resize_width map fst] in Hwidth; try discriminate.
  inversion Hwords as [|? ? Hx Hnil]; subst. now apply (Hf a w x).
Qed.
(** Concatenation of normalized operands gives a normalized result. *)
Theorem concat_word_valued : forall (_ : nat), Desc.word_valued concat_width concat_value.
Proof.
  intros n xs w Hwords Hwidth.
  destruct xs as [|[a x] [|[b y] [|d rest]]]; cbn [concat_width map fst] in Hwidth;
    try discriminate.
  inversion Hwidth; subst w.
  inversion Hwords as [|? ? Hx Htail]; subst.
  inversion Htail as [|? ? Hy Hnil]; subst.
  cbn [concat_value]. rewrite <- (wrap_id a x Hx), <- (wrap_id b y Hy).
  apply concat_is_word.
Qed.
(** The width check for each operator accepts its declared number of operands. *)
Theorem op_desc_wf : forall o, Desc.wf (arity o) (result_width o).
Proof. intros o ws w. apply result_width_arity. Qed.

Inductive action_shape := UnaryShape | BinaryShape | ComparisonShape | SelectionShape |
  ResizingShape | ConcatenationShape.
Definition shape_arity shape :=
  match shape with
  | UnaryShape | ResizingShape => 1%nat
  | SelectionShape => 3%nat
  | _ => 2%nat
  end.
Definition shape_width shape check (ws : list width) :=
  match shape with
  | UnaryShape => unary_width ws
  | BinaryShape => binary_width ws
  | ComparisonShape => compare_width ws
  | SelectionShape => select_width ws
  | ResizingShape => resize_width check ws
  | ConcatenationShape => concat_width ws
  end.
(** Every action shape has a width check that accepts its declared arity. *)
Theorem desc_wf : forall shape check, Desc.wf (shape_arity shape) (shape_width shape check).
Proof.
  intros shape check. destruct shape; cbn [shape_arity shape_width].
  - exact (unary_wf Desc.Bitwise 0 (fun _ x => x)).
  - exact (binary_wf Desc.Bitwise 0 false (fun _ x _ => x)).
  - exact (compare_wf 0 false (fun _ _ _ => false)).
  - exact (select_wf 0).
  - exact (resize_wf 0 (1%positive, 1%positive) check (fun _ x => x)).
  - exact (concat_wf 0).
Qed.

Module Pos.
  TimeFun Corelib.BinNums.PosDef.Pos.of_succ_nat.
  TimeFun Pos.iter_op.
  TimeFun Pos.to_nat.
  TimeFun Pos.of_nat.
End Pos.

Module Nat.
  TimeFun Nat.sub.
  TimeFun Nat.ltb.
End Nat.

Module Z.
  TimeFun Z.of_nat.
End Z.

TimeFun op_widths.
TimeFun eval_unary_tag.
TimeFun eval_binary_tag.
TimeFun eval_comparison_tag.
TimeFun word_fun1.
TimeFun word_fun2.
TimeFun word_cmp.
TimeFun arity.
TimeFun commutative.
TimeFun result_width.
TimeFun op_value.
TimeFun op_code.
TimeFun normalize_word.
TimeFun eval_op.
TimeFun unary_width.
TimeFun binary_width.
TimeFun compare_width.
TimeFun select_width.
TimeFun resize_width.
TimeFun concat_width.
TimeFun unary_value.
TimeFun binary_value.
TimeFun compare_value.
TimeFun select_value.
TimeFun concat_value.
TimeFun shape_arity.
TimeFun shape_width.
