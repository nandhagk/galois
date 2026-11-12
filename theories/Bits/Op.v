(** * Descriptor-based bitvector operators

    One table chooses each operator's action, classification, code and symmetry flag.
    For example, the binary addition action derives both its arity and equal-width check.
    Builds on: Word, Fun, Testbit, Arith and Base code. *)

From Stdlib Require Import ZArith List Bool Lia.
From Argent Require Import Time.
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

Module Desc.

(** Kinds let clients group operators without repeating the operator table. *)
Inductive kind_tag : Type :=
  | Bitwise
  | Additive
  | Multiplicative
  | Division
  | Shift
  | Rotate
  | Count
  | Compare
  | Select
  | Resize.

(** Actions derive arity, width checking and evaluation from a single shape. *)
Inductive action : Type :=
  | Unary (f : width -> Z -> Z)
  | Binary (f : width -> Z -> Z -> Z)
  | Comparison (f : width -> Z -> Z -> bool)
  | Selection
  | Resizing (check : width -> option width) (f : width -> Z -> Z)
  | Concatenation.

(** A descriptor contains computation and metadata without proof fields. *)
Record t : Type := Make {
  kind : kind_tag;
  run : action;
  commutes : bool;
  code : nat * (positive * positive)
}.

(** The action determines the operand count. *)
Definition arity (d : t) : nat :=
  match run d with
  | Unary _ | Resizing _ _ => 1%nat
  | Selection => 3%nat
  | _ => 2%nat
  end.

(** Width checking rejects malformed shapes before raw evaluation. *)
Definition result_width (d : t) (ws : list width) : option width :=
  match run d, ws with
  | Unary _, [w] => Some w
  | Binary _, [a; b] => if Pos.eqb a b then Some a else None
  | Comparison _, [a; b] => if Pos.eqb a b then Some 1%positive else None
  | Selection, [c; a; b] => if Pos.eqb c 1 && Pos.eqb a b then Some a else None
  | Resizing check _, [w] => check w
  | Concatenation, [a; b] => Some (a + b)%positive
  | _, _ => None
  end.

(** The raw result is meaningful after width checking and before the final wrap. *)
Definition value (d : t) (xs : list word) : Z :=
  match run d, xs with
  | Unary f, [(w, x)] => f w x
  | Binary f, [(w, x); (_, y)] => f w x y
  | Comparison f, [(w, x); (_, y)] => if f w x y then 1 else 0
  | Selection, [(_, c); (_, x); (_, y)] => if c =? 1 then x else y
  | Resizing _ f, [(w, x)] => f w x
  | Concatenation, [(_, x); (w2, y)] => x * modulus w2 + y
  | _, _ => 0
  end.

(** Successful width checking implies the descriptor's arity. *)
Record wf (d : t) : Prop := Wf {
  width_arity : forall ws w, result_width d ws = Some w -> length ws = arity d
}.

(** Raw word-valuedness requires normalized operands and a successful width check. *)
Definition word_valued (d : t) : Prop := forall xs w,
  Forall (fun x => is_word (fst x) (snd x)) xs ->
  result_width d (map fst xs) = Some w -> is_word w (value d xs).

End Desc.

(** A unary helper checks one operand and retains its width. *)
Definition unary k n f : Desc.t :=
  Desc.Make k (Desc.Unary f) false (n, (1%positive, 1%positive)).

(** A binary helper checks two equal-width operands and retains their width. *)
Definition binary k n comm f : Desc.t :=
  Desc.Make k (Desc.Binary f) comm (n, (1%positive, 1%positive)).

(** A comparison helper returns a one-bit boolean word. *)
Definition compare n comm f : Desc.t :=
  Desc.Make Desc.Compare (Desc.Comparison f) comm (n, (1%positive, 1%positive)).

(** Selection checks a one-bit condition and equal branch widths. *)
Definition select n : Desc.t :=
  Desc.Make Desc.Select Desc.Selection false (n, (1%positive, 1%positive)).

(** Resizing uses the supplied width check and raw integer conversion. *)
Definition resize n params check f : Desc.t :=
  Desc.Make Desc.Resize (Desc.Resizing check f) false (n, params).

(** Concatenation accepts independently sized operands. *)
Definition concat n : Desc.t :=
  Desc.Make Desc.Resize Desc.Concatenation false (n, (1%positive, 1%positive)).

(** This is the sole operator dispatch table for computation and metadata. *)
Definition op_desc (o : op) : Desc.t :=
  match o with
  | bvnot => unary Desc.Bitwise 0 wnot
  | bvneg => unary Desc.Additive 1 wneg
  | bvclz => unary Desc.Count 2 wclz
  | bvctz => unary Desc.Count 3 wctz
  | bvpopcnt => unary Desc.Count 4 wpopcnt
  | bvadd => binary Desc.Additive 5 true wadd
  | bvsub => binary Desc.Additive 6 false wsub
  | bvmul => binary Desc.Multiplicative 7 true wmul
  | bvudiv => binary Desc.Division 8 false wudiv
  | bvurem => binary Desc.Division 9 false wurem
  | bvsdiv => binary Desc.Division 10 false wsdiv
  | bvsrem => binary Desc.Division 11 false wsrem
  | bvsmod => binary Desc.Division 12 false wsmod
  | bvand => binary Desc.Bitwise 13 true wand
  | bvor => binary Desc.Bitwise 14 true wor
  | bvxor => binary Desc.Bitwise 15 true wxor
  | bvshl => binary Desc.Shift 16 false wshl
  | bvlshr => binary Desc.Shift 17 false wlshr
  | bvashr => binary Desc.Shift 18 false washr
  | bvrotl => binary Desc.Rotate 19 false wrotl
  | bvrotr => binary Desc.Rotate 20 false wrotr
  | bveq => compare 21 true (fun w x y => wrap w x =? wrap w y)
  | bvne => compare 22 true (fun w x y => negb (wrap w x =? wrap w y))
  | bvult => compare 23 false wult
  | bvule => compare 24 false wule
  | bvslt => compare 25 false wslt
  | bvsle => compare 26 false wsle
  | bvite => select 27
  | bvzext n => resize 28 (n, 1%positive) (fun w => Some (w + n)%positive) (fun _ x => x)
  | bvsext n => resize 29 (n, 1%positive) (fun w => Some (w + n)%positive) signed
  | bvtrunc t => resize 30 (t, 1%positive)
      (fun w => if Pos.leb t w then Some t else None) (fun _ x => x)
  | bvextract hi lo => resize 31 (Pos.of_succ_nat hi, Pos.of_succ_nat lo)
      (fun w => if (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w))%bool
        then Some (Pos.of_nat (S (hi - lo))) else None)
      (fun _ x => x / 2 ^ Z.of_nat lo)
  | bvconcat => concat 32
  end.

(** Arity is the descriptor's operand count. *)
Definition arity o := Desc.arity (op_desc o).

(** Commutativity is the descriptor's symmetry flag. *)
Definition commutative o := Desc.commutes (op_desc o).

(** Result widths are checked by the descriptor. *)
Definition result_width o := Desc.result_width (op_desc o).

(** Codes retain the legacy constructor tags and parameter representation. *)
Definition op_code o := Desc.code (op_desc o).

(** Normalization wraps a dynamic word without changing its width. *)
Definition normalize_word (x : word) : word := (fst x, wrap (fst x) (snd x)).

(** Raw operator evaluation is the descriptor's value operation. *)
Definition op_value o := Desc.value (op_desc o).

(** Unary dispatch is recovered from the descriptor action. *)
Definition word_fun1 o : option (width -> Z -> Z) :=
  match Desc.run (op_desc o) with
  | Desc.Unary f => Some f
  | _ => None
  end.

(** Same-width binary dispatch is recovered from the descriptor action. *)
Definition word_fun2 o : option (width -> Z -> Z -> Z) :=
  match Desc.run (op_desc o) with
  | Desc.Binary f => Some f
  | _ => None
  end.

(** Boolean comparison dispatch is recovered from the descriptor action. *)
Definition word_cmp o : option (width -> Z -> Z -> bool) :=
  match Desc.run (op_desc o) with
  | Desc.Comparison f => Some f
  | _ => None
  end.

(** Evaluation wraps normalized operands' raw result at the checked width. *)
Definition eval_op (o : op) (xs : list word) : option word :=
  match result_width o (map fst xs) with
  | Some rw => Some (rw, wrap rw (op_value o (map normalize_word xs)))
  | None => None
  end.

(** Every action derives its arity consistently with its width checker. *)
Theorem desc_wf : forall d, Desc.wf d.
Proof.
  intros [k a comm code]. constructor.
  destruct a; intros ws w; destruct ws as [|a [|b [|c [|d rest]]]];
    cbn [Desc.result_width Desc.run Desc.arity]; try discriminate; intro Hwidth;
    repeat match type of Hwidth with
    | (if ?test then _ else _) = _ => destruct test; try discriminate
    end; reflexivity.
Qed.

(** Unary descriptors have a consistent arity. *)
Theorem unary_wf : forall k n f, Desc.wf (unary k n f).
Proof.
  intros. apply desc_wf.
Qed.

(** Binary descriptors have a consistent arity. *)
Theorem binary_wf : forall k n c f, Desc.wf (binary k n c f).
Proof.
  intros. apply desc_wf.
Qed.

(** Comparison descriptors have a consistent arity. *)
Theorem compare_wf : forall n c f, Desc.wf (compare n c f).
Proof.
  intros. apply desc_wf.
Qed.

(** Selection descriptors have a consistent arity. *)
Theorem select_wf : forall n, Desc.wf (select n).
Proof.
  intros. apply desc_wf.
Qed.

(** Resizing descriptors have a consistent arity for arbitrary width checks. *)
Theorem resize_wf : forall n p check f, Desc.wf (resize n p check f).
Proof.
  intros. apply desc_wf.
Qed.

(** Concatenation descriptors have a consistent arity. *)
Theorem concat_wf : forall n, Desc.wf (concat n).
Proof.
  intros. apply desc_wf.
Qed.

(** Unary word-valued functions produce word-valued descriptors. *)
Theorem unary_word_valued : forall k n f,
  (forall w x, is_word w (f w x)) -> Desc.word_valued (unary k n f).
Proof.
  intros k n f Hf xs w Hwords Hwidth.
  destruct xs as [|[a x] [|b rest]]; cbn in Hwidth; try discriminate.
  inversion Hwidth; subst. apply Hf.
Qed.

(** Binary word-valued functions produce word-valued descriptors. *)
Theorem binary_word_valued : forall k n c f,
  (forall w x y, is_word w (f w x y)) -> Desc.word_valued (binary k n c f).
Proof.
  intros k n c f Hf xs w Hwords Hwidth.
  destruct xs as [|[a x] [|[b y] [|d rest]]]; cbn in Hwidth; try discriminate.
  destruct (Pos.eqb a b); inversion Hwidth; subst. apply Hf.
Qed.

(** Comparisons always produce a one-bit word. *)
Theorem compare_word_valued : forall n c f, Desc.word_valued (compare n c f).
Proof.
  intros n c f xs w Hwords Hwidth.
  destruct xs as [|[a x] [|[b y] [|d rest]]]; cbn in Hwidth; try discriminate.
  destruct (Pos.eqb a b); inversion Hwidth; subst.
  cbn [Desc.value compare Desc.run]. destruct (f a x y);
    [apply one_is_word|apply zero_is_word].
Qed.

(** Selection returns one of its normalized branch words. *)
Theorem select_word_valued : forall n, Desc.word_valued (select n).
Proof.
  intros n xs w Hwords Hwidth.
  destruct xs as [|[c z] [|[a x] [|[b y] [|d rest]]]];
    cbn in Hwidth; try discriminate.
  change ((if Pos.eqb c 1 && Pos.eqb a b then Some a else None) = Some w) in Hwidth.
  destruct (Pos.eqb c 1 && Pos.eqb a b) eqn:Hcheck; inversion Hwidth; subst w.
  apply andb_true_iff in Hcheck as [_ Hab]. apply Pos.eqb_eq in Hab. subst b.
  inversion Hwords as [|? ? Hc Htail]; subst.
  inversion Htail as [|? ? Hx Hlast]; subst.
  inversion Hlast as [|? ? Hy Hnil]; subst.
  cbn [Desc.value select Desc.run]. destruct (z =? 1); assumption.
Qed.

(** Resizing is raw word-valued when its conversion fits each accepted result width. *)
Theorem resize_word_valued : forall n p check f,
  (forall w t x, is_word w x -> check w = Some t -> is_word t (f w x)) ->
  Desc.word_valued (resize n p check f).
Proof.
  intros n p check f Hf xs w Hwords Hwidth.
  destruct xs as [|[a x] [|b rest]]; cbn in Hwidth; try discriminate.
  inversion Hwords as [|? ? Hx Hnil]; subst.
  now apply (Hf a w x).
Qed.

(** Concatenating normalized operands is raw word-valued. *)
Theorem concat_word_valued : forall n, Desc.word_valued (concat n).
Proof.
  intros n xs w Hwords Hwidth.
  destruct xs as [|[a x] [|[b y] [|d rest]]]; cbn in Hwidth; try discriminate.
  inversion Hwidth; subst w.
  inversion Hwords as [|? ? Hx Htail]; subst.
  inversion Htail as [|? ? Hy Hnil]; subst.
  cbn [Desc.value concat Desc.run].
  rewrite <- (wrap_id a x Hx), <- (wrap_id b y Hy). apply concat_is_word.
Qed.

(** Every table entry has width checks consistent with its arity. *)
Theorem op_desc_wf : forall o, Desc.wf (op_desc o).
Proof.
  intro o. op_cases o by apply desc_wf.
Qed.

(** Evaluation fails exactly when width checking fails. *)
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
Theorem eval_op_fun2_width : forall o f wa wb x y r,
  word_fun2 o = Some f -> eval_op o [(wa, x); (wb, y)] = Some r -> wa = wb.
Proof.
  intros o f wa wb x y r Hfun Hresult.
  apply eval_op_width in Hresult.
  unfold word_fun2 in Hfun.
  unfold result_width, Desc.result_width in Hresult.
  destruct (Desc.run (op_desc o)); try discriminate.
  cbn [map fst] in Hresult.
  destruct (Pos.eqb wa wb) eqn:Hwidth; [now apply Pos.eqb_eq|discriminate].
Qed.

(** Successful comparison dispatch requires equal operand widths. *)
Theorem eval_op_cmp_width : forall o f wa wb x y r,
  word_cmp o = Some f -> eval_op o [(wa, x); (wb, y)] = Some r -> wa = wb.
Proof.
  intros o f wa wb x y r Hfun Hresult.
  apply eval_op_width in Hresult.
  unfold word_cmp in Hfun.
  unfold result_width, Desc.result_width in Hresult.
  destruct (Desc.run (op_desc o)); try discriminate.
  cbn [map fst] in Hresult.
  destruct (Pos.eqb wa wb) eqn:Hwidth; [now apply Pos.eqb_eq|discriminate].
Qed.

(** Successful selection requires a one-bit condition and equal branch widths. *)
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
Theorem result_width_arity : forall o ws w,
  result_width o ws = Some w -> length ws = arity o.
Proof.
  intros o. apply (Desc.width_arity _ (op_desc_wf o)).
Qed.

(** A successful evaluation has the required operand count. *)
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

(** Unary dispatch functions always return words. *)
Theorem word_fun1_is_word : forall o f w x,
  word_fun1 o = Some f -> is_word w (f w x).
Proof.
  intros o f w x Hf. op_cases o; cbn [word_fun1 op_desc unary binary compare
    select resize concat Desc.run] in Hf; try discriminate; injection Hf as <-;
    first [apply wnot_is_word|apply wrap_is_word|apply wclz_is_word|
      apply wctz_is_word|apply wpopcnt_is_word].
Qed.

(** Binary dispatch functions always return words. *)
Theorem word_fun2_is_word : forall o f w x y,
  word_fun2 o = Some f -> is_word w (f w x y).
Proof.
  intros o f w x y Hf. op_cases o; cbn [word_fun2 op_desc unary binary compare
    select resize concat Desc.run] in Hf; try discriminate; injection Hf as <-;
    first [apply wrap_is_word|apply wudiv_is_word|apply wurem_is_word|
      apply wsdiv_is_word|apply wsrem_is_word|apply wsmod_is_word|
      apply wand_is_word|apply wor_is_word|apply wxor_is_word|apply wshl_is_word|
      apply wlshr_is_word|apply washr_is_word|
      unfold wrotr, wrotl; apply wrap_is_word|unfold wrotl; apply wrap_is_word].
Qed.

(** Unary dispatch is insensitive to operand normalization. *)
Theorem word_fun1_normalised : forall o f w x,
  word_fun1 o = Some f -> f w (wrap w x) = f w x.
Proof.
  intros o f w x Hf. op_cases o; cbn [word_fun1 op_desc unary binary compare
    select resize concat Desc.run] in Hf; try discriminate; injection Hf as <-;
    unfold wnot, wneg, wclz, wctz, wpopcnt;
    now rewrite ?wrap_wrap, ?wrap_opp.
Qed.

(** Binary dispatch is insensitive to operand normalization. *)
Theorem word_fun2_normalised : forall o f w x y,
  word_fun2 o = Some f -> f w (wrap w x) (wrap w y) = f w x y.
Proof.
  intros o f w x y Hf. op_cases o; cbn [word_fun2 op_desc unary binary compare
    select resize concat Desc.run] in Hf; try discriminate; injection Hf as <-;
    unfold wadd, wsub, wmul, wsdiv, wsrem, wsmod, wudiv, wurem, wneg,
      wand, wor, wxor, wshl, wlshr, washr, wrotr, wrotl, msb, signed;
    repeat rewrite wrap_wrap;
    try rewrite <- wrap_add; try rewrite <- wrap_sub; try rewrite <- wrap_mul;
    repeat rewrite wrap_opp; try reflexivity.
  unfold wadd, wrap. repeat rewrite Z.add_mod_idemp_r by apply modulus_nonzero.
  reflexivity.
Qed.

(** Comparison dispatch is insensitive to operand normalization. *)
Theorem word_cmp_normalised : forall o f w x y,
  word_cmp o = Some f -> f w (wrap w x) (wrap w y) = f w x y.
Proof.
  intros o f w x y Hf. op_cases o; cbn [word_cmp op_desc unary binary compare
    select resize concat Desc.run] in Hf; try discriminate; injection Hf as <-;
    unfold wult, wule, wslt, wsle, signed; now rewrite !wrap_wrap.
Qed.

(** Unary dispatch agrees with its public word function. *)
Theorem eval_op_fun1 : forall o w z f,
  word_fun1 o = Some f -> eval_op o [(w, z)] = Some (w, f w z).
Proof.
  intros o w z f Hf.
  pose proof (word_fun1_normalised o f w z Hf) as Hnorm.
  pose proof (word_fun1_is_word o f w z Hf) as Hrange.
  op_cases o; cbn [word_fun1 op_desc unary binary compare select resize concat
    Desc.run] in Hf; try discriminate; injection Hf as <-;
    cbn [eval_op result_width op_value op_desc unary Desc.result_width Desc.value
      Desc.run normalize_word map fst snd];
    rewrite Hnorm, wrap_id by exact Hrange; reflexivity.
Qed.

(** Binary dispatch agrees with its public word function. *)
Theorem eval_op_fun2 : forall o w x y f, word_fun2 o = Some f ->
  eval_op o [(w, x); (w, y)] = Some (w, f w x y).
Proof.
  intros o w x y f Hf.
  pose proof (word_fun2_normalised o f w x y Hf) as Hnorm.
  pose proof (word_fun2_is_word o f w x y Hf) as Hrange.
  op_cases o; cbn [word_fun2 op_desc unary binary compare select resize concat
    Desc.run] in Hf; try discriminate; injection Hf as <-;
    unfold eval_op;
    cbn [result_width op_value op_desc binary Desc.result_width Desc.value
      Desc.run normalize_word map fst snd];
    rewrite ?Pos.eqb_refl;
    rewrite Hnorm, wrap_id by exact Hrange; reflexivity.
Qed.

(** Comparison dispatch represents false and true by one-bit zero and one. *)
Theorem eval_op_cmp : forall o w x y f, word_cmp o = Some f ->
  eval_op o [(w, x); (w, y)] = Some (1%positive, if f w x y then 1 else 0).
Proof.
  intros o w x y f Hf.
  pose proof (word_cmp_normalised o f w x y Hf) as Hnorm.
  op_cases o; cbn [word_cmp op_desc unary binary compare select resize concat
    Desc.run] in Hf; try discriminate; injection Hf as <-;
    unfold eval_op;
    cbn [result_width op_value op_desc compare Desc.result_width Desc.value
      Desc.run normalize_word map fst snd];
    rewrite ?Pos.eqb_refl; rewrite ?Hnorm;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    end; reflexivity.
Qed.

(** Conditional selection reads its one-bit condition after wrapping. *)
Theorem eval_op_ite : forall w x y c,
  eval_op bvite [(1%positive, c); (w, x); (w, y)] =
    Some (w, if wrap 1%positive c =? 1 then wrap w x else wrap w y).
Proof.
  intros w x y c. unfold eval_op.
  cbn [result_width op_value op_desc select Desc.result_width Desc.value
    Desc.run normalize_word map fst snd].
  rewrite Pos.eqb_refl.
  cbn [andb op_value op_desc select Desc.value Desc.run normalize_word map fst snd].
  rewrite Pos.eqb_refl.
  destruct (wrap 1%positive c =? 1); now rewrite wrap_wrap.
Qed.

(** The marked operators evaluate symmetrically on every pair of dynamic words. *)
Theorem commutative_sound : forall o, commutative o = true -> forall a b : word,
  eval_op o [a; b] = eval_op o [b; a].
Proof.
  intros o Hcomm [w x] [w2 y].
  op_cases o by (cbn [commutative op_desc unary binary compare select resize concat
    Desc.commutes] in Hcomm; discriminate).
  all: unfold eval_op;
    cbn [result_width op_desc binary compare Desc.result_width Desc.run map fst snd];
    rewrite (Pos.eqb_sym w2 w);
    destruct (Pos.eqb w w2) eqn:Hwidth; try reflexivity;
    apply Pos.eqb_eq in Hwidth; subst w2;
    cbn [op_value op_desc binary compare Desc.value Desc.run normalize_word map fst snd];
    repeat rewrite wrap_wrap;
    first [now rewrite wadd_comm|now rewrite wmul_comm|now rewrite wand_comm|
      now rewrite wor_comm|now rewrite wxor_comm|now rewrite (Z.eqb_sym (wrap w y))].
Qed.

(** Equal constructor-and-parameter codes identify operators. *)
Theorem op_code_injective : forall o1 o2, op_code o1 = op_code o2 -> o1 = o2.
Proof.
  intros o1 o2.
  op_cases o1; op_cases o2;
    cbn [op_code op_desc unary binary compare select resize concat Desc.code];
    intro Hcode; try discriminate; try congruence.
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
  cbn [eval_op result_width op_desc resize Desc.result_width Desc.run
    op_value Desc.value map normalize_word fst snd].
  now rewrite signed_wrap.
Qed.

(** Truncation normalizes the input and rejects targets wider than the input. *)
Theorem eval_op_trunc : forall target w x,
  eval_op (bvtrunc target) [(w, x)] =
    if Pos.leb target w then Some (target, wrap target (wrap w x)) else None.
Proof.
  intros target w x.
  unfold eval_op.
  cbn [result_width op_desc resize Desc.result_width Desc.run
    op_value Desc.value map normalize_word fst snd].
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
  cbn [result_width op_desc resize Desc.result_width Desc.run
    op_value Desc.value map normalize_word fst snd].
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
  intros w n x. cbn [eval_op result_width op_desc resize Desc.result_width Desc.run
    op_value Desc.value map normalize_word fst snd].
  rewrite wrap_id; [reflexivity|].
  eapply word_widen; [apply width_add_le|apply wrap_is_word].
Qed.

(** Sign extension wraps the original signed interpretation at the larger width. *)
Theorem eval_sext_value : forall w n x,
  eval_op (bvsext n) [(w, x)] =
    Some ((w + n)%positive, wrap (w + n)%positive (signed w x)).
Proof.
  intros w n x. cbn [eval_op result_width op_desc resize Desc.result_width Desc.run
    op_value Desc.value map normalize_word fst snd].
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
  cbn [eval_op result_width op_desc concat Desc.result_width Desc.run
    op_value Desc.value map normalize_word fst snd].
  rewrite wrap_id by apply concat_is_word. reflexivity.
Qed.
