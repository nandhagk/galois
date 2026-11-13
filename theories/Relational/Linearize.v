(** * Numeric linearization

    The language-independent linearizer recognizes variable leaves.
    For example, a leaf becomes one unit coefficient and an unwrapped zero constant.
    Builds on: LinearizeSig. *)

From Stdlib Require Import List NArith ZArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Bits Require Import Word Fun Arith Op.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ZLang BitsLang.
From Galois.Relational Require Import LinForm LinearizeSig.
Import List.ListNotations.

Local Open Scope nat_scope.

Module LinearizeCode (X : KEY_OPS) (L : LANG_OPS) <: LINEARIZE_OPS X L.
  Definition lin_of (e : term L.op X.t) : option (lin X.t * wrapr) :=
    match e with
    | Leaf x => Some (Lin X.t ((x, 1%Z) :: nil) 0%Z, NoWrap)
    | Node _ _ => None
    end.
  (* STUB-CODE *)
  Definition atoms_of (_ : L.guard) (_ : list (term L.op X.t)) : list (atom X.t) := nil.
End LinearizeCode.

Module Linearize (X : KEY) (L : LANG) (N : NUM_VIEW L) <: LINEARIZE X L N.
  Include LinearizeCode X L.
  Lemma lin_sound : forall st e c f r,
    eval_term L.eval st e = Some c -> lin_of e = Some (f, r) ->
    N.num c = wrap_into r (eval_lin (fun x => N.num (st x)) f).
  Proof.
    intros st [x | o es] c f r Heval Hlin; cbn [lin_of] in Hlin.
    - inversion Hlin; subst f r. cbn [eval_term] in Heval.
      inversion Heval; subst c.
      change (N.num (st x) = (1 * N.num (st x) + 0 + 0)%Z). ring.
    - discriminate.
  Qed.
  Lemma atoms_sound : forall g es st cs,
    eval_terms L.eval st es = Some cs -> L.holds g cs ->
    Forall (atom_holds (fun x => N.num (st x))) (atoms_of g es).
  Proof. Admitted. (* STUB *)
End Linearize.

Module LinearizeT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L) <: LINEARIZE_ALL X L N.
  Include Linearize X L N.
  Definition bits_e (e : term L.op X.t) : nat :=
    match e with
    | Leaf x => X.bits x + 1
    | Node _ _ => 0
    end.
  (* STUB-CODE *)
  Definition bits_es (_ : L.guard) (_ : list (term L.op X.t)) : nat := 0.
  TimeFun lin_of.
  TimeFun atoms_of.
  Definition form_bits (f : lin X.t) : nat :=
    fold_right Nat.max (Z.size_nat (cst f))
      (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) (coef f)).
  Definition wrap_bits (r : wrapr) : nat :=
    match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end.
  (** Recognized forms fit the charged term size and bit size. *)
  Lemma lin_of_size : forall e f r, lin_of e = Some (f, r) ->
    length (coef f) <= tsize e /\ form_bits f + wrap_bits r <= bits_e e.
  Proof.
    intros [x | o es] f r Hlin; cbn [lin_of] in Hlin.
    - inversion Hlin; subst f r.
      change (1 <= 1 /\ Nat.max (X.bits x + 1) 0 + 0 <= X.bits x + 1)%nat.
      rewrite Nat.max_0_r. split; lia.
    - discriminate.
  Qed.
  (** Emitted atoms fit the charged operand sizes and bit size. *)
  Lemma atoms_of_size : forall g es,
    length (atoms_of g es) <= 2 * fold_right Nat.add 1 (map tsize es) /\
    Forall (fun a =>
      length (coef (al a)) + length (coef (ar a)) <= fold_right Nat.add 0 (map tsize es) /\
      form_bits (al a) + wrap_bits (alw a) + form_bits (ar a) + wrap_bits (arw a) <=
        bits_es g es) (atoms_of g es).
  Proof. Admitted. (* STUB *)
  Definition c_linearize : N := 1. (* STUB *)
  Lemma T_lin_of_le : forall e,
    (T_lin_of e <= c_linearize * N.of_nat ((tsize e)%nat) * N.of_nat ((bits_e e + 1)%nat))%N.
  Proof.
    intro e.
    assert (Hsize : (1 <= tsize e)%nat) by (destruct e; cbn [tsize]; lia).
    assert (Hbits : (1 <= bits_e e + 1)%nat) by lia.
    assert (HsizeN : (1 <= N.of_nat (tsize e))%N) by lia.
    assert (HbitsN : (1 <= N.of_nat (bits_e e + 1))%N) by lia.
    unfold c_linearize. time_step; nia.
  Qed.
  Lemma T_atoms_of_le : forall g es,
    (T_atoms_of g es <= c_linearize * N.of_nat ((fold_right Nat.add 0 (map tsize es) + 1)%nat) *
      N.of_nat ((bits_es g es + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma wrap_into_id : forall lo hi z, (lo <= z <= hi)%Z ->
    wrap_into (WrapTo lo hi) z = z.
  Proof.
    intros lo hi z Hbounds. unfold wrap_into.
    rewrite Z.mod_small by lia. lia.
  Qed.
End LinearizeT.

(** * Integer affine forms *)

(** A variable contributes one coefficient and no constant. *)
Definition linear_var {X} (x : X) : lin X := Lin X [(x, 1%Z)] 0%Z.

TimeFun linear_var.

(** A constant has no variable coefficients. *)
Definition linear_const {X} (z : Z) : lin X := Lin X [] z.

TimeFun linear_const.

(** Addition preserves coefficient occurrences in operand order. *)
Definition linear_add {X} (f g : lin X) : lin X :=
  Lin X (coef f ++ coef g) (cst f + cst g)%Z.

TimeFun linear_add.

(** Scaling multiplies every stored coefficient and the constant. *)
Definition linear_scale {X} (a : Z) (f : lin X) : lin X :=
  Lin X (map (fun p => (fst p, (a * snd p)%Z)) (coef f)) (a * cst f)%Z.

TimeFun linear_scale.

(** Subtraction adds the negated right form. *)
Definition linear_sub {X} (f g : lin X) : lin X :=
  linear_add f (linear_scale (-1)%Z g).

TimeFun linear_sub.

(** A product is affine when one recognized form has no variable coefficients. *)
Definition linear_mul {X} (f g : lin X) : option (lin X) :=
  match coef f, coef g with
  | [], _ => Some (linear_scale (cst f) g)
  | _, [] => Some (linear_scale (cst g) f)
  | _, _ => None
  end.

TimeFun linear_mul.

(** Concatenation adds the values of both coefficient lists. *)
Lemma eval_coef_app : forall X (v : X -> Z) xs ys,
  eval_coef v (xs ++ ys) = (eval_coef v xs + eval_coef v ys)%Z.
Proof.
  intros X v xs ys. unfold eval_coef.
  induction xs as [|[x a] xs IH]; cbn [app fold_right fst snd].
  - ring.
  - rewrite IH. ring.
Qed.

(** Coefficient scaling distributes over evaluation. *)
Lemma eval_coef_scale : forall X (v : X -> Z) a xs,
  eval_coef v (map (fun p => (fst p, (a * snd p)%Z)) xs) =
    (a * eval_coef v xs)%Z.
Proof.
  intros X v a xs. unfold eval_coef.
  induction xs as [|[x b] xs IH]; cbn [map fold_right fst snd].
  - ring.
  - rewrite IH. ring.
Qed.

(** Form addition agrees with integer addition. *)
Lemma eval_linear_add : forall X (v : X -> Z) f g,
  eval_lin v (linear_add f g) = (eval_lin v f + eval_lin v g)%Z.
Proof.
  intros X v f g. unfold eval_lin, linear_add. cbn [coef cst].
  rewrite eval_coef_app. ring.
Qed.

(** Form scaling agrees with integer multiplication. *)
Lemma eval_linear_scale : forall X (v : X -> Z) a f,
  eval_lin v (linear_scale a f) = (a * eval_lin v f)%Z.
Proof.
  intros X v a f. unfold eval_lin, linear_scale. cbn [coef cst].
  rewrite eval_coef_scale. ring.
Qed.

(** Form subtraction agrees with integer subtraction. *)
Lemma eval_linear_sub : forall X (v : X -> Z) f g,
  eval_lin v (linear_sub f g) = (eval_lin v f - eval_lin v g)%Z.
Proof.
  intros X v f g. unfold linear_sub.
  rewrite eval_linear_add, eval_linear_scale. ring.
Qed.

(** A form with no coefficients evaluates to its constant. *)
Lemma eval_linear_empty : forall X (v : X -> Z) f,
  coef f = [] -> eval_lin v f = cst f.
Proof.
  intros X v f Hcoef. unfold eval_lin. rewrite Hcoef.
  cbn [eval_coef fold_right]. ring.
Qed.

(** Viewed integer operators recognize affine arithmetic at their exact arity. *)
Definition zlinear_op {X} (o : zview) (fs : list (lin X)) : option (lin X) :=
  match o, fs with
  | ZConst z, [] => Some (linear_const z)
  | ZAdd, [f; g] => Some (linear_add f g)
  | ZSub, [f; g] => Some (linear_sub f g)
  | ZMul, [f; g] => linear_mul f g
  | _, _ => None
  end.

TimeFun zlinear_op.

(** Integer linearization recursively recognizes every affine operand. *)
Fixpoint zlinear_form {X} (e : term zview X) : option (lin X) :=
  match e with
  | Leaf x => Some (linear_var x)
  | Node o es =>
    match sequence (map zlinear_form es) with
    | Some fs => zlinear_op o fs
    | None => None
    end
  end.

TimeFun zlinear_form.

(** Every recognized integer operator preserves its operands' linear interpretation. *)
Lemma zlinear_op_sound : forall X (v : X -> Z) o fs f c,
  zlinear_op o fs = Some f ->
  zview_eval o (map (eval_lin v) fs) = Some c -> c = eval_lin v f.
Proof.
  intros X v o fs f c Hlin Heval.
  destruct o; destruct fs as [|f1 [|f2 [|f3 fs]]];
    cbn [zlinear_op] in Hlin; try discriminate.
  - inversion Hlin; subst f. cbn [zview_eval map] in Heval.
    inversion Heval; subst c. symmetry. apply eval_linear_add.
  - inversion Hlin; subst f. cbn [zview_eval map] in Heval.
    inversion Heval; subst c. symmetry. apply eval_linear_sub.
  - cbn [zview_eval map] in Heval. inversion Heval; subst c.
    unfold linear_mul in Hlin. destruct (coef f1) as [|p ps] eqn:Hleft.
    + inversion Hlin; subst f. rewrite eval_linear_scale.
      rewrite (eval_linear_empty X v f1 Hleft). reflexivity.
    + destruct (coef f2) as [|q qs] eqn:Hright; [|discriminate].
      inversion Hlin; subst f. rewrite eval_linear_scale.
      rewrite (eval_linear_empty X v f2 Hright). ring.
  - inversion Hlin; subst f. cbn [zview_eval map] in Heval.
    inversion Heval; subst c. change (z = (0 + z)%Z). ring.
Qed.

(** Successful integer evaluation agrees with every recognized affine form. *)
Lemma zlinear_form_sound : forall X (e : term zview X) st c f,
  eval_term ZLang.eval st e = Some c ->
  zlinear_form e = Some f -> c = eval_lin st f.
Proof.
  intros X e. induction e as [x|o es IH]; intros st c f Heval Hlin.
  - cbn [eval_term] in Heval. cbn [zlinear_form] in Hlin.
    inversion Heval; subst c. inversion Hlin; subst f.
    change (st x = (1 * st x + 0 + 0)%Z). ring.
  - cbn [eval_term] in Heval. cbn [zlinear_form] in Hlin.
    destruct (sequence (map (eval_term ZLang.eval st) es)) as [cs|] eqn:Hcs;
      [|discriminate].
    destruct (sequence (map zlinear_form es)) as [fs|] eqn:Hfs;
      [|discriminate].
    assert (Hvalues : cs = map (eval_lin st) fs).
    { clear Heval Hlin. revert cs fs Hcs Hfs.
      induction IH as [|e He es Hes IHes]; intros cs fs Hcs Hfs.
      - cbn [map sequence] in Hcs, Hfs.
        inversion Hcs; inversion Hfs; reflexivity.
      - cbn [map sequence] in Hcs, Hfs.
        destruct (eval_term ZLang.eval st e) as [v|] eqn:Heval;
          [|discriminate].
        destruct (zlinear_form e) as [g|] eqn:Hform; [|discriminate].
        destruct (sequence (map (eval_term ZLang.eval st) es)) as [vs|] eqn:Hvs;
          [|discriminate].
        destruct (sequence (map zlinear_form es)) as [gs|] eqn:Hgs;
          [|discriminate].
        inversion Hcs; subst cs. inversion Hfs; subst fs. cbn [map]. f_equal.
        + eapply He; eauto.
        + eapply IHes; eauto. }
    subst cs. eapply zlinear_op_sound; eauto.
Qed.

(** Comparison direction is represented by swapping operands for greater-than. *)
Definition comparison_atom {X} (c : comparison) (f g : lin X) : atom X :=
  match c with
  | Eq => Atom X f NoWrap CEq g NoWrap
  | Lt => Atom X f NoWrap CLt g NoWrap
  | Gt => Atom X g NoWrap CLt f NoWrap
  end.

TimeFun comparison_atom.

(** A true comparison entails the corresponding unwrapped atom. *)
Lemma comparison_atom_sound : forall X (v : X -> Z) c f g,
  Z.compare (eval_lin v f) (eval_lin v g) = c ->
  atom_holds v (comparison_atom c f g).
Proof.
  intros X v [| |] f g Hcmp; cbn [comparison_atom atom_holds wrap_into].
  - now apply Z.compare_eq_iff.
  - now apply Z.compare_lt_iff.
  - now apply Z.compare_gt_iff in Hcmp.
Qed.

Module ZNum <: NUM_VIEW ZLang.
  Definition num (z : Z) := z.
End ZNum.

Module ZLinearizeCode (X : KEY_OPS) <: LINEARIZE_OPS X ZLangCode.
  Definition lin_of (e : term ZLangCode.op X.t) : option (lin X.t * wrapr) :=
    option_map (fun f => (f, NoWrap)) (zlinear_form e).

  Definition atoms_of (g : ZLangCode.guard) (es : list (term ZLangCode.op X.t))
      : list (atom X.t) :=
    match es with
    | [e1; e2] =>
      match zlinear_form e1, zlinear_form e2 with
      | Some f1, Some f2 =>
        match g with
        | ZGuardCmp c => [comparison_atom c f1 f2]
        | ZGuardUlt => [comparison_atom Lt f1 f2]
        | ZGuardOther => []
        end
      | _, _ => []
      end
    | _ => []
    end.
End ZLinearizeCode.

Module ZLinearize (X : KEY) <: LINEARIZE X ZLang ZNum.
  Include ZLinearizeCode X.

  (** Integer recognition uses the identity numeric view and never wraps a result. *)
  Lemma lin_sound : forall st e c f r,
    eval_term ZLang.eval st e = Some c -> lin_of e = Some (f, r) ->
    ZNum.num c = wrap_into r (eval_lin (fun x => ZNum.num (st x)) f).
  Proof.
    intros st e c f r Heval Hlin. unfold lin_of in Hlin.
    destruct (zlinear_form e) as [g|] eqn:Hform; [|discriminate].
    inversion Hlin; subst f r. exact (zlinear_form_sound X.t e st c g Heval Hform).
  Qed.

  (** Recognized two-operand guards imply their emitted comparison atoms. *)
  Lemma atoms_sound : forall g es st cs,
    eval_terms ZLang.eval st es = Some cs -> ZLang.holds g cs ->
    Forall (atom_holds (fun x => ZNum.num (st x))) (atoms_of g es).
  Proof.
    intros g [|e1 [|e2 [|e3 es]]] st cs Heval Hholds;
      cbn [atoms_of]; try constructor.
    destruct (zlinear_form e1) as [f1|] eqn:Hform1; [|constructor].
    destruct (zlinear_form e2) as [f2|] eqn:Hform2; [|constructor].
    cbn [eval_terms map sequence] in Heval.
    destruct (eval_term ZLang.eval st e1) as [c1|] eqn:Heval1; [|discriminate].
    destruct (eval_term ZLang.eval st e2) as [c2|] eqn:Heval2; [|discriminate].
    inversion Heval; subst cs.
    pose proof (zlinear_form_sound X.t e1 st c1 f1 Heval1 Hform1) as Hvalue1.
    pose proof (zlinear_form_sound X.t e2 st c2 f2 Heval2 Hform2) as Hvalue2.
    subst c1 c2. destruct g as [c| |]; [constructor|constructor|constructor].
    - apply comparison_atom_sound. exact Hholds.
    - constructor.
    - apply comparison_atom_sound. apply Z.compare_lt_iff.
      exact (proj2 (proj2 Hholds)).
    - constructor.
  Qed.
End ZLinearize.

(** * Word affine forms *)

(** Word affine arithmetic uses the three integer-preserving binary operators. *)
Inductive affine_binary :=
  | AffineAdd
  | AffineSub
  | AffineMul.

Definition affine_zview (a : affine_binary) : zview :=
  match a with
  | AffineAdd => ZAdd
  | AffineSub => ZSub
  | AffineMul => ZMul
  end.

TimeFun affine_zview.

Definition affine_word_op (a : affine_binary) : Op.op :=
  match a with
  | AffineAdd => bvadd
  | AffineSub => bvsub
  | AffineMul => bvmul
  end.

TimeFun affine_word_op.

Definition affine_word_tag (a : affine_binary) : binary_tag :=
  match a with
  | AffineAdd => BAdd
  | AffineSub => BSub
  | AffineMul => BMul
  end.

TimeFun affine_word_tag.

Definition affine_value (a : affine_binary) (x y : Z) : Z :=
  match a with
  | AffineAdd => (x + y)%Z
  | AffineSub => (x - y)%Z
  | AffineMul => (x * y)%Z
  end.

TimeFun affine_value.

Definition word_affine (o : Op.op) : option affine_binary :=
  match o with
  | bvadd => Some AffineAdd
  | bvsub => Some AffineSub
  | bvmul => Some AffineMul
  | _ => None
  end.

TimeFun word_affine.

(** The numeric views normalize raw words before interpreting their sign. *)
Definition word_number (is_signed : bool) (c : word) : Z :=
  if is_signed then signed (fst c) (snd c) else wrap (fst c) (snd c).

TimeFun word_number.

(** Known-width results use the inclusive interval of their numeric view. *)
Definition word_range (is_signed : bool) (w : positive) : wrapr :=
  if is_signed then WrapTo (- half w)%Z (half w - 1)%Z
  else WrapTo 0%Z (modulus w - 1)%Z.

TimeFun word_range.

(** A width from either operand is enough after the concrete equal-width check. *)
Definition known_width (a b : option positive) : option positive :=
  match a with
  | Some w => Some w
  | None => b
  end.

TimeFun known_width.

(** Binary forms need a syntactically known width for their final wrap. *)
Definition blinear_pair {X} (a : affine_binary)
    (f g : lin X * option positive) : option (lin X * option positive) :=
  match known_width (snd f) (snd g), zlinear_op (affine_zview a) [fst f; fst g] with
  | Some w, Some h => Some (h, Some w)
  | _, _ => None
  end.

TimeFun blinear_pair.

(** Constants establish widths and affine binary operators propagate them. *)
Definition blinear_op {X} (o : bop) (fs : list (lin X * option positive))
    : option (lin X * option positive) :=
  match o, fs with
  | BConst w z, [] => Some (linear_const z, Some w)
  | BOp o, [f; g] =>
    match word_affine o with
    | Some a => blinear_pair a f g
    | None => None
    end
  | _, _ => None
  end.

TimeFun blinear_op.

(** The internal form carries a known width separately from its coefficients. *)
Fixpoint blinear_form {X} (e : term bop X) : option (lin X * option positive) :=
  match e with
  | Leaf x => Some (linear_var x, None)
  | Node o es =>
    match sequence (map blinear_form es) with
    | Some fs => blinear_op o fs
    | None => None
    end
  end.

TimeFun blinear_form.

(** An unknown-width leaf is exact, while a known-width form is exact modulo that width. *)
Definition bform_holds {X} (is_signed : bool) (v : X -> Z) (c : word)
    (fw : lin X * option positive) : Prop :=
  match snd fw with
  | None => word_number is_signed c = eval_lin v (fst fw)
  | Some w => fst c = w /\ wrap w (eval_lin v (fst fw)) = wrap w (snd c)
  end.

(** Both numeric views represent the same residue as the raw word. *)
Lemma wrap_word_number : forall is_signed w z,
  wrap w (word_number is_signed (w, z)) = wrap w z.
Proof.
  intros [|] w z; cbn [word_number fst snd].
  - apply wrap_signed.
  - apply wrap_wrap.
Qed.

(** Every internal form agrees with its concrete word modulo the concrete width. *)
Lemma bform_congruent : forall X is_signed (v : X -> Z) c fw,
  bform_holds is_signed v c fw ->
  wrap (fst c) (eval_lin v (fst fw)) = wrap (fst c) (snd c).
Proof.
  intros X is_signed v [w z] [f ow] Hform.
  destruct ow as [q|]; cbn [bform_holds fst snd] in Hform |- *.
  - destruct Hform as [Hwidth Hvalue]. now subst q.
  - rewrite <- Hform. apply wrap_word_number.
Qed.

(** A selected operand width agrees with both equal-width concrete operands. *)
Lemma known_width_sound : forall X is_signed (v : X -> Z) c d f g ow1 ow2 w,
  fst c = fst d -> bform_holds is_signed v c (f, ow1) ->
  bform_holds is_signed v d (g, ow2) -> known_width ow1 ow2 = Some w -> fst c = w.
Proof.
  intros X is_signed v c d f g [w1|] ow2 w Hsame Hleft Hright Hknown.
  - cbn [known_width] in Hknown. inversion Hknown; subst w.
    exact (proj1 Hleft).
  - destruct ow2 as [w2|]; [|discriminate].
    cbn [known_width] in Hknown. inversion Hknown; subst w.
    rewrite Hsame. exact (proj1 Hright).
Qed.

(** Integer dispatch exposes the mathematical arithmetic of an affine binary tag. *)
Lemma affine_zview_eval : forall a x y,
  zview_eval (affine_zview a) [x; y] = Some (affine_value a x y).
Proof.
  intros [| |] x y; reflexivity.
Qed.

(** Word dispatch selects the matching affine arithmetic primitive. *)
Lemma affine_word_dispatch : forall a,
  word_fun2 (affine_word_op a) = Some (affine_word_tag a).
Proof.
  intros [| |]; reflexivity.
Qed.

(** Affine word primitives wrap their corresponding integer result. *)
Lemma affine_word_value : forall a w x y,
  eval_binary_tag (affine_word_tag a) w x y = wrap w (affine_value a x y).
Proof.
  intros [| |] w x y; reflexivity.
Qed.

(** Successful affine word evaluation checks equal widths and returns the wrapped result. *)
Lemma affine_word_eval : forall a wa wb x y c,
  eval_op (affine_word_op a) [(wa, x); (wb, y)] = Some c ->
  wa = wb /\ c = (wa, wrap wa (affine_value a x y)).
Proof.
  intros a wa wb x y c Heval.
  pose proof (eval_op_fun2_width (affine_word_op a) (affine_word_tag a)
    wa wb x y c (affine_word_dispatch a) Heval) as Hwidth. subst wb.
  rewrite (eval_op_fun2 (affine_word_op a) wa x y (affine_word_tag a)
    (affine_word_dispatch a)), affine_word_value in Heval.
  split; [reflexivity|now inversion Heval].
Qed.

(** Recognition identifies the exact word operator selected by an affine tag. *)
Lemma word_affine_sound : forall o a, word_affine o = Some a -> o = affine_word_op a.
Proof.
  intros o a Htag. destruct o; cbn [word_affine] in Htag;
    try discriminate; inversion Htag; reflexivity.
Qed.

(** Modular equivalence is preserved by every affine binary primitive. *)
Lemma wrap_affine_value : forall a w x y u v,
  wrap w x = wrap w u -> wrap w y = wrap w v ->
  wrap w (affine_value a x y) = wrap w (affine_value a u v).
Proof.
  intros [| |] w x y u v Hleft Hright; cbn [affine_value].
  - rewrite (wrap_add w x y), (wrap_add w u v). now rewrite Hleft, Hright.
  - rewrite (wrap_sub w x y), (wrap_sub w u v). now rewrite Hleft, Hright.
  - rewrite (wrap_mul w x y), (wrap_mul w u v). now rewrite Hleft, Hright.
Qed.

(** Combining recognized word forms preserves their modular interpretation. *)
Lemma blinear_pair_sound : forall X is_signed (v : X -> Z) a c1 c2 f1 f2 fr c,
  bform_holds is_signed v c1 f1 -> bform_holds is_signed v c2 f2 ->
  eval_op (affine_word_op a) [c1; c2] = Some c ->
  blinear_pair a f1 f2 = Some fr -> bform_holds is_signed v c fr.
Proof.
  intros X is_signed v a [wa x] [wb y] [f1 ow1] [f2 ow2] fr c Hleft Hright Heval Hlin.
  destruct (affine_word_eval a wa wb x y c Heval) as [Hsame Hresult]. subst wb c.
  unfold blinear_pair in Hlin. cbn [fst snd] in Hlin.
  destruct (known_width ow1 ow2) as [w|] eqn:Hknown; [|discriminate].
  destruct (zlinear_op (affine_zview a) [f1; f2]) as [f|] eqn:Hform;
    [|discriminate].
  inversion Hlin; subst fr.
  pose proof (known_width_sound X is_signed v (wa, x) (wa, y) f1 f2 ow1 ow2 w
    eq_refl Hleft Hright Hknown) as Hwidth. cbn [fst] in Hwidth. subst w.
  cbn [bform_holds fst snd]. split; [reflexivity|]. rewrite wrap_wrap.
  pose proof (zlinear_op_sound X v (affine_zview a) [f1; f2] f
    (affine_value a (eval_lin v f1) (eval_lin v f2)) Hform
    (affine_zview_eval a (eval_lin v f1) (eval_lin v f2))) as Hvalue.
  rewrite <- Hvalue. apply wrap_affine_value.
  - exact (bform_congruent X is_signed v (wa, x) (f1, ow1) Hleft).
  - exact (bform_congruent X is_signed v (wa, y) (f2, ow2) Hright).
Qed.

(** Every recognized word operator preserves the modular meaning of its operands. *)
Lemma blinear_op_sound : forall X is_signed (v : X -> Z) o cs fs fr c,
  Forall2 (bform_holds is_signed v) cs fs ->
  BitsLang.eval o cs = Some c -> blinear_op o fs = Some fr ->
  bform_holds is_signed v c fr.
Proof.
  intros X is_signed v [w z|o] cs fs fr c Hargs Heval Hlin.
  - destruct fs; cbn [blinear_op] in Hlin; [|discriminate].
    inversion Hargs; subst cs. cbn [BitsLang.eval] in Heval.
    inversion Heval; subst c. inversion Hlin; subst fr.
    cbn [bform_holds fst snd]. split; [reflexivity|].
    change (wrap w (0 + z)%Z = wrap w (wrap w z)). rewrite wrap_wrap.
    reflexivity.
  - destruct fs as [|f1 [|f2 [|f3 fs]]]; cbn [blinear_op] in Hlin;
      try discriminate.
    destruct (word_affine o) as [a|] eqn:Htag; [|discriminate].
    inversion Hargs as [|c1 f1' cs1 fs1 Hleft Htail]; subst.
    inversion Htail as [|c2 f2' cs2 fs2 Hright Hnil]; subst.
    inversion Hnil; subst.
    apply word_affine_sound in Htag. subst o.
    change (eval_op (affine_word_op a) [c1; c2] = Some c) in Heval.
    exact (blinear_pair_sound X is_signed v a c1 c2 f1 f2 fr c
      Hleft Hright Heval Hlin).
Qed.

(** The recursive word recognizer agrees with concrete evaluation in either numeric view. *)
Lemma blinear_form_sound : forall X is_signed (e : term bop X) st c fw,
  eval_term BitsLang.eval st e = Some c -> blinear_form e = Some fw ->
  bform_holds is_signed (fun x => word_number is_signed (st x)) c fw.
Proof.
  intros X is_signed e. induction e as [x|o es IH]; intros st c fw Heval Hlin.
  - cbn [eval_term] in Heval. cbn [blinear_form] in Hlin.
    inversion Heval; subst c. inversion Hlin; subst fw.
    change (word_number is_signed (st x) =
      (1 * word_number is_signed (st x) + 0 + 0)%Z). ring.
  - cbn [eval_term] in Heval. cbn [blinear_form] in Hlin.
    destruct (sequence (map (eval_term BitsLang.eval st) es)) as [cs|] eqn:Hcs;
      [|discriminate].
    destruct (sequence (map blinear_form es)) as [fs|] eqn:Hfs;
      [|discriminate].
    assert (Hvalues : Forall2
      (bform_holds is_signed (fun x => word_number is_signed (st x))) cs fs).
    { clear Heval Hlin. revert cs fs Hcs Hfs.
      induction IH as [|e He es Hes IHes]; intros cs fs Hcs Hfs.
      - cbn [map sequence] in Hcs, Hfs.
        inversion Hcs; inversion Hfs; constructor.
      - cbn [map sequence] in Hcs, Hfs.
        destruct (eval_term BitsLang.eval st e) as [v|] eqn:Heval;
          [|discriminate].
        destruct (blinear_form e) as [g|] eqn:Hform; [|discriminate].
        destruct (sequence (map (eval_term BitsLang.eval st) es)) as [vs|] eqn:Hvs;
          [|discriminate].
        destruct (sequence (map blinear_form es)) as [gs|] eqn:Hgs;
          [|discriminate].
        inversion Hcs; subst cs. inversion Hfs; subst fs. constructor.
        + eapply He; eauto.
        + eapply IHes; eauto. }
    eapply blinear_op_sound; eauto.
Qed.

(** Inclusive wrapping into a word range equals its normalized numeric view. *)
Lemma word_range_value : forall is_signed w z,
  wrap_into (word_range is_signed w) z = word_number is_signed (w, z).
Proof.
  intros [|] w z.
  - change ((- half w + (z - - half w) mod (half w - 1 - - half w + 1))%Z =
      signed w z).
    replace (half w - 1 - - half w + 1)%Z with (modulus w)
      by (pose proof (modulus_half w); lia).
    replace (z - - half w)%Z with (z + half w)%Z by ring.
    pose proof (Z.mod_pos_bound (z + half w) (modulus w) (modulus_pos w)) as Hrem.
    pose proof (modulus_half w) as Hmodulus.
    assert (Hrange : (- half w <= - half w + (z + half w) mod modulus w < half w)%Z)
      by lia.
    rewrite <- (signed_id w (- half w + (z + half w) mod modulus w)%Z Hrange).
    assert (Hwrap : wrap w (- half w + (z + half w) mod modulus w)%Z = wrap w z).
    { unfold wrap. rewrite Z.add_mod_idemp_r by apply modulus_nonzero.
      replace (- half w + (z + half w))%Z with z by ring. reflexivity. }
    unfold signed. now rewrite Hwrap.
  - change ((0 + (z - 0) mod (modulus w - 1 - 0 + 1))%Z = wrap w z).
    replace (modulus w - 1 - 0 + 1)%Z with (modulus w) by ring.
    replace (z - 0)%Z with z by ring. reflexivity.
Qed.

(** Equal residues have equal unsigned and signed numeric interpretations. *)
Lemma word_number_congruent : forall is_signed w x y,
  wrap w x = wrap w y -> word_number is_signed (w, x) = word_number is_signed (w, y).
Proof.
  intros [|] w x y Hwrap; cbn [word_number fst snd].
  - unfold signed. now rewrite Hwrap.
  - exact Hwrap.
Qed.

(** Public word forms expose their known-width wrap and leave variable leaves unwrapped. *)
Definition bits_lin_of {X} (is_signed : bool) (e : term bop X)
    : option (lin X * wrapr) :=
  match blinear_form e with
  | Some (f, Some w) => Some (f, word_range is_signed w)
  | Some (f, None) => Some (f, NoWrap)
  | None => None
  end.

TimeFun bits_lin_of.

(** Public word recognition reproduces every successful concrete numeric result. *)
Lemma bits_lin_of_sound : forall X is_signed st (e : term bop X) c f r,
  eval_term BitsLang.eval st e = Some c -> bits_lin_of is_signed e = Some (f, r) ->
  word_number is_signed c =
    wrap_into r (eval_lin (fun x => word_number is_signed (st x)) f).
Proof.
  intros X is_signed st e c f r Heval Hlin. unfold bits_lin_of in Hlin.
  destruct (blinear_form e) as [[g [w|]]|] eqn:Hform; [| |discriminate].
  - inversion Hlin; subst f r.
    pose proof (blinear_form_sound X is_signed e st c (g, Some w) Heval Hform)
      as Hvalue. destruct c as [q z]. destruct Hvalue as [Hwidth Hresidue].
    cbn [fst] in Hwidth. subst q. rewrite word_range_value.
    apply word_number_congruent. symmetry. exact Hresidue.
  - inversion Hlin; subst f r.
    exact (blinear_form_sound X is_signed e st c (g, None) Heval Hform).
Qed.

(** A supported comparison belongs to the numeric view selected by the caller. *)
Definition word_comparison (is_signed : bool) (o : Op.op) : option cmp :=
  match o with
  | bveq => Some LinForm.CEq
  | bvult => if is_signed then None else Some CLt
  | bvule => if is_signed then None else Some CLe
  | bvslt => if is_signed then Some CLt else None
  | bvsle => if is_signed then Some CLe else None
  | _ => None
  end.

TimeFun word_comparison.

Definition comparison_word_op (is_signed : bool) (c : cmp) : Op.op :=
  match c with
  | LinForm.CEq => bveq
  | CLt => if is_signed then bvslt else bvult
  | CLe => if is_signed then bvsle else bvule
  end.

TimeFun comparison_word_op.

Definition comparison_word_tag (is_signed : bool) (c : cmp) : comparison_tag :=
  match c with
  | LinForm.CEq => Op.CEq
  | CLt => if is_signed then CSlt else CUlt
  | CLe => if is_signed then CSle else CUle
  end.

TimeFun comparison_word_tag.

Definition bool_compare (c : cmp) (x y : Z) : bool :=
  match c with
  | CLe => (x <=? y)%Z
  | CLt => (x <? y)%Z
  | LinForm.CEq => (x =? y)%Z
  end.

TimeFun bool_compare.

(** False strict and non-strict comparisons reverse their operands. *)
Definition guard_relation (c : cmp) (truth : bool) : option (cmp * bool) :=
  match c, truth with
  | CLe, true => Some (CLe, false)
  | CLe, false => Some (CLt, true)
  | CLt, true => Some (CLt, false)
  | CLt, false => Some (CLe, true)
  | LinForm.CEq, true => Some (LinForm.CEq, false)
  | LinForm.CEq, false => None
  end.

TimeFun guard_relation.

(** The three affine comparison relations interpret their integer endpoints. *)
Definition cmp_holds (c : cmp) (x y : Z) : Prop :=
  match c with
  | CLe => (x <= y)%Z
  | CLt => (x < y)%Z
  | LinForm.CEq => x = y
  end.

(** Normalized equality is equivalent in the signed and unsigned views. *)
Lemma word_number_eqb : forall is_signed w x y,
  (word_number is_signed (w, x) =? word_number is_signed (w, y))%Z =
    (wrap w x =? wrap w y)%Z.
Proof.
  intros [|] w x y; [|reflexivity].
  change ((signed w x =? signed w y)%Z = (wrap w x =? wrap w y)%Z).
  destruct (signed w x =? signed w y)%Z eqn:Hsigned;
    destruct (wrap w x =? wrap w y)%Z eqn:Hunsigned; try reflexivity.
  - apply Z.eqb_eq in Hsigned. apply Z.eqb_neq in Hunsigned.
    exfalso. apply Hunsigned. now apply signed_inj.
  - apply Z.eqb_neq in Hsigned. apply Z.eqb_eq in Hunsigned.
    exfalso. apply Hsigned. unfold signed. now rewrite Hunsigned.
Qed.

(** Comparison recognition identifies the selected concrete operator. *)
Lemma word_comparison_op : forall is_signed o c,
  word_comparison is_signed o = Some c -> o = comparison_word_op is_signed c.
Proof.
  intros [|] o c Hcmp; destruct o; cbn [word_comparison] in Hcmp;
    try discriminate; inversion Hcmp; reflexivity.
Qed.

(** The selected concrete operator has the intended comparison tag. *)
Lemma comparison_word_dispatch : forall is_signed c,
  word_cmp (comparison_word_op is_signed c) = Some (comparison_word_tag is_signed c).
Proof.
  intros [|] [| |]; reflexivity.
Qed.

(** Concrete comparison agrees with integer comparison in its chosen numeric view. *)
Lemma comparison_word_value : forall is_signed c w x y,
  eval_comparison_tag (comparison_word_tag is_signed c) w x y =
    bool_compare c (word_number is_signed (w, x)) (word_number is_signed (w, y)).
Proof.
  intros [|] [| |] w x y; try reflexivity.
  symmetry. exact (word_number_eqb true w x y).
Qed.

(** A successful comparison returning the guarded bit determines its numeric truth value. *)
Lemma word_comparison_truth : forall is_signed o cmp (truth : bool) c1 c2,
  word_comparison is_signed o = Some cmp ->
  eval_op o [c1; c2] = Some (1%positive, if truth then 1%Z else 0%Z) ->
  bool_compare cmp (word_number is_signed c1) (word_number is_signed c2) = truth.
Proof.
  intros is_signed o cmp truth [wa x] [wb y] Hcmp Heval.
  apply word_comparison_op in Hcmp. subst o.
  pose proof (eval_op_cmp_width (comparison_word_op is_signed cmp)
    (comparison_word_tag is_signed cmp) wa wb x y
    (1%positive, if truth then 1%Z else 0%Z)
    (comparison_word_dispatch is_signed cmp) Heval) as Hwidth. subst wb.
  pose proof (eq_trans (eq_sym (eval_op_cmp (comparison_word_op is_signed cmp) wa x y
    (comparison_word_tag is_signed cmp) (comparison_word_dispatch is_signed cmp))) Heval)
    as Hbits.
  rewrite comparison_word_value in Hbits.
  destruct (bool_compare cmp (word_number is_signed (wa, x))
    (word_number is_signed (wa, y))) eqn:Htruth;
    destruct truth; try reflexivity; discriminate.
Qed.

(** The comparison selected by a Boolean guard is entailed by its truth value. *)
Lemma guard_relation_sound : forall c truth d swap x y,
  guard_relation c truth = Some (d, swap) -> bool_compare c x y = truth ->
  if swap then cmp_holds d y x else cmp_holds d x y.
Proof.
  intros [| |] [|] d swap x y Hrelation Htruth;
    cbn [guard_relation] in Hrelation; try discriminate;
    inversion Hrelation; subst d swap; cbn [bool_compare] in Htruth; cbn [cmp_holds].
  - now apply Z.leb_le.
  - now apply Z.leb_gt in Htruth.
  - now apply Z.ltb_lt.
  - now apply Z.ltb_ge in Htruth.
  - now apply Z.eqb_eq.
Qed.

(** Atom construction preserves each operand's independent wrap. *)
Definition wrapped_atom {X} (c : cmp) (swap : bool)
    (f g : lin X * wrapr) : atom X :=
  if swap then Atom X (fst g) (snd g) c (fst f) (snd f)
  else Atom X (fst f) (snd f) c (fst g) (snd g).

TimeFun wrapped_atom.

(** Integer comparison of wrapped forms entails their constructed atom. *)
Lemma wrapped_atom_sound : forall X (v : X -> Z) c (swap : bool) f g,
  (if swap then
    cmp_holds c (wrap_into (snd g) (eval_lin v (fst g)))
      (wrap_into (snd f) (eval_lin v (fst f)))
  else
    cmp_holds c (wrap_into (snd f) (eval_lin v (fst f)))
      (wrap_into (snd g) (eval_lin v (fst g)))) ->
  atom_holds v (wrapped_atom c swap f g).
Proof.
  intros X v [| |] [|] [f fr] [g gr] Hcompare; exact Hcompare.
Qed.

(** Word truth guards expose comparisons in the matching numeric view. *)
Definition bits_atoms_of {X} (is_signed : bool) (g : bguard) (es : list (term bop X))
    : list (atom X) :=
  match es with
  | [e] =>
    match e, g with
    | Node (BOp o) [e1; e2], BTruth truth =>
      match word_comparison is_signed o with
      | Some c =>
        match guard_relation c truth with
        | Some (d, swap) =>
          match bits_lin_of is_signed e1, bits_lin_of is_signed e2 with
          | Some f1, Some f2 => [wrapped_atom d swap f1 f2]
          | _, _ => []
          end
        | None => []
        end
      | None => []
      end
    | _, _ => []
    end
  | _ => []
  end.

TimeFun bits_atoms_of.

(** Every word atom follows from a successfully evaluated Boolean guard. *)
Lemma bits_atoms_of_sound : forall X is_signed g (es : list (term bop X)) st cs,
  eval_terms BitsLang.eval st es = Some cs -> BitsLang.holds g cs ->
  Forall (atom_holds (fun x => word_number is_signed (st x)))
    (bits_atoms_of is_signed g es).
Proof.
  intros X is_signed [truth] [|e [|e' es]] st cs Heval Hholds;
    try constructor.
  destruct e as [x|o args]; [constructor|].
  destruct o as [w z|o]; [constructor|].
  destruct args as [|e1 [|e2 [|e3 args]]]; try constructor.
  cbn [bits_atoms_of].
  destruct (word_comparison is_signed o) as [c|] eqn:Hcmp; [|constructor].
  destruct (guard_relation c truth) as [[d swap]|] eqn:Hrelation; [|constructor].
  destruct (bits_lin_of is_signed e1) as [[f1 r1]|] eqn:Hform1; [|constructor].
  destruct (bits_lin_of is_signed e2) as [[f2 r2]|] eqn:Hform2; [|constructor].
  cbn [eval_terms eval_term map sequence] in Heval.
  destruct (eval_term BitsLang.eval st e1) as [c1|] eqn:Heval1; [|discriminate].
  destruct (eval_term BitsLang.eval st e2) as [c2|] eqn:Heval2; [|discriminate].
  cbn [BitsLang.eval] in Heval.
  destruct (eval_op o [c1; c2]) as [[wb zb]|] eqn:Hresult; [|discriminate].
  inversion Heval; subst cs.
  change (wb = 1%positive /\ zb = (if truth then 1 else 0)%Z) in Hholds.
  destruct Hholds as [Hwidth Hbit]. subst wb zb.
  pose proof (word_comparison_truth is_signed o c truth c1 c2 Hcmp Hresult) as Htruth.
  pose proof (guard_relation_sound c truth d swap
    (word_number is_signed c1) (word_number is_signed c2) Hrelation Htruth) as Hcompare.
  rewrite (bits_lin_of_sound X is_signed st e1 c1 f1 r1 Heval1 Hform1),
    (bits_lin_of_sound X is_signed st e2 c2 f2 r2 Heval2 Hform2) in Hcompare.
  constructor; [apply wrapped_atom_sound; exact Hcompare|constructor].
Qed.

Module BitsNumU <: NUM_VIEW BitsLang.
  Definition num (c : word) := word_number false c.
End BitsNumU.

Module BitsNumS <: NUM_VIEW BitsLang.
  Definition num (c : word) := word_number true c.
End BitsNumS.

Module BitsLinearizeUCode (X : KEY_OPS) <: LINEARIZE_OPS X BitsLangCode.
  Definition lin_of := @bits_lin_of X.t false.
  Definition atoms_of := @bits_atoms_of X.t false.
End BitsLinearizeUCode.

Module BitsLinearizeSCode (X : KEY_OPS) <: LINEARIZE_OPS X BitsLangCode.
  Definition lin_of := @bits_lin_of X.t true.
  Definition atoms_of := @bits_atoms_of X.t true.
End BitsLinearizeSCode.

Module BitsLinearizeU (X : KEY) <: LINEARIZE X BitsLang BitsNumU.
  Include BitsLinearizeUCode X.

  (** Unsigned forms reproduce normalized concrete word values. *)
  Lemma lin_sound : forall st e c f r,
    eval_term BitsLang.eval st e = Some c -> lin_of e = Some (f, r) ->
    BitsNumU.num c = wrap_into r (eval_lin (fun x => BitsNumU.num (st x)) f).
  Proof.
    exact (bits_lin_of_sound X.t false).
  Qed.

  (** Unsigned comparison atoms follow from their concrete truth guard. *)
  Lemma atoms_sound : forall g es st cs,
    eval_terms BitsLang.eval st es = Some cs -> BitsLang.holds g cs ->
    Forall (atom_holds (fun x => BitsNumU.num (st x))) (atoms_of g es).
  Proof.
    exact (bits_atoms_of_sound X.t false).
  Qed.
End BitsLinearizeU.

Module BitsLinearizeS (X : KEY) <: LINEARIZE X BitsLang BitsNumS.
  Include BitsLinearizeSCode X.

  (** Signed forms reproduce the concrete two's complement interpretation. *)
  Lemma lin_sound : forall st e c f r,
    eval_term BitsLang.eval st e = Some c -> lin_of e = Some (f, r) ->
    BitsNumS.num c = wrap_into r (eval_lin (fun x => BitsNumS.num (st x)) f).
  Proof.
    exact (bits_lin_of_sound X.t true).
  Qed.

  (** Signed comparison atoms follow from their concrete truth guard. *)
  Lemma atoms_sound : forall g es st cs,
    eval_terms BitsLang.eval st es = Some cs -> BitsLang.holds g cs ->
    Forall (atom_holds (fun x => BitsNumS.num (st x))) (atoms_of g es).
  Proof.
    exact (bits_atoms_of_sound X.t true).
  Qed.
End BitsLinearizeS.

(** * Syntactic size envelopes *)

(** Linear-form bits count the largest coefficient/key pair or constant. *)
Definition linear_bits {X} (key_bits : X -> nat) (f : lin X) : nat :=
  fold_right Nat.max (Z.size_nat (cst f))
    (map (fun p => key_bits (fst p) + Z.size_nat (snd p)) (coef f)).

(** Integer literals contribute their raw bit length to a syntax envelope. *)
Definition zoperator_bits (o : zview) : nat :=
  match o with
  | ZConst z => Z.size_nat z
  | _ => 0
  end.

(** Word literals additionally pay for the numeric value of their explicit width. *)
Definition boperator_bits (o : bop) : nat :=
  match o with
  | BConst w z => Pos.to_nat w + Z.size_nat z
  | BOp o => op_widths o
  end.

(** Every syntax node and every explicit key, literal or width contributes to this envelope. *)
Fixpoint term_mass {K X} (key_bits : X -> nat) (operator_bits : K -> nat)
    (e : term K X) : nat :=
  match e with
  | Leaf x => key_bits x + 1
  | Node o es => operator_bits o + 1 +
    fold_right Nat.add 0 (map (term_mass key_bits operator_bits) es)
  end.

(** Positive addition fits within the sum of the operand bit lengths. *)
Lemma positive_bits_add : forall p q,
  Pos.size_nat (p + q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  intros p q. apply Pos.size_nat_least. rewrite Pos2Nat.inj_add, Nat.pow_add_r.
  pose proof (Pos.size_nat_upper p). pose proof (Pos.size_nat_upper q).
  pose proof (Pos2Nat.is_pos p). pose proof (Pos2Nat.is_pos q). nia.
Qed.

(** A signed difference of positive integers has no more bits than its two inputs together. *)
Lemma zbits_pos_sub : forall p q,
  Z.size_nat (Z.pos_sub p q) <= Pos.size_nat p + Pos.size_nat q.
Proof.
  intros p q. rewrite Z.pos_sub_spec. destruct (Pos.compare p q); cbn [Z.size_nat].
  - lia.
  - pose proof (Pos.size_nat_sub q p). lia.
  - pose proof (Pos.size_nat_sub p q). lia.
Qed.

(** Integer addition fits within the sum of the input bit lengths. *)
Lemma zbits_add : forall x y, Z.size_nat (x + y) <= Z.size_nat x + Z.size_nat y.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.add Z.size_nat]; try lia.
  - apply positive_bits_add.
  - apply zbits_pos_sub.
  - pose proof (zbits_pos_sub q p). lia.
  - apply positive_bits_add.
Qed.

(** Integer multiplication adds at most the input bit lengths. *)
Lemma zbits_mul : forall x y, Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y.
Proof.
  intros [|p|p] [|q|q]; cbn [Z.mul Z.size_nat]; try lia; apply Pos.size_nat_mul.
Qed.

(** A form-bit bound is exactly a bound on its constant and every coefficient/key pair. *)
Lemma linear_bits_components : forall X (key_bits : X -> nat) f bound,
  linear_bits key_bits f <= bound <->
  Z.size_nat (cst f) <= bound /\
    Forall (fun p => key_bits (fst p) + Z.size_nat (snd p) <= bound) (coef f).
Proof.
  intros X key_bits [xs z] bound. unfold linear_bits. cbn [coef cst].
  induction xs as [|p xs IH]; cbn [map fold_right].
  - split; intro H; [split; [exact H|constructor]|exact (proj1 H)].
  - rewrite Nat.max_lub_iff, IH, Forall_cons_iff. tauto.
Qed.

(** Adding two forms adds at most their bit envelopes. *)
Lemma linear_bits_add : forall X (key_bits : X -> nat) f g,
  linear_bits key_bits (linear_add f g) <= linear_bits key_bits f + linear_bits key_bits g.
Proof.
  intros X key_bits f g.
  destruct (proj1 (linear_bits_components X key_bits f (linear_bits key_bits f))
    (Nat.le_refl _)) as [Hconstf Hcoeff].
  destruct (proj1 (linear_bits_components X key_bits g (linear_bits key_bits g))
    (Nat.le_refl _)) as [Hconstg Hcoeffg].
  apply (proj2 (linear_bits_components X key_bits (linear_add f g) _)).
  cbn [linear_add coef cst]. split.
  - pose proof (zbits_add (cst f) (cst g)). lia.
  - apply Forall_app. split.
    + eapply Forall_impl; [|exact Hcoeff]. intros p Hbound.
      exact (Nat.le_trans _ _ _ Hbound (Nat.le_add_r _ _)).
    + eapply Forall_impl; [|exact Hcoeffg]. intros p Hbound.
      exact (Nat.le_trans _ _ _ Hbound (Nat.le_add_l _ _)).
Qed.

(** Scaling a form adds the scalar's bit length to its previous envelope. *)
Lemma linear_bits_scale : forall X (key_bits : X -> nat) a f,
  linear_bits key_bits (linear_scale a f) <= Z.size_nat a + linear_bits key_bits f.
Proof.
  intros X key_bits a f.
  destruct (proj1 (linear_bits_components X key_bits f (linear_bits key_bits f))
    (Nat.le_refl _)) as [Hconst Hcoeff].
  apply (proj2 (linear_bits_components X key_bits (linear_scale a f) _)).
  cbn [linear_scale coef cst]. split.
  - pose proof (zbits_mul a (cst f)). lia.
  - induction Hcoeff as [|[x b] xs Hhead Htail IH]; cbn [map]; constructor.
    + cbn [fst snd] in Hhead |- *. pose proof (zbits_mul a b). lia.
    + exact IH.
Qed.

(** Subtraction needs at most one extra bit for its negative scalar. *)
Lemma linear_bits_sub : forall X (key_bits : X -> nat) f g,
  linear_bits key_bits (linear_sub f g) <=
    linear_bits key_bits f + linear_bits key_bits g + 1.
Proof.
  intros X key_bits f g. unfold linear_sub.
  eapply Nat.le_trans; [apply linear_bits_add|].
  pose proof (linear_bits_scale X key_bits (-1)%Z g) as Hscale.
  change (linear_bits key_bits (linear_scale (-1)%Z g) <= 1 + linear_bits key_bits g)
    in Hscale. lia.
Qed.

(** An affine product adds at most the two operand bit envelopes. *)
Lemma linear_bits_mul : forall X (key_bits : X -> nat) f g h,
  linear_mul f g = Some h ->
  linear_bits key_bits h <= linear_bits key_bits f + linear_bits key_bits g.
Proof.
  intros X key_bits f g h Hmul. unfold linear_mul in Hmul.
  destruct (coef f) as [|p ps] eqn:Hleft.
  - inversion Hmul; subst h.
    pose proof (linear_bits_scale X key_bits (cst f) g).
    pose proof (proj1 (proj1 (linear_bits_components X key_bits f
      (linear_bits key_bits f)) (Nat.le_refl _))). lia.
  - destruct (coef g) as [|q qs] eqn:Hright; [|discriminate].
    inversion Hmul; subst h.
    pose proof (linear_bits_scale X key_bits (cst g) f).
    pose proof (proj1 (proj1 (linear_bits_components X key_bits g
      (linear_bits key_bits g)) (Nat.le_refl _))). lia.
Qed.

(** Addition keeps exactly the coefficient occurrences of both operands. *)
Lemma linear_length_add : forall X (f g : lin X),
  length (coef (linear_add f g)) = length (coef f) + length (coef g).
Proof.
  intros X f g. cbn [linear_add coef]. apply length_app.
Qed.

(** Scaling preserves the number of coefficient occurrences. *)
Lemma linear_length_scale : forall X a (f : lin X),
  length (coef (linear_scale a f)) = length (coef f).
Proof.
  intros X a f. cbn [linear_scale coef]. apply length_map.
Qed.

(** Subtraction keeps exactly the coefficient occurrences of both operands. *)
Lemma linear_length_sub : forall X (f g : lin X),
  length (coef (linear_sub f g)) = length (coef f) + length (coef g).
Proof.
  intros X f g. unfold linear_sub. rewrite linear_length_add, linear_length_scale.
  reflexivity.
Qed.

(** A recognized product keeps at most the coefficient occurrences of its two inputs. *)
Lemma linear_length_mul : forall X (f g h : lin X),
  linear_mul f g = Some h -> length (coef h) <= length (coef f) + length (coef g).
Proof.
  intros X f g h Hmul. unfold linear_mul in Hmul.
  destruct (coef f) as [|p ps] eqn:Hleft.
  - inversion Hmul; subst h. rewrite linear_length_scale. cbn [length]. lia.
  - destruct (coef g) as [|q qs] eqn:Hright; [|discriminate].
    inversion Hmul; subst h. rewrite linear_length_scale, Hleft. cbn [length]. lia.
Qed.

(** Each integer operator pays for its output with its input forms and literal payload. *)
Lemma zlinear_op_size : forall X (key_bits : X -> nat) o fs f,
  zlinear_op o fs = Some f ->
  length (coef f) <= fold_right Nat.add 0 (map (fun g => length (coef g)) fs) /\
  linear_bits key_bits f <= zoperator_bits o + 1 +
    fold_right Nat.add 0 (map (linear_bits key_bits) fs).
Proof.
  intros X key_bits o fs f Hlin.
  destruct o; destruct fs as [|f1 [|f2 [|f3 fs]]];
    cbn [zlinear_op] in Hlin; try discriminate;
    cbn [map fold_right zoperator_bits].
  - inversion Hlin; subst f. split.
    + rewrite linear_length_add. lia.
    + pose proof (linear_bits_add X key_bits f1 f2). lia.
  - inversion Hlin; subst f. split.
    + rewrite linear_length_sub. lia.
    + pose proof (linear_bits_sub X key_bits f1 f2). lia.
  - split.
    + pose proof (linear_length_mul X f1 f2 f Hlin). lia.
    + pose proof (linear_bits_mul X key_bits f1 f2 f Hlin). lia.
  - inversion Hlin; subst f. split.
    + cbn [linear_const coef length]. lia.
    + unfold linear_bits. cbn [linear_const coef cst map fold_right]. lia.
Qed.

(** The nested term induction principle supplies the same child facts as [Forall]. *)
Lemma all_children_forall : forall A (P : A -> Prop) xs,
  list_all A P xs -> Forall P xs.
Proof.
  intros A P xs H. induction H as [|x Hx xs Hxs IH]; constructor; assumption.
Qed.

(** Sequencing successful optional results preserves pointwise bounds on their summed sizes. *)
Lemma sequence_map_bound : forall A B (f : A -> option B) (input : A -> nat)
    (output : B -> nat) xs ys,
  Forall (fun x => forall y, f x = Some y -> output y <= input x) xs ->
  sequence (map f xs) = Some ys ->
  fold_right Nat.add 0 (map output ys) <= fold_right Nat.add 0 (map input xs).
Proof.
  intros A B f input output xs ys Hbounds. revert ys.
  induction Hbounds as [|x xs Hhead Htail IH]; intros ys Hseq.
  - cbn [map sequence] in Hseq. inversion Hseq. cbn [map fold_right]. lia.
  - cbn [map sequence] in Hseq.
    destruct (f x) as [y|] eqn:Hvalue; [|discriminate].
    destruct (sequence (map f xs)) as [zs|] eqn:Hrest; [|discriminate].
    inversion Hseq; subst ys. specialize (Hhead y eq_refl). specialize (IH zs eq_refl).
    cbn [map fold_right]. lia.
Qed.

(** Every term has at least one syntax node. *)
Lemma term_size_pos : forall K X (e : term K X), 1 <= tsize e.
Proof.
  intros K X [x|o es]; cbn [tsize]; lia.
Qed.

(** The syntax mass includes at least one unit for every syntax node. *)
Lemma term_mass_size : forall K X key_bits operator_bits (e : term K X),
  tsize e <= term_mass key_bits operator_bits e.
Proof.
  intros K X key_bits operator_bits e. induction e as [x|o es IH].
  - cbn [tsize term_mass]. lia.
  - cbn [tsize term_mass].
    assert (Hsum : fold_right Nat.add 0 (map tsize es) <=
      fold_right Nat.add 0 (map (term_mass key_bits operator_bits) es)).
    { induction IH as [|e He es Hes IHes]; cbn [map fold_right]; lia. }
    lia.
Qed.

(** Successful integer recognition has linear coefficient count and syntactic bit size. *)
Lemma zlinear_form_size : forall X (key_bits : X -> nat) e f,
  zlinear_form e = Some f ->
  length (coef f) <= tsize e /\
  linear_bits key_bits f <= term_mass key_bits zoperator_bits e.
Proof.
  intros X key_bits e. induction e as [x|o es IH]; intros f Hlin.
  - cbn [zlinear_form] in Hlin. inversion Hlin; subst f.
    change (1 <= 1 /\ Nat.max (key_bits x + 1) 0 <= key_bits x + 1).
    rewrite Nat.max_0_r. split; lia.
  - cbn [zlinear_form] in Hlin. apply all_children_forall in IH.
    destruct (sequence (map zlinear_form es)) as [fs|] eqn:Hforms; [|discriminate].
    assert (Hlength : fold_right Nat.add 0 (map (fun g => length (coef g)) fs) <=
      fold_right Nat.add 0 (map tsize es)).
    { eapply sequence_map_bound; [|exact Hforms].
      eapply Forall_impl; [|exact IH]. intros e He g Hg. exact (proj1 (He g Hg)). }
    assert (Hbits : fold_right Nat.add 0 (map (linear_bits key_bits) fs) <=
      fold_right Nat.add 0 (map (term_mass key_bits zoperator_bits) es)).
    { eapply sequence_map_bound; [|exact Hforms].
      eapply Forall_impl; [|exact IH]. intros e He g Hg. exact (proj2 (He g Hg)). }
    destruct (zlinear_op_size X key_bits o fs f Hlin) as [Hcoef Hform].
    cbn [tsize term_mass]. split; lia.
Qed.
