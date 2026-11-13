(** * Numeric linearization

    The language-independent linearizer recognizes variable leaves.
    For example, a leaf becomes one unit coefficient and an unwrapped zero constant.
    Builds on: LinearizeSig. *)

From Stdlib Require Import List ZArith Lia.
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
  Proof. Admitted. (* STUB *)
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
