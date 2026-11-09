(** * Integer expressions and recurrence observations

    Recurrences describe integer values before the final word observation.
    For example, an additive recurrence with base zero and step two evaluates to twice its index.
    Builds on: BitsWord. *)

From Stdlib Require Import List Bool Arith Lia ZArith NArith PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsWord.
Import Cost.Notations.

(** Invariant expressions distinguish mathematical coefficients from client word literals. *)
Inductive iexpr (V : Type) : Type :=
  | IVar (x : V)
  | IConst (z : Z)
  | IWordConst (z : Z)
  | IAdd (a b : iexpr V)
  | IMul (a b : iexpr V).

Arguments IVar {V}.
Arguments IConst {V}.
Arguments IWordConst {V}.
Arguments IAdd {V}.
Arguments IMul {V}.

(** Invariant evaluation uses integer arithmetic and the supplied entry valuation. *)
Fixpoint eval_iexpr {V} (inv : V -> Z) (e : iexpr V) : Z :=
  match e with
  | IVar x => inv x
  | IConst z => z
  | IWordConst z => z
  | IAdd a b => (eval_iexpr inv a + eval_iexpr inv b)%Z
  | IMul a b => (eval_iexpr inv a * eval_iexpr inv b)%Z
  end.

Module Chrec.

(** A chain integrates additive or multiplicative steps and has pointwise fallback nodes. *)
Inductive t (V : Type) : Type :=
  | CInv (e : iexpr V)
  | CRec (base step : t V)
  | CGeo (base ratio : t V)
  | CSum (left right : t V)
  | CProduct (left right : t V).

Arguments CInv {V}.
Arguments CRec {V}.
Arguments CGeo {V}.
Arguments CSum {V}.
Arguments CProduct {V}.

(** A recurrence advances with the preceding step and starts with its base evaluated at zero. *)
Fixpoint eval {V} (inv : V -> Z) (c : t V) : nat -> Z :=
  match c with
  | CInv e => fun _ => eval_iexpr inv e
  | CRec b s =>
    fix iter k :=
      match k with
      | O => eval inv b O
      | S n => (iter n + eval inv s n)%Z
      end
  | CGeo b r =>
    fix iter k :=
      match k with
      | O => eval inv b O
      | S n => (iter n * eval inv r n)%Z
      end
  | CSum a b => fun k => (eval inv a k + eval inv b k)%Z
  | CProduct a b => fun k => (eval inv a k * eval inv b k)%Z
  end.

(** An invariant additive step gives its affine integer value at every natural index. *)
Theorem eval_affine {V} (inv : V -> Z) b s k :
  eval inv (CRec b (CInv s)) k =
    (eval inv b O + Z.of_nat k * eval_iexpr inv s)%Z.
Proof.
  induction k as [|k IHk].
  - cbn; ring.
  - change ((eval inv (CRec b (CInv s)) k + eval_iexpr inv s)%Z =
      (eval inv b O + Z.of_nat (S k) * eval_iexpr inv s)%Z).
    rewrite IHk, Nat2Z.inj_succ; ring.
Qed.

(** Adding an invariant visits additive bases and preserves their steps. *)
Fixpoint chrec_add_invariant_c {V} (e : iexpr V) (c : t V) : Cost.t (t V) :=
  Cost.step ;;
  match c with
  | CInv f => Cost.ret (CInv (IAdd e f))
  | CRec b s =>
    let* base := chrec_add_invariant_c e b in Cost.ret (CRec base s)
  | _ => Cost.ret (CSum (CInv e) c)
  end.

Definition chrec_add_invariant {V} (e : iexpr V) (c : t V) : t V :=
  Cost.value (chrec_add_invariant_c e c).

(** The projected invariant-addition equation exposes the same additive traversal. *)
Theorem chrec_add_invariant_equation {V} (e : iexpr V) (c : t V) :
  chrec_add_invariant e c =
  match c with
  | CInv f => CInv (IAdd e f)
  | CRec b s => CRec (chrec_add_invariant e b) s
  | _ => CSum (CInv e) c
  end.
Proof.
  destruct c; reflexivity.
Qed.

(** Addition combines additive chains and retains every other sum explicitly. *)
Fixpoint chrec_add_c {V} (a b : t V) {struct a} : Cost.t (t V) :=
  Cost.step ;;
  match a with
  | CInv e => chrec_add_invariant_c e b
  | CRec base step =>
    match b with
    | CInv e =>
      let* combined := chrec_add_c base (CInv e) in Cost.ret (CRec combined step)
    | CRec base' step' =>
      let* combined_base := chrec_add_c base base' in
      let* combined_step := chrec_add_c step step' in
      Cost.ret (CRec combined_base combined_step)
    | _ => Cost.ret (CSum a b)
    end
  | _ => Cost.ret (CSum a b)
  end.

Definition chrec_add {V} (a b : t V) : t V := Cost.value (chrec_add_c a b).

(** Projected addition follows only additive recurrence structure. *)
Theorem chrec_add_equation {V} (a b : t V) :
  chrec_add a b =
  match a with
  | CInv e => chrec_add_invariant e b
  | CRec base step =>
    match b with
    | CInv e => CRec (chrec_add base (CInv e)) step
    | CRec base' step' => CRec (chrec_add base base') (chrec_add step step')
    | _ => CSum a b
    end
  | _ => CSum a b
  end.
Proof.
  destruct a, b; reflexivity.
Qed.

(** Invariant multiplication visits additive chains and geometric bases. *)
Fixpoint chrec_mul_invariant_c {V} (e : iexpr V) (c : t V) : Cost.t (t V) :=
  Cost.step ;;
  match c with
  | CInv f => Cost.ret (CInv (IMul e f))
  | CRec b s =>
    let* base := chrec_mul_invariant_c e b in
    let* step := chrec_mul_invariant_c e s in Cost.ret (CRec base step)
  | CGeo b r =>
    let* base := chrec_mul_invariant_c e b in Cost.ret (CGeo base r)
  | _ => Cost.ret (CProduct (CInv e) c)
  end.

Definition chrec_mul_invariant {V} (e : iexpr V) (c : t V) : t V :=
  Cost.value (chrec_mul_invariant_c e c).

(** Invariant multiplication preserves the geometric ratio. *)
Theorem chrec_mul_invariant_equation {V} (e : iexpr V) (c : t V) :
  chrec_mul_invariant e c =
  match c with
  | CInv f => CInv (IMul e f)
  | CRec b s => CRec (chrec_mul_invariant e b) (chrec_mul_invariant e s)
  | CGeo b r => CGeo (chrec_mul_invariant e b) r
  | _ => CProduct (CInv e) c
  end.
Proof.
  destruct c; reflexivity.
Qed.

(** The affine product's second difference adds the two cross-step products. *)
Definition affine_product {V} (x s y step : iexpr V) : t V :=
  CRec (CInv (IMul x y))
    (CRec (CInv (IAdd (IAdd (IMul x step) (IMul y s)) (IMul s step)))
      (CInv (IAdd (IMul s step) (IMul s step)))).

(** Multiplication normalizes invariant, affine and geometric products. *)
Fixpoint chrec_mul_c {V} (a b : t V) {struct a} : Cost.t (t V) :=
  Cost.step ;;
  match a with
  | CInv e => chrec_mul_invariant_c e b
  | CRec (CInv x) (CInv s) =>
    match b with
    | CInv e => chrec_mul_invariant_c e a
    | CRec (CInv y) (CInv t) => Cost.ret (affine_product x s y t)
    | _ => Cost.ret (CProduct a b)
    end
  | CGeo base ratio =>
    match b with
    | CInv e => chrec_mul_invariant_c e a
    | CGeo base' ratio' =>
      let* combined_base := chrec_mul_c base base' in
      let* combined_ratio := chrec_mul_c ratio ratio' in
      Cost.ret (CGeo combined_base combined_ratio)
    | _ => Cost.ret (CProduct a b)
    end
  | _ =>
    match b with
    | CInv e => chrec_mul_invariant_c e a
    | _ => Cost.ret (CProduct a b)
    end
  end.

Definition chrec_mul {V} (a b : t V) : t V := Cost.value (chrec_mul_c a b).

(** Projected multiplication uses an explicit product when no algebraic rule applies. *)
Theorem chrec_mul_equation {V} (a b : t V) :
  chrec_mul a b =
  match a with
  | CInv e => chrec_mul_invariant e b
  | CRec (CInv x) (CInv s) =>
    match b with
    | CInv e => chrec_mul_invariant e a
    | CRec (CInv y) (CInv t) => affine_product x s y t
    | _ => CProduct a b
    end
  | CGeo base ratio =>
    match b with
    | CInv e => chrec_mul_invariant e a
    | CGeo base' ratio' => CGeo (chrec_mul base base') (chrec_mul ratio ratio')
    | _ => CProduct a b
    end
  | _ =>
    match b with
    | CInv e => chrec_mul_invariant e a
    | _ => CProduct a b
    end
  end.
Proof.
  destruct a as [e|a s|a r|a s|a s]; try (destruct b; reflexivity).
  destruct a, s, b as [f|base step|base ratio|left right|left right]; try reflexivity.
  destruct base, step; reflexivity.
Qed.

Lemma eval_add_invariant {V} (inv : V -> Z) e c k :
  eval inv (chrec_add_invariant e c) k = (eval_iexpr inv e + eval inv c k)%Z.
Proof.
  revert k; induction c as [f|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb];
    intro k; rewrite chrec_add_invariant_equation; try reflexivity.
  induction k as [|k IHk].
  - cbn; apply IHb.
  - change ((eval inv (CRec (chrec_add_invariant e b) s) k + eval inv s k)%Z =
      (eval_iexpr inv e + (eval inv (CRec b s) k + eval inv s k))%Z).
    rewrite IHk; ring.
Qed.

(** Recurrence addition evaluates to integer addition at every index. *)
Theorem eval_add {V} (inv : V -> Z) (a b : t V) (k : nat) :
  eval inv (chrec_add a b) k = (eval inv a k + eval inv b k)%Z.
Proof.
  revert b k; induction a as [e|a IHa s IHs|a IHa r IHr|a IHa b IHb|a IHa b IHb];
    intros other k; rewrite chrec_add_equation; try reflexivity.
  - apply eval_add_invariant.
  - destruct other as [e|b t|b r|b c|b c]; try reflexivity.
    + induction k as [|k IHk].
      * cbn; apply IHa.
      * change ((eval inv (CRec (chrec_add a (CInv e)) s) k + eval inv s k)%Z =
          (eval inv (CRec a s) k + eval inv s k + eval_iexpr inv e)%Z).
        change (eval inv (CRec (chrec_add a (CInv e)) s) k =
          (eval inv (CRec a s) k + eval_iexpr inv e)%Z) in IHk.
        rewrite IHk; ring.
    + induction k as [|k IHk].
      * cbn; apply IHa.
      * change ((eval inv (CRec (chrec_add a b) (chrec_add s t)) k +
          eval inv (chrec_add s t) k)%Z =
          (eval inv (CRec a s) k + eval inv s k +
            (eval inv (CRec b t) k + eval inv t k))%Z).
        rewrite IHk, IHs; ring.
Qed.

Lemma eval_mul_invariant {V} (inv : V -> Z) e c k :
  eval inv (chrec_mul_invariant e c) k = (eval_iexpr inv e * eval inv c k)%Z.
Proof.
  revert k; induction c as [f|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb];
    intro k; rewrite chrec_mul_invariant_equation; try reflexivity.
  - induction k as [|k IHk].
    + cbn; apply IHb.
    + change ((eval inv (CRec (chrec_mul_invariant e b) (chrec_mul_invariant e s)) k +
        eval inv (chrec_mul_invariant e s) k)%Z =
        (eval_iexpr inv e * (eval inv (CRec b s) k + eval inv s k))%Z).
      rewrite IHk, IHs; ring.
  - induction k as [|k IHk].
    + cbn; apply IHb.
    + change ((eval inv (CGeo (chrec_mul_invariant e b) r) k * eval inv r k)%Z =
        (eval_iexpr inv e * (eval inv (CGeo b r) k * eval inv r k))%Z).
      rewrite IHk; ring.
Qed.

(** The generic second difference evaluates to the product of the two affine sequences. *)
Theorem eval_affine_product {V} (inv : V -> Z) x s y t k :
  eval inv (affine_product x s y t) k =
    (eval inv (CRec (CInv x) (CInv s)) k *
      eval inv (CRec (CInv y) (CInv t)) k)%Z.
Proof.
  induction k as [|k IHk]; [reflexivity|].
  change ((eval inv (affine_product x s y t) k +
    eval inv (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
      (CInv (IAdd (IMul s t) (IMul s t)))) k)%Z =
    ((eval inv (CRec (CInv x) (CInv s)) k + eval_iexpr inv s) *
      (eval inv (CRec (CInv y) (CInv t)) k + eval_iexpr inv t))%Z).
  rewrite IHk, !eval_affine; cbn [eval eval_iexpr]; ring.
Qed.

(** Recurrence multiplication evaluates to integer multiplication at every index. *)
Theorem eval_mul {V} (inv : V -> Z) (a b : t V) (k : nat) :
  eval inv (chrec_mul a b) k = (eval inv a k * eval inv b k)%Z.
Proof.
  assert (Hright : forall c e k, eval inv (chrec_mul_invariant e c) k =
    (eval inv c k * eval_iexpr inv e)%Z).
  { intros c e j; rewrite eval_mul_invariant; ring. }
  revert b k; induction a as [e|a IHa s IHs|a IHa r IHr|a IHa b IHb|a IHa b IHb];
    intros other k; rewrite chrec_mul_equation.
  - apply eval_mul_invariant.
  - destruct other as [e|b t|b t|b t|b t].
    + destruct a, s; apply Hright.
    + destruct a, s, b, t; try reflexivity; apply eval_affine_product.
    + destruct a, s; reflexivity.
    + destruct a, s; reflexivity.
    + destruct a, s; reflexivity.
  - destruct other as [e|b s|b t|b s|b s]; try reflexivity.
    + apply Hright.
    + induction k as [|k IHk].
      * cbn; apply IHa.
      * change ((eval inv (CGeo (chrec_mul a b) (chrec_mul r t)) k *
          eval inv (chrec_mul r t) k)%Z =
          ((eval inv (CGeo a r) k * eval inv r k) *
            (eval inv (CGeo b t) k * eval inv t k))%Z).
        change (eval inv (CGeo (chrec_mul a b) (chrec_mul r t)) k =
          (eval inv (CGeo a r) k * eval inv (CGeo b t) k)%Z) in IHk.
        rewrite IHk, IHr; ring.
  - destruct other; try reflexivity; apply Hright.
  - destruct other; try reflexivity; apply Hright.
Qed.

(** Scaling is multiplication by an invariant mathematical coefficient. *)
Definition chrec_scale_c {V} (z : Z) (c : t V) : Cost.t (t V) :=
  chrec_mul_c (CInv (IConst z)) c.

Definition chrec_scale {V} (z : Z) (c : t V) : t V :=
  Cost.value (chrec_scale_c z c).

(** Scaling multiplies every point of a recurrence by its coefficient. *)
Theorem eval_scale {V} (inv : V -> Z) z (c : t V) k :
  eval inv (chrec_scale z c) k = (z * eval inv c k)%Z.
Proof.
  change (eval inv (chrec_mul (CInv (IConst z)) c) k = (z * eval inv c k)%Z).
  rewrite eval_mul; reflexivity.
Qed.

(** Node count measures recurrence structure independently of invariant-expression leaves. *)
Fixpoint nodes {V} (c : t V) : N :=
  match c with
  | CInv _ => 1
  | CRec a b | CGeo a b | CSum a b | CProduct a b => 1 + nodes a + nodes b
  end%N.

Lemma nodes_positive {V} (c : t V) : (0 < nodes c)%N.
Proof.
  destruct c; cbn [nodes]; lia.
Qed.

(** Invariant addition charges at most one tick for each recurrence node. *)
Theorem chrec_add_invariant_cost {V} e (c : t V) :
  (Cost.ticks (chrec_add_invariant_c e c) <= nodes c)%N.
Proof.
  induction c; cbn [chrec_add_invariant_c nodes]; autorewrite with galois_cost; lia.
Qed.

(** Invariant multiplication charges at most one tick for each recurrence node. *)
Theorem chrec_mul_invariant_cost {V} e (c : t V) :
  (Cost.ticks (chrec_mul_invariant_c e c) <= nodes c)%N.
Proof.
  induction c; cbn [chrec_mul_invariant_c nodes]; autorewrite with galois_cost; lia.
Qed.

(** Each addition traversal pays its visited nodes and its invariant-helper traversal. *)
Theorem chrec_add_cost {V} (a b : t V) :
  (Cost.ticks (chrec_add_c a b) <= (nodes a + 1) * (nodes b + 1))%N.
Proof.
  revert b; induction a as [e|a IHa s IHs|a IHa r IHr|a IHa b IHb|a IHa b IHb];
    intro other.
  - cbn [chrec_add_c nodes]; autorewrite with galois_cost.
    pose proof (chrec_add_invariant_cost e other); nia.
  - destruct other as [e|base step|base ratio|left right|left right];
      cbn [chrec_add_c nodes]; autorewrite with galois_cost; try nia.
    + pose proof (IHa (CInv e)); cbn [nodes] in *; nia.
    + pose proof (IHa base); pose proof (IHs step); nia.
  - cbn [chrec_add_c nodes]; autorewrite with galois_cost; nia.
  - cbn [chrec_add_c nodes]; autorewrite with galois_cost; nia.
  - cbn [chrec_add_c nodes]; autorewrite with galois_cost; nia.
Qed.

(** Multiplication pays its structural descent and every invariant-helper call. *)
Theorem chrec_mul_cost {V} (a b : t V) :
  (Cost.ticks (chrec_mul_c a b) <= (nodes a + 1) * (nodes b + 1))%N.
Proof.
  revert b; induction a as [e|a IHa s IHs|a IHa r IHr|a IHa b IHb|a IHa b IHb];
    intro other.
  - cbn [chrec_mul_c nodes]; autorewrite with galois_cost.
    pose proof (chrec_mul_invariant_cost e other); nia.
  - destruct a, s, other as [f|base step|base ratio|left right|left right];
      cbn [chrec_mul_c nodes]; autorewrite with galois_cost; try nia.
    all: repeat match goal with
    | |- context [Cost.ticks (chrec_mul_invariant_c ?e ?c)] =>
      let Hbound := fresh "Hbound" in
      let charge := fresh "charge" in
      pose proof (chrec_mul_invariant_cost e c) as Hbound;
      cbn [nodes] in Hbound;
      remember (Cost.ticks (chrec_mul_invariant_c e c)) as charge in *
    end.
    all: try nia.
    destruct base, step; cbn [chrec_mul_c nodes]; autorewrite with galois_cost; nia.
  - destruct other as [e|base step|base ratio|left right|left right];
      cbn [chrec_mul_c nodes]; autorewrite with galois_cost; try nia.
    + pose proof (chrec_mul_invariant_cost e (CGeo a r)); cbn [nodes] in *; nia.
    + pose proof (IHa base); pose proof (IHr ratio); nia.
  - destruct other; cbn [chrec_mul_c nodes]; autorewrite with galois_cost; try nia.
    pose proof (chrec_mul_invariant_cost e (CSum a b)); cbn [nodes] in *; nia.
  - destruct other; cbn [chrec_mul_c nodes]; autorewrite with galois_cost; try nia.
    pose proof (chrec_mul_invariant_cost e (CProduct a b)); cbn [nodes] in *; nia.
Qed.

End Chrec.
Import Chrec.

(** Comparisons describe strict, inclusive and disequality continuation tests. *)
Inductive cmp_kind : Type :=
  | CmpLt
  | CmpLe
  | CmpNe.

(** Signedness chooses the representative of a wrapped word. *)
Inductive signedness : Type :=
  | Unsigned
  | Signed.

(** Word observation chooses the canonical unsigned or signed representative after wrapping. *)
Definition view_z (w : width) (sg : signedness) (a : Z) : Z :=
  let r := wrap w a in
  match sg with
  | Unsigned => r
  | Signed => if (r <? modulus w / 2)%Z then r else (r - modulus w)%Z
  end.

(** Continuation compares word observations of both the recurrence and its bound. *)
Definition test_holds (w : width) (sg : signedness) (c : cmp_kind) (a b : Z) : Prop :=
  let a' := view_z w sg a in
  let b' := view_z w sg b in
  match c with
  | CmpLt => (a' < b')%Z
  | CmpLe => (a' <= b')%Z
  | CmpNe => a' <> b'
  end.

(** The no-wrap range is the representable interval for the selected signedness. *)
Definition in_range (w : width) (sg : signedness) (v : Z) : Prop :=
  match sg with
  | Unsigned => (0 <= v < modulus w)%Z
  | Signed => (- (modulus w / 2) <= v < modulus w / 2)%Z
  end.

(** Sign normalization changes word literals and leaves mathematical coefficients intact. *)
Fixpoint signed_iexpr {V} (w : width) (sg : signedness) (e : iexpr V) : iexpr V :=
  match e with
  | IVar x => IVar x
  | IConst z => IConst z
  | IWordConst z => IConst (view_z w sg z)
  | IAdd a b => IAdd (signed_iexpr w sg a) (signed_iexpr w sg b)
  | IMul a b => IMul (signed_iexpr w sg a) (signed_iexpr w sg b)
  end.

(** Every recurrence node normalizes its invariant leaves structurally. *)
Fixpoint signed_chrec {V} (w : width) (sg : signedness) (c : Chrec.t V) : Chrec.t V :=
  match c with
  | CInv e => CInv (signed_iexpr w sg e)
  | CRec b s => CRec (signed_chrec w sg b) (signed_chrec w sg s)
  | CGeo b r => CGeo (signed_chrec w sg b) (signed_chrec w sg r)
  | CSum a b => CSum (signed_chrec w sg a) (signed_chrec w sg b)
  | CProduct a b => CProduct (signed_chrec w sg a) (signed_chrec w sg b)
  end.

Lemma wrap_view_z w sg z : wrap w (view_z w sg z) = wrap w z.
Proof.
  unfold view_z; destruct sg; [apply wrap_wrap|].
  destruct (wrap w z <? modulus w / 2)%Z; [apply wrap_wrap|].
  replace (wrap w z - modulus w)%Z with (wrap w z + (-1) * modulus w)%Z by ring.
  rewrite wrap_add_modulus; apply wrap_wrap.
Qed.

(** Sign normalization preserves an invariant expression's wrapped value. *)
Theorem signed_iexpr_wrap {V} (w : width) (sg : signedness)
    (inv : V -> Z) (e : iexpr V) :
  wrap w (eval_iexpr inv e) =
  wrap w (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg e)).
Proof.
  induction e as [x|z|z|a IHa b IHb|a IHa b IHb]; cbn.
  - symmetry; apply wrap_view_z.
  - reflexivity.
  - symmetry; apply wrap_view_z.
  - rewrite (wrap_add w (eval_iexpr inv a) (eval_iexpr inv b)).
    rewrite (wrap_add w
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg a))
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg b))).
    rewrite IHa, IHb; reflexivity.
  - rewrite (wrap_mul w (eval_iexpr inv a) (eval_iexpr inv b)).
    rewrite (wrap_mul w
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg a))
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg b))).
    rewrite IHa, IHb; reflexivity.
Qed.

(** Sign normalization preserves a recurrence's wrapped value at every index. *)
Theorem signed_chrec_wrap {V} (w : width) (sg : signedness)
    (inv : V -> Z) (c : Chrec.t V) (k : nat) :
  wrap w (Chrec.eval inv c k) =
  wrap w (Chrec.eval (fun y => view_z w sg (inv y)) (signed_chrec w sg c) k).
Proof.
  revert k; induction c as [e|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb];
    intro k.
  - apply signed_iexpr_wrap.
  - induction k as [|k IHk]; [apply IHb|].
    change (wrap w (Chrec.eval inv (CRec b s) k + Chrec.eval inv s k) =
      wrap w (Chrec.eval (fun y => view_z w sg (inv y))
        (CRec (signed_chrec w sg b) (signed_chrec w sg s)) k +
        Chrec.eval (fun y => view_z w sg (inv y)) (signed_chrec w sg s) k))%Z.
    rewrite (wrap_add w), IHk, IHs; symmetry; apply wrap_add.
  - induction k as [|k IHk]; [apply IHb|].
    change (wrap w (Chrec.eval inv (CGeo b r) k * Chrec.eval inv r k) =
      wrap w (Chrec.eval (fun y => view_z w sg (inv y))
        (CGeo (signed_chrec w sg b) (signed_chrec w sg r)) k *
        Chrec.eval (fun y => view_z w sg (inv y)) (signed_chrec w sg r) k))%Z.
    rewrite (wrap_mul w), IHk, IHr; symmetry; apply wrap_mul.
  - cbn; rewrite (wrap_add w), IHa, IHb; symmetry; apply wrap_add.
  - cbn; rewrite (wrap_mul w), IHa, IHb; symmetry; apply wrap_mul.
Qed.
