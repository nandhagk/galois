(** * Equality from encoded keys

    Injective encodings turn positive equality into reflected equality of client values.
    For example, equal natural codes imply equal naturals.
    Builds on: BaseEncoding and CostMonad. *)

From Stdlib Require Import Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
Import Cost.Notations.

(** A synchronized digit traversal computes equality and charges the shorter bit count.
    Mismatching digits still traverse the suffixes so the charge is independent of values. *)
Fixpoint positive_eqb_c (p q : positive) : Cost.t bool :=
  Cost.step ;;
  match p, q with
  | xH, xH => Cost.ret true
  | xO p, xO q => positive_eqb_c p q
  | xI p, xI q => positive_eqb_c p q
  | xO p, xI q => Cost.map (fun _ => false) (positive_eqb_c p q)
  | xI p, xO q => Cost.map (fun _ => false) (positive_eqb_c p q)
  | _, _ => Cost.ret false
  end.

(** Synchronized traversal returns standard positive equality. *)
Theorem positive_eqb_equation p q : Cost.value (positive_eqb_c p q) = Pos.eqb p q.
Proof.
  revert q. induction p; intros q; destruct q; cbn [positive_eqb_c Pos.eqb];
    autorewrite with galois_cost; now rewrite ?IHp.
Qed.

(** Digit traversal never charges more than either input's bit count. *)
Theorem positive_eqb_cost p q :
  (Cost.ticks (positive_eqb_c p q) <= N.pos (Pos.size p))%N /\
  (Cost.ticks (positive_eqb_c p q) <= N.pos (Pos.size q))%N.
Proof.
  revert q. induction p; intros q; destruct q; cbn [positive_eqb_c Pos.size];
    autorewrite with galois_cost; try specialize (IHp q); lia.
Qed.

(** Equality charges both encoding callbacks and a synchronized traversal of the shorter key. *)
Definition eqb_c {K} (E : encoding K) (x y : K) : Cost.t bool :=
  Cost.step ;;
  let* p := encode_c E x in
  Cost.step ;;
  let* q := encode_c E y in
  positive_eqb_c p q.

(** Boolean equality is the result of costed equality. *)
Definition eqb {K} (E : encoding K) (x y : K) : bool :=
  Cost.value (eqb_c E x y).

(** Equality tests compare the two encoded positive values. *)
Theorem eqb_equation {K} (E : encoding K) x y :
  eqb E x y = Pos.eqb (encode E x) (encode E y).
Proof.
  unfold eqb, eqb_c. autorewrite with galois_cost.
  apply positive_eqb_equation.
Qed.

(** Equality exposes both encoding costs and bounds digit work by the shorter bit count. *)
Theorem eqb_cost {K} (E : encoding K) x y :
  (Cost.ticks (eqb_c E x y) <=
    2 + Cost.ticks (encode_c E x) + Cost.ticks (encode_c E y) +
      N.min (key_bits E x) (key_bits E y))%N.
Proof.
  unfold eqb_c. autorewrite with galois_cost.
  pose proof (positive_eqb_cost (encode E x) (encode E y)) as [Hx Hy].
  assert (Hmin :
    (Cost.ticks (positive_eqb_c (encode E x) (encode E y)) <=
      N.min (key_bits E x) (key_bits E y))%N).
  { apply N.min_glb; assumption. }
  unfold encode in Hmin. lia.
Qed.

(** A lawful encoding reflects propositional equality through the boolean test. *)
Theorem eqb_spec {K} (E : encoding K) :
  encoding_laws E -> forall x y, reflect (x = y) (eqb E x y).
Proof.
  intros HE x y. rewrite eqb_equation.
  destruct (Pos.eqb_spec (encode E x) (encode E y)) as [Hcode|Hcode].
  - constructor. now apply (encode_injective HE).
  - constructor. intros ->. apply Hcode. reflexivity.
Qed.

(** A true test is equivalent to equality under injectivity. *)
Theorem eqb_true_iff {K} (E : encoding K) (HE : encoding_laws E) x y :
  eqb E x y = true <-> x = y.
Proof.
  destruct (eqb_spec E HE x y); intuition discriminate.
Qed.

(** A false test is equivalent to disequality under injectivity. *)
Theorem eqb_false_iff {K} (E : encoding K) (HE : encoding_laws E) x y :
  eqb E x y = false <-> x <> y.
Proof.
  destruct (eqb_spec E HE x y); intuition discriminate.
Qed.

(** Every key compares equal to itself, even without an injectivity law. *)
Theorem eqb_refl {K} (E : encoding K) x : eqb E x x = true.
Proof.
  rewrite eqb_equation.
  apply Pos.eqb_refl.
Qed.

(** Encoded equality is symmetric for every dictionary. *)
Theorem eqb_sym {K} (E : encoding K) x y : eqb E x y = eqb E y x.
Proof.
  rewrite !eqb_equation.
  apply Pos.eqb_sym.
Qed.

(** A lawful encoding provides constructive decidable equality. *)
Definition eqb_dec {K} (E : encoding K) (HE : encoding_laws E) (x y : K) :
    {x = y} + {x <> y}.
Proof.
  destruct (eqb_spec E HE x y) as [Heq|Hneq].
  - left. exact Heq.
  - right. exact Hneq.
Defined.
