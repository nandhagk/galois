(** * Definitions that derived programs call

    The command [Egglog] of [Derive.v] derives programs and lemmas that use the definitions of
    this file. Engine values are positives, and [id_encode] and [id_decode] make [positive] its
    own value type. A primitive set calls each of its functions through [prim1d], [prim2d] or
    [prim3d], which decode the arguments and encode the result, and [prim_case] selects a
    function by its code. The file also registers the scheme [All] of pairs, so that a client
    of the command can declare a datatype that holds a list of pairs.

    For example, [prim2d da db er f [a; b]] decodes [a] with [da] and [b] with [db], and gives
    [Some (er (f x y))] when they decode to [x] and [y].

    Main results
    - [encode_inj_of] An encoder that decodes its own encodings is injective.
    - [prim1d_some], [prim2d_some] and [prim3d_some] A call on decoded arguments has the
      encoded result.
    - [prim1d_inv], [prim2d_inv] and [prim3d_inv] A result of a call comes from decoded
      arguments.

    Builds on: Stdlib lists and binary arithmetic. *)

From Stdlib Require Import List PArith.

Import List.ListNotations.

(** * Primitives over encoded values

    A primitive function takes values of registered types. The primitive of a set decodes each
    argument, calls the function and encodes the result, and has no result when a decoding
    fails. [id_decode] and [id_encode] are the encoder of [positive], which is its own
    engine value. *)

Create HintDb egglog_decode.
Create HintDb egglog_inj.

Definition id_decode (p : positive) : option positive := Some p.

Definition id_encode (p : positive) : positive := p.

(** Decoding the identity encoding gives the value back. *)
Lemma id_decode_encode : forall x, id_decode (id_encode x) = Some x.
Proof.
  reflexivity.
Qed.

#[export] Hint Resolve id_decode_encode : egglog_decode.

(** An encoder that decodes its own encodings is injective. *)
Lemma encode_inj_of {A : Type} (enc : A -> positive) (dec : positive -> option A)
    (Hdec : forall x, dec (enc x) = Some x) (x y : A) : enc x = enc y -> x = y.
Proof.
  intros Henc. apply (f_equal dec) in Henc. rewrite !Hdec in Henc. injection Henc as Hxy.
  exact Hxy.
Qed.

(** The primitive of a set of arity 1, 2 or 3 on a list of engine values. *)
Definition prim1d {A R : Type} (da : positive -> option A) (er : R -> positive) (f : A -> R)
    (vs : list positive) : option positive :=
  match vs with
  | [a] =>
      match da a with
      | Some x => Some (er (f x))
      | None => None
      end
  | _ => None
  end.

Definition prim2d {A B R : Type} (da : positive -> option A) (db : positive -> option B)
    (er : R -> positive) (f : A -> B -> R) (vs : list positive) : option positive :=
  match vs with
  | [a; b] =>
      match da a, db b with
      | Some x, Some y => Some (er (f x y))
      | _, _ => None
      end
  | _ => None
  end.

Definition prim3d {A B C R : Type} (da : positive -> option A) (db : positive -> option B)
    (dc : positive -> option C) (er : R -> positive) (f : A -> B -> C -> R)
    (vs : list positive) : option positive :=
  match vs with
  | [a; b; c] =>
      match da a, db b, dc c with
      | Some x, Some y, Some z => Some (er (f x y z))
      | _, _, _ => None
      end
  | _ => None
  end.

(** The result of the primitive with code [c] when [p] is [c], and [rest] otherwise. *)
Definition prim_case (p c : positive) (call : list positive -> option positive)
    (vs : list positive) (rest : option positive) : option positive :=
  if Pos.eqb p c then call vs else rest.

Arguments prim1d : simpl never.
Arguments prim2d : simpl never.
Arguments prim3d : simpl never.

(** A call on decoded arguments has the encoded result. *)
Lemma prim1d_some {A R : Type} (da : positive -> option A) (er : R -> positive) (f : A -> R) a x :
  da a = Some x -> prim1d da er f [a] = Some (er (f x)).
Proof.
  intros Ha. unfold prim1d. rewrite Ha. reflexivity.
Qed.

Lemma prim2d_some {A B R : Type} (da : positive -> option A) (db : positive -> option B)
    (er : R -> positive) (f : A -> B -> R) a b x y :
  da a = Some x -> db b = Some y -> prim2d da db er f [a; b] = Some (er (f x y)).
Proof.
  intros Ha Hb. unfold prim2d. rewrite Ha, Hb. reflexivity.
Qed.

Lemma prim3d_some {A B C R : Type} (da : positive -> option A) (db : positive -> option B)
    (dc : positive -> option C) (er : R -> positive) (f : A -> B -> C -> R) a b c x y z :
  da a = Some x -> db b = Some y -> dc c = Some z ->
  prim3d da db dc er f [a; b; c] = Some (er (f x y z)).
Proof.
  intros Ha Hb Hc. unfold prim3d. rewrite Ha, Hb, Hc. reflexivity.
Qed.

(** A result of a call comes from decoded arguments. *)
Lemma prim1d_inv {A R : Type} (da : positive -> option A) (er : R -> positive) (f : A -> R) a w :
  prim1d da er f [a] = Some w -> exists x, da a = Some x /\ w = er (f x).
Proof.
  unfold prim1d. destruct (da a) as [x|]; intros Hw; try discriminate.
  injection Hw as Hw. exists x. auto.
Qed.

Lemma prim2d_inv {A B R : Type} (da : positive -> option A) (db : positive -> option B)
    (er : R -> positive) (f : A -> B -> R) a b w :
  prim2d da db er f [a; b] = Some w ->
  exists x y, da a = Some x /\ db b = Some y /\ w = er (f x y).
Proof.
  unfold prim2d. destruct (da a) as [x|], (db b) as [y|]; intros Hw; try discriminate.
  injection Hw as Hw. exists x, y. auto.
Qed.

Lemma prim3d_inv {A B C R : Type} (da : positive -> option A) (db : positive -> option B)
    (dc : positive -> option C) (er : R -> positive) (f : A -> B -> C -> R) a b c w :
  prim3d da db dc er f [a; b; c] = Some w ->
  exists x y z, da a = Some x /\ db b = Some y /\ dc c = Some z /\ w = er (f x y z).
Proof.
  unfold prim3d. destruct (da a) as [x|], (db b) as [y|], (dc c) as [z|]; intros Hw;
    try discriminate.
  injection Hw as Hw. exists x, y, z. auto.
Qed.

(** * Lists of pairs

    A datatype of a program may hold a list of pairs, such as a list of fields from keys to
    terms. Rocq declares such a datatype with the warning [register-all] when no scheme [All]
    of pairs is registered, and the flags of this project make that warning an error. The
    registration below takes effect in every file that requires this one, so every client of
    the command can declare such a datatype. *)

(** Nested inductives through pairs get their induction hypotheses from this scheme. *)
Scheme All for prod.
