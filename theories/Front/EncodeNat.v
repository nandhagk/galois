(** * The encoder of natural numbers

    The module [NatEncode] encodes a natural number [n] as the positive [n + 1], and
    [Egglog Value nat NatEncode] registers it, so a client that loads this file reads [nat] as a
    value type. A client that does not load it reads [nat] as a datatype, whose constructors [O]
    and [S] are tables of the e-graph, so each client chooses one reading. The encoding is a
    bijection onto the positives, so the decoder accepts every positive.

    For example, [NatEncode.encode 4] is [5], and [NatEncode.decode 5] is [Some 4].

    Builds on: the encoder signature and the derive command. *)

From Stdlib Require Import PArith.
From Argent Require Import Time Std.
From Galois.Front Require Import EncodeSig Derive.

(** * Natural numbers *)

Module NatEncode <: ENCODE.
  Definition t : Type := nat.

  (** The positive [n + 1]. *)
  Fixpoint encode (n : nat) : positive :=
    match n with
    | O => xH
    | S m => Pos.succ (encode m)
    end.

  (** The natural number [p - 1]. *)
  Fixpoint below (p : positive) : nat :=
    match p with
    | xH => O
    | xO q => let m := below q in S (m + m)
    | xI q => let m := below q in S (S (m + m))
    end.

  Definition decode (p : positive) : option nat := Some (below p).

  TimeFun encode below decode.

  (** The number below a successor is one more than the number below the positive. *)
  Lemma below_succ (p : positive) : below (Pos.succ p) = S (below p).
  Proof.
    induction p as [q IH | q IH |]; simpl.
    - rewrite IH. simpl. rewrite PeanoNat.Nat.add_succ_r. reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    intros n. unfold decode. f_equal.
    induction n as [| n IH]; simpl.
    - reflexivity.
    - rewrite below_succ, IH. reflexivity.
  Qed.
End NatEncode.

Egglog Value nat NatEncode.
