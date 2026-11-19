(** * The encoder of characters

    The module [AsciiEncode] encodes a character as the string that holds it alone, with the
    encoder of strings, and [Egglog Value ascii AsciiEncode] registers it, so a client that
    loads this file reads [ascii] as a value type. A client that does not load it reads [ascii]
    as a datatype, whose one constructor [Ascii] takes eight booleans, so each client chooses one
    reading.

    For example, [AsciiEncode.encode "a"%char] is [StringEncode.encode "a"%string], and
    [AsciiEncode.decode] gives nothing for the encoding of a string of two characters.

    Builds on: the encoders of common value types and the derive command. *)

From Stdlib Require Import PArith Ascii String.
From Argent Require Import Time.
From Galois.Front Require Import EncodeSig Encode Derive.

(** * Characters *)

Module AsciiEncode <: ENCODE.
  Definition t : Type := ascii.

  Definition encode (c : ascii) : positive := StringEncode.encode (String c EmptyString).

  Definition decode (p : positive) : option ascii :=
    match StringEncode.decode p with
    | Some (String c EmptyString) => Some c
    | _ => None
    end.

  TimeFun encode decode.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    intros c. unfold decode, encode. rewrite StringEncode.decode_encode. reflexivity.
  Qed.
End AsciiEncode.

Egglog Value ascii AsciiEncode.
