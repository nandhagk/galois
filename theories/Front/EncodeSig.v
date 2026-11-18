(** * Encoders of engine values

    The engine runs on values of one type, [positive]. A client that computes with another type,
    such as [Z] or [string], gives an encoder of that type into [positive]. The encoder is
    computable and injective, because [decode] undoes it. The command [Egglog Value] registers
    an encoder, and every program derived afterwards encodes the values of its type.

    For example, the encoder of [Z] sends [0] to [1], [Zpos p] to [p~0] and [Zneg p] to [p~1].

    Builds on: Stdlib binary numbers. *)

From Stdlib Require Import PArith.

(** * Interface *)

Module Type ENCODE.
  (** The type of the values. *)
  Parameter t : Type.
  (** The engine value of a value. *)
  Parameter encode : t -> positive.
  (** The value of an engine value, when it encodes one. *)
  Parameter decode : positive -> option t.
  (** Decoding undoes encoding, so [encode] is injective. *)
  Parameter decode_encode : forall x, decode (encode x) = Some x.
End ENCODE.
