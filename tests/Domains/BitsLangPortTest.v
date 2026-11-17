(** * Word language observations

    These examples run word operations through the tagged constant harness.
    For example, adding two 32-bit singleton words yields a singleton two.
    Builds on: BitsLang, Tagged and Harness.

    Groups:
    - [BridgeTests] Arithmetic on singleton words.
    - [GuardTests] Truth guards on singleton, unknown and malformed inputs.
    - [ExpressionTests] Bottom results of operations on malformed operands.
    - [PointTests] The wrapping of constants. *)

From Stdlib Require Import List ZArith.
From Galois.Bits Require Import Op.
From Galois.Domains Require Import BitsLang WordSig Const ConstSig Tagged Harness.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

(** The constant payload over the word language. *)
Module Payload := ConstWordCode WordLanguageCode.
(** The constant table over the word language. *)
Module Table := ConstWordTableCode WordLanguageCode Payload.
(** The tagged base over the word language. *)
Module Base := TaggedCode WordLanguageCode Payload.
(** The tagged table over the word language. *)
Module TaggedTable := TaggedTableCode WordLanguageCode Payload Table.
(** The harness over the bit language, the tagged base and the tagged table. *)
Module Domain := HarnessCode BitsLangCode Base TaggedTable.
(** A tagged singleton word of width w and value z. *)
Definition p (w : positive) (z : Z) := TVal w (FVal z).

(** * Bridge *)

Module BridgeTests.

  (** Adding two singleton words of width 32 gives their sum as a singleton. *)
  Example add_of_singletons_is_their_sum :
    Domain.forward (BOp bvadd) [p 32 1; p 32 1] = p 32 2.
  Proof. vm_compute. reflexivity. Qed.

End BridgeTests.

(** * Guards *)

Module GuardTests.

  (** A true guard keeps a positive singleton word unchanged. *)
  Example true_guard_keeps_positive_word :
    Domain.guard (BTruth true) [p 32 7] = [p 32 7].
  Proof. vm_compute. reflexivity. Qed.

  (** A false guard keeps a zero singleton word of width one unchanged. *)
  Example false_guard_keeps_zero_bit :
    Domain.guard (BTruth false) [p 1 0] = [p 1 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A true guard keeps an unknown word unchanged. *)
  Example true_guard_keeps_unknown_word :
    Domain.guard (BTruth true) [TAny] = [TAny].
  Proof. vm_compute. reflexivity. Qed.

  (** A false guard keeps an unknown word unchanged. *)
  Example false_guard_keeps_unknown_word :
    Domain.guard (BTruth false) [TAny] = [TAny].
  Proof. vm_compute. reflexivity. Qed.

  (** A true guard keeps a zero singleton word of width 32 unchanged. *)
  Example true_guard_keeps_zero_word :
    Domain.guard (BTruth true) [p 32 0] = [p 32 0].
  Proof. vm_compute. reflexivity. Qed.

  (** A guard with the wrong number of operands keeps them unchanged. *)
  Example guard_of_wrong_arity_is_unchanged :
    Domain.guard (BTruth true) [p 1 0; p 32 0] = [p 1 0; p 32 0].
  Proof. vm_compute. reflexivity. Qed.

End GuardTests.

(** * Expressions *)

Module ExpressionTests.

  (** An addition with one operand has bottom as its result. *)
  Example add_with_one_operand_is_bottom :
    Domain.forward (BOp bvadd) [p 32 1] = TBot.
  Proof. vm_compute. reflexivity. Qed.

  (** An addition of an empty payload has bottom as its result. *)
  Example add_of_empty_payload_is_bottom :
    Domain.forward (BOp bvadd) [TVal 1%positive FBot] = TBot.
  Proof. vm_compute. reflexivity. Qed.

End ExpressionTests.

(** * Points *)

Module PointTests.

  (** A constant of width one wraps the value two to zero. *)
  Example constant_wraps_at_width_one :
    Payload.pconst 1%positive 2 = FVal 0.
  Proof. vm_compute. reflexivity. Qed.

End PointTests.
