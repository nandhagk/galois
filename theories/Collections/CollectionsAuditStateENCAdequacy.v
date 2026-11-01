(** * Prepared encoding adequacy

    Prepared keys retain injective codes and their concrete bit widths.
    For example, a prepared empty list has a one-bit code.
    Builds on: CollectionsEncoding and CollectionsAuditState. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditState.
Import List.ListNotations.

(** * Prepared keys *)

(** Preparing a key stores its encoding. *)
Theorem prepare_key_valid : prepare_key_valid_statement.
Proof.
  intros K E k. reflexivity.
Qed.

(** Valid prepared keys with equal codes have equal values. *)
Theorem prepared_key_injection : prepared_key_injection_statement.
Proof.
  intros K E p q Hp Hq Heq.
  apply (encode_injective E). unfold key_valid in Hp, Hq.
  congruence.
Qed.

(** Equal prepared pair codes identify the same pair. *)
Theorem prepared_pair : prepared_pair_statement.
Proof.
  intros A B EA EB x y Heq.
  apply (encode_injective (pair_encoding EA EB)). exact Heq.
Qed.

(** Equal prepared list codes identify the same list. *)
Theorem prepared_list_injection : prepared_list_injection_statement.
Proof.
  intros A EA xs ys Heq.
  apply (encode_injective (list_encoding EA)). exact Heq.
Qed.

(** Stream construction adds one bit to the length of its input. *)
Lemma stream_positive_size : forall bits,
  Pos.size_nat (stream_positive bits) = S (length bits).
Proof.
  induction bits as [|[] rest IH]; simpl; now rewrite ?IH.
Qed.

(** Delimited code emission adds twice the code width to its tail. *)
Lemma emit_code_length : forall p tail,
  length (emit_code p tail) = 2 * Pos.size_nat p + length tail.
Proof.
  induction p as [p IH|p IH|]; intro tail; simpl; rewrite ?IH; lia.
Qed.

(** List emission adds twice the sum of component code widths. *)
Lemma emit_list_length : forall A (E : encoding A) xs,
  length (emit_list E xs) =
    2 * fold_right (fun a bits => Pos.size_nat (encode E a) + bits) 0 xs.
Proof.
  intros A E xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite emit_code_length, IH. lia.
Qed.

(** A prepared pair code records both delimited component widths. *)
Theorem prepared_pair_bits : prepared_pair_bits_statement.
Proof.
  intros A B EA EB a b.
  change (Pos.size_nat (stream_positive
    (emit_code (encode EA a) (emit_code (encode EB b) []))) =
    S (2 * Pos.size_nat (encode EA a) + 2 * Pos.size_nat (encode EB b))).
  rewrite stream_positive_size, !emit_code_length. simpl. f_equal. lia.
Qed.

(** A prepared list code records every delimited element width. *)
Theorem prepared_list_bits : prepared_list_bits_statement.
Proof.
  intros A EA xs.
  change (Pos.size_nat (stream_positive (emit_list EA xs)) =
    S (2 * fold_right (fun a bits => Pos.size_nat (encode EA a) + bits) 0 xs)).
  now rewrite stream_positive_size, emit_list_length.
Qed.
