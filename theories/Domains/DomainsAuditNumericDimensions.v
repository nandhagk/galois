(** * Input dimensions and whole-source envelopes

    Numeric widths and unary extract indices are input dimensions.
    For example, an extraction index contributes its full natural value.
    Builds on: numeric source models, audit costs and bit operators. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsKnownBits DomainsAuditNumericCost
  DomainsAuditKnownBitsSource.
Import List.ListNotations.

Definition numeric_operator_dimension o : nat :=
  match o with
  | bvzext w | bvsext w | bvtrunc w => S (Pos.to_nat w)
  | bvextract hi lo => (1 + hi + lo)%nat
  | _ => 1%nat
  end.

Definition numeric_tnum_dimension (a : tnum) :=
  (1 + audit_z_bits (zeros a) + audit_z_bits (ones a))%nat.

Definition numeric_kb_dimension o (args : list (width * tnum)) rw :=
  (1 + numeric_operator_dimension o + Pos.to_nat rw +
    fold_right (fun wa n => (1 + Pos.to_nat (fst wa) + numeric_tnum_dimension (snd wa) + n)%nat)
      0%nat args)%nat.

Definition numeric_envelope (dimension : nat) :=
  (N.to_nat 10000000000%N * Nat.pow (S dimension) 12)%nat.

(** The complete known-bit source work is bounded by the input envelope. *)
Definition kb_forward_source_bound_type : Prop := forall o args rw,
  (kb_source_work (snd (kb_forward_source o args rw)) <=
    numeric_envelope (numeric_kb_dimension o args rw))%nat.

(** Classic multiplication source work is bounded by the same input envelope. *)
Definition kb_classic_mul_source_bound_type : Prop := forall w a b,
  (kb_source_work (snd (kb_classic_mul w a b)) <=
    numeric_envelope (numeric_kb_dimension bvmul [(w, a); (w, b)] w))%nat.

(** Every source execution has a result and trace. *)
Definition kb_source_total_type : Prop := forall o args rw, exists r t,
  kb_forward_source o args rw = (r, t).

(** The result and trace of a source execution are unique. *)
Definition kb_source_unique_type : Prop := forall o args rw r1 t1 r2 t2,
  kb_forward_source o args rw = (r1, t1) -> kb_forward_source o args rw = (r2, t2) ->
  r1 = r2 /\ t1 = t2.
