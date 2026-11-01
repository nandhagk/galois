(** * Shared scalar source charges

    These fixed arithmetic weights and input dimensions have no floor-loop dependency.
    For example, scalar fallback can use word-view weights without importing modular counting.
    Builds on: BitsWord and the shared Collections audit vocabulary. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Bits Require Import BitsWord.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

Definition floor_source_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic site [a] =>
    if Nat.eqb site 0 || Nat.eqb site 1
    then audit_binary_weight (Z.of_N a) 0%Z else 1%nat
  | AuditArithmetic site [a; b] =>
    if Nat.eqb site 3 then audit_multiply_weight (Z.of_N a) (Z.of_N b)
    else if Nat.eqb site 4 || Nat.eqb site 5 then audit_divide_weight (Z.of_N a) (Z.of_N b)
    else audit_binary_weight (Z.of_N a) (Z.of_N b)
  | _ => 1%nat
  end.

Definition floor_sum_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic site [m] =>
    if Nat.eqb site 7 then audit_unary_conversion_weight (audit_z_bits (Z.of_N m))
    else floor_source_frame_weight event
  | _ => floor_source_frame_weight event
  end.

Definition count_frame_weight (e : audit_event unit) : nat :=
  match e with
  | AuditArithmetic 41 [w] | AuditArithmetic 43 [w] => S (N.to_nat w)
  | AuditArithmetic 42 [a; b] => audit_divide_weight (count_zdecode a) (count_zdecode b)
  | AuditArithmetic 44 [a; b] => audit_binary_weight (count_zdecode a) (count_zdecode b)
  | AuditArithmetic 45 [w; a] =>
    (S (N.to_nat w) + audit_divide_weight (count_zdecode a) (2 ^ Z.of_N w))%nat
  | AuditArithmetic 46 [a] => audit_unary_conversion_weight (audit_z_bits (count_zdecode a))
  | _ => floor_sum_frame_weight e
  end.

Definition count_input_size (w : width) (a step bound : Z) (limit : N) : nat :=
  (1 + Pos.to_nat w + audit_z_bits a + audit_z_bits step + audit_z_bits bound +
    audit_z_bits (Z.of_N limit))%nat.
