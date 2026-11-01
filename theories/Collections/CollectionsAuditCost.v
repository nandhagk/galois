(** * Audit event vocabulary

    Shared events and folds describe abstract source-operation accounts.
    For example, a case inspection and an external call contribute two events.
    Builds on: Rocq Stdlib. *)

From Stdlib.Lists Require Import List.
From Stdlib.NArith Require Import NArith.
From Stdlib.PArith Require Import PArith.
From Stdlib.ZArith Require Import ZArith.
Import List.ListNotations.

(** Events retain a fixed source site and, for calls, the typed actual call record. *)
Polymorphic Inductive audit_event (Call : Type) : Type :=
  | AuditCase (site : nat) (operands : list N)
  | AuditCall (call : Call)
  | AuditConstruct (site : nat) (operands : list N)
  | AuditKeyBit (bit : bool)
  | AuditArithmetic (site : nat) (operands : list N).

Arguments AuditCase {Call} _ _.
Arguments AuditCall {Call} _.
Arguments AuditConstruct {Call} _ _.
Arguments AuditKeyBit {Call} _.
Arguments AuditArithmetic {Call} _ _.

Polymorphic Definition audit_trace (Call : Type) : Type := list (audit_event Call).

(** This count is the number of modeled source events, including callback invocations. *)
Polymorphic Definition audit_work {Call} (events : audit_trace Call) : nat := List.length events.

(** Collect calls in their source order, with their actual operands in the call type. *)
Fixpoint audit_calls {Call} (events : audit_trace Call) : list Call :=
  match events with
  | nil => nil
  | AuditCall call :: rest => call :: audit_calls rest
  | _ :: rest => audit_calls rest
  end.

(** Count key-bit events independently of other modeled source events. *)
Fixpoint audit_key_bits {Call} (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditKeyBit _ :: rest => S (audit_key_bits rest)
  | _ :: rest => audit_key_bits rest
  end.

(** Count case inspections at the specified concrete source site. *)
Polymorphic Fixpoint audit_case_count {Call} (site : nat) (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditCase current _ :: rest =>
      (if Nat.eqb site current then 1 else 0) + audit_case_count site rest
  | _ :: rest => audit_case_count site rest
  end.

(** Count constructions at the specified concrete source site. *)
Fixpoint audit_construct_count {Call} (site : nat) (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditConstruct current _ :: rest =>
      (if Nat.eqb site current then 1 else 0) + audit_construct_count site rest
  | _ :: rest => audit_construct_count site rest
  end.

(** Count arithmetic frames at the specified concrete source site. *)
Fixpoint audit_arithmetic_count {Call} (site : nat) (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditArithmetic current _ :: rest =>
      (if Nat.eqb site current then 1 else 0) + audit_arithmetic_count site rest
  | _ :: rest => audit_arithmetic_count site rest
  end.

(** These fixed weights define an abstract operation model, not native work. *)
Definition audit_z_bits (z : Z) : nat := S (Z.to_nat (Z.log2 (Z.abs z))).

Definition audit_key_bits_weight (key : positive) : nat := Pos.size_nat key.

Definition audit_get_weight (key : positive) : nat := 1 + audit_key_bits_weight key.

Definition audit_set_weight (key : positive) : nat := 1 + 2 * audit_key_bits_weight key.

Definition audit_remove_weight (key : positive) : nat := 1 + 2 * audit_key_bits_weight key.

Definition audit_encoding_weight (emitted_bits : nat) : nat := S emitted_bits.

Definition audit_binary_weight (x y : Z) : nat := 1 + audit_z_bits x + audit_z_bits y.

Definition audit_multiply_weight (x y : Z) : nat := 1 + audit_z_bits x * audit_z_bits y.

Definition audit_divide_weight (x y : Z) : nat :=
  1 + (audit_z_bits x + audit_z_bits y) * (audit_z_bits x + audit_z_bits y).

Definition audit_shift_weight (x amount : Z) : nat :=
  1 + audit_z_bits x + Z.to_nat (Z.abs amount).

Definition audit_unary_conversion_weight (converted : nat) : nat := S converted.

(** Encode a signed operand in the natural-valued event payload. *)
Definition count_zencode (z : Z) : N :=
  match z with
  | Z0 => 0%N
  | Zpos p => N.double (N.pos p)
  | Zneg p => N.pred (N.double (N.pos p))
  end.

(** Recover the signed operand represented by an event payload. *)
Definition count_zdecode (n : N) : Z :=
  if N.even n then Z.of_N (N.div2 n)
  else (- Z.of_N (N.succ (N.div2 n)))%Z.

(** Record the two actual signed operands of an arithmetic source site. *)
Definition scalar_z (site : nat) (a b : Z) : audit_event unit :=
  AuditArithmetic site [count_zencode a; count_zencode b].

(** Work is additive for two consecutive source trace segments. *)
Theorem audit_work_app :
  forall Call (left right : audit_trace Call),
    audit_work (left ++ right) = audit_work left + audit_work right.
Proof.
  intros Call left right.
  apply List.length_app.
Qed.

(** Callback calls retain their chronological order across source trace segments. *)
Theorem audit_calls_app :
  forall Call (left right : audit_trace Call),
    audit_calls (left ++ right) = audit_calls left ++ audit_calls right.
Proof.
  intros Call left right.
  induction left as [| event rest IH].
  - reflexivity.
  - destruct event as [current operands | call | current operands | bit | current operands];
      cbn; rewrite IH; reflexivity.
Qed.

(** Key-bit count is additive across source trace segments. *)
Theorem audit_key_bits_app :
  forall Call (left right : audit_trace Call),
    audit_key_bits (left ++ right) = audit_key_bits left + audit_key_bits right.
Proof.
  intros Call left right.
  induction left as [| event rest IH].
  - reflexivity.
  - destruct event as [current operands | call | current operands | bit | current operands];
      cbn; rewrite IH; reflexivity.
Qed.

(** Case counts are additive across source trace segments. *)
Theorem audit_case_count_app :
  forall Call site (left right : audit_trace Call),
    audit_case_count site (left ++ right) =
      audit_case_count site left + audit_case_count site right.
Proof.
  intros Call site left right.
  induction left as [| event rest IH].
  - reflexivity.
  - destruct event as [current operands | call | current operands | bit | current operands];
      cbn; rewrite IH; try reflexivity.
    destruct (Nat.eqb site current); reflexivity.
Qed.

(** Construction counts are additive across source trace segments. *)
Theorem audit_construct_count_app :
  forall Call site (left right : audit_trace Call),
    audit_construct_count site (left ++ right) =
      audit_construct_count site left + audit_construct_count site right.
Proof.
  intros Call site left right.
  induction left as [| event rest IH].
  - reflexivity.
  - destruct event as [current operands | call | current operands | bit | current operands];
      cbn; rewrite IH; try reflexivity.
    destruct (Nat.eqb site current); reflexivity.
Qed.

(** Arithmetic frame counts are additive across source trace segments. *)
Theorem audit_arithmetic_count_app :
  forall Call site (left right : audit_trace Call),
    audit_arithmetic_count site (left ++ right) =
      audit_arithmetic_count site left + audit_arithmetic_count site right.
Proof.
  intros Call site left right.
  induction left as [| event rest IH].
  - reflexivity.
  - destruct event as [current operands | call | current operands | bit | current operands];
      cbn; rewrite IH; try reflexivity.
    destruct (Nat.eqb site current); reflexivity.
Qed.
