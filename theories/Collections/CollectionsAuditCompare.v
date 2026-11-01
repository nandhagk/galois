(** * Counted positive ordering comparisons

    The counted clauses follow the pinned [Pos.compare_cont] source and retain the
    accumulator, operands and returned comparison at every recursive frame.  For
    example, comparing two differently tagged nonterminal bits still recurses.
    Builds on: the standard positive-number implementation. *)

From Stdlib Require Import List PArith.
Import List.ListNotations.

(** One event records an actual comparison frame and its result. *)
Inductive audit_positive_compare_event : Type :=
  | AuditPositiveCompare (acc : comparison) (left right : positive)
      (result : comparison).

(** [Pos.compare_cont] recurses whenever both inputs are nonterminal. *)
Fixpoint audit_positive_compare_cont (acc : comparison) (left right : positive)
    {struct right} : comparison * list audit_positive_compare_event :=
  match left, right with
  | xI l, xI r | xO l, xO r =>
      let '(result, events) := audit_positive_compare_cont acc l r in
      (result, AuditPositiveCompare acc left right result :: events)
  | xI l, xO r =>
      let '(result, events) := audit_positive_compare_cont Gt l r in
      (result, AuditPositiveCompare acc left right result :: events)
  | xO l, xI r =>
      let '(result, events) := audit_positive_compare_cont Lt l r in
      (result, AuditPositiveCompare acc left right result :: events)
  | xH, xH => (acc, [AuditPositiveCompare acc left right acc])
  | xH, _ => (Lt, [AuditPositiveCompare acc left right Lt])
  | _, xH => (Gt, [AuditPositiveCompare acc left right Gt])
  end.

(** The public ordering wrappers inspect the returned comparison once. *)
Definition audit_positive_compare (left right : positive)
    : comparison * list audit_positive_compare_event :=
  audit_positive_compare_cont Eq left right.

Definition audit_positive_ltb (left right : positive)
    : bool * list audit_positive_compare_event :=
  let '(result, events) := audit_positive_compare left right in
  (match result with
  | Lt => true
  | _ => false
  end, events).

Definition audit_positive_leb (left right : positive)
    : bool * list audit_positive_compare_event :=
  let '(result, events) := audit_positive_compare left right in
  (match result with
  | Gt => false
  | _ => true
  end, events).

(** Two selected source inspection frames per recursive comparison event. *)
Definition audit_positive_compare_source_work
    (events : list audit_positive_compare_event) : nat :=
  2 * length events.

(** Ordering wrappers add their fixed entry and comparison-result branches. *)
Definition audit_positive_order_source_work
    (events : list audit_positive_compare_event) : nat :=
  4 + audit_positive_compare_source_work events.

(** The counted comparison agrees with [Pos.compare_cont] and bounds its source work. *)
Definition audit_positive_compare_cont_statement : Prop :=
  forall acc left right,
    let '(result, events) := audit_positive_compare_cont acc left right in
    result = Pos.compare_cont acc left right /\
    audit_positive_compare_source_work events <=
      2 * Nat.min (Pos.size_nat left) (Pos.size_nat right).

(** The counted positive comparison returns the standard comparison result. *)
Definition audit_positive_compare_statement : Prop :=
  forall left right,
    fst (audit_positive_compare left right) = Pos.compare left right.

(** Both counted ordering tests return the standard result within their source-work bounds. *)
Definition audit_positive_order_statement : Prop :=
  forall left right,
    fst (audit_positive_ltb left right) = Pos.ltb left right /\
    fst (audit_positive_leb left right) = Pos.leb left right /\
    audit_positive_order_source_work (snd (audit_positive_ltb left right)) <=
      4 + 2 * Nat.min (Pos.size_nat left) (Pos.size_nat right) /\
    audit_positive_order_source_work (snd (audit_positive_leb left right)) <=
      4 + 2 * Nat.min (Pos.size_nat left) (Pos.size_nat right).

Example audit_positive_compare_different_tags :
  (fst (audit_positive_ltb 2%positive 3%positive),
   length (snd (audit_positive_compare 2%positive 3%positive))) = (true, 2).
Proof.
  reflexivity.
Qed.
