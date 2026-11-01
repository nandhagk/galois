(** * Binary natural addition source model

    Record positive addition, carry and successor calls used by direct IDF counters.
    For example, adding one to an odd value follows its successor carry chain.
    Builds on: the collection positive successor source model. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsAuditEncoding.
Import List.ListNotations.

(** Events retain actual operands and successor source frames. *)
Inductive audit_idf_nadd_event : Type :=
  | IdfNaddFrame : bool -> positive -> positive -> audit_idf_nadd_event
  | IdfNaddSucc : audit_nat_encoding_event -> audit_idf_nadd_event
  | IdfNaddZero : N -> N -> audit_idf_nadd_event.

(** Addition makes its one-bit carry explicit and uses the actual successor helper. *)
Fixpoint audit_idf_positive_add (carry : bool) (left right : positive) {struct left}
    : positive * list audit_idf_nadd_event :=
  let here := IdfNaddFrame carry left right in
  match left, right with
  | xH, xH => (if carry then 3%positive else 2%positive, [here])
  | xH, xO q =>
      if carry then let '(n, events) := audit_positive_succ q in
        (xO n, here :: map IdfNaddSucc events)
      else (xI q, [here])
  | xH, xI q =>
      let '(n, events) := audit_positive_succ q in
      (if carry then xI n else xO n, here :: map IdfNaddSucc events)
  | xO p, xH =>
      if carry then let '(n, events) := audit_positive_succ p in
        (xO n, here :: map IdfNaddSucc events)
      else (xI p, [here])
  | xI p, xH =>
      let '(n, events) := audit_positive_succ p in
      (if carry then xI n else xO n, here :: map IdfNaddSucc events)
  | xO p, xO q =>
      let '(n, events) := audit_idf_positive_add false p q in
      (if carry then xI n else xO n, here :: events)
  | xO p, xI q =>
      let '(n, events) := audit_idf_positive_add carry p q in
      (if carry then xO n else xI n, here :: events)
  | xI p, xO q =>
      let '(n, events) := audit_idf_positive_add carry p q in
      (if carry then xO n else xI n, here :: events)
  | xI p, xI q =>
      let '(n, events) := audit_idf_positive_add true p q in
      (if carry then xI n else xO n, here :: events)
  end.

(** The natural wrapper takes either zero branch without positive addition. *)
Definition audit_idf_nadd_counted (left right : N) : N * list audit_idf_nadd_event :=
  match left, right with
  | N0, _ => (right, [IdfNaddZero left right])
  | _, N0 => (left, [IdfNaddZero left right])
  | Npos a, Npos b => let '(result, events) := audit_idf_positive_add false a b in
      (Npos result, events)
  end.

(** Input widths bound all carry and successor frames. *)
Definition audit_idf_nadd_width (value : N) : nat :=
  match value with
  | N0 => 0
  | Npos p => Pos.size_nat p
  end.

(** The whole source-work allowance depends only on the operands. *)
Definition audit_idf_nadd_budget (left right : N) : nat :=
  64 * S (audit_idf_nadd_width left + audit_idf_nadd_width right) *
    S (audit_idf_nadd_width left + audit_idf_nadd_width right).

(** The source model has the exact Stdlib result and an input-derived bound. *)
Definition audit_idf_nadd_source_statement : Prop :=
  forall left right,
    let '(result, events) := audit_idf_nadd_counted left right in
    result = N.add left right /\ 16 * S (length events) <= audit_idf_nadd_budget left right.
