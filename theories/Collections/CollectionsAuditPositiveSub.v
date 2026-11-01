(** * Positive subtraction source model

    Count the binary subtraction and borrow paths used by direct IDF priorities.
    For example, subtracting one from an even value follows the predecessor carry chain.
    Builds on: Stdlib positive arithmetic. *)

From Stdlib Require Import List PArith.
Import List.ListNotations.

(** Events retain each actual subtraction or predecessor operand. *)
Inductive audit_idf_sub_event : Type :=
  | IdfSubFrame : bool -> positive -> positive -> audit_idf_sub_event
  | IdfSubPredFrame : positive -> audit_idf_sub_event
  | IdfSubFinish : Pos.mask -> positive -> audit_idf_sub_event.

(** The predecessor-of-double helper exposes its complete low-bit borrow chain. *)
Fixpoint audit_idf_pred_double (value : positive) : positive * list audit_idf_sub_event :=
  match value with
  | xH => (xH, [IdfSubPredFrame value])
  | xI p => (xI (xO p), [IdfSubPredFrame value])
  | xO p => let '(result, events) := audit_idf_pred_double p in
      (xI result, IdfSubPredFrame value :: events)
  end.

(** A mask for twice a positive predecessor includes the actual borrow helper when needed. *)
Definition audit_idf_double_pred (value : positive) : Pos.mask * list audit_idf_sub_event :=
  match value with
  | xH => (Pos.IsNul, [IdfSubPredFrame value])
  | xI p => (Pos.IsPos (xO (xO p)), [IdfSubPredFrame value])
  | xO p => let '(result, events) := audit_idf_pred_double p in
      (Pos.IsPos (xO result), IdfSubPredFrame value :: events)
  end.

(** Subtraction carries a single borrow bit and records each actual operand pair. *)
Fixpoint audit_idf_sub_mask (borrow : bool) (left right : positive) {struct right}
    : Pos.mask * list audit_idf_sub_event :=
  let here := IdfSubFrame borrow left right in
  match left, right with
  | xH, xH => (if borrow then Pos.IsNeg else Pos.IsNul, [here])
  | xH, _ => (Pos.IsNeg, [here])
  | xI p, xH =>
      if borrow then let '(result, events) := audit_idf_pred_double p in
        (Pos.IsPos result, here :: events)
      else (Pos.IsPos (xO p), [here])
  | xO p, xH =>
      if borrow then let '(result, events) := audit_idf_double_pred p in (result, here :: events)
      else let '(result, events) := audit_idf_pred_double p in (Pos.IsPos result, here :: events)
  | xI p, xI q =>
      let '(result, events) := audit_idf_sub_mask borrow p q in
      (if borrow then Pos.succ_double_mask result else Pos.double_mask result, here :: events)
  | xI p, xO q =>
      let '(result, events) := audit_idf_sub_mask false p q in
      (if borrow then Pos.double_mask result else Pos.succ_double_mask result, here :: events)
  | xO p, xI q =>
      let '(result, events) := audit_idf_sub_mask true p q in
      (if borrow then Pos.double_mask result else Pos.succ_double_mask result, here :: events)
  | xO p, xO q =>
      let '(result, events) := audit_idf_sub_mask borrow p q in
      (if borrow then Pos.succ_double_mask result else Pos.double_mask result, here :: events)
  end.

(** The public positive subtraction clamps nonpositive differences to one. *)
Definition audit_idf_sub_counted (left right : positive) : positive * list audit_idf_sub_event :=
  let '(mask, events) := audit_idf_sub_mask false left right in
  let result :=
    match mask with
    | Pos.IsPos value => value
    | _ => 1%positive
    end in
  (result, events ++ [IdfSubFinish mask result]).

(** Input widths bound all subtraction and borrow frames and trace construction. *)
Definition audit_idf_sub_budget (left right : positive) : nat :=
  64 * (S (Pos.size_nat left + Pos.size_nat right)) * (S (Pos.size_nat left + Pos.size_nat right)).

(** The source model returns exactly the Stdlib result with input-derived work. *)
Definition audit_idf_sub_source_statement : Prop :=
  forall left right,
    let '(result, events) := audit_idf_sub_counted left right in
    result = Pos.sub left right /\ 16 * S (length events) <= audit_idf_sub_budget left right.
