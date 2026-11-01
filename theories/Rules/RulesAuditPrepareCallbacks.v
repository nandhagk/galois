(** * Join preparation callback receipts

    Each actual predicate encoding is related to its own external source body.
    For example, a repeated predicate in two atoms retains two separate invocations.
    Builds on: RulesAuditNestedPrepare and RulesAuditMultiwayPrepare. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditJoinSyntax RulesAuditNestedPrepare RulesAuditMultiwayPrepare.
Import List.ListNotations.

(** An encoding frame retains the source body for its recorded operand and result. *)
Definition rules_predicate_frame_source {P B} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (frame : mat_frame) (bodies : list (list B)) :
  Prop :=
  match frame with
  | MatEncode _ _ _ _ => exists p code body,
      frame = MatEncode P E p code /\ bodies = [body] /\ source p code body
  | _ => bodies = []
  end.

(** Predicate callback bodies correspond in order to the recorded frames. *)
Definition rules_predicate_trace_source {P B} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (events : list mat_frame)
    (bodies : list (list (list B))) : Prop :=
  Forall2 (rules_predicate_frame_source E source) events bodies.

Definition rules_predicate_bodies_work {B} (weight : B -> nat) (bodies : list (list (list B))) :
  nat :=
  fold_right (fun group n => fold_right (fun body m =>
    fold_right (fun item total => weight item + total) 0 body + m) 0 group + n) 0 bodies.

Definition rules_predicate_input_budget {P} (bound : P -> nat) (atoms : list (atom P)) : nat :=
  fold_right (fun a n => bound (pred a) + n) 0 atoms.

(** Each predicate encoder has a source body bounded by its predicate allowance. *)
Definition rules_predicate_source_laws {P B} (E : encoding P)
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (bound : P -> nat) : Prop :=
  (forall p, exists body, source p (encode E p) body) /\
  (forall p code body, source p code body ->
    fold_right (fun item n => weight item + n) 0 body <= bound p).

(** Each nested preparation call has its own predicate-body receipt. *)
Definition rules_nested_prepare_source_statement : Prop :=
  forall P B (E : encoding P) relations atoms bound
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (price : P -> nat),
    rules_predicate_source_laws E source weight price ->
    let '(out, events) := rules_prepare_nested_full E relations atoms bound in
    exists bodies, rules_predicate_trace_source E source events bodies /\
      out = prepare_nested atoms bound (join_relation_rows E relations) /\
      mat_work events + rules_predicate_bodies_work weight bodies <=
        rules_nested_prepare_input_budget E relations atoms bound +
          rules_predicate_input_budget price atoms.

Definition rules_multiway_prepare_input_size {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (vars : list nat) (bound : FinSet.t nat)
    (atoms : list (atom P)) : nat :=
  rules_nested_prepare_input_size E relations atoms bound +
    fold_right (fun v n => 1 + v + n) 0 vars.

Definition rules_multiway_prepare_input_budget {P} (E : encoding P)
    (relations : Map.t P (list tuple)) (vars : list nat) (bound : FinSet.t nat)
    (atoms : list (atom P)) : nat :=
  (1000 * 1000 * 1000) * Nat.pow (rules_multiway_prepare_input_size E relations vars bound atoms)
    (18 + 2 * length vars).

(** The multiway allowance includes repeated per-variable predicate lookup occurrences. *)
Definition rules_multiway_prepare_source_statement : Prop :=
  forall P B (E : encoding P) relations vars bound atoms
    (source : P -> positive -> list B -> Prop) (weight : B -> nat) (price : P -> nat),
    rules_predicate_source_laws E source weight price ->
    let '(out, events) := rules_prepare_multiway_full E relations vars bound atoms in
    exists bodies, rules_predicate_trace_source E source events bodies /\
      out = prepare_multiway vars bound atoms (join_relation_rows E relations) /\
      mat_work events + rules_predicate_bodies_work weight bodies <=
        rules_multiway_prepare_input_budget E relations vars bound atoms +
          length vars * rules_predicate_input_budget price atoms.
