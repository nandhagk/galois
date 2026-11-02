(** * Stratification trace observations

    These examples observe repeated rules in the counted stratifier.
    For example, a duplicate empty-body rule adds work without adding a predicate.
    Builds on: RulesAuditMaterializeStratify. *)

From Stdlib Require Import List NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesAuditMaterializePrelude
  RulesAuditMaterializeStratify.
Import List.ListNotations.

Definition repeated_rule : rule unit := Rule (Atom tt []) [].

Definition repeated_program (n : nat) : program unit :=
  Program unit_encoding (fun _ => 0) (repeat repeated_rule n).

(** Duplicate empty rules preserve the observed operand width in these runs. *)
Example repeated_rules_width :
  mat_width (snd (mat_stratify (repeated_program 1))) =
  mat_width (snd (mat_stratify (repeated_program 2))).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The second copy increases the observed trace work. *)
Example repeated_rules_work :
  Nat.ltb (mat_work (snd (mat_stratify (repeated_program 1))))
  (mat_work (snd (mat_stratify (repeated_program 2)))) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The singleton program's trace has a small maximum operand. *)
Example repeated_rules_first_width :
  mat_width (snd (mat_stratify (repeated_program 1))) = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The first run has a nonzero counted work total. *)
Example repeated_rules_first_work :
  mat_work (snd (mat_stratify (repeated_program 1))) = N.to_nat 5394%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The second run accumulates work from the extra rule. *)
Example repeated_rules_second_work :
  mat_work (snd (mat_stratify (repeated_program 2))) = N.to_nat 7724%N.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** A third copy keeps the operand width and adds the same work increment. *)
Example repeated_rules_third_observation :
  mat_width (snd (mat_stratify (repeated_program 3))) = 3 /\
  mat_work (snd (mat_stratify (repeated_program 3))) = N.to_nat 10054%N.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** The accepted singleton program returns its actual level and bound. *)
Example repeated_rules_accept :
  match fst (mat_stratify (repeated_program 2)) with
  | Some context =>
    count (mat_native_levels context) = 1 /\
      level (mat_native_levels context) tt = 0
  | None =>
    False
  end.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

Definition negative_self : program unit :=
  Program unit_encoding (fun _ => 0) [Rule (Atom tt []) [LNeg (Atom tt [])]].

(** A negative self-dependency is rejected. *)
Example negative_self_rejected : fst (mat_stratify negative_self) = None.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition two_levels : program bool :=
  Program bool_encoding (fun _ => 0)
    [Rule (Atom true []) [LNeg (Atom false [])]].

(** A negative dependency produces two distinct predicate levels. *)
Example two_levels_accept :
  match fst (mat_stratify two_levels) with
  | Some context =>
    count (mat_native_levels context) = 2 /\
      level (mat_native_levels context) false = 0 /\
      level (mat_native_levels context) true = 1
  | None =>
    False
  end.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

Definition empty_program : program unit := Program unit_encoding (fun _ => 0) [].

(** The empty program succeeds with the native empty level bound. *)
Example empty_program_accept :
  match fst (mat_stratify empty_program) with
  | Some context =>
    count (mat_native_levels context) = 1 /\
      level (mat_native_levels context) tt = 0
  | None =>
    False
  end.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

Definition malformed_program : program unit :=
  Program unit_encoding (fun _ => 2) [Rule (Atom tt []) []].

(** Stratification retains its arity-independent behavior on malformed rules. *)
Example malformed_program_accept :
  match fst (mat_stratify malformed_program) with
  | Some context =>
    count (mat_native_levels context) = 1 /\
      level (mat_native_levels context) tt = 0
  | None =>
    False
  end.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** Completed states still execute each of the remaining counted ticks. *)
Example done_tail_calls :
  let '(state, events) :=
    mat_niter 3%N (mat_stratify_tick (repeated_program 1)) (Map.empty, false) in
  snd state = true /\
  length (filter (fun frame =>
    match frame with
    | MatBlock 80 =>
      true
    | _ =>
      false
    end) events) = 3.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** An empty edge pass marks the initial state done in the first round. *)
Example final_empty_round :
  fst (mat_program_edges (repeated_program 1)) = [] /\
  fst (mat_stratify_tick (repeated_program 1) (Map.empty, false)) = (Map.empty, true).
Proof.
  vm_compute.
  split; reflexivity.
Qed.
