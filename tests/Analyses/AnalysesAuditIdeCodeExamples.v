(** * Finite observations of the IDE source producers

    These examples exercise compatibility, indexed rule generation, finite tables and queries.
    For example, a mismatched edge weight makes the compatibility check return false.
    Builds on: AnalysesAuditIde, AnalysesInterprocedural and CollectionsEncoding. *)

From Stdlib Require Import Bool List.
From Galois.Analyses Require Import AnalysesAuditIde AnalysesInterprocedural.
From Galois.Collections Require Import CollectionsEncoding.
Import List.ListNotations.

Definition same_weight (_ : ip_edge bool unit unit) (_ _ : option unit) : bool := false.

Definition changed_weight (_ : ip_edge bool unit unit) (_ _ : option unit) : bool := true.

Example ide_compatibility_distinguishes_weights :
  (audit_ide_finite_compatible_check audit_ide_selector_client audit_ide_selector_registry
    same_weight,
   audit_ide_finite_compatible_check audit_ide_selector_client audit_ide_selector_registry
    changed_weight) = (true, false).
Proof.
  reflexivity.
Qed.

Example ide_generated_nonempty_rules :
  length (audit_ide_ground_rules unit_encoding audit_ide_selector_registry
    (ide_graph audit_ide_selector_client) same_weight (false, None)) = 4.
Proof.
  reflexivity.
Qed.

Example ide_finite_vectors_nonempty :
  exact_value (ide_vectors_counted [false; true] [false; true]) =
    [[false; false]; [false; true]; [true; false]; [true; true]].
Proof.
  reflexivity.
Qed.

Example ide_generated_solver_reaches_start :
  let summary := ide_registry_solve bool_encoding unit_encoding unit_encoding
    (ide_lattice audit_ide_selector_client) audit_ide_selector_registry
    (ide_graph audit_ide_selector_client) same_weight false None in
  (ide_registry_query bool_encoding unit_encoding audit_ide_selector_registry summary false
    false None,
   ide_registry_query bool_encoding unit_encoding audit_ide_selector_registry summary false
    true None) = (Some false, None).
Proof.
  reflexivity.
Qed.

(** This graph is the [simple_matched] client from the pre-card ANA-8b tests. *)
Definition baseline_matched : ip_problem nat nat unit :=
  IpProblem [0; 1; 2] [0] []
    [IpEdge 0 1 (IpCall 0) [(None, None)];
     IpEdge 1 2 (IpReturn 0) [(None, None)]].

Example ide_baseline_matched_rules :
  length (audit_ide_ground_rules nat_encoding audit_ide_nat_registry baseline_matched
    (fun _ _ _ => false) (0, None)) = 17.
Proof.
  reflexivity.
Qed.
