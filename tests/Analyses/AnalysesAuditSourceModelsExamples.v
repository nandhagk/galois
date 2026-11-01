(** * Finite observations of shared exact source models

    These examples compute retained values, events, and external bodies.
    For example, a true disjunction retains the callback's two frames.
    Builds on: AnalysesAuditSource. *)

From Stdlib Require Import Bool List.
From Galois.Analyses Require Import AnalysesAuditSource.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
Import List.ListNotations.

Example external_true_receipt :
  let run := exact_external_call audit_bool_or_adapter (true, false) (fun b => b) in
  (exact_value run, exact_bodies run) =
    (true, [(true, [ExternalCase 1; ExternalReturn])]).
Proof.
  reflexivity.
Qed.

Example external_false_receipt :
  let run := exact_external_call audit_bool_or_adapter (false, false) (fun b => b) in
  (exact_value run, exact_bodies run) =
    (false, [(false, [ExternalCase 0; ExternalReturn])]).
Proof.
  reflexivity.
Qed.

Example append_nonempty :
  exact_value (@exact_append unit nat 3 [1; 2] [3]) = [1; 2; 3].
Proof.
  reflexivity.
Qed.

Example filter_boundary :
  exact_value (@exact_filter unit nat 0 (fun n => exact_return 0 (Nat.even n)) [1; 2; 3]) = [2].
Proof.
  reflexivity.
Qed.

Example external_call_work :
  exact_units (exact_external_call audit_bool_or_adapter (false, true) (fun b => b)) = 192.
Proof.
  reflexivity.
Qed.

Example external_bind_preserves_order :
  let first := exact_external_call audit_bool_or_adapter (false, false) (fun b => b) in
  let run := exact_bind 7 first (fun _ =>
    exact_external_call audit_bool_or_adapter (true, false) (fun b => b)) in
  exact_bodies run =
    [(false, [ExternalCase 0; ExternalReturn]); (true, [ExternalCase 1; ExternalReturn])].
Proof.
  reflexivity.
Qed.

Example append_empty_boundary :
  exact_value (@exact_append unit nat 3 [] [3]) = [3].
Proof.
  reflexivity.
Qed.

Example counted_map_present_and_absent :
  let table := Map.set nat_encoding 2 9 Map.empty in
  let run key := exact_get (@id (exact_map_call nat nat)) nat_encoding (fun _ => 0) key table in
  (exact_value (run 2), exact_value (run 3), length (exact_events (run 2))) =
    (Some 9, None, 3).
Proof.
  reflexivity.
Qed.
