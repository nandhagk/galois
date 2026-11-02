(** * Observation expiration examples

    These examples inspect last-reader choices, duplicate inputs and actual callback bodies.
    For example, a later reader keeps a predecessor through the later component boundary.
    Builds on: FixpointAuditObserveExpiryAdequacy and the FIX-6 client. *)

From Stdlib Require Import List Bool Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointObserve
  FixpointAuditWorklistCallbacks FixpointAuditObserveExpiry FixpointAuditObserveExpiryAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX6 FixpointAuditNestedExamples
  FixpointAuditObserveCheckExamples.
Import List.ListNotations.

(** * Last readers and persistent expiration buckets *)

(** The predecessor expires at the successor cycle and an unused value has no last reader. *)
Example fx_expiry_last_reader_boundaries :
  let order := observation_components observation_test_plan in
  fst (fx_observe_last_reader nat_encoding observation_test_system observation_test_index order 0) =
    Some 1 /\
  fst (fx_observe_last_reader nat_encoding observation_test_system observation_test_index order
    99) =
    None /\
  fst (fx_observe_last_reader nat_encoding observation_test_system observation_test_index [] 0) =
    None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Duplicate unknown occurrences are retained in the selected persistent expiration bucket. *)
Example fx_expiry_duplicate_occurrences :
  let '(out, _) := fx_observe_expiry_fold nat_encoding fx_nested_client_cycle fx_check_index
    [[3]] [3; 3] in
  Map.get nat_encoding 3 out = Some [3; 3] /\ Map.get nat_encoding 4 out = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition fx_expiry_targets (events : list (fx_observe_expiry_event nat nat)) :=
  flat_map (fun event =>
    match event with
    | FxExpiryTarget c x => [(c, x)]
    | _ => []
    end) events.

(** The chosen last reader records the real target callback from its reader bucket. *)
Example fx_expiry_actual_target_call :
  let '(_, events) := fx_observe_last_reader nat_encoding fx_nested_client_cycle fx_check_index
    [[3]] 3 in
  fx_expiry_targets events = [(3, 3)] /\
  fx_source_target fx_nested_test_source 3 (System.target fx_nested_client_cycle 3) [inr tt] /\
  fx_source_encode_x fx_nested_test_source 3 (fst (fx_nested_test_encode 3))
    (snd (fx_nested_test_encode 3)) /\
  fx_one_body_work fx_nested_test_weight (snd (fx_nested_test_encode 3)) = 16.
Proof.
  repeat split; try reflexivity; apply fx_nested_test_encoder_source_receipt.
Qed.

(** The same duplicate fold has source receipts and its input-derived bound. *)
Example fx_expiry_source_client :
  let '(out, events) := fx_observe_expiry_fold nat_encoding fx_nested_client_cycle fx_check_index
    [[3]] [3; 3] in
  exists groups, Forall2 (fx_observe_expiry_event_source fx_nested_test_source) events groups /\
    out = fold_right (fun x expiration =>
      match observation_last_reader nat_encoding fx_nested_client_cycle fx_check_index [[3]] x with
      | Some h => index_push nat_encoding x h expiration
      | None => expiration
      end) Map.empty [3; 3] /\
    fx_observe_expiry_work events + fx_declared_body_work fx_nested_test_weight groups <=
      fx_observe_expiry_fold_budget nat_encoding fx_nested_client_cycle fx_check_index [[3]]
        [3; 3] +
      fold_right (fun event n => fx_observe_expiry_external_budget fx_nested_test_budget event + n)
        0 events.
Proof.
  apply (fx_observe_expiry_fold_source nat nat _ _ nat_encoding fx_nested_client_cycle
    fx_check_index
    fx_nested_test_source fx_nested_test_budget [[3]] [3; 3] fx_check_expiry_laws).
Qed.

(** A later matching component suppresses the earlier component's reader scan. *)
Example fx_expiry_later_match_skips_earlier :
  let '(last, events) := fx_observe_last_reader nat_encoding fx_nested_client_cycle fx_check_index
    [[3]; []; [3]] 3 in
  last = Some 3 /\ fx_expiry_targets events = [(3, 3)].
Proof.
  vm_compute; split; reflexivity.
Qed.

Lemma fx_expiry_receipt_member X C A B (source : fx_declared_callback_source X C A B)
    events groups event :
  Forall2 (fx_observe_expiry_event_source source) events groups -> In event events ->
  exists group, In group groups /\ fx_observe_expiry_event_source source event group.
Proof.
  intros Hreceipts; induction Hreceipts as [|head group rest groups Hhead Htail IH]; intro Hin.
  - contradiction.
  - cbn [In] in Hin; destruct Hin as [Heq | Hin].
    + subst head; exists group; split; [left; reflexivity | exact Hhead].
    + destruct (IH Hin) as [found [Hfound Hsource]].
      exists found; split; [right; exact Hfound | exact Hsource].
Qed.

(** The fold's actual target event has its own matching target body in the theorem's receipts. *)
Example fx_expiry_reached_target_receipt :
  let '(_, events) := fx_observe_expiry_fold nat_encoding fx_nested_client_cycle fx_check_index
    [[3]] [3; 3] in
  exists groups group,
    Forall2 (fx_observe_expiry_event_source fx_nested_test_source) events groups /\
    In (FxExpiryTarget 3 3) events /\ In group groups /\ group = [[inr tt]].
Proof.
  pose proof fx_expiry_source_client as Hsource.
  destruct (fx_observe_expiry_fold nat_encoding fx_nested_client_cycle fx_check_index [[3]] [3; 3])
    as [out events] eqn:Hrun.
  destruct Hsource as [groups [Hgroups _]].
  assert (Hin : In (FxExpiryTarget 3 3) events).
  { assert (Hevents : events = snd (fx_observe_expiry_fold nat_encoding fx_nested_client_cycle
      fx_check_index [[3]] [3; 3])) by (rewrite Hrun; reflexivity).
    rewrite Hevents; vm_compute; repeat (first [left; reflexivity | right]). }
  destruct (fx_expiry_receipt_member nat nat _ _ fx_nested_test_source events groups
    (FxExpiryTarget 3 3) Hgroups Hin) as [group [Hgroup Hsource]].
  cbn [fx_observe_expiry_event_source fx_nested_test_source fx_source_target] in Hsource.
  destruct Hsource as [body [-> [_ ->]]].
  exists groups, [[inr tt]]; repeat split; assumption.
Qed.
