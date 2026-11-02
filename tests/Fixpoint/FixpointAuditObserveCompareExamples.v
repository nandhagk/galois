(** * Observation comparison and boundary examples

    These examples inspect strict comparison tails, selective expiry checks and forward calls.
    For example, a failed left trie branch skips the parent and right-hand values.
    Builds on: FixpointAuditObserveForwardAdequacy and CollectionsAuditEncodingAdequacy. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsAuditEncoding
  CollectionsAuditEncodingAdequacy CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointObserve FixpointAuditIndex FixpointAuditObserveCompare
  FixpointAuditObserveExpireCheck FixpointAuditObserveForward FixpointAuditObserveForwardAdequacy.
From Galois.Tests.Fixpoint Require Import FixpointFIX1 FixpointAuditModelsExamples
  FixpointAuditIndexExamples.
Import List.ListNotations.

(** * Strict comparisons and selective trie checks *)

(** An early match retains the later unsuccessful comparison with its original operands. *)
Example fx_compare_strict_tail :
  fx_observe_exists_key nat_encoding 1 [1; 2] =
    (true, [FxObserveCompareCase; FxObserveCompare 1 1 2%positive 2%positive true;
      FxObserveCompareCase; FxObserveCompare 1 2 2%positive 3%positive false;
      FxObserveCompareCase]).
Proof.
  vm_compute; reflexivity.
Qed.

(** Duplicate input and a missing element retain the source result in both directions. *)
Example fx_compare_duplicates_and_missing :
  fst (fx_observe_nodup nat_encoding [1; 1; 2]) = false /\
  fst (fx_observe_seteq nat_encoding [1; 1] [1; 2]) = false /\
  fst (fx_observe_seteq nat_encoding [1; 2; 1] [2; 1]) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition fx_expire_branch : Trie.ne (nat * list nat) :=
  Trie.N111 (Trie.N010 (1, [1])) (2, [2]) (Trie.N010 (3, [3])).

(** A failed left comparison prevents the parent and right comparisons from appearing. *)
Example fx_expire_left_failure :
  let '(out, events) := fx_expire_check_ne nat_encoding fx_expire_branch Trie.Empty in
  out = false /\ length events = 3.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Empty values match an absent binding, allowing the traversal to reach its right child. *)
Example fx_expire_left_success_right_failure :
  let first := Trie.N101 (Trie.N010 (1, [])) (Trie.N010 (2, [2])) in
  let '(out, events) := fx_expire_check_ne nat_encoding first Trie.Empty in
  out = false /\ length events = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Forward calls with real recursive encoding *)

(** The two component orders distinguish a legal earlier dependency from a later one. *)
Example fx_forward_order_boundaries :
  fst (fx_observe_forward_run fx_models_callbacks [false; true] [[0]; [1]]) = true /\
  fst (fx_observe_forward_run fx_models_callbacks [false; true] [[1]; [0]]) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Actual boundary events contain the counted encoder bodies and the callback results. *)
Example fx_forward_source_receipts :
  Forall (fx_observe_forward_event_source fx_index_fixture_source)
    (snd (fx_observe_forward_run fx_models_callbacks [false; true] [[1]; [0]])).
Proof.
  vm_compute; repeat constructor; reflexivity.
Qed.

Definition fx_forward_encoder_receipts
    (events : list (fx_observe_forward_event nat bool (audit_nat_encoding_event + unit))) :=
  flat_map (fun event =>
    match event with
    | FxForwardSet entries => flat_map (fun entry =>
        match entry with
        | AuditSetAdd x code _ _ body _ => [(x, code, body)]
        | AuditSetMem x code _ _ body _ => [(x, code, body)]
        | AuditSetRemove x code _ _ body _ => [(x, code, body)]
        | AuditSetFold _ _ => []
        end) entries
    | _ => []
    end) events.

(** The observed forward trace contains the actual nonempty encoder trace for key one. *)
Example fx_forward_actual_encoder_receipt :
  In (1, 2%positive, map inl (snd (audit_nat_encode 1)))
    (fx_forward_encoder_receipts
      (snd (fx_observe_forward_run fx_models_callbacks [false; true] [[1]; [0]]))) /\
  snd (audit_nat_encode 1) <> [].
Proof.
  vm_compute; split; [auto | discriminate].
Qed.

(** The source-indexed natural encoder run agrees with the exact returned recursive trace. *)
Example fx_forward_encoder_source_run :
  exists work, audit_nat_encode_run 1 (fst (audit_nat_encode 1)) (snd (audit_nat_encode 1)) work.
Proof.
  destruct (audit_nat_encode_run_total 1) as [out [events [work Hrun]]].
  pose proof (audit_nat_encode_run_correct 1 out events work Hrun) as [_ [Hsame _]].
  destruct (audit_nat_encode 1) as [code body].
  cbn in Hsame |- *; inversion Hsame; subst; exists work; exact Hrun.
Qed.

(** The full theorem applies to the sample's actual callback values and finite budget. *)
Example fx_forward_source_bound :
  let '(out, events) := fx_observe_forward_run fx_models_callbacks [false; true] [[1]; [0]] in
  Forall (fx_observe_forward_event_source fx_index_fixture_source) events /\
  out = observation_forward_check nat_encoding sample_system sample_static [[1]; [0]] /\
  fx_observe_forward_work fx_models_budget events <=
    2 + 2 * length [[1]; [0]] +
      fx_observe_forward_budget nat_encoding sample_system sample_static fx_models_budget
        [[1]; [0]].
Proof.
  apply (fx_observe_forward_source nat bool bool _ nat_encoding sample_system sample_static
    fx_models_callbacks fx_models_budget fx_index_fixture_source [[1]; [0]]
    fx_index_fixture_erases fx_index_fixture_bounded).
  - intro x; unfold fx_index_fixture_source; destruct (fxi_encode fx_models_callbacks x)
      eqn:Hencode; exact Hencode.
  - intro c; destruct c; reflexivity.
  - intro c; destruct c; reflexivity.
Qed.

Definition fx_forward_target_calls
    (events : list (fx_observe_forward_event nat bool (audit_nat_encoding_event + unit))) :=
  flat_map (fun event =>
    match event with
    | FxForwardIndex calls => flat_map (fun call =>
        match call with
        | FxiTarget c _ _ => [c]
        | _ => []
        end) calls
    | _ => []
    end) events.

Definition fx_forward_deps_calls
    (events : list (fx_observe_forward_event nat bool (audit_nat_encoding_event + unit))) :=
  flat_map (fun event =>
    match event with
    | FxForwardIndex calls => flat_map (fun call =>
        match call with
        | FxiDeps c _ _ => [c]
        | _ => []
        end) calls
    | _ => []
    end) events.

(** A failed dependency scan still checks the next target, whose dependencies are skipped. *)
Example fx_forward_failed_tail_and_skipped_deps :
  let '(out, events) := fx_forward_boundary fx_models_callbacks [true; false] [1] [[0]] in
  out = false /\ fx_forward_target_calls events = [true; false] /\
    fx_forward_deps_calls events = [true].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The failed first map direction still executes the reverse direction's empty-trie frame. *)
Example fx_expire_both_directions :
  let first := Trie.Nodes (Trie.N010 (1, [1])) in
  let '(out, events) := fx_expire_check nat_encoding first Trie.Empty in
  out = false /\ length events = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.
