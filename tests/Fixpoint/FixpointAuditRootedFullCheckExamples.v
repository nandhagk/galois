(** * Strict checker receipt examples

    These examples observe the order and operands of actual counted checker calls.
    For example, a failed first constraint still leaves the second constraint's read and side.
    Builds on: the nonempty rooted checker client. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsAuditCost
  CollectionsAuditEncoding CollectionsAuditEncodingAdequacy.
From Galois.Order Require Import OrderBasic.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck
  FixpointAuditWorklist FixpointAuditNarrowCheck FixpointAuditCheckCallbacks.
From Galois.Tests.Fixpoint Require Import FixpointAuditRootedCheckClient.
Import List.ListNotations.

(** * Exact callback observations *)

Definition rooted_query_calls (events : audit_trace (fx_declared_call nat nat bool)) :
    list (nat * nat * nat) :=
  flat_map (fun (event : audit_event (fx_declared_call nat nat bool)) => match event with
    | AuditCall (FxGet x code _ _ _) => [(0, x, Pos.to_nat code)]
    | AuditCall (FxContinuation x value _ _) => [(1, x, (if value then 1 else 0))]
    | _ => []
    end) events.

Definition rooted_calls (events : list (fx_fullcheck_event nat nat bool)) :
    list (nat * nat * nat) :=
  flat_map (fun event => match event with
    | FfcRhs c _ => [(2, c, 0)]
    | FfcTarget c x => [(3, c, x)]
    | FfcLeb a b _ => [(4, (if a then 1 else 0), (if b then 1 else 0))]
    | FfcQuery body => rooted_query_calls body
    | _ => []
    end) events.

Definition rooted_all_true : assignment nat bool :=
  Map.set nat_encoding 2 true (Map.set nat_encoding 1 true (Map.set nat_encoding 0 true Map.empty)).

(** Empty constraints accept, including with an empty assignment. *)
Example rooted_empty_system :
  fst (fx_fullcheck_counted nat_encoding bool_lattice
    (@System.Make nat nat bool [] (fun c => c) (fun _ => Query.Ret true)) Map.empty) = true.
Proof.
  reflexivity.
Qed.

(** A failed first constraint does not skip the later continuation or its side lookup. *)
Example rooted_false_first_calls :
  let '(out, events) := fx_fullcheck_counted nat_encoding bool_lattice rooted_system Map.empty in
  out = false /\ rooted_calls events =
    [(2, 0, 0); (3, 0, 0); (0, 0, 1); (4, 1, 0);
     (2, 1, 0); (0, 1, 2); (1, 1, 0); (3, 1, 1); (0, 1, 2); (4, 0, 0);
     (0, 2, 3); (4, 0, 0)].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A nonempty assignment accepts the same two constraints. *)
Example rooted_nonempty_accepts :
  fst (fx_fullcheck_counted nat_encoding bool_lattice rooted_system rooted_all_true) = true /\
  check_post bool_lattice rooted_system (lookup nat_encoding bool_lattice rooted_all_true) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The concrete read of key one has the genuine recursive encoder receipt. *)
Example rooted_key_one_receipt :
  rooted_query_calls (snd (@fx_model_lookup nat nat bool nat_encoding bool_lattice Map.empty 1)) =
    [(0, 1, 2)] /\
  exists work, audit_nat_encode_run 1 (fst (audit_nat_encode 1)) (snd (audit_nat_encode 1)) work /\
    snd (audit_nat_encode 1) =
      [AuditNatFrame 1; AuditNatFrame 0; AuditPositiveSuccFrame 1%positive 2%positive].
Proof.
  split; [reflexivity|].
  destruct (audit_nat_encode_run_total 1) as [code [body [work Hrun]]].
  pose proof (audit_nat_encode_run_correct 1 code body work Hrun) as [_ [Hpair _]].
  exists work; split; [rewrite <- Hpair; exact Hrun|reflexivity].
Qed.

(** A populated assignment can still fail the first constraint and visit the second one. *)
Example rooted_nonempty_rejects :
  let values := Map.set nat_encoding 2 true Map.empty in
  let '(out, events) := fx_fullcheck_counted nat_encoding bool_lattice rooted_system values in
  out = false /\ rooted_calls events =
    [(2, 0, 0); (3, 0, 0); (0, 0, 1); (4, 1, 0);
     (2, 1, 0); (0, 1, 2); (1, 1, 0); (3, 1, 1); (0, 1, 2); (4, 0, 0);
     (0, 2, 3); (4, 0, 1)].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The accepted populated assignment has receipts for the concrete callback source rules. *)
Example concrete_rooted_accept_receipts :
  exists events bodies,
    fx_fullcheck_counted nat_encoding bool_lattice rooted_system rooted_all_true = (true, events) /\
    fx_fullcheck_rooted_trace_source concrete_source events bodies.
Proof.
  pose proof (concrete_rooted_source_bound rooted_all_true) as Hsource.
  destruct (fx_fullcheck_counted nat_encoding bool_lattice rooted_system rooted_all_true)
    as [out events] eqn:Hrun.
  destruct Hsource as [bodies [Htrace [Hout Hbound]]].
  vm_compute in Hout; subst out.
  exists events, bodies; split; [reflexivity|exact Htrace].
Qed.

(** A populated rejected assignment also has all concrete callback receipts. *)
Example concrete_rooted_reject_receipts :
  let values := Map.set nat_encoding 2 true Map.empty in
  exists events bodies,
    fx_fullcheck_counted nat_encoding bool_lattice rooted_system values = (false, events) /\
    fx_fullcheck_rooted_trace_source concrete_source events bodies.
Proof.
  cbn zeta.
  pose proof (concrete_rooted_source_bound (Map.set nat_encoding 2 true Map.empty)) as Hsource.
  destruct (fx_fullcheck_counted nat_encoding bool_lattice rooted_system
    (Map.set nat_encoding 2 true Map.empty)) as [out events] eqn:Hrun.
  destruct Hsource as [bodies [Htrace [Hout Hbound]]].
  vm_compute in Hout; subst out.
  exists events, bodies; split; [reflexivity|exact Htrace].
Qed.
