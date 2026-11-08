(** * Search tick observations

    These computations retain both engine work and arbitrary visitor callee charges.
    For example, charging every callback changes the diamond cost by its event count.
    Builds on: GraphSearchTest and GraphSearch. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearch GraphSearchCost.
From Galois.Graph Require Import GraphSearchScopedCost GraphFixtures.
From Galois.Tests.Graph Require Import GraphSearchTest.
Import List.ListNotations Cost.Notations.

Definition charged_visitor {E} : Visitor.t E unit :=
  Visitor.Make (fun _ _ s => Cost.tick 37 ;; Cost.ret s)
    (fun _ _ _ _ s => Cost.tick 37 ;; Cost.ret s)
    (fun _ _ s => Cost.tick 37 ;; Cost.ret s).

Example singleton_ticks :
  Cost.ticks (SearchRun.run_c SearchFixtures.single Visitor.noop
    SearchFixtures.unrestricted [1]%positive tt) = 36%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_extra_visitor_ticks :
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond charged_visitor
    SearchFixtures.unrestricted [1]%positive tt) -
    Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
      SearchFixtures.unrestricted [1]%positive tt))%N = 444%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_search_ticks :
  Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
    SearchFixtures.unrestricted [] tt) = 0%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example evaluated_search_constant : SearchCost.search_k = 64%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_ticks :
  Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
    SearchFixtures.unrestricted [1]%positive tt) = 223%N.
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_cost_bound :
  (Cost.ticks (SearchRun.run_c SearchFixtures.single Visitor.noop
    SearchFixtures.unrestricted [1]%positive tt) <=?
    SearchCost.search_k * SearchCost.search_size SearchFixtures.single [1]%positive 1 1)%N =
    true.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_cost_bound :
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
    SearchFixtures.unrestricted [1]%positive tt) <=?
    SearchCost.search_k * SearchCost.search_size SearchFixtures.diamond [1]%positive 3 1)%N =
    true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition prepaid_c (state : bool) : Cost.t bool :=
  if state then Cost.tick 7 ;; Cost.ret false else Cost.ret false.

Definition prepaid_visitor {E} : Visitor.t E bool :=
  Visitor.Make (fun _ _ state => prepaid_c state)
    (fun _ _ _ _ state => prepaid_c state) (fun _ _ state => prepaid_c state).

Definition prepaid_potential (state : bool) : N := if state then 7 else 0.

(** Finite callback cases discharge the law for a changing, nonconstant prepaid potential. *)
Example prepaid_amortised {E} :
  Visitor.amortised (@prepaid_visitor E) prepaid_potential 1.
Proof.
  intros event state. destruct event; destruct state; vm_compute; congruence.
Qed.

(** The width duty covers both all valid fixture IDs and every supplied unknown/repeated root. *)
Example restricted_root_width :
  SearchCost.width_bound SearchFixtures.diamond SearchTheoremClients.roots 7.
Proof.
  intros v [Hvalid|Hroot].
  - destruct Hvalid as [node [Hnode Hid]]. vm_compute in Hnode.
    destruct Hnode as [<-|[<-|[<-|[<-|Hfalse]]]]; try contradiction;
      vm_compute in Hid; inversion Hid; subst; vm_compute; congruence.
  - vm_compute in Hroot.
    destruct Hroot as [<-|[<-|[<-|[<-|[<-|Hfalse]]]]]; try contradiction;
      vm_compute; congruence.
Qed.

(** The numeric search contract is applied with all real input and callback premises discharged. *)
Example restricted_prepaid_search_cost :
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond prepaid_visitor
    SearchTheoremClients.scope SearchTheoremClients.roots true) <=
    SearchCost.search_k *
      SearchCost.search_size SearchFixtures.diamond SearchTheoremClients.roots 7 1 +
    prepaid_potential true)%N.
Proof.
  apply SearchCost.search_cost.
  - exact SearchTheoremClients.diamond_ready.
  - exact restricted_root_width.
  - apply prepaid_amortised.
Qed.

Example prepaid_potential_changes :
  (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond prepaid_visitor
    SearchTheoremClients.scope SearchTheoremClients.roots true)),
    prepaid_potential true, prepaid_potential false) = (false, 7%N, 0%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example prepaid_charge_is_retained :
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond prepaid_visitor
    SearchTheoremClients.scope SearchTheoremClients.roots true) -
    Cost.ticks (SearchRun.run_c SearchFixtures.diamond Visitor.noop
      SearchTheoremClients.scope SearchTheoremClients.roots true))%N = 7%N.
Proof.
  vm_compute. reflexivity.
Qed.

(** The family corollary retains the initial nonconstant potential for both prepaid states. *)
Example prepaid_search_bigO :
  bigO (fun state : bool =>
    SearchCost.search_size SearchFixtures.diamond SearchTheoremClients.roots 7 1 +
      prepaid_potential state)%N
    (fun state => Cost.ticks (SearchRun.run_c SearchFixtures.diamond prepaid_visitor
      SearchTheoremClients.scope SearchTheoremClients.roots state)).
Proof.
  apply (SearchCost.search_bigO (fun _ : bool => SearchFixtures.diamond)
    prepaid_visitor prepaid_potential 1 (fun _ => SearchTheoremClients.scope)
    (fun _ => SearchTheoremClients.roots) (fun _ => 7) (fun state => state)).
  - intros state. exact SearchTheoremClients.diamond_ready.
  - apply prepaid_amortised.
  - intros state. exact restricted_root_width.
Qed.

Module LocalVisitorClients.

Definition invariant (state : nat) := (state <= 2)%nat.
(** Five units remain reserved after the two spendable callback units are consumed. *)
Definition potential (state : nat) := (5 + N.of_nat state)%N.

Definition spend_c (state : nat) : Cost.t nat :=
  match state with
  | O => Cost.ret O
  | S rest => Cost.step ;; Cost.ret rest
  end.

Definition lookup_c (v : positive) : Cost.t (option unit) :=
  Map.get_c positive_encoding v Map.empty.

Definition visitor : Visitor.t Fixtures.Edge nat :=
  Visitor.Make
    (fun v _ state => lookup_c v ;; spend_c state)
    (fun _ u v _ state => lookup_c u ;; lookup_c v ;; spend_c state)
    (fun v _ state => lookup_c v ;; spend_c state).

Definition domain :=
  ScopedSearchCost.event_domain SearchFixtures.diamond SearchTheoremClients.scope.

(** Valid global IDs are bounded without assuming that arbitrary positive IDs are small. *)
Lemma diamond_valid_cases v :
  Prepared.valid_id SearchFixtures.diamond v ->
    v = 1%positive \/ v = 2%positive \/ v = 3%positive \/ v = 4%positive.
Proof.
  intros [node [Hnode Hid]]. vm_compute in Hnode.
  destruct Hnode as [<-|[<-|[<-|[<-|Hfalse]]]]; try contradiction;
    vm_compute in Hid; inversion Hid; subst; auto.
Qed.

(** Two prepaid state units pay for two callback steps; trie queries need finite event IDs. *)
Example local_amortised :
  Visitor.amortised_on visitor invariant domain potential 11.
Proof.
  intros ev state HI HD.
  assert (Hstate : state = 0%nat \/ state = 1%nat \/ state = 2%nat)
    by (unfold invariant in HI; lia).
  destruct ev as [v via|e u v kind|v parent].
  - destruct HD as [Hv _]. apply diamond_valid_cases in Hv.
    destruct Hv as [Hv|[Hv|[Hv|Hv]]]; subst v;
      destruct Hstate as [Hs|[Hs|Hs]]; subst state;
      vm_compute; (split; [lia|congruence]).
  - destruct HD as [Hu [Hv _]].
    apply diamond_valid_cases in Hu. apply diamond_valid_cases in Hv.
    destruct Hu as [Hu|[Hu|[Hu|Hu]]]; subst u;
      destruct Hv as [Hv|[Hv|[Hv|Hv]]]; subst v;
      destruct Hstate as [Hs|[Hs|Hs]]; subst state; vm_compute;
      (split; [lia|congruence]).
  - destruct HD as [Hv _]. apply diamond_valid_cases in Hv.
    destruct Hv as [Hv|[Hv|[Hv|Hv]]]; subst v;
      destruct Hstate as [Hs|[Hs|Hs]]; subst state;
      vm_compute; (split; [lia|congruence]).
Qed.

(** The same coefficient fails globally: two unknown wide IDs exceed the callback budget. *)
Example not_globally_amortised : ~ Visitor.amortised visitor potential 11.
Proof.
  intro Hglobal.
  specialize (Hglobal (Search.Edge (1%nat, 1%nat) 99 99 Search.Tree) 0%nat).
  vm_compute in Hglobal. exact (Hglobal eq_refl).
Qed.

Example invariant_excludes_three : ~ invariant 3.
Proof.
  unfold invariant. lia.
Qed.

(** This symbolic client retains the actual final state and potential, for every lawful initial state. *)
Example scoped_local_search state :
  invariant state ->
  invariant (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots state))) /\
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots state) +
    potential (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
      SearchTheoremClients.scope SearchTheoremClients.roots state))) <=
    SearchCost.search_k * ScopedSearchCost.search_size SearchFixtures.diamond
      SearchTheoremClients.scope SearchTheoremClients.roots 7 11 + potential state)%N.
Proof.
  intro HI.
  apply (ScopedSearchCost.search_scoped_cost_on SearchFixtures.diamond visitor
    invariant domain potential 11 SearchTheoremClients.scope SearchTheoremClients.roots 7 state).
  - exact SearchTheoremClients.diamond_ready.
  - exact restricted_root_width.
  - exact local_amortised.
  - intros ev HD. exact HD.
  - exact HI.
Qed.

(** A concrete initial state discharges every premise of the same actual-run theorem. *)
Example actual_scoped_local_search :
  invariant (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots 2%nat))) /\
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots 2%nat) +
    potential (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
      SearchTheoremClients.scope SearchTheoremClients.roots 2%nat))) <=
    SearchCost.search_k * ScopedSearchCost.search_size SearchFixtures.diamond
      SearchTheoremClients.scope SearchTheoremClients.roots 7 11 + potential 2%nat)%N.
Proof.
  apply scoped_local_search. unfold invariant. reflexivity.
Qed.

Example actual_final_credit :
  (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots 2%nat)),
    potential 2%nat, potential 0%nat) =
    (0%nat, 7%N, 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** The public producer establishes the event domain, not a caller-supplied whole-trace premise. *)
Example actual_events_local :
  Forall domain (SearchRun.events SearchFixtures.diamond
    SearchTheoremClients.scope SearchTheoremClients.roots).
Proof.
  apply ScopedSearchCost.events_domain. exact SearchTheoremClients.diamond_ready.
Qed.

Example unknown_root_has_no_enter : ~ domain (Search.Enter 99 None).
Proof.
  intros [Hvalid _]. apply diamond_valid_cases in Hvalid.
  destruct Hvalid as [H|[H|[H|H]]]; discriminate.
Qed.

(** Three admitted vertices have three outgoing occurrences, but only two eligible Edge callbacks. *)
Example scoped_work_includes_rejected_target :
  (ScopedSearchCost.node_count SearchFixtures.diamond SearchTheoremClients.scope,
    ScopedSearchCost.edge_count SearchFixtures.diamond SearchTheoremClients.scope,
    length (filter (fun ev =>
      match ev with Search.Edge _ _ _ _ => true | _ => false end)
      (SearchRun.events SearchFixtures.diamond SearchTheoremClients.scope
        SearchTheoremClients.roots))) = (3%nat, 3%nat, 2%nat).
Proof.
  vm_compute. reflexivity.
Qed.

(** The scoped bound is strictly smaller while using the same roots, widths and global fuel. *)
Example scoped_size_discriminator :
  (ScopedSearchCost.search_size SearchFixtures.diamond SearchTheoremClients.scope
    SearchTheoremClients.roots 7 11 <?
    SearchCost.search_size SearchFixtures.diamond SearchTheoremClients.roots 7 11)%N = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** Clients needing a global graph size can use local duties without losing terminal credit. *)
Example global_size_local_search :
  invariant (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots 2%nat))) /\
  (Cost.ticks (SearchRun.run_c SearchFixtures.diamond visitor
    SearchTheoremClients.scope SearchTheoremClients.roots 2%nat) +
    potential (snd (Cost.value (SearchRun.run_c SearchFixtures.diamond visitor
      SearchTheoremClients.scope SearchTheoremClients.roots 2%nat))) <=
    SearchCost.search_k * SearchCost.search_size SearchFixtures.diamond
      SearchTheoremClients.roots 7 11 + potential 2%nat)%N.
Proof.
  apply (ScopedSearchCost.search_cost_on SearchFixtures.diamond visitor
    invariant domain potential 11 SearchTheoremClients.scope SearchTheoremClients.roots 7 2%nat).
  - exact SearchTheoremClients.diamond_ready.
  - exact restricted_root_width.
  - exact local_amortised.
  - intros ev HD. exact HD.
  - unfold invariant. reflexivity.
Qed.

End LocalVisitorClients.
