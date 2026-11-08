(** * Search tick observations

    These computations retain both engine work and arbitrary visitor callee charges.
    For example, charging every callback changes the diamond cost by its event count.
    Builds on: GraphSearchTest and GraphSearch. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearch GraphSearchCost.
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
