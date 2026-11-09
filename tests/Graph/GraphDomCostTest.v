(** * Primitive checker-bound clients

    Resource witnesses instantiate the coarse bound without an assumed checker result.
    For example, the line's raw candidate storage is counted independently of graph node count.
    Builds on: GraphDomCost, GraphDomCheckBound and GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFixtures
  GraphDomCost GraphDomCheckBound GraphCheckDomCost GraphFrontierSweep.
Import List.ListNotations.
Open Scope positive_scope.

Local Lemma line_ids i :
  Prepared.valid_id Fixtures.Line.prepared i -> i = 1 \/ i = 2 \/ i = 3 \/ i = 4.
Proof.
  intros [v [Hnodes Hid]]. vm_compute in Hnodes.
  destruct Hnodes as [Hv|[Hv|[Hv|[Hv|Hfalse]]]]; [| | | |contradiction];
    subst v; vm_compute in Hid; injection Hid as <-; auto.
Qed.

(** Reduce a valid fixture ID to its finite cases and close the resulting literal cost bounds. *)
Local Ltac finite_id :=
  intros i Hi;
  destruct (line_ids i Hi) as [Hcase|[Hcase|[Hcase|Hcase]]];
  subst i;
  vm_compute; try lia; intuition discriminate.

Example line_resources :
  FrontierSweep.resources Fixtures.Line.prepared
    (Dom.Tree Fixtures.Line.parents Map.empty Map.empty)
    4 1 1 3 3%N 5%N 5%N 6%N 4%N.
Proof.
  constructor.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. intuition discriminate.
  - finite_id.
  - intros v Hv. vm_compute in Hv.
    destruct Hv as [Hv|[Hv|[Hv|[Hv|Hfalse]]]]; [| | | |contradiction];
      subst v; vm_compute; intuition discriminate.
  - finite_id.
  - finite_id.
  - finite_id.
  - finite_id.
  - finite_id.
Qed.

Example line_parent_width : DomCheckCost.parent_width Fixtures.Line.parents 3%N.
Proof.
  intros v u Hget.
  apply (Map.elements_spec positive_encoding positive_encoding_laws v u _
    Fixtures.Line.parents_wf) in Hget.
  vm_compute in Hget.
  destruct Hget as [Heq|[Heq|[Heq|Hfalse]]]; [| | |contradiction];
    injection Heq as <- <-; vm_compute; intuition discriminate.
Qed.

Example line_stored_width : DomCheckBound.stored_width Fixtures.Line.parents 3%N.
Proof.
  intros vu Hin. vm_compute in Hin.
  destruct Hin as [Heq|[Heq|[Heq|Hfalse]]]; [| | |contradiction];
    subst vu; vm_compute; intuition discriminate.
Qed.

Example actual_line_closed_bound :
  (Cost.ticks (DomCost.check_c Fixtures.Line.prepared Fixtures.Line.parents) <=
    DomCheckBound.checker_bound 4 1 1 3 3%N 5%N 5%N 6%N 4%N)%N.
Proof.
  apply DomCost.check_cost.
  - exact Fixtures.Line.fixture_ready.
  - exact line_resources.
  - exact line_parent_width.
  - exact line_stored_width.
Qed.

Example empty_bound_has_nonzero_driver_overhead :
  N.ltb 0 (DomCheckBound.checker_bound 0 0 0 0 1%N 1%N 3%N 4%N 0%N) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_cost_contract_client {V E} (p : Prepared.t V E) candidate n m l b w a q h s :
  Prepared.ready p ->
  FrontierSweep.resources p (Dom.Tree candidate Map.empty Map.empty) n m l b w a q h s ->
  DomCheckCost.parent_width candidate w -> DomCheckBound.stored_width candidate w ->
  (Cost.ticks (DomCost.check_c p candidate) <=
    DomCheckBound.checker_bound n m l b w a q h s)%N.
Proof.
  apply DomCost.check_cost.
Qed.
