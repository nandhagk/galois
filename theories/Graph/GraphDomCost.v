(** * Dominance checker cost entry points

    Dominance clients reuse the separately checked raw checker implementation.
    For example, a backend candidate can be checked without running another producer.
    Builds on: GraphCheckDomCost and GraphCheckDom. *)

From Stdlib Require Import PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphPrepared GraphDomSpec GraphCheckDom GraphCheckDomCost
  GraphDomCheckBound GraphFrontierSweep GraphDomBackend GraphDomGlobalCost GraphDomFastCheck
  GraphDomFastCheckCost GraphDomFiniteCost GraphDomFiniteView GraphDomCheckedCost GraphDomInputCost.

Module DomCost.

(** The dominance-facing compatibility entry point reuses the independent costed checker. *)
Definition check_c := @DomCheckCost.check_c.
Arguments check_c {V E} p m.

(** Every computational input receives the exact fixed DomCheck.check result. *)
Theorem check_c_value {V E} (p : Prepared.t V E) (m : Map.t positive positive) :
  Cost.value (check_c p m) = DomCheck.check p m.
Proof.
  apply DomCheckCost.check_c_value.
Qed.

(** The raw checker has a coarse closed bound retaining callbacks and candidate storage. *)
Theorem check_cost {V E} (p : Prepared.t V E) candidate n m l b w a q h s :
  Prepared.ready p ->
  FrontierSweep.resources p (Dom.Tree candidate Map.empty Map.empty) n m l b w a q h s ->
  DomCheckCost.parent_width candidate w -> DomCheckBound.stored_width candidate w ->
  (Cost.ticks (check_c p candidate) <=
    DomCheckBound.checker_bound n m l b w a q h s)%N.
Proof.
  apply DomCheckBound.check_cost.
Qed.

(** The big-O corollary uses the full proved primitive/callee bound and claims no smaller target. *)
Theorem check_bigO {X V E} (p : X -> Prepared.t V E)
    (candidate : X -> Map.t positive positive)
    (n m l b : X -> nat) (w a q h s : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, FrontierSweep.resources (p x)
    (Dom.Tree (candidate x) Map.empty Map.empty)
    (n x) (m x) (l x) (b x) (w x) (a x) (q x) (h x) (s x)) ->
  (forall x, DomCheckCost.parent_width (candidate x) (w x)) ->
  (forall x, DomCheckBound.stored_width (candidate x) (w x)) ->
  bigO (fun x => DomCheckBound.checker_bound
    (n x) (m x) (l x) (b x) (w x) (a x) (q x) (h x) (s x))
    (fun x => Cost.ticks (check_c (p x) (candidate x))).
Proof.
  intros Hready Hresources Hparents Hstored.
  exists 1%N. intro x.
  pose proof (check_cost (p x) (candidate x) (n x) (m x) (l x) (b x)
    (w x) (a x) (q x) (h x) (s x)
    (Hready x) (Hresources x) (Hparents x) (Hstored x)).
  lia.
Qed.

(** The complete producer coefficient retains public primitive constants symbolically. *)
Definition lt_k := DomGlobalCost.lt_k.

(** Complete LT trees retain augmented edges, raw roots and finite primitive width duties. *)
Theorem lt_cost {V E} (p : Prepared.t V E) n m r w :
  Prepared.ready p -> DomGlobalCost.bounds p n m r w ->
  Cost.ticks (DomBackend.compute_c DomBackend.lt p) <= (lt_k * DomGlobalCost.work n m r w)%N.
Proof.
  apply DomGlobalCost.lt_cost.
Qed.

(** Complete NCA trees include every actual quadratic walk in the augmented-edge product bound. *)
Theorem semi_nca_cost {V E} (p : Prepared.t V E) n m r w :
  Prepared.ready p -> DomGlobalCost.bounds p n m r w ->
  Cost.ticks (DomBackend.compute_c DomBackend.semi_nca p) <= (lt_k * DomGlobalCost.work n m r w)%N.
Proof.
  apply DomGlobalCost.semi_nca_cost.
Qed.

(** Complete LT family costs use the stated original primitive and finite input domain. *)
Theorem lt_bigO {X V E} (p : X -> Prepared.t V E) (n m r : X -> nat) (w : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, DomGlobalCost.bounds (p x) (n x) (m x) (r x) (w x)) ->
  bigO (fun x => DomGlobalCost.work (n x) (m x) (r x) (w x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.lt (p x))).
Proof.
  apply DomGlobalCost.lt_bigO.
Qed.

(** Complete NCA family costs retain every actual setup and output phase. *)
Theorem semi_nca_bigO {X V E} (p : X -> Prepared.t V E) (n m r : X -> nat) (w : X -> N) :
  (forall x, Prepared.ready (p x)) ->
  (forall x, DomGlobalCost.bounds (p x) (n x) (m x) (r x) (w x)) ->
  bigO (fun x => DomGlobalCost.work (n x) (m x) (r x) (w x))
    (fun x => Cost.ticks (DomBackend.compute_c DomBackend.semi_nca (p x))).
Proof.
  apply DomGlobalCost.semi_nca_bigO.
Qed.

(** Indexed checking has a distinct name that leaves compatibility values and ticks unchanged. *)
Definition fast_check_c := @DomFastCheck.check_c.
Arguments fast_check_c {V E} p parents.

(** Indexed checking retains unconditional Boolean agreement with the compatibility checker. *)
Theorem fast_check_c_value {V E} (p : Prepared.t V E) parents :
  Cost.value (fast_check_c p parents) = DomCheck.check p parents.
Proof.
  apply DomFastCheck.check_c_value.
Qed.

(** The fast checker has the design-table upper bound on its explicit bounded raw-input domain. *)
Theorem fast_check_cost {V E} (p : Prepared.t V E) parents n m r ek bk w :
  DomFiniteCost.bounds p (Prepared.entry_ids p) n m r ek bk w ->
  (N.pos (Pos.size (Prepared.fuel (DomFiniteView.prepared p (Prepared.entry_ids p)))) <= w)%N ->
  Map.wf positive_encoding parents -> (Map.size parents <= n)%nat ->
  DomCheckBound.stored_width parents w -> (r <= n)%nat -> (ek <= w)%N -> (bk <= w)%N ->
  (Cost.ticks (fast_check_c p parents) <=
    DomFastCheckCost.table_k * (1 + N.of_nat n) * (1 + N.of_nat n + N.of_nat m) * (1 + w))%N.
Proof.
  apply DomFastCheckCost.check_table_cost.
Qed.

End DomCost.
