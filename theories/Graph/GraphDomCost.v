(** * Dominance checker cost entry points

    Dominance clients reuse the separately checked raw checker implementation.
    For example, a backend candidate can be checked without running another producer.
    Builds on: GraphCheckDomCost and GraphCheckDom. *)

From Stdlib Require Import PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseMap.
From Galois.Graph Require Import GraphPrepared GraphDomSpec GraphCheckDom GraphCheckDomCost
  GraphDomCheckBound GraphFrontierSweep.

Module DomCost.

(** The dominance-facing checker is the independent costed checker, with no second implementation. *)
Definition check_c := @DomCheckCost.check_c.
Arguments check_c {V E} p m.

(** Every computational input receives the exact fixed DomCheck.check result. *)
Theorem check_c_value {V E} (p : Prepared.t V E) (m : Map.t positive positive) :
  Cost.value (check_c p m) = DomCheck.check p m.
Proof.
  apply DomCheckCost.check_c_value.
Qed.

(** The raw checker has a coarse closed bound retaining actual graph callbacks and candidate storage. *)
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

End DomCost.
