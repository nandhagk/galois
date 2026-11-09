(** * Supplied search contracts and reduced-row propagation

    Reduced rows retain parallel successors and compute reflexive reachability in one pass.
    For example, two diamond arms both include the same join without repeating that point.
    Builds on: AnalysesSsaLiveIndex, GraphSearchSpec and BaseRel. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet BaseRel.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphSearchOrder.
From Galois.Analyses.Ssa Require Import AnalysesSsaLiveIndex.
Import List.ListNotations Cost.Notations.
Local Open Scope positive_scope.

Module ReducedFixture.

Definition next_c (n : positive) :=
  Cost.tick 7 ;;
  Cost.ret
    (match n with
    | 1 => [2; 3]
    | 2 | 3 => [4]
    | _ => []
    end).

Definition order := [1; 2; 3; 4].

Definition rows := LiveIndex.reduced_rows next_c order.

Example diamond_rows :
  map (fun n => map (fun u => FinSet.mem positive_encoding u (LiveIndex.row rows n))
    [1; 2; 3; 4; 99]) [1; 2; 3; 4; 99] =
    [[true; true; true; true; false]; [false; true; false; true; false];
     [false; false; true; true; false]; [false; false; false; true; false];
     [false; false; false; false; false]].
Proof.
  vm_compute; reflexivity.
Qed.

Example parallel_successors_do_not_duplicate_members :
  LiveIndex.reduced_rows (fun n => Cost.tick 7 ;;
    Cost.ret (match n with 1 => [2; 3; 2; 3] | 2 | 3 => [4; 4] | _ => [] end)) order = rows.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_rows :
  FinSet.mem positive_encoding 1
    (LiveIndex.row (LiveIndex.reduced_rows next_c []) 1) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example raw_bad_order_has_no_exactness_guarantee :
  FinSet.mem positive_encoding 4
    (LiveIndex.row (LiveIndex.reduced_rows next_c [1; 4; 3; 2]) 1) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_rows_have_finite_charged_work :
  (N.ltb 0 (Cost.ticks (LiveIndex.reduced_rows_c next_c order)) &&
    N.leb (Cost.ticks (LiveIndex.reduced_rows_c next_c order)) 4096) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_rows_have_no_work :
  Cost.ticks (LiveIndex.reduced_rows_c next_c []) = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** The fixture's bound is derived from its actual callback, adjacency and scalar widths. *)
Theorem fixture_numeric_cost :
  (Cost.ticks (LiveIndex.reduced_rows_c next_c order) <=
    N.of_nat (length order) * LiveIndex.reduced_vertex_price 7 2
      (N.of_nat (length order)) 3)%N.
Proof.
  apply LiveIndex.reduced_rows_cost.
  - intros u Hu; change (1 = u \/ 2 = u \/ 3 = u \/ 4 = u \/ False) in Hu.
    destruct Hu as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      rewrite positive_encoding_bits; vm_compute; discriminate.
  - intros n Hn; change (1 = n \/ 2 = n \/ 3 = n \/ 4 = n \/ False) in Hn.
    destruct Hn as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction.
    all: split.
    all: try (intros u Hu; vm_compute in Hu |- *; intuition congruence).
    all: split; vm_compute; solve [lia | discriminate].
Qed.

Example reflexive_and_transitive_paths :
  Rel.star (fun a b => In b (Cost.value (next_c a))) 1 1 /\
  Rel.star (fun a b => In b (Cost.value (next_c a))) 1 4.
Proof.
  split; [constructor|].
  econstructor 2 with (y := 2).
  - vm_compute; auto.
  - econstructor 2 with (y := 4); [vm_compute; auto|constructor].
Qed.

(** An importing client uses any certified supplied result without choosing a DFS implementation. *)
Theorem supplied_result_client {N E} (p : Prepared.t N E) scope roots r u e v :
  Search.exact p scope roots r ->
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  Prepared.arc p u e v -> ~ Search.ancestor r v u ->
  before (SearchOrder.rpo r) u v.
Proof.
  apply LiveIndex.nonback_rpo.
Qed.

(** The kernel's importing agreement theorem requires only a duplicate-free forward order. *)
Theorem reduced_rows_client next order n u :
  NoDup order ->
  (forall a b, In a order -> In b (Cost.value (next a)) -> before order a b) ->
  In n order ->
  (FinSet.mem positive_encoding u (LiveIndex.row (LiveIndex.reduced_rows next order) n) = true <->
    Rel.star (fun a b => In b (Cost.value (next a))) n u).
Proof.
  intros Hnodup Horder Hn.
  exact (LiveIndex.reduced_rows_exact next order Hnodup Horder n u Hn).
Qed.

End ReducedFixture.
Import ReducedFixture.
