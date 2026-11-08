(** * Frontier closure fixtures

    Iterated queries use checked supplied trees and apply liveness at every step.
    For example, a nonlive join never enters the pruned closure.
    Builds on: GraphFrontierIdf and GraphFixtures. *)

From Stdlib Require Import List PArith NArith Arith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphFixtures GraphCheckDom GraphPrepared GraphDomSpec
  GraphFrontierSweep GraphFrontierIdf.
Import List.ListNotations.

Example diamond_checked :
  DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_idf :
  FinSet.elements (FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree [2]) =
    [4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_checked :
  DomCheck.check Fixtures.JoinLoop.prepared Fixtures.JoinLoop.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_idf :
  FinSet.elements (FrontierIdf.idf Fixtures.JoinLoop.prepared Fixtures.JoinLoop.tree [4]) =
    [4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_checked :
  DomCheck.check Fixtures.TwoEntry.prepared Fixtures.TwoEntry.parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_idf :
  FinSet.elements (FrontierIdf.idf Fixtures.TwoEntry.prepared Fixtures.TwoEntry.tree [1; 2]) =
    [3]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_seeds :
  FinSet.elements (FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree []) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example unknown_seed :
  FinSet.elements (FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree [42]) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example nonlive_join :
  FinSet.elements (FrontierIdf.idf_pruned Fixtures.Diamond.prepared Fixtures.Diamond.tree [2]
    (fun v => Cost.ret (negb (Pos.eqb v 4)))) = [].
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_seed :
  FinSet.elements (FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree [2; 2]) =
    [4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition reference_closure {V E} (p : Prepared.t V E) tree defs :=
  let df := FrontierSweep.dominance_frontier p tree in
  let next := fun d => FinSet.elements (Map.find_or positive_encoding FinSet.empty d df) in
  FinSet.of_list positive_encoding
    (Nat.iter 4 (fun xs => nodup Pos.eq_dec (xs ++ flat_map next xs)) (flat_map next defs)).

Example diamond_closure_comparison :
  FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree [2] =
    reference_closure Fixtures.Diamond.prepared Fixtures.Diamond.tree [2]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_closure_comparison :
  FrontierIdf.idf Fixtures.JoinLoop.prepared Fixtures.JoinLoop.tree [4] =
    reference_closure Fixtures.JoinLoop.prepared Fixtures.JoinLoop.tree [4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example two_entry_closure_comparison :
  FrontierIdf.idf Fixtures.TwoEntry.prepared Fixtures.TwoEntry.tree [1; 2] =
    reference_closure Fixtures.TwoEntry.prepared Fixtures.TwoEntry.tree [1; 2]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example live_callback_charge_retained :
  N.ltb (Cost.ticks (FrontierIdf.idf_pruned_c Fixtures.Diamond.prepared
    Fixtures.Diamond.tree [2] (fun _ => Cost.ret true)))
    (Cost.ticks (FrontierIdf.idf_pruned_c Fixtures.Diamond.prepared
      Fixtures.Diamond.tree [2] (fun _ => Cost.lift (fun _ => 7%N) (fun _ => true) tt))) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition nested_joins := Fixtures.prepare [0] [0; 1; 2; 3; 4]
  [(0, 1); (0, 4); (1, 2); (1, 3); (2, 3); (3, 4)].
Definition nested_join_parents := Fixtures.parents [(2, 1); (3, 2); (4, 2); (5, 1)]%positive.
Definition nested_join_tree := DomCheck.of_parents nested_joins nested_join_parents.

Example nested_joins_checked : DomCheck.check nested_joins nested_join_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example pruning_suppresses_further_propagation :
  (FinSet.elements (FrontierIdf.idf nested_joins nested_join_tree [2]),
   FinSet.elements (FrontierIdf.idf_pruned nested_joins nested_join_tree [2]
     (fun i => Cost.ret (Pos.eqb i 4))),
   FinSet.elements (FrontierIdf.idf_pruned nested_joins nested_join_tree [2]
     (fun i => Cost.ret (Pos.eqb i 5))),
   FinSet.elements (FrontierIdf.idf_pruned nested_joins nested_join_tree [3]
     (fun i => Cost.ret (Pos.eqb i 5)))) =
    ([4; 5], [4], [], [5])%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Public canonicality is available without readiness or exactness premises. *)
Example public_idf_wf {V E} (p : Prepared.t V E) (tree : Dom.tree) defs :
  FinSet.wf positive_encoding (FrontierIdf.idf p tree defs).
Proof.
  apply FrontierIdf.idf_wf.
Qed.

(** The pruned callback can be arbitrary when deriving representation validity. *)
Example public_pruned_idf_wf {V E} (p : Prepared.t V E) (tree : Dom.tree) defs live :
  FinSet.wf positive_encoding (FrontierIdf.idf_pruned p tree defs live).
Proof.
  apply FrontierIdf.pruned_idf_wf.
Qed.

(** The actual returned set can be enumerated through the public membership specification. *)
Example diamond_idf_enumeration_client i :
  In i (FinSet.elements (FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree [2])) <->
    FinSet.mem positive_encoding i
      (FrontierIdf.idf Fixtures.Diamond.prepared Fixtures.Diamond.tree [2]) = true.
Proof.
  apply (FinSet.elements_spec positive_encoding positive_encoding_laws).
  apply FrontierIdf.idf_wf.
Qed.
