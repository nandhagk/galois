(** * Hierarchy numeric and family clients

    These clients discharge readiness, global key width and finite component-counter width.
    For example, an inner scope counts its outgoing rejected target and retains global fuel width.
    Builds on: GraphHierCost, GraphHierTest and GraphFixtures. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Galois.Cost Require Import CostMonad CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchCost
  GraphSearchScopedCost GraphHierSpec GraphHier GraphHierWork GraphHierLocalCost GraphHierCost
  GraphFixtures.
From Galois.Tests.Graph Require Import GraphHierTest.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Local Lemma seven_counter_width i :
  (Pos.to_nat i <= 7)%nat -> key_bits positive_encoding i <= 3.
Proof.
  intro Hbound. change (N.pos (Pos.size i) <= 3).
  destruct i as [[[i|i|]|[i|i|]|]|[[i|i|]|[i|i|]|]|];
    try (vm_compute; discriminate).
  all: rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in Hbound.
  all: repeat rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in Hbound.
  all: pose proof (Pos2Nat.is_pos i); lia.
Qed.

Definition family (nested : bool) :=
  if nested then Fixtures.NestedLoop.prepared else Fixtures.Line.prepared.

Definition family_scope (nested : bool) :=
  if nested then Scope.Make FinSet.empty
    (Some (FinSet.of_list positive_encoding [2; 3]%positive)) else unrestricted.

Definition family_roots (nested : bool) := if nested then [2]%positive else [1]%positive.

Example family_ready b : Prepared.ready (family b).
Proof.
  destruct b; [exact Fixtures.NestedLoop.fixture_ready|exact Fixtures.Line.fixture_ready].
Qed.

Example family_width b : SearchCost.width_bound (family b) (family_roots b) 3.
Proof.
  intros v [[name [Hin Hi]]|Hv].
  - destruct b; cbn [family] in Hin, Hi.
    all: change (In name [1; 2; 3; 4]%nat) in Hin.
    all: destruct Hin as [<-|[<-|[<-|[<-|Hfalse]]]]; try contradiction.
    all: vm_compute in Hi; inversion Hi; subst v; vm_compute; discriminate.
  - destruct b; cbn [family_roots In] in Hv; destruct Hv as [<-|Hfalse];
      try contradiction; vm_compute; discriminate.
Qed.

Example family_counter b : HierLocalCost.counter_width (family b) 3.
Proof.
  intros i Hbound. apply seven_counter_width.
  assert (Hcount : length (Graph.nodes (Prepared.graph (family b))) = 4%nat).
  { destruct b; vm_compute; reflexivity. }
  rewrite Hcount in Hbound. lia.
Qed.

Example line_cost_client :
  Cost.ticks (HierRun.compute_c (family false) (family_scope false) (family_roots false)) <=
    HierCost.hier_k * HierCost.size (family false) (family_scope false) (family_roots false) 3.
Proof.
  apply HierCost.hier_cost; [apply family_ready|apply family_width].
Qed.

Example inner_scope_cost_client :
  Cost.ticks (HierRun.compute_c (family true) (family_scope true) (family_roots true)) <=
    HierCost.hier_k *
      HierCost.scoped_size (family true) (family_scope true) (family_roots true) 3.
Proof.
  apply HierCost.hier_scoped_cost; [apply family_ready|apply family_width].
Qed.

Example hierarchy_bigO_family_client :
  bigO (fun b => HierCost.size (family b) (family_scope b) (family_roots b) 3)
    (fun b => Cost.ticks (HierRun.compute_c (family b) (family_scope b) (family_roots b))).
Proof.
  apply HierCost.hier_bigO; [apply family_ready|apply family_width].
Qed.

Example hierarchy_scoped_bigO_family_client :
  bigO (fun b => HierCost.scoped_size (family b) (family_scope b) (family_roots b) 3)
    (fun b => Cost.ticks (HierRun.compute_c (family b) (family_scope b) (family_roots b))).
Proof.
  apply HierCost.hier_scoped_bigO; [apply family_ready|apply family_width].
Qed.

Example distinct_valid_root_cost_client :
  Cost.ticks (HierRun.compute_c (family false) unrestricted [1]%positive) <=
    2 * HierCost.hier_k *
      HierCost.root_restricted_size (family false) unrestricted [1]%positive 3.
Proof.
  apply HierCost.hier_cost_distinct_valid_roots.
  - apply family_ready.
  - apply (family_width false).
  - constructor; [intro Hfalse; contradiction|constructor].
  - intros v [<-|Hfalse]; [|contradiction].
    exists 1%nat. split; vm_compute; auto.
Qed.

Example scoped_outgoing_and_global_width_discriminator :
  (ScopedSearchCost.node_count (family true) (family_scope true),
    ScopedSearchCost.edge_count (family true) (family_scope true),
    HierWork.fuel_width (family true)) = (2%nat, 3%nat, 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example actual_depth_three :
  HierWork.depth (HierRun.compute depth_three unrestricted [1]%positive) = 3%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example depth_three_below_numeric_bound :
  (Cost.ticks (HierRun.compute_c depth_three unrestricted [1]%positive) <=?
    HierCost.hier_k * HierCost.size depth_three unrestricted [1]%positive 3) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example repeated_unknown_roots_below_general_bound :
  (Cost.ticks (HierRun.compute_c Fixtures.Empty.prepared unrestricted [99; 99]%positive) <=?
    HierCost.hier_k *
      HierCost.size Fixtures.Empty.prepared unrestricted [99; 99]%positive 7) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example nonempty_unknown_root_overhead :
  (Cost.ticks (HierRun.compute_c Fixtures.Line.prepared unrestricted [99; 1; 1]%positive) <=?
    HierCost.hier_k *
      HierCost.size Fixtures.Line.prepared unrestricted [99; 1; 1]%positive 7) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example callback_charge_is_retained :
  Cost.ticks (HierRun.assemble_c [[1]%positive]
    (fun _ _ => Cost.tick 50 ;; Cost.ret (Some (Hier.Vertex 1%positive)))) = 51.
Proof.
  vm_compute. reflexivity.
Qed.

Example selection_charges_absent_preference :
  Cost.ticks (HierRun.select_c None [1; 2; 3]%positive) = 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example line_tick_observation :
  Cost.ticks (HierRun.compute_c Fixtures.Line.prepared unrestricted [1]%positive) = 521.
Proof.
  vm_compute. reflexivity.
Qed.

Example nested_tick_observation :
  Cost.ticks (HierRun.compute_c Fixtures.NestedLoop.prepared unrestricted [1]%positive) = 1234.
Proof.
  vm_compute. reflexivity.
Qed.

Example depth_three_tick_observation :
  Cost.ticks (HierRun.compute_c depth_three unrestricted [1]%positive) = 2443.
Proof.
  vm_compute. reflexivity.
Qed.

Example depth_three_width : SearchCost.width_bound depth_three [1]%positive 3.
Proof.
  intros v [[name [Hin Hi]]|Hv].
  - change (In name [1; 2; 3; 4; 5; 6; 7]%nat) in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|Hfalse]]]]]]]; try contradiction.
    all: vm_compute in Hi; inversion Hi; subst v; vm_compute; discriminate.
  - destruct Hv as [<-|Hfalse]; [vm_compute; discriminate|contradiction].
Qed.

Example depth_three_counter : HierLocalCost.counter_width depth_three 3.
Proof.
  intros i Hbound. apply seven_counter_width. exact Hbound.
Qed.

Example depth_three_cost_client :
  Cost.ticks (HierRun.compute_c depth_three unrestricted [1]%positive) <=
    HierCost.hier_k * HierCost.size depth_three unrestricted [1]%positive 3.
Proof.
  apply HierCost.hier_cost; [exact depth_three_ready|exact depth_three_width].
Qed.

Example composed_hierarchy_coefficient : HierCost.hier_k = 10496.
Proof.
  vm_compute. reflexivity.
Qed.

Example inner_scope_distinct_root_cost_client :
  Cost.ticks (HierRun.compute_c (family true) (family_scope true) [2]%positive) <=
    2 * HierCost.hier_k *
      HierCost.scoped_root_restricted_size (family true) (family_scope true) [2]%positive 3.
Proof.
  apply HierCost.hier_scoped_cost_distinct_roots.
  - apply family_ready.
  - apply (family_width true).
  - constructor; [intro Hfalse; contradiction|constructor].
  - intros v [<-|Hfalse]; [|contradiction]. split.
    + exists 2%nat. split; vm_compute; auto.
    + vm_compute. reflexivity.
Qed.

Example repeated_roots_need_general_bound :
  (length [1; 1; 1; 1; 1]%positive >
    length (Graph.nodes (Prepared.graph Fixtures.Line.prepared)))%nat.
Proof.
  vm_compute. repeat constructor.
Qed.
