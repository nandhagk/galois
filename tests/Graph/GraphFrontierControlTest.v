(** * Control dependence and exit coverage

    Reversed certificates distinguish covered exits from a non-exiting component.
    For example, a self-loop with no exits has an empty reversed sweep.
    Builds on: GraphFrontierControl and GraphFixtures. *)

From Stdlib Require Import List PArith Arith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphFixtures GraphCheckDom
  GraphDomSpec GraphFrontierSpec GraphFrontierControl.
Import List.ListNotations.

Definition diamond_reverse := Prepared.reverse Fixtures.Diamond.prepared [4]%positive.
Definition diamond_parents := Fixtures.parents [(1, 4); (2, 4); (3, 4)]%positive.
Definition diamond_post := DomCheck.of_parents diamond_reverse diamond_parents.

Example diamond_post_checked : DomCheck.check diamond_reverse diamond_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example diamond_controls :
  map (fun i => Map.find_or positive_encoding [] i
    (FrontierControl.control_deps Fixtures.Diamond.prepared [4]%positive diamond_post))
    [1; 2; 3; 4]%positive = [[]; [(1, 2)]; [(1, 3)]; []].
Proof.
  vm_compute. reflexivity.
Qed.

Definition labelled_graph :=
  Graph.of_pure [1] [1; 2; 3; 4]
    (fun n =>
      filter (fun e => Nat.eqb
        (if Nat.leb e 13 then 1 else if Nat.eqb e 24 then 2 else 3) n)
        [11; 12; 13; 24; 34])
    (fun e => if Nat.leb e 13 then 1 else if Nat.eqb e 24 then 2 else 3)
    (fun e => if Nat.leb e 12 then 2 else if Nat.eqb e 13 then 3 else 4).
Definition labelled := Prepared.prepare nat_encoding labelled_graph.
Definition labelled_reverse := Prepared.reverse labelled [4]%positive.
Definition labelled_post := DomCheck.of_parents labelled_reverse diamond_parents.

Example labelled_post_checked :
  DomCheck.check labelled_reverse diamond_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example parallel_control_labels :
  Map.find_or positive_encoding [] 2%positive
    (FrontierControl.control_deps labelled [4]%positive labelled_post) = [12; 11].
Proof.
  vm_compute. reflexivity.
Qed.

Definition loop := Fixtures.prepare [1] [1; 2; 3] [(1, 2); (2, 2); (2, 3)].
Definition loop_reverse := Prepared.reverse loop [3]%positive.
Definition loop_parents := Fixtures.parents [(1, 2); (2, 3)]%positive.
Definition loop_post := DomCheck.of_parents loop_reverse loop_parents.

Example loop_post_checked : DomCheck.check loop_reverse loop_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example loop_controls :
  map (fun i => Map.find_or positive_encoding [] i
    (FrontierControl.control_deps loop [3]%positive loop_post)) [1; 2; 3]%positive =
    [[]; [(2, 2)]; []].
Proof.
  vm_compute. reflexivity.
Qed.

Definition noexit := Fixtures.prepare [1] [1] [(1, 1)].
Definition noexit_parents := Fixtures.parents [].
Definition noexit_reverse := Prepared.reverse noexit [].
Definition noexit_post := DomCheck.of_parents noexit_reverse noexit_parents.

Example noexit_post_checked : DomCheck.check noexit_reverse noexit_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example noexit_sweep_empty :
  Map.elements (FrontierControl.control_deps noexit [] noexit_post) = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** The semantic predicate remains true outside the exit-coverage theorem domain. *)
Example noexit_semantic_countercontrol :
  control_dependent (Prepared.graph noexit) [] (1, 1) 1.
Proof.
  unfold control_dependent, post_dominates. vm_compute.
  split; [now left|]. split; [intros z es Hfalse; contradiction|].
  intros [_ Hne]. apply Hne. reflexivity.
Qed.

Definition unlisted_source := Fixtures.prepare [] [1; 2] [(0, 1); (0, 2)].
Definition unlisted_reverse := Prepared.reverse unlisted_source [1; 2]%positive.
Definition unlisted_post := DomCheck.of_parents unlisted_reverse noexit_parents.

Example unlisted_post_checked :
  DomCheck.check unlisted_reverse noexit_parents = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example unlisted_sweep_empty :
  Map.elements (FrontierControl.control_deps unlisted_source [1; 2]%positive unlisted_post) = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** Exit coverage alone cannot recover edges supplied only at an unlisted source. *)
Example unlisted_semantic_countercontrol :
  control_dependent (Prepared.graph unlisted_source) [1; 2] (0, 1) 1.
Proof.
  unfold control_dependent. split.
  - vm_compute. now left.
  - split.
    + intros z es Hz Hpath. left. reflexivity.
    + intros [Hpost _].
      assert (Hpath : path (Prepared.graph unlisted_source) 0 [(0, 2)] 2).
      { refine (@path_cons nat (nat * nat) (Prepared.graph unlisted_source) (0, 2) [] 2 _ _).
        - vm_compute. right. now left.
        - change (path (Prepared.graph unlisted_source) 2 [] 2). constructor. }
      specialize (Hpost 2 [(0, 2)] (or_intror (or_introl eq_refl)) Hpath).
      vm_compute in Hpost.
      destruct Hpost as [Hfalse|[e [[Heq|Hfalse] Htarget]]];
        try contradiction; try discriminate.
      subst e. discriminate.
Qed.
