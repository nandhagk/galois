(** * Structured graph and machine fixtures

    Fixtures retain loops, duplicate switch targets and malformed labels.
    For example, a loop's depth-zero jump returns to its body entry.
    Builds on: ProgramSkeletonCfg. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramCfg ProgramSkeleton
  ProgramSkeletonMachine ProgramSkeletonCfg.
Import List.ListNotations Skeleton.

Definition leaf : stmt nat bool := Atom 0.
Definition loop_jump : stmt nat bool := Loop (Jump 0).
Definition loop_break : stmt nat bool := Block (Loop (Jump 1)).
Definition branch : stmt nat bool := If true (Atom 1) (Atom 2).
Definition switch : stmt nat bool := Block (JumpTable true [0; 0] 0).
Definition invalid_jump : stmt nat bool := Jump 0.
Definition invalid_switch : stmt nat bool := Block (JumpTable false [0; 1] 0).
Definition sequence : stmt nat bool := Seq leaf branch.
Definition conditional_jump : stmt nat bool := Block (JumpIf false 0).

Definition fixtures :=
  [leaf; loop_jump; loop_break; branch; switch; invalid_jump;
    invalid_switch; sequence; conditional_jump].

Definition endpoints (s : stmt nat bool) :=
  let g := Cfg.graph (skeleton_cfg s) in
  map (fun e => (Graph.source g e, Graph.target g e)) (Cfg.edges (skeleton_cfg s)).

Example good_labels : map (labels_ok 0) [loop_jump; loop_break; switch] = [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example bad_labels : map (labels_ok 0) [invalid_jump; invalid_switch] = [false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example leaf_nodes :
  Graph.nodes (Cfg.graph (skeleton_cfg leaf)) = [PEntry []; PExit []].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_backedge :
  endpoints loop_jump =
    [(PEntry [], PEntry [DBody]); (PEntry [DBody], PEntry [DBody]);
      (PExit [DBody], PEntry [DBody])].
Proof.
  vm_compute; reflexivity.
Qed.

Example if_alternatives :
  map (fun e => (Graph.target (Cfg.graph (skeleton_cfg branch)) e, skel_acts branch e))
    (Graph.out (Cfg.graph (skeleton_cfg branch)) (PEntry [])) =
    [(PEntry [DFirst], [AGuard true true]); (PEntry [DSecond], [AGuard true false])].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_switch_targets :
  map (Graph.target (Cfg.graph (skeleton_cfg switch)))
    (Graph.out (Cfg.graph (skeleton_cfg switch)) (PEntry [DBody])) =
    [PExit []; PExit []; PExit []].
Proof.
  vm_compute; reflexivity.
Qed.

Example invalid_label_has_no_edge : Cfg.edges (skeleton_cfg invalid_jump) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example invalid_position :
  Graph.out (Cfg.graph (skeleton_cfg leaf)) (PEntry [DBody]) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example absent_slot :
  (skel_to leaf (SkelEdge (PEntry []) 3), skel_acts leaf (SkelEdge (PEntry []) 3)) =
    (PEntry [], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example cached_positions : indexed_positions (skeleton_index branch) = [[]; [DFirst]; [DSecond]].
Proof.
  vm_compute; reflexivity.
Qed.

Example cached_ranks :
  (Map.get skel_point_encoding (PEntry [DSecond]) (indexed_rank (skeleton_index branch)),
    Map.get skel_point_encoding (PExit []) (indexed_rank (skeleton_index branch)),
    indexed_span (skeleton_index branch)) = (Some 3, Some 5, 6).
Proof.
  vm_compute; reflexivity.
Qed.

Example charged_empty_position : (Cost.ticks (encode_c position_encoding []) > 0)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition client : skeleton_client nat bool nat unit :=
  SkeletonClient (fun st => st = 0) (fun _ st l st' => l = [] /\ st' = S st)
    (fun _ _ => False) (fun _ _ => False)
    (fun b _ => Some b) (fun _ st => Some st) (fun _ _ st st' => st' = st).

Example jump_resumes_loop :
  resume 0 [FLoop []] 7 = Some (Go [DBody] [FLoop []] 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_label_rejected : resume 0 [] 7 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example atom_observation :
  atom_step client 0 3 [] 4 /\ ~ atom_step client 0 3 [] 3.
Proof.
  vm_compute; split; [split; reflexivity|intros [_ Hbad]; discriminate].
Qed.

Example final_root : final (skeleton_endings leaf client) (Ret [] [] 1).
Proof.
  vm_compute; exact I.
Qed.

Example invalid_subtree : sub leaf [DFirst] = None.
Proof.
  vm_compute; reflexivity.
Qed.
