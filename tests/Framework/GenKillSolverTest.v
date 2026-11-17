(** * Gen/kill solver observations

    Certified worklists run the loop, diamond and disconnected fixtures.
    For example, an unreachable generator still contributes to the may solution.

    Groups:
    - [MayTests] The may analysis gives the reaching facts of loops, diamonds and empty graphs.
    - [MustTests] The must analysis gives the available facts, and it stays fresh where nothing
      reaches.
    - [BackwardTests] The backward analyses give liveness and invalidation facts.
    - [PathTests] The enumerated gen/kill paths give the facts of a diamond and of one node.
    - [CheckTests] Candidates for the may and must systems are accepted or rejected.

    Builds on: Framework.GenKill and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Trie TrieSet Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig GenKillSig GenKill.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := nat. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Sets := TrieSetCode NatKeyCode.

(** The set of the given facts. *)
Definition facts (xs : list nat) := fold_left (fun s x => Sets.add x s) xs Sets.empty.

(** A family of graphs indexed by program: loops, a diamond, an empty graph and a singleton. *)
Module Graph <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries p := match p with
    | 0 | 7 => [0; 1; 2]
    | 3 | 9 => []
    | 8 => [3]
    | _ => [0]
    end.
  Definition edges p := match p with
    | 0 | 1 | 7 => [0; 1; 2]
    | 2 | 8 => [0; 1; 2; 3]
    | 6 | 9 | 10 => [0]
    | 11 => [0; 1]
    | 13 => [0; 0]
    | _ => []
    end.
  Definition src p e := match p with
    | 0 | 1 | 7 => if Nat.eqb e 0 then 0 else 1
    | 2 | 8 => match e with 2 => 1 | 3 => 2 | _ => 0 end
    | 6 | 10 => 1
    | 11 => e
    | _ => 0
    end.
  Definition dst p e := match p with
    | 0 | 1 | 7 => if Nat.eqb e 2 then 2 else 1
    | 2 | 8 => match e with 0 => 1 | 1 => 2 | _ => 3 end
    | 6 | 10 | 11 => 2
    | _ => 0
    end.
End Graph.

(** Forward gen/kill facts, with a generator on node 2 and a kill on node 10. *)
Module Forward <: GENKILL_OPS Prog Edge NatKeyCode Sets.
  Definition dir := Forward.
  Definition may := true.
  Definition gen p e := facts (match p, e with
    | 1, 0 => [0] | 1, 1 => [1]
    | 2, 0 => [7] | 2, 2 => [8]
    | 6, _ | 11, 1 => [7] | _, _ => [] end).
  Definition kill p e := facts (match p, e with 1, 1 => [0] | 10, _ => [7] | _, _ => [] end).
  Definition init p := facts (match p with 4 | 5 | 10 => [7] | _ => [] end).
End Forward.

(** Backward gen/kill facts, with uses on the loop and an invalidating kill on node 8 and 9. *)
Module Backward <: GENKILL_OPS Prog Edge NatKeyCode Sets.
  Definition dir := Backward.
  Definition may := true.
  Definition gen p e := facts (match p, e with
    | 0, 1 => [0] | 0, 2 => [1] | 7, 1 => [7]
    | 8, 2 | 8, 3 | 9, _ => [1] | _, _ => [] end).
  Definition kill p e := facts (match p, e with 0, 0 => [0] | 8, 0 | 9, _ => [1] | _, _ => [] end).
  Definition init (_ : nat) := Sets.empty.
End Backward.

(** The may lattice of sets, widened by join and narrowed by intersection. *)
Module MayLat <: WLATTICE_OPS.
  Include GenKillMayDomainCode NatKeyCode Sets.
  Definition wparam := unit.
  Definition widen (_ : unit) := join.
  Definition narrow := Sets.inter.
End MayLat.

(** The must lattice of sets, widened and narrowed by join. *)
Module MustLat <: WLATTICE_OPS.
  Include GenKillMustDomainCode NatKeyCode Sets.
  Definition wparam := unit.
  Definition widen (_ : unit) := join.
  Definition narrow := join.
End MustLat.

Module MF := GenKillMayFlowCode Prog NatKeyCode Edge NatKeyCode Sets Forward MayLat.
Module BF := GenKillMayFlowCode Prog NatKeyCode Edge NatKeyCode Sets Backward MayLat.
Module UF := GenKillMustFlowCode Prog NatKeyCode Edge NatKeyCode Sets Forward MustLat.
Module BUF := GenKillMustFlowCode Prog NatKeyCode Edge NatKeyCode Sets Backward MustLat.
Module MS := GenKillMayCode Prog NatKeyCode Edge Graph NatKeyCode Sets Forward MayLat MF.
Module BS := GenKillMayCode Prog NatKeyCode Edge Graph NatKeyCode Sets Backward MayLat BF.
Module US := GenKillMustCode Prog NatKeyCode Edge Graph NatKeyCode Sets Forward MustLat UF.
Module BUS := GenKillMustCode Prog NatKeyCode Edge Graph NatKeyCode Sets Backward MustLat BUF.
Module MP := PolicyCode MayLat.
Module UP := PolicyCode MustLat.
Module MC := CheckCode MayLat MS.
Module BC := CheckCode MayLat BS.
Module UC := CheckCode MustLat US.
Module BUC := CheckCode MustLat BUS.
Module MW := WorklistCode MayLat MS MP HeapCode.
Module BW := WorklistCode MayLat BS MP HeapCode.
Module UW := WorklistCode MustLat US UP HeapCode.
Module BUW := WorklistCode MustLat BUS UP HeapCode.
Module MR := NarrowCode MayLat MS MC.
Module BR := NarrowCode MayLat BS BC.
Module UR := NarrowCode MustLat US UC.
Module BUR := NarrowCode MustLat BUS BUC.
Module MA := CertifiedCode MayLat MS MW MC MR.
Module BA := CertifiedCode MayLat BS BW BC BR.
Module UA := CertifiedCode MustLat US UW UC UR.
Module BUA := CertifiedCode MustLat BUS BUW BUC BUR.

(** The policy with empty tries, unit parameter and bound 0. *)
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.

(** The may facts of the nodes xs in the solution of program p, if it is solved within fuel. *)
Definition observe_may p xs := match MA.analyze p flat 16%N with
  | Solved m => Some (map (fun x => Sets.elements (MC.look m x)) xs)
  | _ => None
  end.

(** The backward may facts of the nodes xs in the solution of program p, if it is solved. *)
Definition observe_back p xs := match BA.analyze p flat 16%N with
  | Solved m => Some (map (fun x => Sets.elements (BC.look m x)) xs)
  | _ => None
  end.

(** The must facts of the nodes xs in the solution of program p, if it is solved. *)
Definition observe_must p xs := match UA.analyze p flat 16%N with
  | Solved m => Some (map (fun x => option_map Sets.elements (UC.look m x)) xs)
  | _ => None
  end.

(** Whether the candidate look satisfies every row of the may system for program p. *)
Definition check_may p look := forallb (fun r =>
  row_ok MayLat.leb look (MS.target p r)
    (eval_query (MS.resume p) look (S (length (MS.deps p r))) (MS.start p r))) (MS.rows p).

(** Whether the candidate look satisfies every row of the must system for program p. *)
Definition check_must p look := forallb (fun r =>
  row_ok MustLat.leb look (US.target p r)
    (eval_query (US.resume p) look (S (length (US.deps p r))) (US.start p r))) (US.rows p).

(** * May *)

Module MayTests.

  (** The reaching facts of the loop are the empty set at 0 and the facts 0 and 1 at 1 and 2. *)
  Example reaching_loop_facts :
    observe_may 1 [0; 1; 2] = Some [[]; [1; 0]; [1; 0]].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty graph has no reaching facts at its node. *)
  Example empty_graph_may_empty :
    observe_may 3 [0] = Some [[]].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Entry node 0 of program 4 keeps fact 7, and the absent node 99 has none. *)
  Example may_entry_and_absent_node :
    observe_may 4 [0; 99] = Some [[7]; []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The singleton graph reaches fact 7 at node 0 and nothing at node 1. *)
  Example singleton_may_facts :
    observe_may 5 [0; 1] = Some [[7]; []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unreachable generator still contributes fact 7 to the may solution. *)
  Example unreachable_generation_may :
    observe_may 6 [0; 1; 2] = Some [[]; []; [7]].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A closed seed with fact 7 gives the same may facts as the singleton graph. *)
  Example closed_seed_may :
    observe_may 5 [0; 99] = Some [[7]; []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty candidate is rejected for program 6, whose generator is unreachable. *)
  Example empty_candidate_rejected_at_six :
    check_may 6 (fun _ => Sets.empty) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty candidate is rejected for program 4, which misses its raw seed. *)
  Example empty_candidate_missing_seed_rejected :
    check_may 4 (fun _ => Sets.empty) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End MayTests.

(** * Must *)

Module MustTests.

  (** The available facts of the diamond are empty at the entry and at the join, and [7] at node 1. *)
  Example available_diamond :
    observe_must 2 [0; 1; 2; 3; 99] =
      Some [Some []; Some [7]; Some []; Some []; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty graph has no available facts at its node. *)
  Example empty_graph_must_none :
    observe_must 3 [0] = Some [None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Entry node 0 keeps fact 7 under the must analysis, and the absent node 99 has no facts. *)
  Example must_entry_and_absent_node :
    observe_must 4 [0; 99] = Some [Some [7]; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The singleton graph has fact 7 available at node 0 and none at node 1. *)
  Example singleton_must_facts :
    observe_must 5 [0; 1] = Some [Some [7]; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unreachable generator leaves node 2 with fact 7 and the other nodes unknown. *)
  Example unreachable_generation_must :
    observe_must 6 [0; 1; 2] = Some [Some []; None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A closed seed with fact 7 gives the same must facts as the singleton graph. *)
  Example closed_seed_must :
    observe_must 5 [0; 99] = Some [Some [7]; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The kill on node 10 keeps fact 7 at entry, and the other nodes stay unknown. *)
  Example unreachable_kill_keeps_fact :
    observe_must 10 [0; 1; 2] = Some [Some [7]; None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The must transfer of the kill on node 10 maps fact 7 to the empty set. *)
  Example unreachable_kill_empties_transfer :
    option_map Sets.elements (UF.transfer 10 0 (Some (facts [7]))) = Some [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The must transfer keeps the unreached state at None. *)
  Example unreachable_transfer_keeps_none :
    UF.transfer 6 0 None = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The must transfer of a reached state is not None. *)
  Example reached_transfer_not_none :
    UF.transfer 6 0 (Some (facts [7])) <> None.
  Proof.
    vm_compute. discriminate.
  Qed.

  (** The hand candidate that reads fact 7 for node 1 satisfies the must system for program 2. *)
  Example must_hand_candidate_accepted :
    check_must 2 (fun n => Some (facts (if Nat.eqb n 1 then [7] else []))) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A candidate that gives fact 7 everywhere is rejected for program 2 by the join. *)
  Example must_wrong_join_rejected :
    check_must 2 (fun _ => Some (facts [7])) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The empty candidate misses the raw seed of program 4 under the must system. *)
  Example missing_must_raw_seed_rejected :
    check_must 4 (fun _ => None) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End MustTests.

(** * Backward *)

Module BackwardTests.

  (** The backward liveness of the loop is [1] at node 0, [1; 0] at node 1 and empty at node 2. *)
  Example liveness_loop_facts :
    observe_back 0 [0; 1; 2] = Some [[1]; [1; 0]; []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The finite use of fact 7 is live at nodes 0 and 1 and dead at node 2. *)
  Example finite_use_backward :
    observe_back 7 [0; 1; 2] = Some [[7]; [7]; []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The backward must solution of program 8 is invalidated at nodes 0 to 3 as stated. *)
  Example invalidation_backward_must :
    match BUA.analyze 8 flat 16%N with
    | Solved m => Some (map (fun x => option_map (fun s => map (Nat.eqb 1) (Sets.elements s))
        (BUC.look m x)) [0; 1; 2; 3])
    | _ => None
    end = Some [Some []; Some [true]; Some [true]; Some []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A cycle without a boundary leaves node 0 unseeded in the backward must solution. *)
  Example cycle_without_boundary_unseeded :
    match BUA.analyze 9 flat 8%N with
    | Solved m => Some (map (fun x => match BUC.look m x with
        | None => true | Some _ => false end) [0])
    | _ => None
    end = Some [true].
  Proof.
    vm_compute; reflexivity.
  Qed.

End BackwardTests.

(** * Paths *)

Module PathTests.

  (** The path 0 to 2 through the diamond gives facts 7 and 8, in that order. *)
  Example diamond_path_zero_two :
    Sets.elements (genkill_path Sets.union Sets.diff (Forward.gen 2) (Forward.kill 2)
      Sets.empty [0; 2]) = [7; 8].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The path 1 to 3 through the diamond gives no facts. *)
  Example diamond_path_one_three_empty :
    Sets.elements (genkill_path Sets.union Sets.diff (Forward.gen 2) (Forward.kill 2)
      Sets.empty [1; 3]) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The path of the singleton graph gives fact 7 from its initial value. *)
  Example singleton_path_gives_seven :
    Sets.elements (genkill_path Sets.union Sets.diff (Forward.gen 5) (Forward.kill 5)
      (Forward.init 5) []) = [7].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The may solution for program 11 is empty at nodes 0 and 1, and it has fact 7 at node 2. *)
  Example implicit_starts_not_absorbed_may :
    observe_may 11 [0; 1; 2] = Some [[]; []; [7]].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The path that starts at node 0 of program 11 has no facts. *)
  Example implicit_start_path_empty :
    Sets.elements (genkill_path Sets.union Sets.diff (Forward.gen 11) (Forward.kill 11)
      Sets.empty [0]) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End PathTests.

(** * Checks *)

Module CheckTests.

  (** Program 12 has no edges. *)
  Example unlisted_node_has_no_edges :
    Graph.edges 12 = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The may solution of the unlisted node 12 is empty at every key, including 99. *)
  Example unlisted_node_may_empty :
    observe_may 12 [0; 1; 99] = Some [[]; []; []].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Program 13 has two copies of its single flow edge, so its rows repeat the flow row. *)
  Example duplicate_edges_give_flow_rows :
    MS.rows 13 = [Seed 0; Flow 0; Flow 0].
  Proof.
    vm_compute; reflexivity.
  Qed.

End CheckTests.
