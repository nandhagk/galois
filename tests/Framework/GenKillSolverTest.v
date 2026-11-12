(** * Gen/kill solver observations

    Certified worklists run the old loop, diamond and disconnected fixtures.
    For example, an unreachable generator still contributes to the may solution.
    Builds on: Framework.GenKill and Fixpoint.Certified. *)

From Stdlib Require Import List Bool NArith.
From Galois.Base Require Import KeySig Key Trie TrieSet Heap.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig GenKillSig GenKill.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := nat. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Sets := TrieSetCode NatKeyCode.
Definition facts (xs : list nat) := fold_left (fun s x => Sets.add x s) xs Sets.empty.
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
    | _ => []
    end.
  Definition src p e := match p with
    | 0 | 1 | 7 => if Nat.eqb e 0 then 0 else 1
    | 2 | 8 => match e with 2 => 1 | 3 => 2 | _ => 0 end
    | 6 | 10 => 1
    | _ => 0
    end.
  Definition dst p e := match p with
    | 0 | 1 | 7 => if Nat.eqb e 2 then 2 else 1
    | 2 | 8 => match e with 0 => 1 | 1 => 2 | _ => 3 end
    | 6 | 10 => 2
    | _ => 0
    end.
End Graph.
Module Forward <: GENKILL_OPS Prog Edge NatKeyCode Sets.
  Definition dir := Forward.
  Definition may := true.
  Definition gen p e := facts (match p, e with
    | 1, 0 => [0] | 1, 1 => [1]
    | 2, 0 => [7] | 2, 2 => [8]
    | 6, _ => [7] | _, _ => [] end).
  Definition kill p e := facts (match p, e with 1, 1 => [0] | 10, _ => [7] | _, _ => [] end).
  Definition init p := facts (match p with 4 | 5 | 10 => [7] | _ => [] end).
End Forward.
Module Backward <: GENKILL_OPS Prog Edge NatKeyCode Sets.
  Definition dir := Backward.
  Definition may := true.
  Definition gen p e := facts (match p, e with
    | 0, 1 => [0] | 0, 2 => [1] | 7, 1 => [7]
    | 8, 2 | 8, 3 | 9, _ => [1] | _, _ => [] end).
  Definition kill p e := facts (match p, e with 0, 0 => [0] | 8, 0 | 9, _ => [1] | _, _ => [] end).
  Definition init (_ : nat) := Sets.empty.
End Backward.
Module MayLat <: WLATTICE_OPS.
  Include GenKillMayDomainCode NatKeyCode Sets.
  Definition wparam := unit.
  Definition widen (_ : unit) := join.
  Definition narrow := Sets.inter.
End MayLat.
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
Definition flat : policy unit := Policy unit PTrieCode.empty PTrieCode.empty tt 0.
Definition observe_may p xs := match MA.analyze p flat 16%N with
  | Solved m => Some (map (fun x => Sets.elements (MC.look m x)) xs)
  | _ => None
  end.
Definition observe_back p xs := match BA.analyze p flat 16%N with
  | Solved m => Some (map (fun x => Sets.elements (BC.look m x)) xs)
  | _ => None
  end.
Definition observe_must p xs := match UA.analyze p flat 16%N with
  | Solved m => Some (map (fun x => option_map Sets.elements (UC.look m x)) xs)
  | _ => None
  end.

Example liveness_loop : observe_back 0 [0; 1; 2] = Some [[1]; [1; 0]; []].
Proof. vm_compute; reflexivity. Qed.

Example reaching_loop : observe_may 1 [0; 1; 2] = Some [[]; [1; 0]; [1; 0]].
Proof. vm_compute; reflexivity. Qed.

Example available_diamond : observe_must 2 [0; 1; 2; 3; 99] =
  Some [Some []; Some [7]; Some []; Some []; None].
Proof. vm_compute; reflexivity. Qed.

Example empty_may : observe_may 3 [0] = Some [[]].
Proof. vm_compute; reflexivity. Qed.

Example empty_must : observe_must 3 [0] = Some [None].
Proof. vm_compute; reflexivity. Qed.

Example may_entry_absent_from_nodes : observe_may 4 [0; 99] = Some [[7]; []].
Proof. vm_compute; reflexivity. Qed.

Example must_entry_absent_from_nodes : observe_must 4 [0; 99] = Some [Some [7]; None].
Proof. vm_compute; reflexivity. Qed.

Example singleton_may_solver : observe_may 5 [0; 1] = Some [[7]; []].
Proof. vm_compute; reflexivity. Qed.

Example singleton_must_solver : observe_must 5 [0; 1] = Some [Some [7]; None].
Proof. vm_compute; reflexivity. Qed.

Example unreachable_generation_solver : observe_may 6 [0; 1; 2] = Some [[]; []; [7]].
Proof. vm_compute; reflexivity. Qed.

Example unreachable_generation_must_stays_fresh :
  observe_must 6 [0; 1; 2] = Some [Some []; None; None].
Proof. vm_compute; reflexivity. Qed.

Example backward_finite_use_solver : observe_back 7 [0; 1; 2] = Some [[7]; [7]; []].
Proof. vm_compute; reflexivity. Qed.

Example may_closed_seed_control : observe_may 5 [0; 99] = Some [[7]; []].
Proof. vm_compute; reflexivity. Qed.

Example must_closed_seed_control : observe_must 5 [0; 99] = Some [Some [7]; None].
Proof. vm_compute; reflexivity. Qed.

Example unreachable_kill_is_strict :
  observe_must 10 [0; 1; 2] = Some [Some [7]; None; None] /\
  option_map Sets.elements (UF.transfer 10 0 (Some (facts [7]))) = Some [].
Proof. vm_compute; split; reflexivity. Qed.

Example invalidation_solver :
  match BUA.analyze 8 flat 16%N with
  | Solved m => Some (map (fun x => option_map (fun s => map (Nat.eqb 1) (Sets.elements s))
      (BUC.look m x)) [0; 1; 2; 3])
  | _ => None
  end = Some [Some []; Some [true]; Some [true]; Some []].
Proof. vm_compute; reflexivity. Qed.

Example no_boundary_cycle_solver_all :
  match BUA.analyze 9 flat 8%N with
  | Solved m => Some (map (fun x => match BUC.look m x with
      | None => true | Some _ => false end) [0])
  | _ => None
  end = Some [true].
Proof. vm_compute; reflexivity. Qed.

Example diamond_enumerated_path_values :
  (Sets.elements (genkill_path Sets.union Sets.diff (Forward.gen 2) (Forward.kill 2)
     Sets.empty [0; 2]),
   Sets.elements (genkill_path Sets.union Sets.diff (Forward.gen 2) (Forward.kill 2)
     Sets.empty [1; 3])) = ([7; 8], []).
Proof. vm_compute; reflexivity. Qed.

Definition check_may p look := forallb (fun r =>
  row_ok MayLat.leb look (MS.target p r)
    (eval_query (MS.resume p) look (S (length (MS.deps p r))) (MS.start p r))) (MS.rows p).
Definition check_must p look := forallb (fun r =>
  row_ok MustLat.leb look (US.target p r)
    (eval_query (US.resume p) look (S (length (US.deps p r))) (US.start p r))) (US.rows p).

Example must_hand_candidate :
  check_must 2 (fun n => Some (facts (if Nat.eqb n 1 then [7] else []))) = true.
Proof. vm_compute; reflexivity. Qed.

Example must_wrong_join_rejected : check_must 2 (fun _ => Some (facts [7])) = false.
Proof. vm_compute; reflexivity. Qed.

Example unreachable_generation_equation_rejects_empty :
  check_may 6 (fun _ => Sets.empty) = false.
Proof. vm_compute; reflexivity. Qed.

Example missing_may_raw_seed_rejected : check_may 4 (fun _ => Sets.empty) = false.
Proof. vm_compute; reflexivity. Qed.

Example missing_must_raw_seed_rejected : check_must 4 (fun _ => None) = false.
Proof. vm_compute; reflexivity. Qed.

Example strict_all_is_not_finite_universe :
  UF.transfer 6 0 None = None /\ UF.transfer 6 0 (Some (facts [7])) <> None.
Proof. vm_compute; split; [reflexivity|discriminate]. Qed.
