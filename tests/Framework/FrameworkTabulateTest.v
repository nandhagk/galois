(** * Actual symbolic tabulator clients

    These fixtures run the changed-key jump engine and the prefix-value engine.
    For example, a tainted callee prefix is reachable before its pending call returns.
    Builds on: FrameworkTabulate, FrameworkTabValues and FrameworkIdeTest. *)

From Stdlib Require Import List Bool NArith ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Domains Require Import DomainsPoint.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabValues.
From Galois.Tests.Framework Require Import FrameworkIdeTest.
Import List.ListNotations.

Definition completed {N E P D A F} (I : Ide.t N E P D A F) start fuel :=
  match Tab.tabulate I start fuel with
  | Tab.Certified c => Some (proj1_sig c)
  | _ => None
  end.

Definition completed_values {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel :=
  match TabValues.tabulate_values I J start a0 fuel with
  | TabValues.Certified c => Some (proj1_sig c)
  | _ => None
  end.

Definition three_functions : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2; 3; 4; 5; 6; 7]
    (fun n => if Nat.ltb n 7 then [n] else [])
    (fun e => e) S) nat_encoding nat_encoding.

Definition three_icfg :=
  Icfg.of_pure three_functions nat_encoding
    (fun e => match e with
    | 1 => Icfg.Call 7
    | 3 => Icfg.Return 7
    | 4 => Icfg.Call 8
    | 6 => Icfg.Return 8
    | _ => Icfg.Internal
    end).

Definition source_sink : Ifds.t nat nat nat unit :=
  Ifds.of_pure three_icfg unit_encoding [tt]
    (fun e d => match e, d with
    | 0, None => [None; Some tt]
    | 4, Some _ => []
    | _, _ => [d]
    end).

Definition source_sink_ide := Ifds.as_ide source_sink.
Definition source_sink_result := completed source_sink_ide 0 512%positive.

Example source_sink_certifies :
  option_map (check_jumps source_sink_ide 0) source_sink_result = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example taint_crosses_the_first_call :
  option_map (fun J => Jump.lookup source_sink_ide J ((0, None), (4, Some tt)))
    source_sink_result = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example taint_does_not_cross_the_killing_call :
  option_map (fun J => Jump.lookup source_sink_ide J ((0, None), (7, Some tt)))
    source_sink_result = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example pending_callee_is_not_a_balanced_jump :
  option_map (fun J => Jump.lookup source_sink_ide J ((0, None), (3, Some tt)))
    source_sink_result = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition prefixes :=
  match source_sink_result with
  | Some J => completed_values (TabValues.reach_ide source_sink) J (0, None) true 512%positive
  | None => None
  end.

Example pending_callee_prefix_is_reachable :
  option_map (fun V => TabValues.lookup (TabValues.reach_ide source_sink) V (3, Some tt))
    prefixes = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example killed_prefix_is_unreachable :
  option_map (fun V => TabValues.lookup (TabValues.reach_ide source_sink) V (7, Some tt))
    prefixes = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example tampered_return_rejected :
  option_map (fun J => check_jumps source_sink_ide 0
    (Map.remove positive_encoding
      (encode (Jump.enc source_sink_ide) ((0, None), (4, Some tt))) J))
    source_sink_result = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example exhausted_is_explicit :
  match Tab.tabulate source_sink_ide 0 1%positive with
  | Tab.Exhausted _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example uncertified_candidate_is_explicitly_rejected :
  match Cost.value (Tab.certify_c source_sink_ide 0
    (Tab.State Map.empty Map.empty Map.empty [] Map.empty)) with
  | Tab.Rejected _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition wrong_icfg :=
  Icfg.of_pure two_functions nat_encoding
    (fun e => match e with
    | 0 => Icfg.Call 7
    | 2 => Icfg.Return 8
    | _ => Icfg.Internal
    end).

Definition wrong_returns : Ifds.t nat nat nat unit :=
  Ifds.of_pure wrong_icfg unit_encoding [] (fun _ d => [d]).

Example wrong_return_site_does_not_match :
  option_map (fun J => Jump.lookup (Ifds.as_ide wrong_returns) J ((0, None), (3, None)))
    (completed (Ifds.as_ide wrong_returns) 0 64%positive) = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_certifies :
  option_map (check_jumps no_flow_ide 0)
    (completed no_flow_ide 0 8%positive) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_cfg : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [] [] (fun _ => []) (fun e => e) (fun e => e))
    nat_encoding nat_encoding.

Definition empty_ifds : Ifds.t nat nat nat unit :=
  Ifds.of_pure (Icfg.of_pure empty_cfg nat_encoding (fun _ => Icfg.Internal))
    unit_encoding [] (fun _ _ => []).

Example empty_inventory_keeps_the_start_identity :
  option_map (fun J => Jump.lookup (Ifds.as_ide empty_ifds) J ((0, None), (0, None)))
    (completed (Ifds.as_ide empty_ifds) 0 8%positive) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example unlisted_empty_start_is_an_informative_value_seed :
  match completed (TabValues.reach_ide empty_ifds) 99 8%positive with
  | Some J =>
    option_map (fun V => TabValues.lookup (TabValues.reach_ide empty_ifds) V (99, None))
      (completed_values (TabValues.reach_ide empty_ifds) J (99, None) true 8%positive)
  | None => None
  end = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition recursive_cfg : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2]
    (fun n => match n with 0 => [0] | 1 => [1; 2] | _ => [] end)
    (fun e => match e with 0 => 0 | _ => 1 end)
    (fun e => match e with 2 => 2 | _ => 1 end)) nat_encoding nat_encoding.

Definition recursive_ifds : Ifds.t nat nat nat unit :=
  Ifds.of_pure
    (Icfg.of_pure recursive_cfg nat_encoding
      (fun e => match e with 2 => Icfg.Return 7 | _ => Icfg.Call 7 end))
    unit_encoding [] (fun _ d => [d]).

Example recursive_call_returns :
  option_map (fun J => Jump.lookup (Ifds.as_ide recursive_ifds) J ((0, None), (2, None)))
    (completed (Ifds.as_ide recursive_ifds) 0 128%positive) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example infinite_carrier_translations_certify :
  option_map (check_jumps affine 0) (completed affine 0 64%positive) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example infinite_carrier_translation_values :
  match completed affine 0 64%positive with
  | Some J => option_map (fun V =>
      TabValues.lookup affine V (3, None))
      (completed_values affine J (0, None) (PVal 41) 64%positive)
  | None => None
  end = Some (PVal 42).
Proof.
  vm_compute; reflexivity.
Qed.

Example value_exhaustion_is_explicit :
  match completed affine 0 64%positive with
  | Some J =>
    match TabValues.tabulate_values affine J (0, None) (PVal 41) 1%positive with
    | TabValues.Exhausted _ => true
    | _ => false
    end
  | None => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition linear_constants :=
  Ide.Make affine_ifds point_lattice noncommuting_micro
    (fun e _ _ => Cost.ret
      (match e with
      | 0 => FLinear 1 1
      | 1 => FLinear 2 0
      | _ => FLinear 1 3
      end)).

Example affine_noncommuting_jump_runs :
  option_map (fun J => Jump.lookup linear_constants J ((0, None), (3, None)))
    (completed linear_constants 0 64%positive) = Some (FLinear 2 5).
Proof.
  vm_compute; reflexivity.
Qed.

Example affine_noncommuting_values_run :
  match completed linear_constants 0 64%positive with
  | Some J => option_map (fun V => TabValues.lookup linear_constants V (3, None))
      (completed_values linear_constants J (0, None) (PVal 4) 64%positive)
  | None => None
  end = Some (PVal 13).
Proof.
  vm_compute; reflexivity.
Qed.

Definition diamond_cfg : Cfg.t nat nat :=
  Cfg.Make (Graph.of_pure [0] [0; 1; 2; 3; 4]
    (fun n => match n with
    | 0 => [0; 1]
    | 1 => [2]
    | 2 => [3]
    | 3 => [4]
    | _ => []
    end)
    (fun e => match e with 0 | 1 => 0 | 2 => 1 | 3 => 2 | _ => 3 end)
    (fun e => match e with 0 => 1 | 1 => 2 | 2 | 3 => 3 | _ => 4 end))
    nat_encoding nat_encoding.

Definition diamond_ifds : Ifds.t nat nat nat unit :=
  Ifds.of_pure (Icfg.of_pure diamond_cfg nat_encoding (fun _ => Icfg.Internal))
    unit_encoding [] (fun _ d => [d]).

Definition upper_diamond : Ide.t nat nat nat unit point affine_fn :=
  Ide.Make diamond_ifds point_lattice noncommuting_micro
    (fun e _ _ => Cost.ret
      (match e with
      | 1 => FLinear 0 0
      | 4 => FLinear 0 7
      | _ => FLinear 1 0
      end)).

Example nondistributive_diamond_certifies :
  option_map (check_jumps upper_diamond 0) (completed upper_diamond 0 128%positive) =
    Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nondistributive_diamond_jump :
  option_map (fun J => Jump.lookup upper_diamond J ((0, None), (4, None)))
    (completed upper_diamond 0 128%positive) = Some FAny.
Proof.
  vm_compute; reflexivity.
Qed.

Definition diamond_left_weight :=
  Micro.compose noncommuting_micro (FLinear 0 7)
    (Micro.compose noncommuting_micro (FLinear 1 0) (FLinear 1 0)).

Definition diamond_right_weight :=
  Micro.compose noncommuting_micro (FLinear 0 7)
    (Micro.compose noncommuting_micro (FLinear 1 0) (FLinear 0 0)).

Example nondistributive_diamond_path_join_is_smaller :
  (join (Micro.lat noncommuting_micro) diamond_left_weight diamond_right_weight,
   leb (Micro.lat noncommuting_micro) FAny
     (join (Micro.lat noncommuting_micro) diamond_left_weight diamond_right_weight)) =
    (FLinear 0 7, false).
Proof.
  vm_compute; reflexivity.
Qed.
