(** * Presentation observations

    First-order tables retain the observations of the presentation fixtures.
    For example, resolver targets remain in their supplied order.
    Builds on: Program presentation code and Base tries. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data.
From Galois.Program Require Import CfgSig Vars SsaSig Ssa CallsSig Calls IcfgSig Icfg MemorySig Memory.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Unit <: TYPE. Definition t := unit. End Unit.
Module BoolType <: TYPE. Definition t := bool. End BoolType.
Module Cfg <: CFG_INDEXED_OPS Prog NatKeyCode NatKeyCode.
  Definition entries (p : bool) := if p then [0] else [].
  Definition edges (p : bool) := if p then [0; 1; 2] else [].
  Definition src (_ : bool) e := match e with 0 => 0 | _ => 1 end.
  Definition dst (_ : bool) e := match e with 0 => 1 | 1 => 1 | _ => 2 end.
  Definition nodes (p : bool) := if p then [0; 1; 2] else [].
  Definition out (p : bool) n := if p then match n with 0 => [0] | 1 => [1; 2] | _ => [] end else [].
  Definition inc (p : bool) n := if p then match n with 1 => [0; 1] | 2 => [2] | _ => [] end else [].
End Cfg.

Module VarData <: VARS_DATA Prog NatKeyCode.
  Definition tables (_ : bool) := VarTables
    (PTrieCode.set (NatKeyCode.encode 0) [0; 1]
      (PTrieCode.set (NatKeyCode.encode 1) [1] (PTrieCode.set (NatKeyCode.encode 2) [1] Empty)))
    (PTrieCode.set (NatKeyCode.encode 0) [0]
      (PTrieCode.set (NatKeyCode.encode 1) [0] (PTrieCode.set (NatKeyCode.encode 2) [0] Empty)))
    (PTrieCode.set (NatKeyCode.encode 2) [2] Empty).
End VarData.
Module V := VarsCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode VarData.

Example variable_universe : V.universe true = [1; 0; 2].
Proof. vm_compute; reflexivity. Qed.
Example empty_variable_universe : V.universe false = [].
Proof. vm_compute; reflexivity. Qed.

Module SsaData <: SSA_DATA Prog NatKeyCode NatKeyCode NatKeyCode Unit BoolType.
  Definition tables (p : bool) : ssa_tables nat nat nat unit bool := SsaTables [0; 1] (if p then [0] else []) []
    (PTrieCode.set (NatKeyCode.encode 0) (Param 0 0)
      (PTrieCode.set (NatKeyCode.encode 1) (Op tt [0]) Empty))
    Empty 0 (PTrieCode.set (NatKeyCode.encode 0) [0] Empty) Empty
    (PTrieCode.set (NatKeyCode.encode 0) [(true, [0; 1])] Empty).
End SsaData.
Module S := SsaCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode Unit BoolType SsaData.
Example prepared_ssa_inventories :
  (S.entry_params true, S.entry_params false, S.arg_rows true) = ([0], [], []).
Proof. vm_compute; reflexivity. Qed.
Example multi_operand_guard : S.guards true 0 = [(true, [0; 1])].
Proof. vm_compute; reflexivity. Qed.
Example ssa_definition : S.def true 1 = Op tt [0].
Proof. vm_compute; reflexivity. Qed.

Module PointData <: SSA_POINTS_DATA Prog NatKeyCode NatKeyCode NatKeyCode NatKeyCode NatKeyCode.
  Definition tables (_ : bool) : ssa_point_tables nat nat nat nat nat := SsaPointTables Empty Empty Empty 0 Empty 0
    (PTrieCode.set (NatKeyCode.encode 2) 2 Empty)
    (PTrieCode.set (NatKeyCode.encode 0) [0] Empty)
    (PTrieCode.set (NatKeyCode.encode 1) [1] Empty) Empty.
End PointData.
Module SP := SsaPointsCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode NatKeyCode Cfg
  NatKeyCode V PointData.
Example point_projection :
  (SP.block_params true 0, SP.block_edge_args true 1, SP.block_edge_of true 2) = ([0], [1], Some 2).
Proof. vm_compute; reflexivity. Qed.
Example point_definition_absent : SP.point_definition true 0 = None.
Proof. vm_compute; reflexivity. Qed.

Module CallData <: CALLS_DATA Prog NatKeyCode NatKeyCode.
  Definition tables (_ : bool) := CallsTables [0; 1] [(0, 0); (0, 1)] [0]
    (PTrieCode.set (NatKeyCode.encode 0) [0; 1] Empty) Empty 0
    (PTrieCode.set (NatKeyCode.encode 0) [0; 1] Empty).
End CallData.
Module CallView := CallsCode Prog NatKeyCode NatKeyCode CallData.
Example prepared_call_inventory : CallView.calls true = [(0, 0); (0, 1)].
Proof. vm_compute; reflexivity. Qed.
Example recursive_call_edges :
  call_edges (CallView.resolve true) (CallView.sites_of true 0) = [CallEdge 0 0; CallEdge 0 1].
Proof. vm_compute; reflexivity. Qed.
Example unresolved_site : CallView.resolve true 1 = [].
Proof. vm_compute; reflexivity. Qed.
Example empty_calls : call_edges (CallView.resolve true) (CallView.sites_of true 1) = [].
Proof. vm_compute; reflexivity. Qed.

Module KindData <: ICFG_DATA Prog NatKeyCode.
  Definition kinds (_ : bool) :=
    PTrieCode.set (NatKeyCode.encode 0) (IcfgSig.Call 7)
      (PTrieCode.set (NatKeyCode.encode 2) (IcfgSig.Return 7) Empty).
End KindData.
Module I := IcfgCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode KindData.
Example icfg_kinds : (I.kind true 0, I.kind true 1, I.kind true 2) =
  (IcfgSig.Call 7, IcfgSig.Intra, IcfgSig.Return 7).
Proof. vm_compute; reflexivity. Qed.

Module FlagData <: EFFECTS_DATA Unit.
  Definition flags (_ : unit) := EffectFlags false false true false false false false false false.
End FlagData.
Module F := EffectsCode Unit FlagData.
Example effect_flags : (F.may_trap tt, F.observes tt) = (true, false).
Proof. vm_compute; reflexivity. Qed.
Example barrier_regions :
  (effect_reads true Barrier, effect_writes true Barrier) = ([true], [true]).
Proof. vm_compute; reflexivity. Qed.
Example pure_write_has_no_read : effect_reads true (Write false) = [].
Proof. vm_compute; reflexivity. Qed.

Example call_graph_successors :
  succs (CallView.call_graph true) (NatKeyCode.encode 0) =
    [NatKeyCode.encode 0; NatKeyCode.encode 1].
Proof. vm_compute; reflexivity. Qed.

Example allocation_and_free_writes :
  (effect_writes true (Alloc false), effect_writes true (Free false)) = ([false], [false]).
Proof. vm_compute; reflexivity. Qed.
