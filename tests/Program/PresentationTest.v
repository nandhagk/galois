(** * Presentation observations

    First-order tables keep the observations of the presentation fixtures.
    For example, resolver targets remain in their supplied order.

    Groups:
    - Variables: the variable universe lists the variables in order, and an empty program has none.
    - Ssa: the SSA inventories give entry parameters, guards and definitions.
    - Points: the point projections give block parameters, edge arguments and definitions.
    - Calls: the call inventory, resolved sites and call graph keep their order.
    - Icfg: the edge kinds of the interprocedural graph.
    - Effects: the effect flags and the reads and writes of each effect.

    Builds on: Program presentation code and Base tries. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data.
From Galois.Program Require Import CfgSig Vars SsaSig Ssa CallsSig Calls IcfgSig Icfg MemorySig Memory.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := bool. End Prog.
Module Unit <: TYPE. Definition t := unit. End Unit.
Module BoolType <: TYPE. Definition t := bool. End BoolType.

(** A CFG with edges 0, 1 and 2 when the program is true, and nodes 0, 1 and 2. *)
Module Cfg <: CFG_INDEXED_OPS Prog NatKeyCode NatKeyCode.
  Definition entries (p : bool) := if p then [0] else [].
  Definition edges (p : bool) := if p then [0; 1; 2] else [].
  Definition src (_ : bool) e := match e with 0 => 0 | _ => 1 end.
  Definition dst (_ : bool) e := match e with 0 => 1 | 1 => 1 | _ => 2 end.
  Definition nodes (p : bool) := if p then [0; 1; 2] else [].
  Definition out (p : bool) n := if p then match n with 0 => [0] | 1 => [1; 2] | _ => [] end else [].
  Definition inc (p : bool) n := if p then match n with 1 => [0; 1] | 2 => [2] | _ => [] end else [].
End Cfg.

(** * Variables *)

Module VariableTests.

  (** The variable tables of the program, with variables 0, 1 and 2. *)
  Module VarData <: VARS_DATA Prog NatKeyCode.
    Definition tables (_ : bool) := VarTables
      (PTrieCode.set (NatKeyCode.encode 0) [0; 1]
        (PTrieCode.set (NatKeyCode.encode 1) [1] (PTrieCode.set (NatKeyCode.encode 2) [1] Empty)))
      (PTrieCode.set (NatKeyCode.encode 0) [0]
        (PTrieCode.set (NatKeyCode.encode 1) [0] (PTrieCode.set (NatKeyCode.encode 2) [0] Empty)))
      (PTrieCode.set (NatKeyCode.encode 2) [2] Empty).
  End VarData.

  Module V := VarsCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode VarData.

  (** The universe of the program lists the variables 1, 0 and 2 in that order. *)
  Example universe_in_order : V.universe true = [1; 0; 2].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A program without entries has an empty universe. *)
  Example empty_program_no_variables : V.universe false = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

End VariableTests.

(** * Ssa *)

Module SsaTests.

  (** The SSA tables with parameters, one operation and a guard with two operands. *)
  Module SsaData <: SSA_DATA Prog NatKeyCode NatKeyCode NatKeyCode Unit BoolType.
    Definition tables (p : bool) : ssa_tables nat nat nat unit bool :=
      SsaTables [0; 1] (if p then [0] else []) []
        (PTrieCode.set (NatKeyCode.encode 0) (Param 0 0)
          (PTrieCode.set (NatKeyCode.encode 1) (Op tt [0]) Empty))
        Empty 0 (PTrieCode.set (NatKeyCode.encode 0) [0] Empty) Empty
        (PTrieCode.set (NatKeyCode.encode 0) [(true, [0; 1])] Empty).
  End SsaData.

  Module S := SsaCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode Unit BoolType SsaData.

  (** The program's entry parameters are [0], and it has no argument rows. *)
  Example entry_parameters_and_arg_rows :
    (S.entry_params true, S.entry_params false, S.arg_rows true) = ([0], [], []).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The guard of value 0 keeps both of its operands. *)
  Example guard_keeps_both_operands : S.guards true 0 = [(true, [0; 1])].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Value 1 is defined by the operation over value 0. *)
  Example definition_of_value_one : S.def true 1 = Op tt [0].
  Proof.
    vm_compute; reflexivity.
  Qed.

End SsaTests.

(** * Points *)

Module PointTests.

  (** The point tables with block parameters, edge arguments and an edge of block 2. *)
  Module PointData <: SSA_POINTS_DATA Prog NatKeyCode NatKeyCode NatKeyCode NatKeyCode NatKeyCode.
    Definition tables (_ : bool) : ssa_point_tables nat nat nat nat nat :=
      SsaPointTables Empty Empty Empty 0 Empty 0
        (PTrieCode.set (NatKeyCode.encode 2) 2 Empty)
        (PTrieCode.set (NatKeyCode.encode 0) [0] Empty)
        (PTrieCode.set (NatKeyCode.encode 1) [1] Empty) Empty.
  End PointData.

  Module SP := SsaPointsCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode NatKeyCode Cfg
    NatKeyCode VariableTests.V PointData.

  (** The block projections give parameters [0], arguments [1], and edge 2 of block 2. *)
  Example block_projections :
    (SP.block_params true 0, SP.block_edge_args true 1, SP.block_edge_of true 2) =
      ([0], [1], Some 2).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A point with no definition has none. *)
  Example absent_point_has_no_definition : SP.point_definition true 0 = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

End PointTests.

(** * Calls *)

Module CallTests.

  (** The call tables with sites 0 and 1 and the single function 0. *)
  Module CallData <: CALLS_DATA Prog NatKeyCode NatKeyCode.
    Definition tables (_ : bool) := CallsTables [0; 1] [(0, 0); (0, 1)] [0]
      (PTrieCode.set (NatKeyCode.encode 0) [0; 1] Empty) Empty 0
      (PTrieCode.set (NatKeyCode.encode 0) [0; 1] Empty).
  End CallData.

  Module CallView := CallsCode Prog NatKeyCode NatKeyCode CallData.
  Module CallFull := Calls Prog NatKey NatKey CallData.
  Module CallContract <: CALLS Prog NatKey NatKey := CallFull.

  (** The call record is a pair of call tables. *)
  Module CallRecord <: TYPE. Definition t := calls_tables nat nat. End CallRecord.

  Module PlainCallData <: CALLS_DATA CallRecord NatKey NatKey.
    Definition tables (p : CallRecord.t) := p.
  End PlainCallData.

  Module PlainCalls := Calls CallRecord NatKey NatKey PlainCallData.
  Module PlainCallContract <: CALLS CallRecord NatKey NatKey := PlainCalls.

  (** The call inventory lists the pairs (0, 0) and (0, 1) in order. *)
  Example call_inventory_in_order : CallView.calls true = [(0, 0); (0, 1)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Site 0 of function 0 gives the call edges to 0 and to 1. *)
  Example self_call_edges :
    call_edges (CallView.resolve true) (CallView.sites_of true 0) = [CallEdge 0 0; CallEdge 0 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unresolved site has no targets. *)
  Example unresolved_site_no_targets : CallView.resolve true 1 = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A function without sites has no call edges. *)
  Example function_without_sites_no_edges :
    call_edges (CallView.resolve true) (CallView.sites_of true 1) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The call graph of program true has successors 0 and 1 from node 0, in order. *)
  Example call_graph_successors :
    succs (CallView.call_graph true) (NatKeyCode.encode 0) =
      [NatKeyCode.encode 0; NatKeyCode.encode 1].
  Proof.
    vm_compute; reflexivity.
  Qed.

End CallTests.

(** * Icfg *)

Module IcfgTests.

  (** The kinds of edges 0 and 2 are a call and a return, and edge 1 is internal. *)
  Module KindData <: ICFG_DATA Prog NatKeyCode.
    Definition kinds (_ : bool) :=
      PTrieCode.set (NatKeyCode.encode 0) (IcfgSig.Call 7)
        (PTrieCode.set (NatKeyCode.encode 2) (IcfgSig.Return 7) Empty).
  End KindData.

  Module I := IcfgCode Prog NatKeyCode NatKeyCode Cfg NatKeyCode KindData.

  (** The three edges have the kinds call, internal and return. *)
  Example edge_kinds : (I.kind true 0, I.kind true 1, I.kind true 2) =
    (IcfgSig.Call 7, IcfgSig.Intra, IcfgSig.Return 7).
  Proof.
    vm_compute; reflexivity.
  Qed.

End IcfgTests.

(** * Effects *)

Module EffectTests.

  (** The effect flags set may trap and do not observe. *)
  Module FlagData <: EFFECTS_DATA Unit.
    Definition flags (_ : unit) := EffectFlags false false true false false false false false false.
  End FlagData.

  Module F := EffectsCode Unit FlagData.

  (** The flagged effect may trap and does not observe. *)
  Example flags_may_trap_not_observe : (F.may_trap tt, F.observes tt) = (true, false).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A barrier reads and writes the region of the program. *)
  Example barrier_reads_and_writes :
    (effect_reads true Barrier, effect_writes true Barrier) = ([true], [true]).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A pure write has no read. *)
  Example write_has_no_read : effect_reads true (Write false) = [].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An allocation and a free each write their region. *)
  Example alloc_and_free_write :
    (effect_writes true (Alloc false), effect_writes true (Free false)) = ([false], [false]).
  Proof.
    vm_compute; reflexivity.
  Qed.

End EffectTests.
