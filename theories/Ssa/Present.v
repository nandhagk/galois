(** * Language control-flow occurrences

    Edges retain the source block and the selected exit arm.
    For example, two arms aimed at the same block remain distinct.
    Builds on: Ssa.Lang. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Code KeySig Key Trie.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang ValidateSig.
Import List.ListNotations.

Inductive exit_arm :=
  | Jump_arm
  | True_arm
  | False_arm.

Record block_edge := BlockEdge {
  edge_source : positive;
  edge_arm : exit_arm;
  edge_target : positive;
  edge_arguments : list positive
}.

Definition exit_edges {G} (source : positive) (e : exit positive G) : list block_edge :=
  match e with
  | Jump target args => [BlockEdge source Jump_arm target args]
  | Branch _ _ yes yes_args no no_args =>
      [BlockEdge source True_arm yes yes_args; BlockEdge source False_arm no no_args]
  | Return _ => []
  end.
TimeFun exit_edges.

Definition language_edges {K G} (p : func positive K G) : list block_edge :=
  flat_map (fun item => exit_edges (fst item) (term _ _ _ (snd item))) (blocks _ _ _ p).
TimeFun language_edges.

TimeFun edge_source.
TimeFun edge_target.
TimeFun edge_arm.
TimeFun edge_arguments.

Module LangProgram (O : OPS) <: TYPE.
  Definition t := func positive O.K O.G.
End LangProgram.

Module ArmKeyCode <: KEY_OPS.
  Definition t := exit_arm.
  Definition encode a := match a with Jump_arm => 1%positive | True_arm => 2%positive
    | False_arm => 3%positive end.
  Definition eqb a b := match a, b with
    | Jump_arm, Jump_arm | True_arm, True_arm | False_arm, False_arm => true
    | _, _ => false
    end.
End ArmKeyCode.

Module ArmKey <: KEY.
  Include ArmKeyCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. Admitted. (* STUB *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. Admitted. (* STUB *)
End ArmKey.

Module ArmKeyT <: KEY_T.
  Include ArmKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End ArmKeyT.

Module EdgeArgsKey := ListKeyT PosKeyT.
Module EdgeTargetArgsKey := PairKeyT PosKeyT EdgeArgsKey.
Module EdgeArmTargetArgsKey := PairKeyT ArmKeyT EdgeTargetArgsKey.
Module EdgeTupleKey := PairKeyT PosKeyT EdgeArmTargetArgsKey.

Definition block_edge_tuple (e : block_edge) : EdgeTupleKey.t :=
  (edge_source e, (edge_arm e, (edge_target e, edge_arguments e))).
TimeFun block_edge_tuple.

Module BlockEdgeCode <: KEY_OPS.
  Definition t := block_edge.
  Definition encode e := EdgeTupleKey.encode (block_edge_tuple e).
  Definition eqb a b := EdgeTupleKey.eqb (block_edge_tuple a) (block_edge_tuple b).
End BlockEdgeCode.

Module BlockEdgeKey <: KEY.
  Include BlockEdgeCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. Admitted. (* STUB *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. Admitted. (* STUB *)
End BlockEdgeKey.

Module BlockEdge <: KEY_T.
  Include BlockEdgeKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End BlockEdge.

Module BlockCfgCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    <: CFG_INDEXED_OPS P PosKeyCode BlockEdge.
  Definition entries (p : P.t) := [entry _ _ _ p].
  Definition edges (p : P.t) := language_edges p.
  Definition src (_ : P.t) (e : block_edge) := edge_source e.
  Definition dst (_ : P.t) (e : block_edge) := edge_target e.
  Definition nodes (p : P.t) := map fst (blocks _ _ _ p).
  Definition out (p : P.t) b :=
    filter (fun e => Pos.eqb (edge_source e) b) (edges p).
  Definition inc (p : P.t) b :=
    filter (fun e => Pos.eqb (edge_target e) b) (edges p).
End BlockCfgCode.

Module BlockCfg (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    <: CFG P PosKey BlockEdge.
  Include BlockCfgCode O P.
  Definition wf (p : P.t) := ssa_wf p.
  Lemma nodes_nodup : forall p, wf p -> NoDup (nodes p).
  Proof. Admitted. (* STUB *)
  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof. Admitted. (* STUB *)
  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof. Admitted. (* STUB *)
  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof. Admitted. (* STUB *)
  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof. Admitted. (* STUB *)
End BlockCfg.

Module BlockCfgT (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    <: CFG_T P PosKeyT BlockEdge.
  Include BlockCfg O P.
  TimeFun entries.
  TimeFun edges.
  TimeFun src.
  TimeFun dst.
  TimeFun nodes.
  TimeFun out.
  TimeFun inc.
  Definition c_cfg : N := 1. (* STUB *)
  Definition c_cfg_adj : N := 1. (* STUB *)
  Lemma T_entries_le : forall p,
    (T_entries p <= c_cfg * N.of_nat (length (entries p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_edges_le : forall p,
    (T_edges p <= c_cfg * N.of_nat (length (edges p) + 1))%N.
  Proof. Admitted. (* SIG-QUESTION: scanning return blocks is not bounded by output edges *)
  Lemma T_src_le : forall p e, (T_src p e <= c_cfg)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_dst_le : forall p e, (T_dst p e <= c_cfg)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_nodes_le : forall p,
    (T_nodes p <= c_cfg_adj * N.of_nat (length (nodes p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_out_le : forall p n,
    (T_out p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (out p n) + 1))%N.
  Proof. Admitted. (* SIG-QUESTION: filtering scans edges absent from the output *)
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (inc p n) + 1))%N.
  Proof. Admitted. (* SIG-QUESTION: filtering scans edges absent from the output *)
End BlockCfgT.

Module BlockSsaCode (O : OPS)
    (K : TYPE with Definition t := O.K) (G : TYPE with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (C : CFG_INDEXED_OPS P PosKeyCode BlockEdge)
    <: SSA_OPS P PosKeyCode BlockEdge C PosKeyCode K G.
  (* STUB-CODE *)
  Definition values (_ : P.t) : list positive := [].
  (* STUB-CODE *)
  Definition def (_ : P.t) (_ : positive) : definition positive positive O.K := Arbitrary.
  (* STUB-CODE *)
  Definition home (_ : P.t) (_ : positive) : positive := 1%positive.
  Definition params (p : P.t) (b : positive) : list positive :=
    match find_block b (blocks _ _ _ p) with
    | Some body => Lang.params _ _ _ body
    | None => []
    end.
  (* STUB-CODE *)
  Definition args (_ : P.t) (_ : block_edge) : list (positive * positive) := [].
  (* STUB-CODE *)
  Definition guards (_ : P.t) (_ : block_edge) : list (O.G * list positive) := [].
End BlockSsaCode.

Module BlockSsa (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (C : CFG P PosKey BlockEdge)
    <: SSA P PosKey BlockEdge C PosKey K G.
  Include BlockSsaCode O K G P C.
  Include SSA_SPEC P PosKey BlockEdge C PosKey K G.
  Definition wf (p : P.t) := ssa_wf p.
  Lemma cfg_wf : forall p, wf p -> C.wf p.
  Proof. Admitted. (* STUB *)
  Lemma values_nodup : forall p, wf p -> NoDup (values p).
  Proof. Admitted. (* STUB *)
  Lemma homes_listed : forall p x, wf p -> In x (values p) -> In (home p x) (C.nodes p).
  Proof. Admitted. (* STUB *)
  Lemma param_defs : forall p x b i, wf p ->
    (def p x = Param b i <-> nth_error (params p b) i = Some x).
  Proof. Admitted. (* STUB *)
  Lemma param_home : forall p b x, wf p -> In x (params p b) -> home p x = b.
  Proof. Admitted. (* STUB *)
  Lemma params_listed : forall p b x, wf p -> In b (C.nodes p) ->
    In x (params p b) -> In x (values p).
  Proof. Admitted. (* STUB *)
  Lemma args_params : forall p e, wf p -> In e (C.edges p) ->
    map fst (args p e) = params p (C.dst p e).
  Proof. Admitted. (* STUB *)
  Lemma args_dominate : forall p e x y, wf p -> In e (C.edges p) ->
    In (x, y) (args p e) -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p y) route.
  Proof. Admitted. (* STUB *)
  Lemma guards_dominate : forall p e g xs x, wf p -> In e (C.edges p) ->
    In (g, xs) (guards p e) -> In x xs -> In x (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p x) route.
  Proof. Admitted. (* STUB *)
  Lemma op_args_dominate : forall p x op xs y, wf p -> In x (values p) ->
    def p x = Op op xs -> In y xs -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (home p x) ->
      In (home p y) route.
  Proof. Admitted. (* STUB *)
  Lemma op_args_acyclic : forall p, wf p ->
    well_founded (fun y x => In x (values p) /\ home p y = home p x /\
      exists op xs, def p x = Op op xs /\ In y xs).
  Proof. Admitted. (* STUB *)
End BlockSsa.

Module BlockSsaT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (C : CFG_T P PosKeyT BlockEdge)
    <: SSA_T P PosKeyT BlockEdge C PosKeyT K G.
  Include BlockSsa O K G P C.
  TimeFun values.
  TimeFun def.
  TimeFun home.
  TimeFun params.
  TimeFun args.
  TimeFun guards.
  Definition c_ssa : N := 1. (* STUB *)
  (** The value inventory pays for its output. *)
  Lemma T_values_le : forall p,
    (T_values p <= c_ssa * N.of_nat (length (values p) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Definition lookup pays for the value key and the returned operands. *)
  Lemma T_def_le : forall p x,
    (T_def p x <= c_ssa * N.of_nat (PosKeyT.bits x + length (operands p x) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Home lookup pays for the value key. *)
  Lemma T_home_le : forall p x, (T_home p x <= c_ssa * N.of_nat (PosKeyT.bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Parameter lookup pays for the node key and the returned values. *)
  Lemma T_params_le : forall p n,
    (T_params p n <= c_ssa * N.of_nat (PosKeyT.bits n + length (params p n) + 1))%N.
  Proof. Admitted. (* SIG-QUESTION: linear block lookup exceeds this key and output budget *)
  (** Incoming operands pay for the edge key and the returned pairs. *)
  Lemma T_args_le : forall p e,
    (T_args p e <= c_ssa * N.of_nat (BlockEdge.bits e + length (args p e) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Guards pay for the edge key and the returned guard list. *)
  Lemma T_guards_le : forall p e,
    (T_guards p e <= c_ssa * N.of_nat (BlockEdge.bits e + length (guards p e) + 1))%N.
  Proof. Admitted. (* STUB *)
End BlockSsaT.

Module PointKey := PairKeyT PosKeyT NKeyT.

Record point_edge := PointEdge {
  point_src : PointKey.t;
  point_dst : PointKey.t;
  point_block_edge : option block_edge
}.

TimeFun point_src.
TimeFun point_dst.
TimeFun point_block_edge.
Module OptionalBlockEdgeKey := OptionKeyT BlockEdge.
Module PointTargetEdgeKey := PairKeyT PointKey OptionalBlockEdgeKey.
Module PointEdgeTupleKey := PairKeyT PointKey PointTargetEdgeKey.

Definition point_edge_tuple (e : point_edge) : PointEdgeTupleKey.t :=
  (point_src e, (point_dst e, point_block_edge e)).
TimeFun point_edge_tuple.

Module PointEdgeCode <: KEY_OPS.
  Definition t := point_edge.
  Definition encode e := PointEdgeTupleKey.encode (point_edge_tuple e).
  Definition eqb a b := PointEdgeTupleKey.eqb (point_edge_tuple a) (point_edge_tuple b).
End PointEdgeCode.

Module PointEdgeKey <: KEY.
  Include PointEdgeCode.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof. Admitted. (* STUB *)
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof. Admitted. (* STUB *)
End PointEdgeKey.

Module PointEdge <: KEY_T.
  Include PointEdgeKey.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End PointEdge.

Module PointCfgCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    <: CFG_INDEXED_OPS P PointKey PointEdge.
  (* STUB-CODE *)
  Definition entries (_ : P.t) : list PointKey.t := [].
  (* STUB-CODE *)
  Definition edges (_ : P.t) : list point_edge := [].
  Definition src (_ : P.t) (e : point_edge) := point_src e.
  Definition dst (_ : P.t) (e : point_edge) := point_dst e.
  (* STUB-CODE *)
  Definition nodes (_ : P.t) : list PointKey.t := [].
  (* STUB-CODE *)
  Definition out (_ : P.t) (_ : PointKey.t) : list point_edge := [].
  (* STUB-CODE *)
  Definition inc (_ : P.t) (_ : PointKey.t) : list point_edge := [].
End PointCfgCode.

Module PointCfg (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    <: CFG P PointKey PointEdge.
  Include PointCfgCode O P.
  Definition wf (p : P.t) := ssa_wf p.
  Lemma nodes_nodup : forall p, wf p -> NoDup (nodes p).
  Proof. Admitted. (* STUB *)
  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof. Admitted. (* STUB *)
  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof. Admitted. (* STUB *)
  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof. Admitted. (* STUB *)
  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof. Admitted. (* STUB *)
End PointCfg.

Module PointCfgT (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    <: CFG_T P PointKey PointEdge.
  Include PointCfg O P.
  TimeFun entries.
  TimeFun edges.
  TimeFun src.
  TimeFun dst.
  TimeFun nodes.
  TimeFun out.
  TimeFun inc.
  Definition c_cfg : N := 1. (* STUB *)
  Definition c_cfg_adj : N := 1. (* STUB *)
  Lemma T_entries_le : forall p,
    (T_entries p <= c_cfg * N.of_nat (length (entries p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_edges_le : forall p,
    (T_edges p <= c_cfg * N.of_nat (length (edges p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_src_le : forall p e, (T_src p e <= c_cfg)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_dst_le : forall p e, (T_dst p e <= c_cfg)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_nodes_le : forall p,
    (T_nodes p <= c_cfg_adj * N.of_nat (length (nodes p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_out_le : forall p n,
    (T_out p n <= c_cfg_adj * N.of_nat (PointKey.bits n + length (out p n) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PointKey.bits n + length (inc p n) + 1))%N.
  Proof. Admitted. (* STUB *)
End PointCfgT.

Module PointVarsCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (C : CFG_INDEXED_OPS P PointKey PointEdge)
    <: VARS_OPS P PointKey PointEdge C PosKeyCode.
  (* STUB-CODE *)
  Definition uses (_ : P.t) (_ : point_edge) : list positive := [].
  (* STUB-CODE *)
  Definition defs (_ : P.t) (_ : point_edge) : list positive := [].
  (* STUB-CODE *)
  Definition exits (_ : P.t) (_ : PointKey.t) : list positive := [].
  (* STUB-CODE *)
  Definition universe (_ : P.t) : list positive := [].
End PointVarsCode.

Module PointVars (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    (C : CFG P PointKey PointEdge) <: VARS P PointKey PointEdge C PosKey.
  Include PointVarsCode O P C.
  Include VARS_SPEC P PointKey PointEdge C PosKey.
  Lemma universe_spec : forall p x,
    In x (universe p) <->
      (exists e, In e (C.edges p) /\ (In x (uses p e) \/ In x (defs p e))) \/
      (exists n, In n (C.nodes p) /\ In x (exits p n)).
  Proof. Admitted. (* STUB *)
  Lemma universe_nodup : forall p, NoDup (universe p).
  Proof. Admitted. (* STUB *)
End PointVars.

Module PointVarsT (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    (C : CFG_T P PointKey PointEdge) <: VARS_ALL P PointKey PointEdge C PosKeyT.
  Include PointVars O P C.
  TimeFun uses.
  TimeFun defs.
  TimeFun exits.
  TimeFun universe.
  Definition c_vars : N := 1. (* STUB *)
  Lemma T_uses_le : forall p e,
    (T_uses p e <= c_vars * N.of_nat (PointEdge.bits e + length (uses p e) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_defs_le : forall p e,
    (T_defs p e <= c_vars * N.of_nat (PointEdge.bits e + length (defs p e) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_exits_le : forall p n,
    (T_exits p n <= c_vars * N.of_nat (PointKey.bits n + length (exits p n) + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition universe_work p :=
    (C.T_edges p + C.T_nodes p +
      fold_right N.add 0%N (map (fun e => T_uses p e + T_defs p e)%N (C.edges p)) +
      fold_right N.add 0%N (map (T_exits p) (C.nodes p)) +
      N.of_nat (length (C.edges p) + length (C.nodes p) + length (occurrences p) + 1) *
        N.of_nat (occurrence_width p + 1) +
      fold_right N.add 0%N (map PosKeyT.T_encode (occurrences p)))%N.
  Lemma T_universe_le : forall p, (T_universe p <= c_vars * universe_work p)%N.
  Proof. Admitted. (* STUB *)
  Lemma universe_bigO : bigO (fun _ : P.t => True) universe_work T_universe.
  Proof. Admitted. (* STUB *)
  Lemma F1_occurrences : forall p x, In x (occurrences p) <-> occurs p x.
  Proof. Admitted. (* STUB *)
  Lemma F2_universe : forall p x, In x (universe p) <-> In x (occurrences p).
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition seen (_ : P.t) : ptrie positive := Empty.
  TimeFun seen.
  Definition k_seen : N := 1. (* STUB *)
  Definition k_collect : N := 1. (* STUB *)
  Lemma F3_seen : forall p,
    seen p = fold_left (fun s x => PTrieCode.set (PosKeyT.encode x) x s) (occurrences p)
      PTrieCode.empty.
  Proof. Admitted. (* STUB *)
  Lemma F4_seen_nodes : forall p,
    PTrie.nodes (seen p) <= length (occurrences p) * occurrence_width p.
  Proof. Admitted. (* STUB *)
  Lemma T1_seen : forall p, (T_seen p <= k_seen * universe_work p)%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_universe : forall p,
    (T_universe p <= k_collect * (T_seen p +
      N.of_nat (length (occurrences p) + 1) * N.of_nat (occurrence_width p + 1)))%N.
  Proof. Admitted. (* STUB *)
End PointVarsT.

Module PointsCode (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    (BC : CFG_INDEXED_OPS P PosKeyCode BlockEdge)
    (C : CFG_INDEXED_OPS P PointKey PointEdge) (U : VARS_OPS P PointKey PointEdge C PosKeyCode)
    <: SSA_POINTS_OPS P PosKeyCode BlockEdge BC PointKey PointEdge C PosKeyCode U.
  (* STUB-CODE *)
  Definition points_in_block (_ : P.t) (_ : positive) : list PointKey.t := [].
  (* STUB-CODE *)
  Definition instruction_edges (_ : P.t) (_ : positive) : list point_edge := [].
  (* STUB-CODE *)
  Definition parameter_edge (_ : P.t) (b : positive) : point_edge :=
    PointEdge (b, 0%N) (b, 0%N) None.
  (* STUB-CODE *)
  Definition block_of_point (_ : P.t) (n : PointKey.t) : positive := fst n.
  Definition block_edge_of (_ : P.t) (e : point_edge) : option block_edge := point_block_edge e.
  (* STUB-CODE *)
  Definition block_params (_ : P.t) (_ : positive) : list positive := [].
  Definition block_edge_args (_ : P.t) (e : block_edge) : list positive := edge_arguments e.
  (* STUB-CODE *)
  Definition point_definition (_ : P.t) (_ : positive) : option PointKey.t := None.
End PointsCode.

Module Points (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    (BC : CFG P PosKey BlockEdge) (C : CFG P PointKey PointEdge)
    (U : VARS P PointKey PointEdge C PosKey)
    <: SSA_POINTS P PosKey BlockEdge BC PointKey PointEdge C PosKey U.
  Include PointsCode O P BC C U.
  Definition wf (p : P.t) := ssa_wf p.
  Lemma graphs_wf : forall p, wf p -> C.wf p /\ BC.wf p.
  Proof. Admitted. (* STUB *)
  Lemma points_out_nodup : forall p n, wf p -> NoDup (C.out p n).
  Proof. Admitted. (* STUB *)
  Lemma blocks_out_nodup : forall p b, wf p -> NoDup (BC.out p b).
  Proof. Admitted. (* STUB *)
  Lemma points_covered : forall p n, wf p ->
    (In n (C.nodes p) <-> exists b, In b (BC.nodes p) /\ In n (points_in_block p b)).
  Proof. Admitted. (* STUB *)
  Lemma points_unique : forall p b, wf p -> NoDup (points_in_block p b).
  Proof. Admitted. (* STUB *)
  Lemma points_owner : forall p b n, wf p -> In b (BC.nodes p) ->
    In n (points_in_block p b) -> block_of_point p n = b.
  Proof. Admitted. (* STUB *)
  Lemma blocks_nonempty : forall p b, wf p -> In b (BC.nodes p) ->
    points_in_block p b <> nil.
  Proof. Admitted. (* STUB *)
  Lemma points_ordered : forall p b, wf p -> In b (BC.nodes p) ->
    presentation_chain (C.edges p) (C.src p) (C.dst p)
      (points_in_block p b) (instruction_edges p b).
  Proof. Admitted. (* STUB *)
  Lemma instruction_edges_internal : forall p b e, wf p -> In b (BC.nodes p) ->
    In e (instruction_edges p b) -> block_edge_of p e = None.
  Proof. Admitted. (* STUB *)
  Lemma instruction_edges_complete : forall p e, wf p -> In e (C.edges p) ->
    block_edge_of p e = None -> In e (instruction_edges p (block_of_point p (C.src p e))).
  Proof. Admitted. (* STUB *)
  Lemma parameter_edge_first : forall p b, wf p -> In b (BC.nodes p) ->
    nth_error (instruction_edges p b) 0 = Some (parameter_edge p b).
  Proof. Admitted. (* STUB *)
  Lemma parameter_edge_defs : forall p b x, wf p -> In b (BC.nodes p) ->
    (In x (U.defs p (parameter_edge p b)) <-> In x (block_params p b)).
  Proof. Admitted. (* STUB *)
  Lemma point_edge_projection : forall p e, wf p -> In e (C.edges p) ->
    match block_edge_of p e with
    | None => block_of_point p (C.src p e) = block_of_point p (C.dst p e)
    | Some be => In be (BC.edges p) /\ BC.src p be = block_of_point p (C.src p e) /\
        BC.dst p be = block_of_point p (C.dst p e) /\
        last (points_in_block p (block_of_point p (C.src p e))) (C.src p e) = C.src p e /\
        nth_error (points_in_block p (BC.dst p be)) 0 = Some (C.dst p e)
    end.
  Proof. Admitted. (* STUB *)
  Lemma phi_args_length : forall p be, wf p -> In be (BC.edges p) ->
    length (block_edge_args p be) = length (block_params p (BC.dst p be)).
  Proof. Admitted. (* STUB *)
  Lemma phi_edge_use : forall p e be x, wf p -> In e (C.edges p) ->
    block_edge_of p e = Some be -> In x (block_edge_args p be) -> In x (U.uses p e).
  Proof. Admitted. (* STUB *)
  Lemma block_edge_covered : forall p be, wf p -> In be (BC.edges p) ->
    exists e, In e (C.edges p) /\ block_edge_of p e = Some be.
  Proof. Admitted. (* STUB *)
  Lemma block_edge_unique : forall p e1 e2 be, wf p ->
    In e1 (C.edges p) -> In e2 (C.edges p) ->
    block_edge_of p e1 = Some be -> block_edge_of p e2 = Some be -> e1 = e2.
  Proof. Admitted. (* STUB *)
End Points.

Module PointsT (O : OPS) (P : TYPE with Definition t := func positive O.K O.G)
    (BC : CFG_T P PosKeyT BlockEdge) (C : CFG_T P PointKey PointEdge)
    (U : VARS_T P PointKey PointEdge C PosKeyT)
    <: SSA_POINTS_T P PosKeyT BlockEdge BC PointKey PointEdge C PosKeyT U.
  Include Points O P BC C U.
  TimeFun points_in_block.
  TimeFun instruction_edges.
  TimeFun parameter_edge.
  TimeFun block_of_point.
  TimeFun block_edge_of.
  TimeFun block_params.
  TimeFun block_edge_args.
  TimeFun point_definition.
  Definition c_points : N := 1. (* STUB *)
  (** Block point lists pay for the key and the returned points. *)
  Lemma T_points_in_block_le : forall p b,
    (T_points_in_block p b <=
      c_points * N.of_nat (PosKeyT.bits b + length (points_in_block p b) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Instruction edge lists pay for the key and the returned edges. *)
  Lemma T_instruction_edges_le : forall p b,
    (T_instruction_edges p b <=
      c_points * N.of_nat (PosKeyT.bits b + length (instruction_edges p b) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The parameter edge lookup pays for the block key. *)
  Lemma T_parameter_edge_le : forall p b,
    (T_parameter_edge p b <= c_points * N.of_nat (PosKeyT.bits b + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The owner lookup pays for the point key. *)
  Lemma T_block_of_point_le : forall p n,
    (T_block_of_point p n <= c_points * N.of_nat (PointKey.bits n + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The edge projection pays for the edge key. *)
  Lemma T_block_edge_of_le : forall p e,
    (T_block_edge_of p e <= c_points * N.of_nat (PointEdge.bits e + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Block parameters pay for the key and the returned values. *)
  Lemma T_block_params_le : forall p b,
    (T_block_params p b <=
      c_points * N.of_nat (PosKeyT.bits b + length (block_params p b) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Phi operands pay for the block-edge key and the returned values. *)
  Lemma T_block_edge_args_le : forall p be,
    (T_block_edge_args p be <=
      c_points * N.of_nat (BlockEdge.bits be + length (block_edge_args p be) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The definition point lookup pays for the value key. *)
  Lemma T_point_definition_le : forall p x,
    (T_point_definition p x <= c_points * N.of_nat (PosKeyT.bits x + 1))%N.
  Proof. Admitted. (* STUB *)
End PointsT.

Module LanguageLink (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (C : CFG P PosKey BlockEdge
      with Definition entries := fun (p : P.t) => [entry _ _ _ p]
      with Definition nodes := fun (p : P.t) => map fst (blocks _ _ _ p)
      with Definition edges := fun (p : P.t) => language_edges p
      with Definition src := fun (_ : P.t) (e : block_edge) => edge_source e
      with Definition dst := fun (_ : P.t) (e : block_edge) => edge_target e)
    (S : SSA P PosKey BlockEdge C PosKey K G
      with Definition wf := fun (p : P.t) => ssa_wf p
      with Definition params := fun (p : P.t) (b : positive) =>
        match find_block b (blocks _ _ _ p) with
        | Some body => Lang.params _ _ _ body
        | None => []
        end)
    <: LANG_SSA_LINK O K G P BlockEdge C S.
  Lemma entries_agree : forall p, C.entries p = [entry _ _ _ p].
  Proof. Admitted. (* STUB *)
  Lemma nodes_agree : forall p, C.nodes p = map fst (blocks _ _ _ p).
  Proof. Admitted. (* STUB *)
  Lemma paths_agree : forall p a route b,
    presentation_path (C.edges p) (C.src p) (C.dst p) a route b <-> Lang.path p a route b.
  Proof. Admitted. (* STUB *)
  Lemma params_agree : forall p b, S.params p b =
    match find_block b (blocks _ _ _ p) with
    | Some body => Lang.params _ _ _ body
    | None => []
    end.
  Proof. Admitted. (* STUB *)
  Lemma wf_from_lang : forall p, ssa_wf p -> S.wf p.
  Proof. Admitted. (* STUB *)
End LanguageLink.
