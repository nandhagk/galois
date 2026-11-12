(** * Language control-flow occurrences

    Edges retain the source block and the selected exit arm.
    For example, two arms aimed at the same block remain distinct.
    Builds on: Ssa.Lang. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Code KeySig Key.
From Galois.Program Require Import CfgSig SsaSig.
From Galois.Ssa Require Import Lang.
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

Module LangProgram (O : OPS) <: TYPE.
  Definition t := func positive O.K O.G.
End LangProgram.

Module BlockEdge <: TYPE.
  Definition t := block_edge.
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
  Proof. Admitted.
  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof. Admitted.
  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof. Admitted.
  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof. Admitted.
  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof. Admitted.
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
  Proof. Admitted. (* STUB *)
  Lemma T_src_le : forall p e, (T_src p e <= c_cfg)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_dst_le : forall p e, (T_dst p e <= c_cfg)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_nodes_le : forall p,
    (T_nodes p <= c_cfg_adj * N.of_nat (length (nodes p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_out_le : forall p n,
    (T_out p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (out p n) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_inc_le : forall p n,
    (T_inc p n <= c_cfg_adj * N.of_nat (PosKeyT.bits n + length (inc p n) + 1))%N.
  Proof. Admitted. (* STUB *)
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
  (* STUB-CODE *)
  Definition params (_ : P.t) (_ : positive) : list positive := [].
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
  Proof. Admitted.
  Lemma values_nodup : forall p, wf p -> NoDup (values p).
  Proof. Admitted.
  Lemma homes_listed : forall p x, wf p -> In x (values p) -> In (home p x) (C.nodes p).
  Proof. Admitted.
  Lemma param_defs : forall p x b i, wf p ->
    (def p x = Param b i <-> nth_error (params p b) i = Some x).
  Proof. Admitted.
  Lemma param_home : forall p b x, wf p -> In x (params p b) -> home p x = b.
  Proof. Admitted.
  Lemma params_listed : forall p b x, wf p -> In b (C.nodes p) ->
    In x (params p b) -> In x (values p).
  Proof. Admitted.
  Lemma args_params : forall p e, wf p -> In e (C.edges p) ->
    map fst (args p e) = params p (C.dst p e).
  Proof. Admitted.
  Lemma args_dominate : forall p e x y, wf p -> In e (C.edges p) ->
    In (x, y) (args p e) -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p y) route.
  Proof. Admitted.
  Lemma guards_dominate : forall p e g xs x, wf p -> In e (C.edges p) ->
    In (g, xs) (guards p e) -> In x xs -> In x (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p x) route.
  Proof. Admitted.
  Lemma op_args_dominate : forall p x op xs y, wf p -> In x (values p) ->
    def p x = Op op xs -> In y xs -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (home p x) ->
      In (home p y) route.
  Proof. Admitted.
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
End BlockSsaT.
