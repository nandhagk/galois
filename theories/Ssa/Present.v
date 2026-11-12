(** * Language control-flow occurrences

    Edges retain the source block and the selected exit arm.
    For example, two arms aimed at the same block remain distinct.
    Builds on: Ssa.Lang. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Code KeySig Key Trie.
From Galois.Program Require Import CfgSig VarsSig Vars SsaSig Ssa.
From Galois.Ssa Require Import Lang LiveSig ValidateSig.
Import List.ListNotations.

Inductive exit_arm :=
  | Jump_arm
  | True_arm
  | False_arm.

Record block_edge := BlockEdge {
  edge_source : positive;
  edge_arm : exit_arm;
  edge_target : positive
}.
TimeFun edge_source.
TimeFun edge_arm.
TimeFun edge_target.

Definition point_key := (positive * N)%type.

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

Module EdgeArmTargetKey := PairKeyT ArmKeyT PosKeyT.
Module EdgeTupleKey := PairKeyT PosKeyT EdgeArmTargetKey.
Definition block_edge_tuple (e : block_edge) : EdgeTupleKey.t :=
  (edge_source e, (edge_arm e, edge_target e)).
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

Definition point_row := (point_edge * list positive * list positive)%type.

(** Instruction rows start at index `i` and return the index of the exit point. *)
Fixpoint code_rows {K} (b : positive) (i : N) (cs : list (positive * K * list positive))
    : list point_row * N :=
  match cs with
  | [] => ([], i)
  | (x, _, ys) :: rest =>
      let rows := code_rows b (N.succ i) rest in
      ((PointEdge (b, i) (b, N.succ i) None, ys, [x]) :: fst rows, snd rows)
  end.
TimeFun code_rows.

(** Each exit edge with the arguments that it passes. *)
Definition exit_edge_args {G} (source : positive) (e : exit positive G)
    : list (block_edge * list positive) :=
  match e with
  | Jump target args => [(BlockEdge source Jump_arm target, args)]
  | Branch _ _ yes yes_args no no_args =>
      [(BlockEdge source True_arm yes, yes_args); (BlockEdge source False_arm no, no_args)]
  | Return _ => []
  end.
TimeFun exit_edge_args.

(** The guard and its operands hold on the true arm of a branch. *)
Definition exit_guards {G} (source : positive) (e : exit positive G)
    : list (block_edge * list (G * list positive)) :=
  match e with
  | Jump target _ => [(BlockEdge source Jump_arm target, [])]
  | Branch g xs yes _ no _ =>
      [(BlockEdge source True_arm yes, [(g, xs)]); (BlockEdge source False_arm no, [])]
  | Return _ => []
  end.
TimeFun exit_guards.

Definition guard_uses {G} (e : exit positive G) : list positive :=
  match e with
  | Branch _ xs _ _ _ _ => xs
  | _ => []
  end.
TimeFun guard_uses.

Definition exit_returns {G} (e : exit positive G) : list positive :=
  match e with
  | Return xs => xs
  | _ => []
  end.
TimeFun exit_returns.

Fixpoint pair_args (xs ys : list positive) : list (positive * positive) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: pair_args xs' ys'
  | _, _ => []
  end.
TimeFun pair_args.

(** The rows of one kept block, computed once. *)
Record block_summary := BlockSummary {
  summary_block : positive;
  summary_params : list positive;
  summary_points : list point_key;
  summary_internal : list point_row;
  summary_exit : point_key;
  summary_outgoing : list point_row;
  summary_returns : list positive
}.

TimeFun summary_block.
TimeFun summary_params.
TimeFun summary_points.
TimeFun summary_internal.
TimeFun summary_exit.
TimeFun summary_outgoing.
TimeFun summary_returns.

(** A key is listed when the table has a row for it. *)
Definition is_listed {A} (m : ptrie A) (b : positive) : bool :=
  match trie_get b m with
  | Some _ => true
  | None => false
  end.
TimeFun is_listed.

(** Exit edges whose target is a kept block, with their arguments. *)
Definition listed_edge_args {A G} (kept : ptrie A) (source : positive) (e : exit positive G)
    : list (block_edge * list positive) :=
  filter (fun ea => is_listed kept (edge_target (fst ea))) (exit_edge_args source e).
TimeFun listed_edge_args.

(** Guard rows of the exit edges whose target is a kept block. *)
Definition listed_guards {A G} (kept : ptrie A) (source : positive) (e : exit positive G)
    : list (block_edge * list (G * list positive)) :=
  filter (fun eg => is_listed kept (edge_target (fst eg))) (exit_guards source e).
TimeFun listed_guards.

Definition summarize {A K G} (kept : ptrie A) (item : positive * block positive K G)
    : block_summary :=
  let b := fst item in
  let body := snd item in
  let rows := code_rows b 1%N (code _ _ _ body) in
  let last := (b, snd rows) in
  let internal := (PointEdge (b, 0%N) (b, 1%N) None, nil, params _ _ _ body) :: fst rows in
  BlockSummary b (params _ _ _ body)
    ((b, 0%N) :: map (fun r => point_dst (fst (fst r))) internal)
    internal last
    (map (fun ea => (PointEdge last (edge_target (fst ea), 0%N) (Some (fst ea)),
        guard_uses (term _ _ _ body) ++ snd ea, nil))
      (listed_edge_args kept b (term _ _ _ body)))
    (exit_returns (term _ _ _ body)).
TimeFun summarize.

Fixpoint param_defs {K} (b : positive) (i : nat) (xs : list positive)
    : list (positive * definition positive positive K) :=
  match xs with
  | [] => []
  | x :: rest => (x, Param b i) :: param_defs b (S i) rest
  end.
TimeFun param_defs.

Definition block_value_defs {K G} (item : positive * block positive K G)
    : list (positive * definition positive positive K) :=
  param_defs (fst item) 0 (params _ _ _ (snd item)) ++
    map (fun i => (fst (fst i), Op (snd (fst i)) (snd i))) (code _ _ _ (snd item)).
TimeFun block_value_defs.

Definition block_homes {K G} (item : positive * block positive K G)
    : list (positive * positive) :=
  map (fun x => (x, fst item)) (block_defs (snd item)).
TimeFun block_homes.

(** A table keeps the first row of each key, as `find_block` does. *)
Definition first_table {A B} (key : A -> positive) (rows : list (A * B)) : ptrie B :=
  fold_right (fun r m => PTrieCode.set (key (fst r)) (snd r) m) Empty rows.
TimeFun first_table.

(** A multi-table lists every row of a key in row order. *)
Definition multi_table {A} (key : A -> positive) (rows : list A) : ptrie (list A) :=
  fold_right (fun r m => PTrieCode.set (key r) (r :: index_row m (key r)) m) Empty rows.
TimeFun multi_table.

Record lang_prepared (K G : Type) := LangPrepared {
  lang_source : func positive K G;
  lang_entries : list positive;
  lang_blocks : list positive;
  lang_edges : list block_edge;
  lang_out : ptrie (list block_edge);
  lang_inc : ptrie (list block_edge);
  lang_points : list point_key;
  lang_point_edges : list point_edge;
  lang_point_out : ptrie (list point_edge);
  lang_point_inc : ptrie (list point_edge);
  lang_vars : var_tables positive;
  lang_ssa : ssa_tables positive block_edge positive K G;
  lang_point_tables : ssa_point_tables positive block_edge point_key point_edge positive
}.

Arguments LangPrepared {K G}.
Arguments lang_source {K G}.
Arguments lang_entries {K G}.
Arguments lang_blocks {K G}.
Arguments lang_edges {K G}.
Arguments lang_out {K G}.
Arguments lang_inc {K G}.
Arguments lang_points {K G}.
Arguments lang_point_edges {K G}.
Arguments lang_point_out {K G}.
Arguments lang_point_inc {K G}.
Arguments lang_vars {K G}.
Arguments lang_ssa {K G}.
Arguments lang_point_tables {K G}.

TimeFun lang_source.
TimeFun lang_entries.
TimeFun lang_blocks.
TimeFun lang_edges.
TimeFun lang_out.
TimeFun lang_inc.
TimeFun lang_points.
TimeFun lang_point_edges.
TimeFun lang_point_out.
TimeFun lang_point_inc.
TimeFun lang_vars.
TimeFun lang_ssa.
TimeFun lang_point_tables.

(** Preparation keeps the first block of each identifier, lists the edges and the entry
    that reach a kept block, and indexes their rows. *)
Definition lang_prepare {K G} (p : func positive K G) : lang_prepared K G :=
  let bs := first_blocks (blocks _ _ _ p) in
  let params_table := first_table PosKeyCode.encode
    (map (fun item => (fst item, params _ _ _ (snd item))) bs) in
  let ss := map (summarize params_table) bs in
  let block_rows := flat_map (fun item =>
    listed_edge_args params_table (fst item) (term _ _ _ (snd item))) bs in
  let edges := map fst block_rows in
  let rows := flat_map (fun s => summary_internal s ++ summary_outgoing s) ss in
  let pedges := map (fun r => fst (fst r)) rows in
  let entries :=
    if is_listed params_table (entry _ _ _ p) then [entry _ _ _ p] else [] in
  LangPrepared p entries (map fst bs) edges
    (multi_table edge_source edges) (multi_table edge_target edges)
    (flat_map summary_points ss) pedges
    (multi_table (fun e => PointKey.encode (point_src e)) pedges)
    (multi_table (fun e => PointKey.encode (point_dst e)) pedges)
    (VarTables
      (first_table PointEdge.encode (map (fun r => (fst (fst r), snd (fst r))) rows))
      (first_table PointEdge.encode (map (fun r => (fst (fst r), snd r)) rows))
      (first_table PointKey.encode
        (map (fun s => (summary_exit s, summary_returns s)) ss)))
    (SsaTables
      (inputs _ _ _ p ++ flat_map (fun item => block_defs (snd item)) bs)
      (flat_map (index_row params_table) entries)
      (flat_map (fun r => map (pair (fst r))
        (pair_args (index_row params_table (edge_target (fst r))) (snd r))) block_rows)
      (first_table PosKeyCode.encode (flat_map block_value_defs bs))
      (first_table PosKeyCode.encode
        (map (fun x => (x, entry _ _ _ p)) (inputs _ _ _ p) ++ flat_map block_homes bs))
      (entry _ _ _ p)
      params_table
      (first_table BlockEdge.encode (map (fun r =>
        (fst r, pair_args (index_row params_table (edge_target (fst r))) (snd r)))
        block_rows))
      (first_table BlockEdge.encode
        (flat_map (fun item =>
          listed_guards params_table (fst item) (term _ _ _ (snd item))) bs)))
    (SsaPointTables
      (first_table PosKeyCode.encode
        (map (fun s => (summary_block s, summary_points s)) ss))
      (first_table PosKeyCode.encode (map (fun s =>
        (summary_block s, map (fun r => fst (fst r)) (summary_internal s))) ss))
      (first_table PosKeyCode.encode (map (fun s => (summary_block s,
        PointEdge (summary_block s, 0%N) (summary_block s, 1%N) None)) ss))
      (PointEdge (entry _ _ _ p, 0%N) (entry _ _ _ p, 1%N) None)
      (first_table PointKey.encode
        (flat_map (fun s => map (fun n => (n, summary_block s)) (summary_points s)) ss))
      (entry _ _ _ p)
      (first_table PointEdge.encode (flat_map (fun r =>
        match point_block_edge (fst (fst r)) with
        | Some be => [(fst (fst r), be)]
        | None => []
        end) rows))
      params_table
      (first_table BlockEdge.encode block_rows)
      (first_table PosKeyCode.encode
        (flat_map (fun r => map (fun x => (x, point_src (fst (fst r)))) (snd r)) rows))).
TimeFun lang_prepare.

Module Prepared (O : OPS) <: TYPE.
  Definition t := lang_prepared O.K O.G.
End Prepared.

Module PrepareCode (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: LANG_PREPARE_OPS O Q.
  Definition prepare (p : func positive O.K O.G) : Q.t := lang_prepare p.
End PrepareCode.

Module PrepareT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: LANG_PREPARE_T O Q.
  Include PrepareCode O Q.
  TimeFun prepare.
  Definition c_prepare : N := 1. (* STUB *)
  Lemma T_prepare_le : forall p,
    (T_prepare p <= c_prepare * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma prepare_bigO : bigO (fun _ : func positive O.K O.G => True)
    (fun p => N.of_nat ((function_size p + 1) * (function_width p + 1))) T_prepare.
  Proof. Admitted. (* STUB *)
End PrepareT.

Module BlockCfgCode (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_INDEXED_OPS Q PosKeyCode BlockEdge.
  Definition entries (q : Q.t) := lang_entries q.
  Definition edges (q : Q.t) := lang_edges q.
  Definition src (_ : Q.t) (e : block_edge) := edge_source e.
  Definition dst (_ : Q.t) (e : block_edge) := edge_target e.
  Definition nodes (q : Q.t) := lang_blocks q.
  Definition out (q : Q.t) (b : positive) := index_row (lang_out q) (PosKeyCode.encode b).
  Definition inc (q : Q.t) (b : positive) := index_row (lang_inc q) (PosKeyCode.encode b).
End BlockCfgCode.

Module BlockCfg (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG Q PosKey BlockEdge.
  Include BlockCfgCode O Q.
  Definition wf (p : Q.t) := p = lang_prepare (lang_source p).
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

(* F2-100 retires the former edge, adjacency and parameter scan SIG-QUESTIONs. *)
Module BlockCfgT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_T Q PosKeyT BlockEdge.
  Include BlockCfg O Q.
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

Module PointCfgCode (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_INDEXED_OPS Q PointKey PointEdge.
  Definition entries (q : Q.t) : list point_key :=
    map (fun b => (b, 0%N)) (lang_entries q).
  Definition edges (q : Q.t) := lang_point_edges q.
  Definition src (_ : Q.t) (e : point_edge) := point_src e.
  Definition dst (_ : Q.t) (e : point_edge) := point_dst e.
  Definition nodes (q : Q.t) := lang_points q.
  Definition out (q : Q.t) (n : point_key) := index_row (lang_point_out q) (PointKey.encode n).
  Definition inc (q : Q.t) (n : point_key) := index_row (lang_point_inc q) (PointKey.encode n).
End PointCfgCode.

Module PointCfg (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG Q PointKey PointEdge.
  Include PointCfgCode O Q.
  Definition wf (p : Q.t) := p = lang_prepare (lang_source p).
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

Module PointCfgT (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: CFG_T Q PointKey PointEdge.
  Include PointCfg O Q.
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

Module PresentVarsData (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: VARS_DATA_T Q PosKeyT.
  Definition tables (q : Q.t) := lang_vars q.
  TimeFun tables.
  Definition c_tables : N := 1. (* STUB *)
  Lemma T_tables_le : forall q, (T_tables q <= c_tables)%N.
  Proof. Admitted. (* STUB *)
End PresentVarsData.

Module PresentSsaData (O : OPS)
    (K : TYPE with Definition t := O.K) (G : TYPE with Definition t := O.G)
    (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: SSA_DATA_T Q PosKeyT BlockEdge PosKeyT K G.
  Definition tables (q : Q.t) := lang_ssa q.
  TimeFun tables.
  Definition c_tables : N := 1. (* STUB *)
  Lemma T_tables_le : forall q, (T_tables q <= c_tables)%N.
  Proof. Admitted. (* STUB *)
End PresentSsaData.

Module PresentPointsData (O : OPS) (Q : TYPE with Definition t := lang_prepared O.K O.G)
    <: SSA_POINTS_DATA_T Q PosKeyT BlockEdge PointKey PointEdge PosKeyT.
  Definition tables (q : Q.t) := lang_point_tables q.
  TimeFun tables.
  Definition c_tables : N := 1. (* STUB *)
  Lemma T_tables_le : forall q, (T_tables q <= c_tables)%N.
  Proof. Admitted. (* STUB *)
End PresentPointsData.

Module PresentT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G).
  Module Q := Prepared O.
  Module R := PrepareT O Q.
  Module BC := BlockCfgT O Q.
  Module C := PointCfgT O Q.
  Module VD := PresentVarsData O Q.
  Module U := VarsT Q PointKey PointEdge C PosKeyT VD.
  Module SD := PresentSsaData O K G Q.
  Module S := SsaT Q PosKeyT BlockEdge BC PosKeyT K G SD.
  Module PD := PresentPointsData O Q.
  Module SP := SsaPointsT Q PosKeyT BlockEdge BC PointKey PointEdge C PosKeyT U PD.

  Module Link <: LANG_SSA_LINK O K G Q R BlockEdge BC S.
    Lemma entries_agree : forall p, In (entry _ _ _ p) (map fst (blocks _ _ _ p)) ->
      BC.entries (R.prepare p) = [entry _ _ _ p].
    Proof. Admitted. (* STUB *)
    Lemma nodes_agree : forall p,
      BC.nodes (R.prepare p) = map fst (first_blocks (blocks _ _ _ p)).
    Proof. Admitted. (* STUB *)
    Lemma paths_agree : forall p a route b, NoDup (map fst (blocks _ _ _ p)) ->
      targets_listed p ->
      (presentation_path (BC.edges (R.prepare p)) (BC.src (R.prepare p))
        (BC.dst (R.prepare p)) a route b <-> Lang.path p a route b).
    Proof. Admitted. (* STUB *)
    Lemma params_agree : forall p b, S.params (R.prepare p) b =
      match find_block b (blocks _ _ _ p) with
      | Some body => Lang.params _ _ _ body
      | None => []
      end.
    Proof. Admitted. (* STUB *)
    Lemma wf_from_lang : forall p, ssa_wf p -> S.wf (R.prepare p).
    Proof. Admitted. (* STUB *)
  End Link.

  Module Budget <: LANG_PRESENT_BUDGET O Q R BlockEdge PointEdge PointKey BC C U SP.
    Definition c_present : N := 1. (* STUB *)

  (** Both prepared graphs are well formed for every raw function. *)
  Lemma prepared_wf : forall p, BC.wf (R.prepare p) /\ C.wf (R.prepare p).
  Proof. Admitted. (* STUB *)
  (** The point laws hold on the prepared form of an SSA function. *)
  Lemma points_wf : forall p, ssa_wf p -> SP.wf (R.prepare p).
  Proof. Admitted. (* STUB *)
  (** The block presentation lists each block identifier at most once per listed block. *)
  Lemma block_nodes_le : forall p,
    length (BC.nodes (R.prepare p)) <= length (blocks _ _ _ p).
  Proof. Admitted. (* STUB *)
  (** Each listed block contributes at most its two exit edges. *)
  Lemma block_edges_le : forall p,
    length (BC.edges (R.prepare p)) <= 2 * length (blocks _ _ _ p).
  Proof. Admitted. (* STUB *)
  (** Presented block identifiers are identifiers of the syntax. *)
  Lemma block_bits_le : forall p b,
    (In b (BC.nodes (R.prepare p)) \/ exists e, In e (BC.edges (R.prepare p)) /\
      (BC.src (R.prepare p) e = b \/ BC.dst (R.prepare p) e = b)) ->
    PosKeyT.bits b <= function_width p.
  Proof. Admitted. (* STUB *)
  (** Parameter rows of listed blocks and argument rows of listed edges are syntax. *)
  Lemma block_rows_le : forall p,
    fold_right (fun b n => length (SP.block_params (R.prepare p) b) + n) 0
      (BC.nodes (R.prepare p)) +
    fold_right (fun be n => length (SP.block_edge_args (R.prepare p) be) + n) 0
      (BC.edges (R.prepare p)) <= function_size p.
  Proof. Admitted. (* STUB *)
  (** Points, point edges and variable occurrences are linear in the syntax. *)
  Lemma points_le : forall p,
    (N.of_nat (length (C.nodes (R.prepare p)) + length (C.edges (R.prepare p)) +
      length (U.occurrences (R.prepare p))) <=
      c_present * N.of_nat (function_size p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Occurring variables are identifiers of the syntax. *)
  Lemma occurrence_width_le : forall p,
    U.occurrence_width (R.prepare p) <= function_width p.
  Proof. Admitted. (* STUB *)
  (** Listed point keys are within a constant factor of the syntax width. *)
  Lemma point_bits_le : forall p n, In n (C.nodes (R.prepare p)) ->
    (N.of_nat (PointKey.bits n) <= c_present * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Listed edge keys are within a constant factor of the syntax width. *)
  Lemma edge_bits_le : forall p e, In e (C.edges (R.prepare p)) ->
    (N.of_nat (PointEdge.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Listed block-edge keys are within a constant factor of the syntax width. *)
  Lemma block_edge_bits_le : forall p e, In e (BC.edges (R.prepare p)) ->
    (N.of_nat (BlockEdge.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)

  End Budget.
End PresentT.
