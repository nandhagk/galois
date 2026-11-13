(** * Checked Cytron SSA construction

    The builder validates an untrusted placement and renaming result before returning it.
    For example, a join receives a parameter for a variable live on both incoming paths.
    Builds on: core point presentations, liveness, dominance frontiers and SSA validation. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig FrontierSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig.
Import List.ListNotations.

Definition exit_arg_count {G} (e : exit positive G) : nat :=
  match e with
  | Jump _ xs => length xs
  | Branch _ _ _ xs _ ys => length xs + length ys
  | Return _ => 0
  end.
TimeFun exit_arg_count.

Definition function_edge_args {K G} (p : func positive K G) : nat :=
  fold_right (fun item n => exit_arg_count (term _ _ _ (snd item)) + n) 0 (blocks _ _ _ p).
TimeFun function_edge_args.

Definition definition_blocks {K G} (p : func positive K G) (x : positive) : list positive :=
  (if existsb (Pos.eqb x) (inputs _ _ _ p) then [entry _ _ _ p] else []) ++
    map fst (filter (fun item => existsb (Pos.eqb x) (block_defs (snd item))) (blocks _ _ _ p)).
TimeFun definition_blocks.

Record rename_state (K G : Type) := RenameState {
  rename_bodies : ptrie (block positive K G);
  rename_stack : list (positive * renaming);
  renamed_blocks : list (positive * block positive K G);
  renamed_envs : list (positive * renaming);
  next_value : N
}.

Module Type BUILD_OPS (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS Q PosKeyCode BE) (C : CFG_INDEXED_OPS Q N E)
    (U : VARS_OPS Q N E C PosKeyCode)
    (SP : SSA_POINTS_OPS Q PosKeyCode BE BC N E C PosKeyCode U)
    (S : SSA_OPS Q PosKeyCode BE BC PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) (F : FRONTIER_OPS)
    (L : LIVE_OPS O P Q R BE E N BC C U SP)
    (Va : VALIDATE_OPS O K G P Q R BE BC S DG D).
  Parameter produce : P.t -> option (P.t * cert).
  Parameter build : P.t -> option P.t.
End BUILD_OPS.

Module Type BUILD_LAWS (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (BE E : TYPE) (N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E)
    (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U)
    (S : SSA Q PosKey BE BC PosKey K G)
    (DG : DIGRAPH) (D : DOM) (F : FRONTIER)
    (L : LIVE O P Q R BE E N BC C U SP)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE O K G P Q R BE BC S DG D B)
    (Import A : BUILD_OPS O K G P Q R BE E N BC C U SP S DG D F L Va).
  (** The wrapper returns a candidate exactly when both validators accept it. *)
  Parameter build_checked : forall p, build p =
    match produce p with
    | None => None
    | Some (s, c) => if andb (Va.check p s c) (Va.check_ssa s) then Some s else None
    end.
  (** Every returned candidate is SSA and has the source result at every fuel and input. *)
  Parameter build_correct : forall p s, imp_form p -> build p = Some s ->
    ssa_wf s /\ forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
End BUILD_LAWS.

Module Type BUILD (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q) (BE E : TYPE) (N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E)
    (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U)
    (S : SSA Q PosKey BE BC PosKey K G)
    (DG : DIGRAPH) (D : DOM) (F : FRONTIER)
    (L : LIVE O P Q R BE E N BC C U SP)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE O K G P Q R BE BC S DG D B) :=
  BUILD_OPS O K G P Q R BE E N BC C U SP S DG D F L Va <+
  BUILD_LAWS O K G P Q R BE E N BC C U SP S DG D F L B Va.

Module Type BUILD_TIME (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E)
    (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (S : SSA_T Q PosKeyT BE BC PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (F : FRONTIER_T)
    (L : LIVE_T O P Q R BE E N BC C U SP PB)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE_T O K G P Q R BE BC S DG D B)
    (Import A : BUILD O K G P Q R BE E N BC C U SP S DG D F L B Va).
  Parameter T_produce : P.t -> N.
  Parameter T_build : P.t -> N.
  Parameter c_build : N.
  Definition graph p := DG.prepare (cfg_graph (BC.nodes (R.prepare p))
    (BC.edges (R.prepare p)) (BC.src (R.prepare p)) (BC.dst (R.prepare p))).
  Definition dom_result p := D.build (graph p) (entry _ _ _ p).
  Definition dom_tree p := D.tree (graph p) (entry _ _ _ p)
    (fst (dom_result p)) (snd (dom_result p)).
  Definition frontiers p := F.df (graph p) (dom_tree p).
  Definition df_size p := F.df_size (graph p) (dom_tree p).
  Definition phi_sites p x := F.idf (frontiers p) (definition_blocks p x).
  Definition placement_work p := fold_right (fun x n =>
    fold_right (fun b m => 1 + length (frontier_row (frontiers p) b) + m) 0 (phi_sites p x) + n)
    0 (U.universe (R.prepare p)).
  Definition phi_args p :=
    match produce p with Some (s, _) => function_edge_args s | None => 0 end.
  Definition dom_work p :=
    (graph_n (base (graph p)) + graph_e (base (graph p)) + 1) *
      (Nat.log2 (graph_n (base (graph p))) + 1).
  Definition build_work p := function_size p + length (BC.nodes (R.prepare p)) +
    length (BC.edges (R.prepare p)) + dom_work p + df_size p + placement_work p +
    L.live_size p + phi_args p + 1.
  (** Construction keeps the published dominator, placement, liveness and argument budget. *)
  Parameter T_build_le : forall p,
    (T_build p <= c_build * N.of_nat (build_work p) * N.of_nat (function_width p + 1) +
      c_build * N.of_nat (Va.op_bits p + 1))%N.
  Parameter build_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (build_work p * (function_width p + 1) + Va.op_bits p + 1)) T_build.
End BUILD_TIME.

Module Type BUILD_T (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E)
    (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (S : SSA_T Q PosKeyT BE BC PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (F : FRONTIER_T)
    (L : LIVE_T O P Q R BE E N BC C U SP PB)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE_T O K G P Q R BE BC S DG D B) :=
  BUILD O K G P Q R BE E N BC C U SP S DG D F L B Va <+
  BUILD_TIME O K G P Q R BE E N BC C U SP PB S DG D F L B Va.

Module Type BUILD_PLAN (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E)
    (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (S : SSA_T Q PosKeyT BE BC PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (F : FRONTIER_T)
    (L : LIVE_T O P Q R BE E N BC C U SP PB)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE_T O K G P Q R BE BC S DG D B)
    (Import A : BUILD_T O K G P Q R BE E N BC C U SP PB S DG D F L B Va).
  Parameter def_index : P.t -> ptrie (list positive).
  Parameter live_sets : list (positive * list positive) -> ptrie (ptrie unit).
  Parameter place_var : ptrie (list positive) -> ptrie (list positive) ->
    ptrie (ptrie unit) -> positive -> list positive.
  Parameter T_def_index : P.t -> N.
  Parameter T_live_sets : list (positive * list positive) -> N.
  Parameter T_place_var : ptrie (list positive) -> ptrie (list positive) ->
    ptrie (ptrie unit) -> positive -> N.
  Parameter placement : P.t -> ptrie (list positive).
  Parameter T_placement : P.t -> N.
  Parameter rename : P.t -> domtree -> ptrie (list positive) ->
    list (positive * list positive) -> option (P.t * cert).
  Parameter rename_init : P.t -> rename_state O.K O.G.
  Parameter rename_step : P.t -> domtree -> ptrie (list positive) ->
    list (positive * list positive) -> rename_state O.K O.G ->
      rename_state O.K O.G + option (P.t * cert).
  Parameter T_rename : P.t -> domtree -> ptrie (list positive) ->
    list (positive * list positive) -> N.
  Parameter T_rename_init : P.t -> N.
  Parameter T_rename_step : P.t -> domtree -> ptrie (list positive) ->
    list (positive * list positive) -> rename_state O.K O.G -> N.
  Parameter k_graph k_place k_rename k_wrap k_size : N.
  Definition placed p x :=
    place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x.

  (** The graph of every prepared function is well formed. *)
  Parameter F1_graph_wf : forall p, wf_graph (base (graph p)).
  (** The definition index lists each variable's definition blocks. *)
  Parameter F2a_def_index : forall p x,
    frontier_row (def_index p) x = definition_blocks p x.
  (** The live sets answer certificate membership. *)
  Parameter F2b_live_sets : forall rows b x,
    (exists m, trie_get b (live_sets rows) = Some m /\ trie_get x m = Some tt) <->
      In x (cert_live ([], rows) b).
  (** Every variable enters a placement worklist at most once per block. *)
  Parameter F2_place_unique : forall p x, NoDup (placed p x).
  (** Pruned placement uses iterated-frontier blocks with a certified live entry. *)
  Parameter F3_place_region : forall p x b, In b (placed p x) ->
    In b (phi_sites p x) /\ In x (cert_live ([], L.live_in p) b).
  (** The placement table lists exactly the placed variables of each block. *)
  Parameter F3a_placement : forall p b x,
    In x (frontier_row (placement p) b) <->
      In x (U.universe (R.prepare p)) /\ In b (placed p x).
  (** Renaming uses a bounded explicit stack with two visits per listed block. *)
  Parameter F4_rename_loop : forall p t rows live,
    rename p t rows live =
      match loop_fuel (rename_step p t rows live) (2 * length (blocks _ _ _ p) + 1)
        (rename_init p) with
      | inl _ => None
      | inr answer => answer
      end.
  (** The producer checks dominators before using their numbered tree. *)
  Parameter F5_produce_checked : forall p s c, produce p = Some (s, c) ->
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true /\
    rename p (dom_tree p) (placement p) (L.live_in p) = Some (s, c).
  (** The two indexes charge syntax and emitted live rows once. *)
  Parameter T0_indexes : forall p,
    (T_def_index p + T_live_sets (L.live_in p) <= k_place *
      N.of_nat (function_size p + L.live_size p + 1) * N.of_nat (function_width p + 1))%N.
  (** One placement search for a variable of the universe charges seed and
      discovered-frontier incidences. *)
  Parameter T1_place_var : forall p x, In x (U.universe (R.prepare p)) ->
    (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x <= k_place *
      N.of_nat (length (definition_blocks p x) +
        fold_right (fun b n => (1 + length (frontier_row (frontiers p) b) + n)%nat)
          0%nat (phi_sites p x) + 1) * N.of_nat (function_width p + 1))%N.
  (** Placement indexes the rows once and sums the indexed variable searches. *)
  Parameter T1a_placement : forall p,
    (T_placement p <= k_place * N.of_nat (function_size p + placement_work p + 1) *
      N.of_nat (function_width p + 1) +
      fold_right N.add 0%N (map
        (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)))
        (U.universe (R.prepare p))))%N.
  (** Initialization charges the source inventory at its syntax width. *)
  Parameter T2a_rename_init : forall p,
    (T_rename_init p <= k_rename * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** The driver counts the blocks for its fuel and runs its bounded rename loop. *)
  Parameter T2b_rename_driver : forall p,
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <= T_rename_init p +
      T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
        (T_rename_step p (dom_tree p) (placement p) (L.live_in p))
        (2 * length (blocks _ _ _ p) + 1) (rename_init p) +
      k_rename * N.of_nat (length (blocks _ _ _ p) + 1))%N.
  (** Both visits to each block charge their statements and emitted incoming arguments. *)
  Parameter T2c_rename_loop : forall p,
    (T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
      (T_rename_step p (dom_tree p) (placement p) (L.live_in p))
      (2 * length (blocks _ _ _ p) + 1) (rename_init p) <=
      k_rename * N.of_nat (function_size p + placement_work p + phi_args p + 1) *
        N.of_nat (function_width p + 1))%N.
  (** Renaming charges statements and the incoming arguments it emits. *)
  Parameter T2_rename : forall p,
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <=
      k_rename * N.of_nat (function_size p + placement_work p + phi_args p + 1) *
        N.of_nat (function_width p + 1))%N.
  (** A candidate keeps the source blocks and stays within the published work and width. *)
  Parameter F6_produce_size : forall p s c, produce p = Some (s, c) ->
    map fst (blocks _ _ _ s) = map fst (blocks _ _ _ p) /\
    (N.of_nat (function_size s + cert_size c) <= k_size * N.of_nat (build_work p))%N /\
    (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
      k_size * N.of_nat (function_width p + 1))%N.
  (** The producer prepares once, builds and prepares the graph, and stops when the
      dominator check rejects. *)
  Parameter T3_produce : forall p,
    (T_produce p <= R.T_prepare p + k_graph +
      k_graph * N.of_nat (length (BC.nodes (R.prepare p)) +
        length (BC.edges (R.prepare p)) + 1) * N.of_nat (function_width p + 1) +
      DG.T_prepare (cfg_graph (BC.nodes (R.prepare p)) (BC.edges (R.prepare p))
        (BC.src (R.prepare p)) (BC.dst (R.prepare p))) +
      D.T_build (graph p) (entry _ _ _ p) +
      D.T_check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
      (if D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p))
       then D.T_tree (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
         F.T_df (graph p) (dom_tree p) + L.T_live_in p + T_def_index p +
         T_live_sets (L.live_in p) + T_placement p +
         T_rename p (dom_tree p) (placement p) (L.live_in p)
       else 0))%N.
  (** The wrapper charges the actual certificate and candidate validators. *)
  Parameter T4_wrapper : forall p,
    (T_build p <= T_produce p +
      match produce p with
      | None => k_wrap
      | Some (s, c) => Va.T_check p s c + Va.T_check_ssa s + k_wrap
      end)%N.
End BUILD_PLAN.

Module Type BUILD_ALL (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q) (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E)
    (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    (S : SSA_T Q PosKeyT BE BC PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (F : FRONTIER_T)
    (L : LIVE_T O P Q R BE E N BC C U SP PB)
    (B : LANG_SSA_LINK O K G Q R BE BC S)
    (Va : VALIDATE_T O K G P Q R BE BC S DG D B) :=
  BUILD_T O K G P Q R BE E N BC C U SP PB S DG D F L B Va <+
  BUILD_PLAN O K G P Q R BE E N BC C U SP PB S DG D F L B Va.
