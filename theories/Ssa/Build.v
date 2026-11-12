(** * Placeholder SSA construction

    This module supplies a checked construction interface.
    For example, its placeholder produces no candidate.
    Builds on: BuildSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data Spec DigraphSig DomSig FrontierSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig ValidateSig BuildSig.
Import List.ListNotations.

Module BuildCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS P PosKeyCode BE) (C : CFG_INDEXED_OPS P N E)
    (U : VARS_OPS P N E C PosKeyCode)
    (SP : SSA_POINTS_OPS P PosKeyCode BE BC N E C PosKeyCode U)
    (S : SSA_OPS P PosKeyCode BE BC PosKeyCode K G)
    (DG : DIGRAPH_OPS) (D : DOM_OPS) (F : FRONTIER_OPS)
    (L : LIVE_OPS O P BE E N BC C U SP)
    (Va : VALIDATE_OPS O K G P BE BC S DG D) <: BUILD_OPS O K G P BE E N BC C U SP S DG D F L Va.
  (* STUB-CODE *)
  Definition produce (_ : P.t) : option (P.t * cert) := None.
  (* STUB-CODE *)
  Definition build (_ : P.t) : option P.t := None.
End BuildCode.

Module Build (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (BE E : TYPE) (N : KEY)
    (BC : CFG P PosKey BE) (C : CFG P N E)
    (U : VARS P N E C PosKey)
    (SP : SSA_POINTS P PosKey BE BC N E C PosKey U)
    (S : SSA P PosKey BE BC PosKey K G)
    (DG : DIGRAPH) (D : DOM) (F : FRONTIER)
    (L : LIVE O P BE E N BC C U SP)
    (B : LANG_SSA_LINK O K G P BE BC S)
    (Va : VALIDATE O K G P BE BC S DG D B) <: BUILD O K G P BE E N BC C U SP S DG D F L B Va.
  Include BuildCode O K G P BE E N BC C U SP S DG D F L Va.
  Lemma build_checked : forall p, build p =
    match produce p with
    | None => None
    | Some (s, c) => if andb (Va.check p s c) (Va.check_ssa s) then Some s else None
    end.
  Proof. Admitted. (* STUB *)
  Lemma build_correct : forall p s, imp_form p -> build p = Some s ->
    ssa_wf s /\ forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof. Admitted. (* STUB *)
End Build.

Module BuildT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G) (BE E N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E)
    (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O P BE E N BC C U SP)
    (S : SSA_T P PosKeyT BE BC PosKeyT K G)
    (DG : DIGRAPH_T) (D : DOM_T) (F : FRONTIER_T)
    (L : LIVE_T O P BE E N BC C U SP PB)
    (B : LANG_SSA_LINK O K G P BE BC S)
    (Va : VALIDATE_T O K G P BE BC S DG D B) <: BUILD_ALL O K G P BE E N BC C U SP PB S DG D F L B Va.
  Include Build O K G P BE E N BC C U SP S DG D F L B Va.
  TimeFun produce.
  TimeFun build.
  Definition c_build : N := 1. (* STUB *)
  Definition graph p := DG.prepare (cfg_graph (BC.nodes p) (BC.edges p) (BC.src p) (BC.dst p)).
  Definition dom_result p := D.build (graph p) (entry _ _ _ p).
  Definition dom_tree p := D.tree (graph p) (entry _ _ _ p)
    (fst (dom_result p)) (snd (dom_result p)).
  Definition frontiers p := F.df (graph p) (dom_tree p).
  Definition df_size p := F.df_size (graph p) (dom_tree p).
  Definition phi_sites p x := F.idf (frontiers p) (definition_blocks p x).
  Definition placement_work p := fold_right (fun x n =>
    fold_right (fun b m => 1 + length (frontier_row (frontiers p) b) + m) 0 (phi_sites p x) + n)
    0 (U.universe p).
  Definition phi_args p :=
    match produce p with Some (s, _) => function_edge_args s | None => 0 end.
  Definition dom_work p :=
    (graph_n (base (graph p)) + graph_e (base (graph p)) + 1) *
      (Nat.log2 (graph_n (base (graph p))) + 1).
  Definition build_work p := function_size p + length (BC.nodes p) + length (BC.edges p) +
    dom_work p + df_size p + placement_work p + L.live_size p + phi_args p + 1.
  (** Construction keeps the published dominator, placement, liveness and argument budget. *)
  Lemma T_build_le : forall p,
    (T_build p <= c_build * N.of_nat (build_work p) * N.of_nat (function_width p + 1) +
      c_build * N.of_nat (Va.op_bits p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma build_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat (build_work p * (function_width p + 1) + Va.op_bits p + 1)) T_build.
  Proof. Admitted. (* STUB *)
  (* STUB-CODE *)
  Definition graph_ok (_ : P.t) : bool := false.
  (* STUB-CODE *)
  Definition def_index (_ : P.t) : ptrie (list positive) := Empty.
  (* STUB-CODE *)
  Definition live_sets (_ : list (positive * list positive)) : ptrie (ptrie unit) := Empty.
  (* STUB-CODE *)
  Definition place_var (_ _ : ptrie (list positive)) (_ : ptrie (ptrie unit))
      (_ : positive) : list positive := [].
  (* STUB-CODE *)
  Definition placement (_ : P.t) : ptrie (list positive) := Empty.
  (* STUB-CODE *)
  Definition rename (_ : P.t) (_ : domtree) (_ : ptrie (list positive))
      (_ : list (positive * list positive)) : option (P.t * cert) := None.
  (* STUB-CODE *)
  Definition rename_init (_ : P.t) : rename_state O.K O.G := RenameState O.K O.G [] [] [] 0%N.
  (* STUB-CODE *)
  Definition rename_step (_ : P.t) (_ : domtree) (_ : ptrie (list positive))
      (_ : list (positive * list positive)) (_ : rename_state O.K O.G)
      : rename_state O.K O.G + option (P.t * cert) := inr None.
  TimeFun graph_ok.
  TimeFun def_index.
  TimeFun live_sets.
  TimeFun place_var.
  TimeFun placement.
  TimeFun rename.
  TimeFun rename_init.
  TimeFun rename_step.
  Definition k_graph : N := 1. (* STUB *)
  Definition k_place : N := 1. (* STUB *)
  Definition k_rename : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Definition k_size : N := 1. (* STUB *)
  Definition placed p x :=
    place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x.

  (** The producer rejects malformed block graphs before frontier construction. *)
  Lemma F1_graph_checked : forall p, graph_ok p = true -> wf_graph (base (graph p)).
  Proof. Admitted. (* STUB *)
  (** The definition index lists each variable's definition blocks. *)
  Lemma F2a_def_index : forall p x,
    frontier_row (def_index p) x = definition_blocks p x.
  Proof. Admitted. (* STUB *)
  (** The live sets answer certificate membership. *)
  Lemma F2b_live_sets : forall rows b x,
    (exists m, trie_get b (live_sets rows) = Some m /\ trie_get x m = Some tt) <->
      In x (cert_live ([], rows) b).
  Proof. Admitted. (* STUB *)
  (** Every variable enters a placement worklist at most once per block. *)
  Lemma F2_place_unique : forall p x, NoDup (placed p x).
  Proof. Admitted. (* STUB *)
  (** Pruned placement uses iterated-frontier blocks with a certified live entry. *)
  Lemma F3_place_region : forall p x b, In b (placed p x) ->
    In b (phi_sites p x) /\ In x (cert_live ([], L.live_in p) b).
  Proof. Admitted. (* STUB *)
  (** The placement table lists exactly the placed variables of each block. *)
  Lemma F3a_placement : forall p b x,
    In x (frontier_row (placement p) b) <-> In x (U.universe p) /\ In b (placed p x).
  Proof. Admitted. (* STUB *)
  (** Renaming uses a bounded explicit stack with one entering and one leaving visit per block. *)
  Lemma F4_rename_loop : forall p t rows live,
    rename p t rows live =
      match loop_fuel (rename_step p t rows live) (2 * length (BC.nodes p) + 1) (rename_init p) with
      | inl _ => None
      | inr answer => answer
      end.
  Proof. Admitted. (* STUB *)
  (** The producer checks dominators before using their numbered tree. *)
  Lemma F5_produce_checked : forall p s c, produce p = Some (s, c) ->
    graph_ok p = true /\
    D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) = true /\
    rename p (dom_tree p) (placement p) (L.live_in p) = Some (s, c).
  Proof. Admitted. (* STUB *)
  (** The two indexes charge syntax and emitted live rows once. *)
  Lemma T0_indexes : forall p,
    (T_def_index p + T_live_sets (L.live_in p) <= k_place *
      N.of_nat (function_size p + L.live_size p + 1) * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** One placement search charges seed and discovered-frontier incidences. *)
  Lemma T1_place_var : forall p x,
    (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)) x <= k_place *
      N.of_nat (length (definition_blocks p x) +
        fold_right (fun b n => (1 + length (frontier_row (frontiers p) b) + n)%nat)
          0%nat (phi_sites p x) + 1) * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Placement indexes the rows once and sums the indexed variable searches. *)
  Lemma T1a_placement : forall p,
    (T_placement p <= k_place * N.of_nat (function_size p + placement_work p + 1) *
      N.of_nat (function_width p + 1) +
      fold_right N.add 0%N (map
        (T_place_var (frontiers p) (def_index p) (live_sets (L.live_in p)))
        (U.universe p)))%N.
  Proof. Admitted. (* STUB *)
  (** Initialization charges the source inventory at its syntax width. *)
  Lemma T2a_rename_init : forall p,
    (T_rename_init p <= k_rename * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The driver charges the clock of its actual bounded rename loop. *)
  Lemma T2b_rename_driver : forall p,
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <= T_rename_init p +
      T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
        (T_rename_step p (dom_tree p) (placement p) (L.live_in p))
        (2 * length (BC.nodes p) + 1) (rename_init p) + k_rename)%N.
  Proof. Admitted. (* STUB *)
  (** Both visits to each block charge their statements and emitted incoming arguments. *)
  Lemma T2c_rename_loop : forall p,
    (T_loop_fuel (rename_step p (dom_tree p) (placement p) (L.live_in p))
      (T_rename_step p (dom_tree p) (placement p) (L.live_in p))
      (2 * length (BC.nodes p) + 1) (rename_init p) <=
      k_rename * N.of_nat (function_size p + placement_work p + phi_args p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Renaming charges statements and the incoming arguments it emits. *)
  Lemma T2_rename : forall p,
    (T_rename p (dom_tree p) (placement p) (L.live_in p) <=
      k_rename * N.of_nat (function_size p + placement_work p + phi_args p + 1) *
        N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** A candidate keeps the source blocks and stays within the published work and width. *)
  Lemma F6_produce_size : forall p s c, produce p = Some (s, c) ->
    map fst (blocks _ _ _ s) = map fst (blocks _ _ _ p) /\
    (N.of_nat (function_size s + cert_size c) <= k_size * N.of_nat (build_work p))%N /\
    (N.of_nat (function_width s + vertex_width (cert_ids c)) <=
      k_size * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The producer checks the graph before preparing it and stops at the first rejection. *)
  Lemma T3_produce : forall p,
    (T_produce p <= T_graph_ok p + k_graph +
      if graph_ok p then
        DG.T_prepare (cfg_graph (BC.nodes p) (BC.edges p) (BC.src p) (BC.dst p)) +
        D.T_build (graph p) (entry _ _ _ p) +
        D.T_check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
        (if D.check (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p))
         then D.T_tree (graph p) (entry _ _ _ p) (fst (dom_result p)) (snd (dom_result p)) +
           F.T_df (graph p) (dom_tree p) + L.T_live_in p + T_def_index p +
           T_live_sets (L.live_in p) + T_placement p +
           T_rename p (dom_tree p) (placement p) (L.live_in p)
         else 0)
      else 0)%N.
  Proof. Admitted. (* STUB *)
  (** Graph screening reads the block presentation once. *)
  Lemma T3a_graph_ok : forall p,
    (T_graph_ok p <= k_graph * N.of_nat (length (BC.nodes p) + length (BC.edges p) + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The wrapper charges the actual certificate and candidate validators. *)
  Lemma T4_wrapper : forall p,
    (T_build p <= T_produce p +
      match produce p with
      | None => k_wrap
      | Some (s, c) => Va.T_check p s c + Va.T_check_ssa s + k_wrap
      end)%N.
  Proof. Admitted. (* STUB *)
End BuildT.
