(** * Untrusted liveness production

    A producer lists variables needed at each block entry for the SSA certificate.
    For example, an operand read before any assignment is live at its block's entry.
    Builds on: Ssa.Lang, Program variable and point presentations, and graph measures. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std BigO.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang.
Import List.ListNotations.

Definition function_vars {K G} (p : func positive K G) : list positive :=
  inputs _ _ _ p ++ flat_map (fun item =>
    params _ _ _ (snd item) ++ flat_map (fun '(x, _, ys) => x :: ys)
      (code _ _ _ (snd item)) ++ exit_uses (term _ _ _ (snd item))) (blocks _ _ _ p).
TimeFun function_vars.

Definition exit_targets {X G} (e : exit X G) : list positive :=
  match e with
  | Jump b _ => [b]
  | Branch _ _ b _ c _ => [b; c]
  | Return _ => []
  end.
TimeFun exit_targets.

Definition function_ids {K G} (p : func positive K G) : list positive :=
  entry _ _ _ p :: function_vars p ++ flat_map (fun item =>
    fst item :: exit_targets (term _ _ _ (snd item))) (blocks _ _ _ p).
TimeFun function_ids.

Definition function_size {K G} (p : func positive K G) : nat :=
  length (function_vars p) + length (blocks _ _ _ p) +
    fold_right (fun item n => length (code _ _ _ (snd item)) + n) 0 (blocks _ _ _ p).
TimeFun function_size.

Definition function_width {K G} (p : func positive K G) : nat :=
  graph_max (vertex_width (function_ids p))
    (Pos.size_nat (Pos.of_succ_nat (function_size p))).
TimeFun function_width.

(** Liveness follows listed outgoing edges to a use without an intervening definition. *)
Inductive point_live {N E V} (nodes : list N) (out : N -> list E) (dst : E -> N)
    (uses defs : E -> list V) (exits : N -> list V) (x : V) : N -> Prop :=
  | Point_live_exit : forall n, In x (exits n) ->
      point_live nodes out dst uses defs exits x n
  | Point_live_use : forall n e, In e (out n) -> In x (uses e) ->
      point_live nodes out dst uses defs exits x n
  | Point_live_next : forall n e, In e (out n) -> ~ In x (defs e) -> In (dst e) nodes ->
      point_live nodes out dst uses defs exits x (dst e) ->
      point_live nodes out dst uses defs exits x n.

Definition index_row {A} (m : ptrie (list A)) (x : positive) : list A :=
  match trie_get x m with
  | Some row => row
  | None => []
  end.
TimeFun index_row.

Module Type LIVE_OPS (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS P PosKeyCode BE) (C : CFG_INDEXED_OPS P N E)
    (U : VARS_OPS P N E C PosKeyCode)
    (SP : SSA_POINTS_OPS P PosKeyCode BE BC N E C PosKeyCode U).
  Parameter live_in : P.t -> list (positive * list positive).
End LIVE_OPS.

Module Type LIVE (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E : TYPE) (N : KEY)
    (BC : CFG P PosKey BE) (C : CFG P N E) (U : VARS P N E C PosKey)
    (SP : SSA_POINTS P PosKey BE BC N E C PosKey U) :=
  LIVE_OPS O P BE E N BC C U SP.

Module Type LANG_PRESENT_BUDGET (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E) (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U).
  Parameter c_present : N.
  (** Each listed block contributes at most its two exit edges. *)
  Parameter block_edges_le : forall p, length (BC.edges p) <= 2 * length (blocks _ _ _ p).
  (** Points, point edges and variable occurrences are linear in the syntax. *)
  Parameter points_le : forall p,
    (N.of_nat (length (C.nodes p) + length (C.edges p) + length (U.occurrences p)) <=
      c_present * N.of_nat (function_size p + 1))%N.
  (** Listed point keys are within a constant factor of the syntax width. *)
  Parameter point_bits_le : forall p n, In n (C.nodes p) ->
    (N.of_nat (N.bits n) <= c_present * N.of_nat (function_width p + 1))%N.
  (** Listed edge keys are within a constant factor of the syntax width. *)
  Parameter edge_bits_le : forall p e, In e (C.edges p) ->
    (N.of_nat (E.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
  (** Listed block-edge keys are within a constant factor of the syntax width. *)
  Parameter block_edge_bits_le : forall p e, In e (BC.edges p) ->
    (N.of_nat (BE.bits e) <= c_present * N.of_nat (function_width p + 1))%N.
End LANG_PRESENT_BUDGET.

Module Type LIVE_TIME (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E) (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O P BE E N BC C U SP)
    (Import L : LIVE O P BE E N BC C U SP).
  (* spec: live_region *)
  Parameter live_region : P.t -> list (N.t * positive).
  (** The cost region enumerates each live point/value pair exactly once. *)
  Parameter live_region_spec : forall p,
    NoDup (live_region p) /\ forall n x,
      (In (n, x) (live_region p) <-> In n (C.nodes p) /\ In x (U.universe p) /\
        point_live (C.nodes p) (C.out p) (C.dst p) (U.uses p) (U.defs p) (U.exits p) x n).
  Definition live_size p := fold_right (fun pair n =>
    1 + length (C.inc p (fst pair)) + n) 0 (live_region p).
  Definition rows_size (rows : list (positive * list positive)) :=
    fold_right (fun row n => 1 + length (snd row) + n) 0 rows.
  (** The producer emits at most one row entry per charged block and live pair. *)
  Parameter live_in_size : forall p,
    rows_size (live_in p) <= length (blocks _ _ _ p) + live_size p.

  Parameter T_live_in : P.t -> N.
  Parameter c_live : N.
  (** Path exploration pays for syntax and live predecessor incidences. *)
  Parameter T_live_in_le : forall p,
    (T_live_in p <= c_live * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** The producer has the published output-sensitive bit-cost bound. *)
  Parameter live_in_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
    T_live_in.
End LIVE_TIME.

Module Type LIVE_T (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E) (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O P BE E N BC C U SP) :=
  LIVE O P BE E N BC C U SP <+ LIVE_TIME O P BE E N BC C U SP PB.

Module Type LIVE_PLAN (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E) (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O P BE E N BC C U SP)
    (Import L : LIVE_T O P BE E N BC C U SP PB).
  Parameter use_index : P.t -> ptrie (list N.t).
  Parameter T_use_index : P.t -> N.
  Parameter explore : P.t -> ptrie (list N.t) -> positive -> list N.t.
  Parameter T_explore : P.t -> ptrie (list N.t) -> positive -> N.
  Parameter k_index : N.
  Parameter k_explore k_rows : N.
  Definition visits p x := filter (fun pair => Pos.eqb (snd pair) x) (live_region p).
  Definition variable_work p x := fold_right (fun pair n =>
    1 + length (C.inc p (fst pair)) + n) 0 (visits p x).
  (** Indexed use points of a variable are distinct charged live pairs. *)
  Parameter F0_use_index : forall p x, NoDup (index_row (use_index p) x) /\
    forall n, In n (index_row (use_index p) x) -> In (n, x) (live_region p).
  (** Each per-variable search visits a point at most once. *)
  Parameter F1_explore_nodup : forall p x, NoDup (explore p (use_index p) x).
  (** Every visited search point belongs to its charged semantic region. *)
  Parameter F2_explore_region : forall p x n, In n (explore p (use_index p) x) ->
    In (n, x) (live_region p).
  (** Deduplicated variables partition the total live-incidence budget. *)
  Parameter F3_partition : forall p,
    fold_right (fun x n => variable_work p x + n) 0 (U.universe p) = live_size p.
  (** Indexing reads each variable occurrence once at the syntax width. *)
  Parameter T0_use_index : forall p,
    (T_use_index p <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  (** A variable's search charges each visited point and incoming occurrence. *)
  Parameter T1_explore : forall p x,
    (T_explore p (use_index p) x <= k_explore * N.of_nat (variable_work p x + 1) *
      N.of_nat (function_width p + 1))%N.
  (** The driver indexes once, searches each variable and groups points into block rows. *)
  Parameter T2_rows : forall p,
    (T_live_in p <= k_rows * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1) + T_use_index p +
      fold_right N.add 0%N (map (T_explore p (use_index p)) (U.universe p)))%N.
End LIVE_PLAN.

Module Type LIVE_ALL (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (BE E N : KEY_T)
    (BC : CFG_T P PosKeyT BE) (C : CFG_T P N E) (U : VARS_T P N E C PosKeyT)
    (SP : SSA_POINTS_T P PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O P BE E N BC C U SP) :=
  LIVE_T O P BE E N BC C U SP PB <+ LIVE_PLAN O P BE E N BC C U SP PB.
