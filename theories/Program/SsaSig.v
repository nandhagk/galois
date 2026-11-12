(** * Static single-assignment presentations

    Presentations expose value definitions, block parameters, edge operands and guards.
    For example, an incoming edge pairs each destination parameter with its source operand.
    Builds on: Program.CfgSig, Program.VarsSig and Base keys. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import CfgSig SemanticsSig VarsSig.

Inductive definition (N V K : Type) : Type :=
  | Op (operator : K) (operands : list V)
  | Param (block : N) (index : nat)
  | Arbitrary.

Arguments Op {N V K}.
Arguments Param {N V K}.
Arguments Arbitrary {N V K}.

(** Paths follow concrete edges and include both endpoint nodes. *)
Inductive presentation_path {N E : Type} (edges : list E) (src dst : E -> N) :
    N -> list N -> N -> Prop :=
  | Presentation_here : forall n, presentation_path edges src dst n (n :: nil) n
  | Presentation_next : forall e rest target, In e edges ->
      presentation_path edges src dst (dst e) rest target ->
      presentation_path edges src dst (src e) (src e :: rest) target.

(** A chain pairs each adjacent point with its concrete edge occurrence. *)
Inductive presentation_chain {N E : Type} (edges : list E) (src dst : E -> N) :
    list N -> list E -> Prop :=
  | Chain_one : forall n, presentation_chain edges src dst (n :: nil) nil
  | Chain_next : forall n m rest e es, In e edges -> src e = n -> dst e = m ->
      presentation_chain edges src dst (m :: rest) es ->
      presentation_chain edges src dst (n :: m :: rest) (e :: es).

Module Type SSA_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (V : KEY_OPS) (K G : TYPE).
  Parameter values : P.t -> list V.t.
  Parameter entry_params : P.t -> list V.t.
  Parameter arg_rows : P.t -> list (E.t * (V.t * V.t)).
  Parameter def : P.t -> V.t -> definition N.t V.t K.t.
  Parameter home : P.t -> V.t -> N.t.
  Parameter params : P.t -> N.t -> list V.t.
  Parameter args : P.t -> E.t -> list (V.t * V.t).
  Parameter guards : P.t -> E.t -> list (G.t * list V.t).
End SSA_OPS.

Module Type SSA_SPEC (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (V : KEY_OPS) (K G : TYPE)
    (Import S : SSA_OPS P N E C V K G).
  Definition dominates p d n := forall entry route,
    In entry (C.entries p) ->
    presentation_path (C.edges p) (C.src p) (C.dst p) entry route n -> In d route.
  Definition edge_uses p e := map snd (args p e) ++ flat_map snd (guards p e).
  Definition operands p x :=
    match def p x with
    | Op _ xs => xs
    | Param _ _ => nil
    | Arbitrary => nil
    end.
End SSA_SPEC.

Module Type SSA_LAWS (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (V : KEY) (K G : TYPE)
    (Import S : SSA_OPS P N E C V K G).
  (* spec: wf *)
  Parameter wf : P.t -> Prop.
  (** The entry inventory of a well-formed presentation follows entry and parameter
      order. *)
  Parameter entry_params_spec : forall p, wf p ->
    entry_params p = flat_map (params p) (C.entries p).
  (** The operand inventory of a well-formed presentation follows edge and operand
      order. *)
  Parameter arg_rows_spec : forall p, wf p ->
    arg_rows p = flat_map (fun e => map (pair e) (args p e)) (C.edges p).
  (** A well-formed SSA presentation has a well-formed underlying CFG. *)
  Parameter cfg_wf : forall p, wf p -> C.wf p.
  (** A value has one entry in the definition inventory. *)
  Parameter values_nodup : forall p, wf p -> NoDup (values p).
  (** Each inventoried value has a listed definition home. *)
  Parameter homes_listed : forall p x, wf p -> In x (values p) -> In (home p x) (C.nodes p).
  (** Parameter positions and definition readers agree in both directions. *)
  Parameter param_defs : forall p x b i, wf p ->
    (def p x = Param b i <-> nth_error (params p b) i = Some x).
  (** A block parameter is defined at its receiving block. *)
  Parameter param_home : forall p b x, wf p -> In x (params p b) -> home p x = b.
  (** Every listed block parameter belongs to the value inventory. *)
  Parameter params_listed : forall p b x, wf p -> In b (C.nodes p) ->
    In x (params p b) -> In x (values p).
  (** Each incoming operand list follows the destination parameter order. *)
  Parameter args_params : forall p e, wf p -> In e (C.edges p) ->
    map fst (args p e) = params p (C.dst p e).
  (** Incoming operands have inventoried definitions dominating the edge source. *)
  Parameter args_dominate : forall p e x y, wf p -> In e (C.edges p) ->
    In (x, y) (args p e) -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p y) route.
  (** Guard operands have inventoried definitions dominating the edge source. *)
  Parameter guards_dominate : forall p e g xs x, wf p -> In e (C.edges p) ->
    In (g, xs) (guards p e) -> In x xs -> In x (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (C.src p e) ->
      In (home p x) route.
  (** Every operation operand is defined at a dominator of the result's home. *)
  Parameter op_args_dominate : forall p x op xs y, wf p -> In x (values p) ->
    def p x = Op op xs -> In y xs -> In y (values p) /\ forall entry route,
      In entry (C.entries p) ->
      presentation_path (C.edges p) (C.src p) (C.dst p) entry route (home p x) ->
      In (home p y) route.
  (** Operations that share a home depend on each other without a cycle. *)
  Parameter op_args_acyclic : forall p, wf p ->
    well_founded (fun y x => In x (values p) /\ home p y = home p x /\
      exists op xs, def p x = Op op xs /\ In y xs).
End SSA_LAWS.

Module Type SSA (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (V : KEY) (K G : TYPE) :=
  SSA_OPS P N E C V K G <+ SSA_SPEC P N E C V K G <+ SSA_LAWS P N E C V K G.

Module Type SSA_TIME (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (V : KEY_T) (K G : TYPE)
    (Import S : SSA P N E C V K G).
  Parameter T_values : P.t -> N.
  Parameter T_entry_params T_arg_rows : P.t -> N.
  Parameter T_def : P.t -> V.t -> N.
  Parameter T_home : P.t -> V.t -> N.
  Parameter T_params : P.t -> N.t -> N.
  Parameter T_args : P.t -> E.t -> N.
  Parameter T_guards : P.t -> E.t -> N.
  Parameter c_ssa : N.
  (** Entry-parameter enumeration pays for its output. *)
  Parameter T_entry_params_le : forall p,
    (T_entry_params p <= c_ssa * N.of_nat (length (entry_params p) + 1))%N.
  (** Operand enumeration pays for its output. *)
  Parameter T_arg_rows_le : forall p,
    (T_arg_rows p <= c_ssa * N.of_nat (length (arg_rows p) + 1))%N.
  (** The value inventory pays for its output. *)
  Parameter T_values_le : forall p,
    (T_values p <= c_ssa * N.of_nat (length (values p) + 1))%N.
  (** Definition lookup pays for the value key and the returned operands. *)
  Parameter T_def_le : forall p x,
    (T_def p x <= c_ssa * N.of_nat (V.bits x + length (operands p x) + 1))%N.
  (** Home lookup pays for the value key. *)
  Parameter T_home_le : forall p x, (T_home p x <= c_ssa * N.of_nat (V.bits x + 1))%N.
  (** Parameter lookup pays for the node key and the returned values. *)
  Parameter T_params_le : forall p n,
    (T_params p n <= c_ssa * N.of_nat (N.bits n + length (params p n) + 1))%N.
  (** Incoming operands pay for the edge key and the returned pairs. *)
  Parameter T_args_le : forall p e,
    (T_args p e <= c_ssa * N.of_nat (E.bits e + length (args p e) + 1))%N.
  (** Guards pay for the edge key and the returned guard list. *)
  Parameter T_guards_le : forall p e,
    (T_guards p e <= c_ssa * N.of_nat (E.bits e + length (guards p e) + 1))%N.
End SSA_TIME.

Module Type SSA_T (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (V : KEY_T) (K G : TYPE) :=
  SSA P N E C V K G <+ SSA_TIME P N E C V K G.

Module Type SSA_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (V : KEY) (K G Val : TYPE)
    (S : SSA P N E C V K G) (M : SEMANTICS P) (L : CFG_LINK P N E C M).
  Parameter venv : M.state -> V.t -> option Val.t.
  Parameter eval : K.t -> list Val.t -> option Val.t.
  Parameter holds : G.t -> list Val.t -> Prop.
  Definition guard_ops_consistent p s e :=
    forall g xs x op ys, In (g, xs) (S.guards p e) -> In x xs ->
      S.def p x = Op op ys -> exists cs c,
        Forall2 (fun y d => venv s y = Some d) ys cs /\
        venv s x = Some c /\ eval op cs = Some c.
  (** The taken edge's guards hold on their source-state operands. *)
  Parameter guards_hold : forall p s t e,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> L.taken p s t e ->
    forall g xs, In (g, xs) (S.guards p e) -> exists cs,
      Forall2 (fun x c => venv s x = Some c) xs cs /\ holds g cs.
  (** Operations used by guards agree with their source-state arguments. *)
  Parameter guard_op_defined : forall p s t e,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> L.taken p s t e ->
    guard_ops_consistent p s e.
  (** New bindings originate from an operation, an incoming operand, or an arbitrary value. *)
  Parameter value_origin : forall p s t x c,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> venv t x = Some c ->
    venv s x = Some c \/
    (exists op xs cs, S.def p x = Op op xs /\
      Forall2 (fun y d => venv t y = Some d) xs cs /\ eval op cs = Some c) \/
    (exists e b i y, S.def p x = Param b i /\ L.taken p s t e /\
      C.dst p e = b /\ nth_error (S.args p e) i = Some (x, y) /\ venv s y = Some c) \/
    S.def p x = Arbitrary.
  (** Every defined runtime binding belongs to the static value inventory. *)
  Parameter coverage : forall p s x c,
    reachable (M.initial p) (M.step p) s -> venv s x = Some c -> In x (S.values p).
  (** An edge can change a binding only on arrival at its definition home. *)
  Parameter redefine_on_edge : forall p s t e x,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> L.taken p s t e ->
    venv t x <> venv s x -> S.home p x = L.point t.
  (** Bindings retain their values across edges arriving away from their homes. *)
  Parameter frame_on_edge : forall p s t e x,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> L.taken p s t e ->
    S.home p x <> L.point t -> venv t x = venv s x.
End SSA_LINK.

Module Type SSA_POINTS_OPS (P : TYPE) (B : KEY_OPS) (BE : TYPE)
    (BC : CFG_INDEXED_OPS P B BE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (V : KEY_OPS) (U : VARS_OPS P N E C V).
  Parameter points_in_block : P.t -> B.t -> list N.t.
  Parameter instruction_edges : P.t -> B.t -> list E.t.
  Parameter parameter_edge : P.t -> B.t -> E.t.
  Parameter block_of_point : P.t -> N.t -> B.t.
  Parameter block_edge_of : P.t -> E.t -> option BE.t.
  Parameter block_params : P.t -> B.t -> list V.t.
  Parameter block_edge_args : P.t -> BE.t -> list V.t.
  Parameter point_definition : P.t -> V.t -> option N.t.
End SSA_POINTS_OPS.

Module Type SSA_POINTS_LAWS (P : TYPE) (B : KEY) (BE : TYPE)
    (BC : CFG P B BE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (V : KEY) (U : VARS P N E C V)
    (Import S : SSA_POINTS_OPS P B BE BC N E C V U).
  (* spec: wf *)
  Parameter wf : P.t -> Prop.
  (** Point and block presentations have well-formed underlying graphs. *)
  Parameter graphs_wf : forall p, wf p -> C.wf p /\ BC.wf p.
  (** Point adjacency contains no duplicate edge identity. *)
  Parameter points_out_nodup : forall p n, wf p -> NoDup (C.out p n).
  (** Block adjacency contains no duplicate edge identity. *)
  Parameter blocks_out_nodup : forall p b, wf p -> NoDup (BC.out p b).
  (** The block inventories cover exactly the point domain. *)
  Parameter points_covered : forall p n, wf p ->
    (In n (C.nodes p) <-> exists b, In b (BC.nodes p) /\ In n (points_in_block p b)).
  (** A block's point order contains no repeated point. *)
  Parameter points_unique : forall p b, wf p -> NoDup (points_in_block p b).
  (** Every listed point has the block that lists it as its owner. *)
  Parameter points_owner : forall p b n, wf p -> In b (BC.nodes p) ->
    In n (points_in_block p b) -> block_of_point p n = b.
  (** Every listed block contains at least one point. *)
  Parameter blocks_nonempty : forall p b, wf p -> In b (BC.nodes p) ->
    points_in_block p b <> nil.
  (** Instruction edges connect points in their listed order. *)
  Parameter points_ordered : forall p b, wf p -> In b (BC.nodes p) ->
    presentation_chain (C.edges p) (C.src p) (C.dst p)
      (points_in_block p b) (instruction_edges p b).
  (** Internal instruction edges have no block-edge projection. *)
  Parameter instruction_edges_internal : forall p b e, wf p -> In b (BC.nodes p) ->
    In e (instruction_edges p b) -> block_edge_of p e = None.
  (** Every unprojected edge is an instruction edge of its source block. *)
  Parameter instruction_edges_complete : forall p e, wf p -> In e (C.edges p) ->
    block_edge_of p e = None -> In e (instruction_edges p (block_of_point p (C.src p e))).
  (** The parameter-binding edge is the first instruction edge of a block. *)
  Parameter parameter_edge_first : forall p b, wf p -> In b (BC.nodes p) ->
    nth_error (instruction_edges p b) 0 = Some (parameter_edge p b).
  (** The parameter-binding edge defines exactly the block's parameters. *)
  Parameter parameter_edge_defs : forall p b x, wf p -> In b (BC.nodes p) ->
    (In x (U.defs p (parameter_edge p b)) <-> In x (block_params p b)).
  (** Projected edges connect the last source point to the first target point. *)
  Parameter point_edge_projection : forall p e, wf p -> In e (C.edges p) ->
    match block_edge_of p e with
    | None => block_of_point p (C.src p e) = block_of_point p (C.dst p e)
    | Some be => In be (BC.edges p) /\ BC.src p be = block_of_point p (C.src p e) /\
        BC.dst p be = block_of_point p (C.dst p e) /\
        last (points_in_block p (block_of_point p (C.src p e))) (C.src p e) = C.src p e /\
        nth_error (points_in_block p (BC.dst p be)) 0 = Some (C.dst p e)
    end.
  (** Each incoming block edge supplies one operand per destination parameter. *)
  Parameter phi_args_length : forall p be, wf p -> In be (BC.edges p) ->
    length (block_edge_args p be) = length (block_params p (BC.dst p be)).
  (** Incoming operands are uses of that edge's own point occurrence. *)
  Parameter phi_edge_use : forall p e be x, wf p -> In e (C.edges p) ->
    block_edge_of p e = Some be -> In x (block_edge_args p be) -> In x (U.uses p e).
  (** Every block edge has a point-edge occurrence. *)
  Parameter block_edge_covered : forall p be, wf p -> In be (BC.edges p) ->
    exists e, In e (C.edges p) /\ block_edge_of p e = Some be.
  (** Distinct point edges cannot project to the same block-edge identity. *)
  Parameter block_edge_unique : forall p e1 e2 be, wf p ->
    In e1 (C.edges p) -> In e2 (C.edges p) ->
    block_edge_of p e1 = Some be -> block_edge_of p e2 = Some be -> e1 = e2.
End SSA_POINTS_LAWS.

Module Type SSA_POINTS (P : TYPE) (B : KEY) (BE : TYPE)
    (BC : CFG P B BE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (V : KEY) (U : VARS P N E C V) :=
  SSA_POINTS_OPS P B BE BC N E C V U <+ SSA_POINTS_LAWS P B BE BC N E C V U.

Module Type SSA_POINTS_TIME (P : TYPE) (B : KEY_T) (BE : KEY_T)
    (BC : CFG_T P B BE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (V : KEY_T) (U : VARS_T P N E C V)
    (Import S : SSA_POINTS P B BE BC N E C V U).
  Parameter T_points_in_block T_instruction_edges T_parameter_edge : P.t -> B.t -> N.
  Parameter T_block_of_point : P.t -> N.t -> N.
  Parameter T_block_edge_of : P.t -> E.t -> N.
  Parameter T_block_params : P.t -> B.t -> N.
  Parameter T_block_edge_args : P.t -> BE.t -> N.
  Parameter T_point_definition : P.t -> V.t -> N.
  Parameter c_points : N.
  (** Block point lists pay for the key and the returned points. *)
  Parameter T_points_in_block_le : forall p b,
    (T_points_in_block p b <=
      c_points * N.of_nat (B.bits b + length (points_in_block p b) + 1))%N.
  (** Instruction edge lists pay for the key and the returned edges. *)
  Parameter T_instruction_edges_le : forall p b,
    (T_instruction_edges p b <=
      c_points * N.of_nat (B.bits b + length (instruction_edges p b) + 1))%N.
  (** The parameter edge lookup pays for the block key. *)
  Parameter T_parameter_edge_le : forall p b,
    (T_parameter_edge p b <= c_points * N.of_nat (B.bits b + 1))%N.
  (** The owner lookup pays for the point key. *)
  Parameter T_block_of_point_le : forall p n,
    (T_block_of_point p n <= c_points * N.of_nat (N.bits n + 1))%N.
  (** The edge projection pays for the edge key. *)
  Parameter T_block_edge_of_le : forall p e,
    (T_block_edge_of p e <= c_points * N.of_nat (E.bits e + 1))%N.
  (** Block parameters pay for the key and the returned values. *)
  Parameter T_block_params_le : forall p b,
    (T_block_params p b <=
      c_points * N.of_nat (B.bits b + length (block_params p b) + 1))%N.
  (** Phi operands pay for the block-edge key and the returned values. *)
  Parameter T_block_edge_args_le : forall p be,
    (T_block_edge_args p be <=
      c_points * N.of_nat (BE.bits be + length (block_edge_args p be) + 1))%N.
  (** The definition point lookup pays for the value key. *)
  Parameter T_point_definition_le : forall p x,
    (T_point_definition p x <= c_points * N.of_nat (V.bits x + 1))%N.
End SSA_POINTS_TIME.

Module Type SSA_POINTS_T (P : TYPE) (B : KEY_T) (BE : KEY_T)
    (BC : CFG_T P B BE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (V : KEY_T) (U : VARS_T P N E C V) :=
  SSA_POINTS P B BE BC N E C V U <+ SSA_POINTS_TIME P B BE BC N E C V U.

Module Type SSA_POINTS_STRICT_LAWS (P : TYPE) (B : KEY) (BE : TYPE)
    (BC : CFG P B BE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (V : KEY) (U : VARS P N E C V) (S : SSA_POINTS P B BE BC N E C V U).
  Definition point_reachable p n := exists entry route, In entry (C.entries p) /\
    presentation_path (C.edges p) (C.src p) (C.dst p) entry route n.
  Definition point_dominates p d n := forall entry route, In entry (C.entries p) ->
    presentation_path (C.edges p) (C.src p) (C.dst p) entry route n -> In d route.
  Definition point_use_at p n x := In x (U.exits p n) \/
    exists e, In e (C.out p n) /\ In x (U.uses p e).
  (** The point graph has exactly one entry. *)
  Parameter single_entry : forall p, S.wf p -> exists entry, C.entries p = entry :: nil.
  (** A reachable use has a reachable definition strictly dominating its point. *)
  Parameter uses_defined : forall p n x, S.wf p -> point_reachable p n ->
    point_use_at p n x -> exists d, S.point_definition p x = Some d /\
      point_reachable p d /\ point_dominates p d n /\ d <> n.
  (** A reachable definition edge leaves the value's unique definition point. *)
  Parameter defs_at_home : forall p n e x, S.wf p -> point_reachable p n ->
    In e (C.out p n) -> In x (U.defs p e) -> S.point_definition p x = Some n.
  (** Every outgoing edge of a reachable definition point kills that value. *)
  Parameter home_kills : forall p x d e, S.wf p -> S.point_definition p x = Some d ->
    point_reachable p d -> In e (C.out p d) -> In x (U.defs p e).
  (** Two reachable definition edges of one value have the same source point. *)
  Parameter definitions_unique : forall p n1 n2 e1 e2 x, S.wf p ->
    point_reachable p n1 -> point_reachable p n2 ->
    In e1 (C.out p n1) -> In e2 (C.out p n2) ->
    In x (U.defs p e1) -> In x (U.defs p e2) -> n1 = n2.
End SSA_POINTS_STRICT_LAWS.
