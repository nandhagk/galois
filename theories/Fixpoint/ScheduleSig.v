(** * Checked widening schedules

    Schedules rank dependency vertices and place widening heads on backward dependencies.
    For example, a self-dependency requires its target to be a head.
    Builds on: Fixpoint.PolicySig, Fixpoint.SystemSig and Graph.WtoSig. *)

From Stdlib Require Import List PArith Arith NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import Data Spec DigraphSig WtoSig.
From Galois.Fixpoint Require Import SystemSig PolicySig.

Module Type SCHEDULE_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L).
  Parameter dep_graph : S.prog -> digraph.
  Parameter of_wto : wto -> head_cfg -> L.wparam -> nat -> policy L.wparam.
  Parameter plan : S.prog -> head_cfg -> L.wparam -> nat -> option (policy L.wparam).
  Parameter cuts : S.prog -> policy L.wparam -> bool.
End SCHEDULE_OPS.

Module Type SCHEDULE_SPEC (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (Import H : SCHEDULE_OPS L S).
  (** Dependency edges connect every declared read to every declared write of a row. *)
  Definition dependency_edge (p : S.prog) (u v : positive) : Prop :=
    exists r x y, In r (S.rows p) /\ In x (S.deps p r) /\
      In y (S.target p r :: S.sides p r) /\ S.key_code x = u /\ S.key_code y = v.
  Definition priority (pol : policy L.wparam) (c : positive) : positive :=
    match trie_get c (prio pol) with
    | Some rank => rank
    | None => 1%positive
    end.
  Definition row_count p : nat := length (S.rows p).
  Definition occurrence_count p : nat := fold_right Nat.add 0
    (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (S.rows p)).
  Definition edge_count (p : S.prog) : nat := fold_right Nat.add 0
    (List.map (fun r => length (S.deps p r) * (length (S.sides p r) + 1)) (S.rows p)).
  Definition prio_width (p : S.prog) (pol : policy L.wparam) : nat :=
    fold_right Nat.max 0 (List.map (fun c => Pos.size_nat (priority pol c))
      (flat_map (fun r => List.map S.key_code ((S.target p r :: S.sides p r) ++ S.deps p r)) (S.rows p))).
End SCHEDULE_SPEC.

Module Type SCHEDULE_LAWS (L : WLATTICE) (S : SYSTEM L)
    (G : DIGRAPH) (W : WTO) (Import H : SCHEDULE_OPS L S)
    (Import HS : SCHEDULE_SPEC L S H).
  (** The dependency graph has exactly the declared dependency edges. *)
  Parameter dep_graph_edges : forall p u v,
    edge (dep_graph p) u v <-> dependency_edge p u v.
  (** The graph lists exactly the key codes read or written by a row. *)
  Parameter dep_graph_vertices : forall p c,
    In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\ In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\
        S.key_code x = c.
  (** WTO priorities use the WTO's public rank projection. *)
  Parameter of_wto_prio : forall w cfg wp n, prio (of_wto w cfg wp n) = W.ranks w.
  (** WTO loop heads receive the supplied head configuration. *)
  Parameter of_wto_heads : forall w cfg wp n c,
    trie_get c (heads (of_wto w cfg wp n)) =
      if existsb (Pos.eqb c) (W.heads w) then Some cfg else None.
  (** Schedule construction retains widening parameters. *)
  Parameter of_wto_wp : forall w cfg wp n, PolicySig.wp (of_wto w cfg wp n) = wp.
  (** Schedule construction retains the requested narrowing pass count. *)
  Parameter of_wto_passes : forall w cfg wp n, passes (of_wto w cfg wp n) = n.
  (** Planning accepts a built WTO only when its checker accepts it. *)
  Parameter plan_spec : forall p cfg wp n,
    let g := G.prepare (dep_graph p) in
    let roots := verts (dep_graph p) in
    let w := W.build g roots in
    plan p cfg wp n = if W.check g roots w then Some (of_wto w cfg wp n) else None.
  (** Every non-increasing dependency edge enters a configured head. *)
  Parameter cuts_spec : forall p pol,
    cuts p pol = true <-> forall u v, dependency_edge p u v ->
      (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  (** A checked WTO cuts every non-increasing dependency edge. *)
  Parameter of_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  (** Every accepted schedule cuts the program's dependency edges. *)
  Parameter plan_cuts : forall p cfg wp n pol,
    plan p cfg wp n = Some pol -> cuts p pol = true.
End SCHEDULE_LAWS.

Module Type SCHEDULE (L : WLATTICE) (S : SYSTEM L) (G : DIGRAPH) (W : WTO) :=
  SCHEDULE_OPS L S <+ SCHEDULE_SPEC L S <+ SCHEDULE_LAWS L S G W.

Module Type SCHEDULE_TIME (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) (Import H : SCHEDULE L S G W).
  Parameter T_dep_graph : S.prog -> N.
  Parameter T_of_wto : wto -> head_cfg -> L.wparam -> nat -> N.
  Parameter T_plan : S.prog -> head_cfg -> L.wparam -> nat -> N.
  Parameter T_cuts : S.prog -> policy L.wparam -> N.
  Parameter c_sched : N.
  (** Dependency graph construction charges every declared occurrence. *)
  Parameter T_dep_graph_le : forall p, S.wf p ->
    (T_dep_graph p <= c_sched * (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
      N.of_nat (S.kw p + 1) +
      N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  (** WTO conversion charges traversal, ranks and encoded vertices. *)
  Parameter T_of_wto_le : forall w cfg wp n,
    (T_of_wto w cfg wp n <= c_sched * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  (** Planning pays for graph preparation and the nesting depth of the built WTO. *)
  Parameter T_plan_le : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched * (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
      N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
      N.of_nat (S.kw p + 1) +
      N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  (** Cut checking is linear in declared occurrences and program key width. *)
  Parameter T_cuts_le : forall p pol, S.wf p ->
    (T_cuts p pol <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + 1) *
       N.of_nat (S.kw p + prio_width p pol + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  (** Every planned priority fits the program key width. *)
  Parameter plan_prio_width : forall p cfg wp n pol, S.wf p ->
    plan p cfg wp n = Some pol -> prio_width p pol <= S.kw p + 1.
End SCHEDULE_TIME.

Module Type SCHEDULE_T (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) := SCHEDULE L S G W <+ SCHEDULE_TIME L S G W.

(** * Schedule construction helpers *)

Record schedule_graph_state := ScheduleGraphState {
  schedule_vertices : list positive;
  schedule_seen : ptrie bool;
  schedule_successors : ptrie (list positive)
}.

(** Vertex insertion keeps one reverse-order inventory entry per encoded key. *)
Definition schedule_vertex (v : positive) (st : schedule_graph_state) : schedule_graph_state :=
  match st with
  | ScheduleGraphState vs seen adjacency =>
    match trie_get v seen with
    | Some _ => st
    | None => ScheduleGraphState (v :: vs) (PTrieCode.set v true seen) adjacency
    end
  end.

TimeFun schedule_vertex.

(** Edge insertion retains every dependency occurrence. *)
Definition schedule_edge (u v : positive) (st : schedule_graph_state) : schedule_graph_state :=
  match st with
  | ScheduleGraphState vs seen adjacency =>
    let old := match trie_get u adjacency with Some xs => xs | None => nil end in
    ScheduleGraphState vs seen (PTrieCode.set u (v :: old) adjacency)
  end.

TimeFun schedule_edge.

(** A row contributes all read and write vertices and the product of its dependency lists. *)
Definition schedule_graph_row {R K} (code : K -> positive) (target : R -> K)
    (deps sides : R -> list K) (st : schedule_graph_state) (r : R) : schedule_graph_state :=
  let writes := map code (target r :: sides r) in
  let reads := map code (deps r) in
  let listed := fold_left (fun acc v => schedule_vertex v acc) (writes ++ reads) st in
  fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc) reads listed.

TimeFun schedule_graph_row.

(** Dependency graphs keep a unique vertex inventory and all generated edge occurrences. *)
Definition schedule_graph {R K} (code : K -> positive) (target : R -> K)
    (deps sides : R -> list K) (rows : list R) : digraph :=
  match fold_left (schedule_graph_row code target deps sides) rows
    (ScheduleGraphState nil Empty Empty) with
  | ScheduleGraphState vs _ adjacency => Digraph (rev_append vs nil) adjacency
  end.

TimeFun schedule_graph.

(** Missing priorities receive the same default as the public schedule projection. *)
Definition schedule_priority {W} (pol : policy W) (v : positive) : positive :=
  match trie_get v (prio pol) with Some rank => rank | None => 1%positive end.

TimeFun schedule_priority.

(** The largest dependency rank suffices to check all writes of one row. *)
Definition schedule_read_rank {W} (pol : policy W) (reads : list positive) : option positive :=
  fold_left (fun best v => let rank := schedule_priority pol v in
    match best with
    | None => Some rank
    | Some old => Some (if Pos.ltb old rank then rank else old)
    end) reads None.

TimeFun schedule_read_rank.

(** A write is legal when it raises every dependency rank or has a widening head. *)
Definition schedule_write_cut {W} (pol : policy W) (read_rank v : positive) : bool :=
  if Pos.ltb read_rank (schedule_priority pol v) then true else
    match trie_get v (heads pol) with Some _ => true | None => false end.

TimeFun schedule_write_cut.

(** Cut checking scans each row's dependency and write occurrences once. *)
Definition schedule_cut_row {R K W} (code : K -> positive) (target : R -> K)
    (deps sides : R -> list K) (pol : policy W) (r : R) : bool :=
  match schedule_read_rank pol (map code (deps r)) with
  | None => true
  | Some rank => forallb (fun x => schedule_write_cut pol rank (code x)) (target r :: sides r)
  end.

TimeFun schedule_cut_row.

(** Head insertion assigns the supplied configuration to each structural loop head. *)
Definition schedule_head_map (cfg : head_cfg) (vs : list positive) : ptrie head_cfg :=
  fold_left (fun m v => PTrieCode.set v cfg m) vs Empty.

TimeFun schedule_head_map.

Module Type SCHEDULE_PLAN (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) (Import H : SCHEDULE_T L S G W).
  Parameter k_graph k_heads k_cuts k_plan : N.
  (** Construction uses the shared first-order graph builder. *)
  Parameter F1_graph : forall p, dep_graph p =
    schedule_graph S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p).
  (** The graph builder lists each read or write code exactly once. *)
  Parameter F2_vertices : forall p, NoDup (verts (dep_graph p)) /\
    forall c, In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\ In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\
        S.key_code x = c.
  (** Every emitted adjacency occurrence comes from a declared dependency product. *)
  Parameter F3_edges : forall p u v, edge (dep_graph p) u v <-> dependency_edge p u v.
  (** Preparation retains a well-formed graph whose vertices are all roots. *)
  Parameter F4_prepared : forall p,
    wf_graph (dep_graph p) /\ base (G.prepare (dep_graph p)) = dep_graph p /\
    forall u, In u (verts (dep_graph p)) ->
      reach (base (G.prepare (dep_graph p))) (verts (dep_graph p)) u.
  (** WTO conversion pairs its public ranks with its configured structural heads. *)
  Parameter F5_policy : forall w cfg wp n, of_wto w cfg wp n =
    @Policy L.wparam (W.ranks w) (schedule_head_map cfg (W.heads w)) wp n.
  (** Cut checking uses the maximum dependency rank for each row. *)
  Parameter F6_cut_code : forall p pol, cuts p pol =
    forallb (schedule_cut_row S.key_code (S.target p) (S.deps p) (S.sides p) pol) (S.rows p).
  (** Maximum-rank checking is equivalent to the public dependency-edge criterion. *)
  Parameter F7_cut_spec : forall p pol, cuts p pol = true <-> forall u v,
    dependency_edge p u v -> (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  (** Checked WTO forward ranks discharge every non-head dependency. *)
  Parameter F8_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  (** Program vertices and edge occurrences fit the declared occurrence budgets. *)
  Parameter F9_graph_sizes : forall p,
    graph_n (dep_graph p) <= occurrence_count p /\
    graph_e (dep_graph p) = edge_count p.
  (** All dependency graph identifiers fit the program's key budget. *)
  Parameter F10_width : forall p, S.wf p -> graph_width (dep_graph p) <= S.kw p.
  (** Unique bounded-width identifiers bound the width of their assigned positive ranks. *)
  Parameter F11_rank_width : forall p cfg wp n pol, S.wf p ->
    plan p cfg wp n = Some pol -> prio_width p pol <= S.kw p + 1.
  (** Accepted WTO conversion scans distinct program vertices with bounded identifiers. *)
  Parameter F12_checked_size : forall p w,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    length (wto_order w) <= graph_n (dep_graph p) /\
    vertex_width (wto_order w) <= graph_width (dep_graph p).
  (** Graph construction charges readers, encoded occurrences and emitted edges. *)
  Parameter T1_graph : forall p, S.wf p ->
    (T_dep_graph p <= k_graph *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) * N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  (** WTO conversion charges the public projections and configured-head insertion. *)
  Parameter T2_policy : forall w cfg wp n,
    (T_of_wto w cfg wp n <= k_heads *
      (W.T_ranks w + W.T_heads w + T_schedule_head_map cfg (W.heads w) + 1))%N.
  (** Maximum-rank cut checking retains the linear public occurrence bound. *)
  Parameter T3_cuts : forall p pol, S.wf p ->
    (T_cuts p pol <= k_cuts *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  (** Planning pays each graph, WTO and conversion phase explicitly. *)
  Parameter T4_plan_phases : forall p cfg wp n,
    let graph := dep_graph p in
    let prepared := G.prepare graph in
    let roots := verts graph in
    let order := W.build prepared roots in
    (T_plan p cfg wp n <= k_plan * (T_dep_graph p + G.T_prepare graph +
      W.T_build prepared roots + W.T_check prepared roots order +
      (if W.check prepared roots order then T_of_wto order cfg wp n else 0) + 1))%N.
  (** The phase bounds discharge the unchanged public schedule contract. *)
  Parameter T5_plan_public : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
       N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
       N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
End SCHEDULE_PLAN.

Module Type SCHEDULE_ALL (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) := SCHEDULE_T L S G W <+ SCHEDULE_PLAN L S G W.
