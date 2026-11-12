(** * Checked widening schedules

    This file constructs schedules from dependency graphs and checked WTOs.
    For example, a self-dependency requires its target to be a widening head.
    Builds on: Fixpoint.ScheduleSig, Fixpoint.PolicySig and Graph.WtoSig. *)

From Stdlib Require Import List PArith Arith NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import Data Spec DigraphSig WtoSig.
From Galois.Fixpoint Require Import SystemSig PolicySig ScheduleSig.

Module ScheduleCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (G : DIGRAPH_OPS) (W : WTO_OPS) <: SCHEDULE_OPS L S.
  Definition dep_graph (p : S.prog) : digraph :=
    schedule_graph S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p).

  Definition of_wto (w : wto) (cfg : head_cfg) (wp : L.wparam) (n : nat)
      : policy L.wparam :=
    @Policy L.wparam (W.ranks w) (schedule_head_map cfg (W.heads w)) wp n.

  Definition plan (p : S.prog) (cfg : head_cfg) (wp : L.wparam) (n : nat)
      : option (policy L.wparam) :=
    let graph := dep_graph p in
    let prepared := G.prepare graph in
    let roots := verts graph in
    let order := W.build prepared roots in
    if W.check prepared roots order then Some (of_wto order cfg wp n) else None.

  Definition cuts (p : S.prog) (pol : policy L.wparam) : bool :=
    forallb (schedule_cut_row S.key_code (S.target p) (S.deps p) (S.sides p) pol)
      (S.rows p).
End ScheduleCode.

Module Schedule (L : WLATTICE) (S : SYSTEM L) (G : DIGRAPH) (W : WTO)
    <: SCHEDULE L S G W.
  Include ScheduleCode L S G W.
  Include SCHEDULE_SPEC L S.
  (** The dependency graph has exactly the declared dependency edges. *)
  Lemma dep_graph_edges : forall p u v,
    edge (dep_graph p) u v <-> dependency_edge p u v.
  Proof. Admitted. (* STUB *)
  (** The graph lists exactly the key codes read or written by a row. *)
  Lemma dep_graph_vertices : forall p c,
    In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\ In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\
        S.key_code x = c.
  Proof. Admitted. (* STUB *)
  (** WTO priorities use the WTO's public rank projection. *)
  Lemma of_wto_prio : forall w cfg wp n, prio (of_wto w cfg wp n) = W.ranks w.
  Proof. Admitted. (* STUB *)
  (** WTO loop heads receive the supplied head configuration. *)
  Lemma of_wto_heads : forall w cfg wp n c,
    trie_get c (heads (of_wto w cfg wp n)) =
      if existsb (Pos.eqb c) (W.heads w) then Some cfg else None.
  Proof. Admitted. (* STUB *)
  (** Schedule construction retains widening parameters. *)
  Lemma of_wto_wp : forall w cfg wp n, PolicySig.wp (of_wto w cfg wp n) = wp.
  Proof. Admitted. (* STUB *)
  (** Schedule construction retains the requested narrowing pass count. *)
  Lemma of_wto_passes : forall w cfg wp n, passes (of_wto w cfg wp n) = n.
  Proof. Admitted. (* STUB *)
  (** Planning accepts a built WTO only when its checker accepts it. *)
  Lemma plan_spec : forall p cfg wp n,
    let g := G.prepare (dep_graph p) in
    let roots := verts (dep_graph p) in
    let w := W.build g roots in
    plan p cfg wp n = if W.check g roots w then Some (of_wto w cfg wp n) else None.
  Proof. Admitted. (* STUB *)
  (** Every non-increasing dependency edge enters a configured head. *)
  Lemma cuts_spec : forall p pol,
    cuts p pol = true <-> forall u v, dependency_edge p u v ->
      (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  Proof. Admitted. (* STUB *)
  (** A checked WTO cuts every non-increasing dependency edge. *)
  Lemma of_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  Proof. Admitted. (* STUB *)
  (** Every accepted schedule cuts the program's dependency edges. *)
  Lemma plan_cuts : forall p cfg wp n pol,
    plan p cfg wp n = Some pol -> cuts p pol = true.
  Proof. Admitted. (* STUB *)
End Schedule.

Module ScheduleT (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) <: SCHEDULE_ALL L S G W.
  Include Schedule L S G W.

  TimeFun dep_graph.
  TimeFun of_wto.
  TimeFun plan.
  TimeFun cuts.

  Definition c_sched : N := 1%N. (* STUB *)

  (** Dependency graph construction charges every declared occurrence. *)
  Lemma T_dep_graph_le : forall p, S.wf p ->
    (T_dep_graph p <= c_sched * (N.of_nat (row_count p + occurrence_count p +
      edge_count p + 1) * N.of_nat (S.kw p + 1) +
      N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** WTO conversion charges traversal, ranks and encoded vertices. *)
  Lemma T_of_wto_le : forall w cfg wp n,
    (T_of_wto w cfg wp n <= c_sched * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Planning pays for graph preparation and the nesting depth of the built WTO. *)
  Lemma T_plan_le : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
        N.of_nat (S.kw p + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Cut checking is linear in declared occurrences and program key width. *)
  Lemma T_cuts_le : forall p pol, S.wf p ->
    (T_cuts p pol <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Every planned priority fits the program key width. *)
  Lemma plan_prio_width : forall p cfg wp n pol, S.wf p ->
    plan p cfg wp n = Some pol -> prio_width p pol <= S.kw p + 1.
  Proof. Admitted. (* STUB *)

  Definition k_graph : N := 1%N. (* STUB *)
  Definition k_heads : N := 1%N. (* STUB *)
  Definition k_cuts : N := 1%N. (* STUB *)
  Definition k_plan : N := 1%N. (* STUB *)

  (** Construction uses the shared first-order graph builder. *)
  Lemma F1_graph : forall p, dep_graph p =
    schedule_graph S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p).
  Proof. Admitted. (* STUB *)

  (** The graph builder lists each read or write code exactly once. *)
  Lemma F2_vertices : forall p, NoDup (verts (dep_graph p)) /\
    forall c, In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\
        In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\ S.key_code x = c.
  Proof. Admitted. (* STUB *)

  (** Every emitted adjacency occurrence comes from a declared dependency product. *)
  Lemma F3_edges : forall p u v,
    edge (dep_graph p) u v <-> dependency_edge p u v.
  Proof. Admitted. (* STUB *)

  (** Preparation retains a well-formed graph whose vertices are all roots. *)
  Lemma F4_prepared : forall p,
    wf_graph (dep_graph p) /\ base (G.prepare (dep_graph p)) = dep_graph p /\
    forall u, In u (verts (dep_graph p)) ->
      reach (base (G.prepare (dep_graph p))) (verts (dep_graph p)) u.
  Proof. Admitted. (* STUB *)

  (** WTO conversion pairs its public ranks with its configured structural heads. *)
  Lemma F5_policy : forall w cfg wp n, of_wto w cfg wp n =
    @Policy L.wparam (W.ranks w) (schedule_head_map cfg (W.heads w)) wp n.
  Proof. Admitted. (* STUB *)

  (** Cut checking uses the maximum dependency rank for each row. *)
  Lemma F6_cut_code : forall p pol, cuts p pol =
    forallb (schedule_cut_row S.key_code (S.target p) (S.deps p) (S.sides p) pol)
      (S.rows p).
  Proof. Admitted. (* STUB *)

  (** Maximum-rank checking is equivalent to the public dependency-edge criterion. *)
  Lemma F7_cut_spec : forall p pol, cuts p pol = true <-> forall u v,
    dependency_edge p u v -> (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  Proof. Admitted. (* STUB *)

  (** Checked WTO forward ranks discharge every non-head dependency. *)
  Lemma F8_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  Proof. Admitted. (* STUB *)

  (** Program vertices and edge occurrences fit the declared occurrence budgets. *)
  Lemma F9_graph_sizes : forall p,
    graph_n (dep_graph p) <= occurrence_count p /\
    graph_e (dep_graph p) = edge_count p.
  Proof. Admitted. (* STUB *)

  (** All dependency graph identifiers fit the program key budget. *)
  Lemma F10_width : forall p, S.wf p -> graph_width (dep_graph p) <= S.kw p.
  Proof. Admitted. (* STUB *)

  (** Unique bounded-width identifiers bound the width of their assigned positive ranks. *)
  Lemma F11_rank_width : forall p cfg wp n pol, S.wf p ->
    plan p cfg wp n = Some pol -> prio_width p pol <= S.kw p + 1.
  Proof. Admitted. (* STUB *)

  (** Accepted WTO conversion scans distinct program vertices with bounded identifiers. *)
  Lemma F12_checked_size : forall p w,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    length (wto_order w) <= graph_n (dep_graph p) /\
    vertex_width (wto_order w) <= graph_width (dep_graph p).
  Proof. Admitted. (* STUB *)

  (** Graph construction charges readers, encoded occurrences and emitted edges. *)
  Lemma T1_graph : forall p, S.wf p ->
    (T_dep_graph p <= k_graph *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** WTO conversion charges the public projections and configured-head insertion. *)
  Lemma T2_policy : forall w cfg wp n,
    (T_of_wto w cfg wp n <= k_heads *
      (W.T_ranks w + W.T_heads w + T_schedule_head_map cfg (W.heads w) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Maximum-rank cut checking retains the linear public occurrence bound. *)
  Lemma T3_cuts : forall p pol, S.wf p ->
    (T_cuts p pol <= k_cuts *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Planning pays each graph, WTO and conversion phase explicitly. *)
  Lemma T4_plan_phases : forall p cfg wp n,
    let graph := dep_graph p in
    let prepared := G.prepare graph in
    let roots := verts graph in
    let order := W.build prepared roots in
    (T_plan p cfg wp n <= k_plan * (T_dep_graph p + G.T_prepare graph +
      W.T_build prepared roots + W.T_check prepared roots order +
      (if W.check prepared roots order then T_of_wto order cfg wp n else 0) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The phase bounds discharge the unchanged public schedule contract. *)
  Lemma T5_plan_public : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
       N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
       N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)
End ScheduleT.
