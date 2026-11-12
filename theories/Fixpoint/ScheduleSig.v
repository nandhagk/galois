(** * Checked widening schedules

    Schedules rank dependency vertices and place widening heads on backward dependencies.
    For example, a self-dependency requires its target to be a head.
    Builds on: Fixpoint.PolicySig, Fixpoint.SystemSig and Graph.WtoSig. *)

From Stdlib Require Import List PArith Arith.
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
      exists r x, In r (S.rows p) /\ In x (S.writes p r ++ S.deps p r) /\
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
  Parameter T_dep_graph : S.prog -> nat.
  Parameter T_of_wto : wto -> head_cfg -> L.wparam -> nat -> nat.
  Parameter T_plan : S.prog -> head_cfg -> L.wparam -> nat -> nat.
  Parameter T_cuts : S.prog -> policy L.wparam -> nat.
  Parameter c_sched : nat.
  (** Dependency graph construction charges every declared occurrence. *)
  Parameter T_dep_graph_le : forall p, S.wf p ->
    T_dep_graph p <= c_sched * (row_count p + occurrence_count p + 1) * (S.kw p + 1).
  (** WTO conversion charges traversal, ranks and encoded vertices. *)
  Parameter T_of_wto_le : forall w cfg wp n,
    T_of_wto w cfg wp n <= c_sched * (length (wto_order w) + 1) *
      (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1).
  (** Planning pays for graph preparation and the nesting depth of the built WTO. *)
  Parameter T_plan_le : forall p cfg wp n, S.wf p ->
    T_plan p cfg wp n <= c_sched * (row_count p + occurrence_count p + 1) *
      (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
      (S.kw p + 1).
  (** Cut checking is linear in declared occurrences and program key width. *)
  Parameter T_cuts_le : forall p pol, S.wf p ->
    T_cuts p pol <= c_sched * (row_count p + occurrence_count p + 1) * (S.kw p + 1).
End SCHEDULE_TIME.

Module Type SCHEDULE_T (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) := SCHEDULE L S G W <+ SCHEDULE_TIME L S G W.
