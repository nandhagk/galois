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
  Proof. Admitted.
  (** The graph lists exactly the key codes read or written by a row. *)
  Lemma dep_graph_vertices : forall p c,
    In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\ In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\
        S.key_code x = c.
  Proof. Admitted.
  (** WTO priorities use the WTO's public rank projection. *)
  Lemma of_wto_prio : forall w cfg wp n, prio (of_wto w cfg wp n) = W.ranks w.
  Proof. Admitted.
  (** WTO loop heads receive the supplied head configuration. *)
  Lemma of_wto_heads : forall w cfg wp n c,
    trie_get c (heads (of_wto w cfg wp n)) =
      if existsb (Pos.eqb c) (W.heads w) then Some cfg else None.
  Proof. Admitted.
  (** Schedule construction retains widening parameters. *)
  Lemma of_wto_wp : forall w cfg wp n, PolicySig.wp (of_wto w cfg wp n) = wp.
  Proof. Admitted.
  (** Schedule construction retains the requested narrowing pass count. *)
  Lemma of_wto_passes : forall w cfg wp n, passes (of_wto w cfg wp n) = n.
  Proof. Admitted.
  (** Planning accepts a built WTO only when its checker accepts it. *)
  Lemma plan_spec : forall p cfg wp n,
    let g := G.prepare (dep_graph p) in
    let roots := verts (dep_graph p) in
    let w := W.build g roots in
    plan p cfg wp n = if W.check g roots w then Some (of_wto w cfg wp n) else None.
  Proof. Admitted.
  (** Every non-increasing dependency edge enters a configured head. *)
  Lemma cuts_spec : forall p pol,
    cuts p pol = true <-> forall u v, dependency_edge p u v ->
      (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  Proof. Admitted.
  (** A checked WTO cuts every non-increasing dependency edge. *)
  Lemma of_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  Proof. Admitted.
  (** Every accepted schedule cuts the program's dependency edges. *)
  Lemma plan_cuts : forall p cfg wp n pol,
    plan p cfg wp n = Some pol -> cuts p pol = true.
  Proof. Admitted.
End Schedule.
