(** * The complete factored redundancy graph contract

    Every field retains its adopted legacy meaning for versions, occurrences, operands and unsafe seeds.
    For example, an incoming unavailable sentinel excludes every reusable source definition.
    Builds on: AnalysesSsaPreFrg, AnalysesSsaPreRename and AnalysesSsaPreFrameEdges. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Program Require Import ProgramCfg.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreFrameEdges.
Import List.ListNotations.

Module PreFrameWf.

Section Contract.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable g : PreFrg.frg B BE E U.

(** Well-formed graphs satisfy all thirteen adopted clauses of the legacy graph contract. *)
Record frg_wf : Prop := FrgWf {
  versions_nodup : NoDup (PreFrg.versions g);
  versions_exact : forall d, In d (PreFrg.versions g) <->
    match d with
    | PreFrg.Unavailable u => PreFamily.in_family c u /\ Pre.pure c u = true
    | PreFrg.Initial u => PreFamily.in_family c u /\ Pre.pure c u = true /\ Pre.initial c u = true
    | PreFrg.Fresh e u => In e (Cfg.edges (Pre.point_cfg c)) /\
        Pre.recomputed c e = Some u /\ FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh g) = true
    | PreFrg.Phi b u => FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis g) = true
    end;
  phi_exact : forall b u,
    FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis g) = true <->
    PreFamily.in_family c u /\ Pre.pure c u = true /\ PreFrg.phi_needed c u b;
  occurrence_exact : forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    exists d, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d /\
      In d (PreFrg.versions g) /\ PreFrg.version_expr d = u /\
      (d = PreFrg.Fresh e u \/ PreRename.reusable c g u (Graph.source (Pre.pg c) e) d);
  occurrence_domain : forall e d,
    Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d ->
    In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some (PreFrg.version_expr d) /\
    Pre.pure c (PreFrg.version_expr d) = true;
  fresh_exact : forall e u, Pre.recomputed c e = Some u ->
    (FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh g) = true <->
      Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some (PreFrg.Fresh e u));
  fresh_domain : forall e, FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh g) = true ->
    In e (Cfg.edges (Pre.point_cfg c));
  fresh_required : forall e u, In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.recomputed c e = Some u -> Pre.pure c u = true ->
    (FinSet.mem (Pre.ee (Pre.keys c)) e (PreFrg.fresh g) = true <->
      ~ exists d, PreRename.reusable c g u (Graph.source (Pre.pg c) e) d);
  operand_exact : forall b u be,
    FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis g) = true ->
    In be (Cfg.edges (Pre.block_cfg c)) -> Graph.target (Pre.bg c) be = b ->
    exists op v, Pre.translate c be u = Some v /\
      Map.get (PreFrg.link_encoding c) ((b, u), be) (PreFrg.operands g) = Some op /\
      PreFrg.version_expr (PreFrg.operand_version op) = v /\
      (PreFrg.operand_version op = PreFrg.Unavailable v \/
        exists n pe, PreFrg.version_point c (PreFrg.operand_version op) = Some n /\
          Map.get (Pre.ebe (Pre.keys c)) be (PreFrameEdges.point_edge_index c) = Some pe /\
          dominates (Pre.pg c) n (Graph.source (Pre.pg c) pe));
  operand_domain : forall b u be op,
    Map.get (PreFrg.link_encoding c) ((b, u), be) (PreFrg.operands g) = Some op ->
    FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.phis g) = true /\
    In be (Cfg.edges (Pre.block_cfg c)) /\ Graph.target (Pre.bg c) be = b;
  operand_selection : forall b u be op pe v,
    Map.get (PreFrg.link_encoding c) ((b, u), be) (PreFrg.operands g) = Some op ->
    Map.get (Pre.ebe (Pre.keys c)) be (PreFrameEdges.point_edge_index c) = Some pe ->
    Pre.translate c be u = Some v ->
    (PreFrg.operand_version op = PreFrg.Unavailable v <->
      ~ exists d, PreRename.reusable c g v (Graph.source (Pre.pg c) pe) d) /\
    (PreFrg.operand_version op <> PreFrg.Unavailable v ->
      PreRename.reusable c g v (Graph.source (Pre.pg c) pe) (PreFrg.operand_version op));
  operand_real_use_exact : forall b u be op pe,
    Map.get (PreFrg.link_encoding c) ((b, u), be) (PreFrg.operands g) = Some op ->
    Map.get (Pre.ebe (Pre.keys c)) be (PreFrameEdges.point_edge_index c) = Some pe ->
    (PreFrg.real_use op = true <-> exists e,
      Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some (PreFrg.operand_version op) /\
      dominates (Pre.pg c) (Graph.target (Pre.pg c) e) (Graph.source (Pre.pg c) pe));
  down_seed_exact : forall b u,
    (FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreFrg.unsafe g) = true <->
      exists n, In n (Graph.nodes (Pre.pg c)) /\
        PreRename.nearest_version c g u n (PreFrg.Phi b u) /\
        PreRename.no_dominating_real_use c g n (PreFrg.Phi b u) /\
        (Pre.exit_point c n = true \/ Graph.out (Pre.pg c) n = [] \/
          exists e, In e (Graph.out (Pre.pg c) n) /\
            Pre.killed c e u = true /\ Pre.recomputed c e <> Some u))
}.

End Contract.

End PreFrameWf.
