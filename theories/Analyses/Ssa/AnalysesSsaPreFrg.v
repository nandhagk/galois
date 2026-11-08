(** * Factored expression definitions

    Version origins distinguish missing entry values, initial values, computations and phis.
    For example, a phi definition is after parameter binding rather than at block entry.
    Builds on: AnalysesSsaPreFamily, ProgramSsaPoints and GraphFrontierSpec. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFrontierSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily.
Import List.ListNotations Cost.Notations.

Module PreFrg.

(** Constructor origins keep unavailable sentinels distinct from valid entry values. *)
Inductive version (B E U : Type) :=
  | Unavailable (u : U)
  | Initial (u : U)
  | Fresh (e : E) (u : U)
  | Phi (b : B) (u : U).
Arguments Unavailable {B E U}.
Arguments Initial {B E U}.
Arguments Fresh {B E U}.
Arguments Phi {B E U}.

(** Each incoming link retains the real-use bit of its selected version. *)
Record operand (B E U : Type) := Operand {
  operand_version : version B E U;
  real_use : bool
}.
Arguments Operand {B E U}.
Arguments operand_version {B E U}.
Arguments real_use {B E U}.

(** The indexes distinguish incoming edge identities even when their endpoints coincide. *)
Record frg (B BE E U : Type) := Frg {
  versions : list (version B E U);
  occurrences : Map.t E (version B E U);
  fresh : FinSet.t E;
  phis : FinSet.t (B * U);
  operands : Map.t ((B * U) * BE) (operand B E U);
  unsafe : FinSet.t (B * U)
}.
Arguments Frg {B BE E U}.
Arguments versions {B BE E U}.
Arguments occurrences {B BE E U}.
Arguments fresh {B BE E U}.
Arguments phis {B BE E U}.
Arguments operands {B BE E U}.
Arguments unsafe {B BE E U}.

Definition version_expr {B E U} (d : version B E U) :=
  match d with
  | Unavailable u => u
  | Initial u => u
  | Fresh _ u => u
  | Phi _ u => u
  end.

Section Definitions.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** Definition seeds include entry, pure occurrence blocks and every ordered operand home. *)
Inductive definition_block (u : U) : B -> Prop :=
  | definition_entry : forall b, In b (Graph.entries (Pre.bg c)) -> definition_block u b
  | definition_occurrence : forall e,
      In e (Cfg.edges (Pre.point_cfg c)) ->
      Pre.recomputed c e = Some u -> Pre.pure c u = true ->
      definition_block u
        (SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e))
  | definition_operand : forall x, In x (Pre.operands c u) ->
      definition_block u (Ssa.home (Pre.ssa (Pre.input c)) x).

(** Phi placement is the least frontier closure including translated predecessor expressions. *)
Inductive phi_needed : U -> B -> Prop :=
  | phi_parameter : forall u b x, PreFamily.in_family c u ->
      In b (Graph.nodes (Pre.bg c)) -> ~ In b (Graph.entries (Pre.bg c)) ->
      In x (Pre.operands c u) ->
      In x (SsaPoints.block_params (Pre.points (Pre.input c)) b) -> phi_needed u b
  | phi_seed : forall u d b, PreFamily.in_family c u -> definition_block u d ->
      in_df (Pre.bg c) d b -> phi_needed u b
  | phi_iterate : forall u d b, phi_needed u d -> in_df (Pre.bg c) d b -> phi_needed u b
  | phi_translate : forall u b be v target, phi_needed u b ->
      In be (Cfg.edges (Pre.block_cfg c)) -> Graph.target (Pre.bg c) be = b ->
      Pre.translate c be u = Some v ->
      in_df (Pre.bg c) (Graph.source (Pre.bg c) be) target -> phi_needed v target.

(** Every recursively translated phi retains membership in the same least expression family. *)
Theorem phi_needed_family {u b} :
  phi_needed u b -> PreFamily.in_family c u.
Proof.
  intro Hneeded; induction Hneeded as
    [u b x Hu Hb Hentry Hoperand Hparam|
     u d b Hu Hdef Hfrontier|
     u d b Hneeded IH Hfrontier|
     u b be v target Hneeded IH Hbe Htarget Htranslate Hfrontier].
  - exact Hu.
  - exact Hu.
  - exact IH.
  - eapply Pre.family_translate; eassumption.
Qed.

Local Lemma frontier_target_listed {d b} :
  Pre.laws c -> in_df (Pre.bg c) d b -> In b (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw [e [Hsource [Hedge [Htarget _]]]].
  rewrite <- Htarget; apply (reachable_in_nodes _ _ (blocks_graph_wf
    (Pre.point_laws c (Pre.graphs c Hlaw)))).
  eapply reachable_step; eassumption.
Qed.

(** Every phi site is a listed source block, including sites reached through translation. *)
Theorem phi_needed_nodes {u b} :
  Pre.laws c -> phi_needed u b -> In b (Graph.nodes (Pre.bg c)).
Proof.
  intros Hlaw Hneeded; destruct Hneeded.
  - assumption.
  - eapply frontier_target_listed; eassumption.
  - eapply frontier_target_listed; eassumption.
  - eapply frontier_target_listed; eassumption.
Qed.

Definition version_point_c (d : version B E U) :=
  match d with
  | Unavailable _ => Cost.ret None
  | Initial _ => Cost.ret (nth_error (Graph.entries (Pre.pg c)) 0)
  | Fresh e _ =>
    Cost.step ;;
    Cost.map (@Some N) (Graph.target_c (Pre.pg c) e)
  | Phi b _ =>
    Cost.step ;;
    let* e := SsaPoints.parameter_edge_c (Pre.points (Pre.input c)) b in
    Cost.step ;;
    Cost.map (@Some N) (Graph.target_c (Pre.pg c) e)
  end.
Definition version_point d := Cost.value (version_point_c d).

(** Definitions become available after their actual instruction or parameter-edge occurrence. *)
Theorem version_point_equation d :
  version_point d =
    match d with
    | Unavailable _ => None
    | Initial _ => nth_error (Graph.entries (Pre.pg c)) 0
    | Fresh e _ => Some (Graph.target (Pre.pg c) e)
    | Phi b _ => Some (Graph.target (Pre.pg c)
        (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
    end.
Proof.
  destruct d; unfold version_point, version_point_c; autorewrite with galois_cost;
    reflexivity.
Qed.

(** Eligible definitions use the static source domains independently of a graph producer. *)
Definition definition_domain (d : version B E U) : Prop :=
  match d with
  | Unavailable u => PreFamily.in_family c u
  | Initial u => PreFamily.in_family c u /\ Pre.initial c u = true
  | Fresh e u => In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some u
  | Phi b u => phi_needed u b
  end.

End Definitions.

Local Lemma tail_member {X} (x : X) xs : In x (tl xs) -> In x xs.
Proof.
  destruct xs; cbn; tauto.
Qed.

(** Ordered instruction chains place every edge target strictly after the first point. *)
Lemma chain_target {N E} (g : Graph.t N E) {ns es e} :
  point_chain g ns es -> In e es -> In (Graph.target g e) (tl ns).
Proof.
  intros Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH].
  - intros [].
  - intros [<-|Hin]; [cbn; left; symmetry; exact Htarget|].
    cbn; right; exact (IH Hin).
Qed.

Local Lemma chain_target_unique {N E} (g : Graph.t N E) {ns es} :
  point_chain g ns es -> NoDup ns ->
  forall e e', In e es -> In e' es -> Graph.target g e = Graph.target g e' -> e = e'.
Proof.
  intro Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH];
    intros Hnodup e e' He He' Heq; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfirst Htail].
  apply NoDup_cons_iff in Htail; destruct Htail as [Hnext Hrest].
  destruct He as [<-|He], He' as [<-|He'].
  - reflexivity.
  - exfalso; apply Hnext; rewrite <- Htarget, Heq; exact (chain_target g Hchain He').
  - exfalso; apply Hnext; rewrite <- Htarget, <- Heq; exact (chain_target g Hchain He).
  - apply IH; [constructor; assumption|exact He|exact He'|exact Heq].
Qed.

Local Lemma chain_source {N E} (g : Graph.t N E) {ns es e} :
  point_chain g ns es -> In e es -> exists n, In n ns /\ In e (Graph.out g n).
Proof.
  intro Hchain; induction Hchain as [n|n next ns edge es Hedge Htarget Hchain IH].
  - intros [].
  - intros [<-|Hin].
    + exists n; split; [now left|exact Hedge].
    + destruct (IH Hin) as [q [Hq He]]; exists q; split; [now right|exact He].
Qed.

Section PointDomains.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Let s := Pre.points (Pre.input c).

(** Every listed point belongs to the ordered point list of its actual owner block. *)
Lemma point_owner_listed {n} :
  Pre.laws c -> In n (Graph.nodes (Pre.pg c)) ->
  In (SsaPoints.block_of_point s n) (Graph.nodes (Pre.bg c)) /\
    In n (SsaPoints.points_in_block s (SsaPoints.block_of_point s n)).
Proof.
  intros Hlaw Hn; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  apply (points_covered Hpoints) in Hn; destruct Hn as [b [Hb Hpoint]].
  rewrite (points_owner Hpoints b n Hb Hpoint); auto.
Qed.

Local Lemma internal_edge_block {e} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None ->
  exists b, In b (Graph.nodes (Pre.bg c)) /\
    In e (SsaPoints.instruction_edges s b) /\
    In (Graph.target (Pre.pg c) e) (tl (SsaPoints.points_in_block s b)).
Proof.
  intros Hlaw He Hinternal; apply Cfg.edges_spec in He; destruct He as [n [Hn He]].
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  destruct (point_owner_listed Hlaw Hn) as [Hb Hpoint].
  pose proof (instruction_edges_complete Hpoints n e Hn He Hinternal) as Hin.
  exists (SsaPoints.block_of_point s n); split; [exact Hb|]; split; [exact Hin|].
  exact (chain_target _ (points_ordered Hpoints _ Hb) Hin).
Qed.

(** Distinct internal instruction occurrences have distinct target points. *)
Lemma internal_target_unique {e e'} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  In e' (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None -> SsaPoints.block_edge_of s e' = None ->
  Graph.target (Pre.pg c) e = Graph.target (Pre.pg c) e' -> e = e'.
Proof.
  intros Hlaw He He' Hi Hi' Heq.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  destruct (internal_edge_block Hlaw He Hi) as [b [Hb [Hedge Htarget]]].
  destruct (internal_edge_block Hlaw He' Hi') as [b' [Hb' [Hedge' Htarget']]].
  assert (Hsame : b = b').
  { rewrite <- (points_owner Hpoints b _ Hb (tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hpoints b' _ Hb' (tail_member _ _ Htarget')). }
  subst b'; eapply chain_target_unique.
  - exact (points_ordered Hpoints b Hb).
  - exact (points_unique Hpoints b).
  - exact Hedge.
  - exact Hedge'.
  - exact Heq.
Qed.

(** A listed block's parameter edge is an internal occurrence in the point graph. *)
Lemma parameter_edge_listed {b} :
  Pre.laws c -> In b (Graph.nodes (Pre.bg c)) ->
  In (SsaPoints.parameter_edge s b) (Cfg.edges (Pre.point_cfg c)) /\
    SsaPoints.block_edge_of s (SsaPoints.parameter_edge s b) = None.
Proof.
  intros Hlaw Hb; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  pose proof (nth_error_In _ _ (parameter_edge_first Hpoints b Hb)) as He.
  split; [|exact (instruction_edges_internal Hpoints b _ Hb He)].
  destruct (chain_source _ (points_ordered Hpoints b Hb) He) as [n [Hn Hedge]].
  apply Cfg.edges_spec; exists n; split; [|exact Hedge].
  apply (points_covered Hpoints); exists b; auto.
Qed.

(** Internal definition targets cannot be the unique entry's first instruction point. *)
Lemma internal_target_not_entry {e n} :
  Pre.laws c -> In e (Cfg.edges (Pre.point_cfg c)) ->
  SsaPoints.block_edge_of s e = None -> In n (Graph.entries (Pre.pg c)) ->
  Graph.target (Pre.pg c) e <> n.
Proof.
  intros Hlaw He Hi Hentry Heq.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  destruct (Pre.entry_position c (Pre.graphs c Hlaw))
    as [entry [first [Hb [Hn Hfirst]]]].
  fold s in Hfirst.
  rewrite Hn in Hentry; destruct Hentry as [<-|[]].
  assert (Hentryblock : In entry (Graph.nodes (Pre.bg c))).
  { apply (entries_in (blocks_graph_wf Hpoints)).
    change (In entry (Graph.entries (Pre.bg c))); rewrite Hb; now left. }
  destruct (internal_edge_block Hlaw He Hi) as [b [Hblock [Hedge Htarget]]].
  pose proof (nth_error_In _ _ Hfirst) as Hfirstpoint.
  assert (Howner : b = entry).
  { rewrite <- (points_owner Hpoints b _ Hblock (tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hpoints entry first Hentryblock Hfirstpoint). }
  subst b; rewrite Heq in Htarget.
  pose proof (points_unique Hpoints entry) as Hunique.
  destruct (SsaPoints.points_in_block s entry) as [|head rest];
    cbn in Hfirst; [discriminate|].
  inversion Hfirst; subst head; inversion Hunique; subst; contradiction.
Qed.

Local Lemma initial_fresh_disjoint {e u q} :
  Pre.laws c -> definition_domain c (Fresh e u) ->
  version_point c (Initial u) = Some q -> version_point c (Fresh e u) <> Some q.
Proof.
  intros Hlaw [He Hcomputed] Hentry Hpoint.
  rewrite version_point_equation in Hentry, Hpoint.
  inversion Hpoint; subst q.
  eapply internal_target_not_entry; [exact Hlaw|exact He| | |reflexivity].
  - exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)).
  - exact (nth_error_In _ _ Hentry).
Qed.

Local Lemma initial_phi_disjoint {b u q} :
  Pre.laws c -> definition_domain c (Phi b u) ->
  version_point c (Initial u) = Some q -> version_point c (Phi b u) <> Some q.
Proof.
  intros Hlaw Hphi Hentry Hpoint.
  destruct (parameter_edge_listed Hlaw (phi_needed_nodes c Hlaw Hphi)) as [He Hi].
  rewrite version_point_equation in Hentry, Hpoint.
  inversion Hpoint; subst q.
  eapply internal_target_not_entry; [exact Hlaw|exact He|exact Hi| |reflexivity].
  exact (nth_error_In _ _ Hentry).
Qed.

Local Lemma fresh_phi_disjoint {e b u q} :
  Pre.laws c -> definition_domain c (Fresh e u) -> definition_domain c (Phi b u) ->
  version_point c (Fresh e u) = Some q -> version_point c (Phi b u) <> Some q.
Proof.
  intros Hlaw [He Hcomputed] Hphi Hfresh Hpoint.
  destruct (parameter_edge_listed Hlaw (phi_needed_nodes c Hlaw Hphi)) as [Hparam Hinternal].
  rewrite version_point_equation in Hfresh, Hpoint.
  fold s in Hpoint.
  assert (Hsame : e = SsaPoints.parameter_edge s b).
  { eapply internal_target_unique; [exact Hlaw|exact He|exact Hparam| |exact Hinternal|].
    - exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)).
    - congruence. }
  exact (proj2 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed) b Hsame).
Qed.

Local Lemma phi_points_unique {b b' u q} :
  Pre.laws c -> definition_domain c (Phi b u) -> definition_domain c (Phi b' u) ->
  version_point c (Phi b u) = Some q -> version_point c (Phi b' u) = Some q -> b = b'.
Proof.
  intros Hlaw Hb Hb' Hpoint Hpoint'.
  pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hpoints.
  fold s in Hpoints.
  pose proof (phi_needed_nodes c Hlaw Hb) as Hbn.
  pose proof (phi_needed_nodes c Hlaw Hb') as Hb'n.
  pose proof (chain_target _ (points_ordered Hpoints b Hbn)
    (nth_error_In _ _ (parameter_edge_first Hpoints b Hbn))) as Htarget.
  pose proof (chain_target _ (points_ordered Hpoints b' Hb'n)
    (nth_error_In _ _ (parameter_edge_first Hpoints b' Hb'n))) as Htarget'.
  rewrite version_point_equation in Hpoint, Hpoint'.
  fold s in Hpoint, Hpoint'.
  rewrite <- (points_owner Hpoints b _ Hbn (tail_member _ _ Htarget)).
  assert (Heq : Graph.target (live_graph (SsaPoints.point_model s))
    (SsaPoints.parameter_edge s b) =
    Graph.target (live_graph (SsaPoints.point_model s)) (SsaPoints.parameter_edge s b')).
  { change (Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b) =
      Graph.target (Pre.pg c) (SsaPoints.parameter_edge s b')); congruence. }
  rewrite Heq.
  exact (points_owner Hpoints b' _ Hb'n (tail_member _ _ Htarget')).
Qed.

(** Matching eligible definitions at the same instruction point have the same origin identity. *)
Theorem definition_points_unique :
  Pre.laws c ->
  forall d d' q, definition_domain c d -> definition_domain c d' ->
    version_expr d = version_expr d' ->
    version_point c d = Some q -> version_point c d' = Some q -> d = d'.
Proof.
  intros Hlaw d d' q Hd Hd' Hexpr Hpoint Hpoint'.
  destruct d as [u|u|e u|b u], d' as [v|v|e' v|b' v];
    cbn [version_expr] in Hexpr; subst v;
    try (rewrite version_point_equation in Hpoint; discriminate);
    try (rewrite version_point_equation in Hpoint'; discriminate); try reflexivity.
  - exfalso; exact (initial_fresh_disjoint Hlaw Hd' Hpoint Hpoint').
  - exfalso; exact (initial_phi_disjoint Hlaw Hd' Hpoint Hpoint').
  - exfalso; exact (initial_fresh_disjoint Hlaw Hd Hpoint' Hpoint).
  - f_equal; destruct Hd as [He Hcomputed], Hd' as [He' Hcomputed'].
    eapply internal_target_unique; [exact Hlaw|exact He|exact He'| | |].
    + exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e u Hcomputed)).
    + exact (proj1 (Pre.real_internal c (Pre.kills c Hlaw) e' u Hcomputed')).
    + rewrite version_point_equation in Hpoint, Hpoint'; congruence.
  - exfalso; exact (fresh_phi_disjoint Hlaw Hd Hd' Hpoint Hpoint').
  - exfalso; exact (initial_phi_disjoint Hlaw Hd Hpoint' Hpoint).
  - exfalso; exact (fresh_phi_disjoint Hlaw Hd' Hd Hpoint' Hpoint).
  - f_equal; eapply phi_points_unique; eassumption.
Qed.

End PointDomains.

End PreFrg.
