(** * Alteration coverage and the meaning of scoped frames

    Frame laws retain the nearest definition even after availability has been invalidated.
    For example, an unused phi can become an unsafe seed while its definition remains nearest.
    Builds on: AnalysesSsaPreRename and GraphFrontierSpec. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseMap.
From Galois.Graph Require Import GraphModel GraphDomSpec GraphFrontierSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename.

Module PreCoverage.

Section Coverage.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** The frontier of an operand's home is a required expression phi boundary. *)
Theorem operand_frontier_phi :
  forall u x b, PreFamily.in_family c u -> In x (Pre.operands c u) ->
    in_df (Pre.bg c) (Ssa.home (Pre.ssa (Pre.input c)) x) b ->
    PreFrg.phi_needed c u b.
Proof.
  intros u x b Hfamily Hoperand Hfrontier.
  eapply PreFrg.phi_seed; [exact Hfamily| |exact Hfrontier].
  apply PreFrg.definition_operand; exact Hoperand.
Qed.

(** Every killing definition's block frontier is covered by an expression phi. *)
Theorem kill_frontier_phi :
  Pre.laws c ->
  forall u e b, PreFamily.in_family c u -> In e (Cfg.edges (Pre.point_cfg c)) ->
    Pre.killed c e u = true ->
    in_df (Pre.bg c)
      (SsaPoints.block_of_point (Pre.points (Pre.input c)) (Graph.source (Pre.pg c) e)) b ->
    PreFrg.phi_needed c u b.
Proof.
  intros Hlaw u e b Hfamily He Hkill Hfrontier.
  destruct (Pre.kill_operand c (Pre.kills c Hlaw) e u He Hfamily Hkill)
    as [x [Hx Hdef]].
  pose proof (Pre.def_home c (Pre.kills c Hlaw) e x He Hdef) as Hhome.
  eapply operand_frontier_phi; [exact Hfamily|exact Hx|].
  rewrite Hhome; exact Hfrontier.
Qed.

(** A real-use witness names its selected occurrence and the dominance of its target. *)
Definition real_use_at (g : PreFrg.frg B BE E U) n d : Prop :=
  exists e, Map.get (Pre.ee (Pre.keys c)) e (PreFrg.occurrences g) = Some d /\
    dominates (Pre.pg c) (Graph.target (Pre.pg c) e) n.

(** No graph definition of the expression dominates the point. *)
Definition no_reaching_version (g : PreFrg.frg B BE E U) u n : Prop :=
  forall d q, In d (PreFrg.versions g) -> PreFrg.version_expr d = u ->
    PreFrg.version_point c d = Some q -> ~ dominates (Pre.pg c) q n.

(** Alterations below a definition and dominating a use are precisely its local killing events. *)
Definition no_dominating_kill u q n : Prop :=
  forall e, In e (Cfg.edges (Pre.point_cfg c)) ->
    strictly_dominates (Pre.pg c) q (Graph.target (Pre.pg c) e) ->
    dominates (Pre.pg c) (Graph.target (Pre.pg c) e) n -> Pre.killed c e u = false.

(** Frame availability and real-use bits describe the same selected definition at this point. *)
Definition frame_laws (g : PreFrg.frg B BE E U) u n (frame : PreRename.frame B E U) : Prop :=
  let d := PreFrg.operand_version (PreRename.selected frame) in
  PreFrg.version_expr d = u /\
  (PreFrg.real_use (PreRename.selected frame) = true <-> real_use_at g n d) /\
  match PreFrg.version_point c d with
  | Some q => PreRename.nearest_version c g u n d /\
      (PreRename.available frame = true <-> no_dominating_kill u q n)
  | None => d = PreFrg.Unavailable u /\ PreRename.available frame = false /\
      no_reaching_version g u n
  end.

(** Each eligible expression has a frame meaning at the same point of the scope. *)
Definition scope_laws (g : PreFrg.frg B BE E U) n (frames : PreRename.scope B E U) : Prop :=
  forall u, PreFamily.in_family c u -> Pre.pure c u = true ->
    frame_laws g u n (PreRename.top c frames u).

(** Provenance records expression identity, dominance and a definition for every available frame. *)
Definition frame_sound u n (frame : PreRename.frame B E U) : Prop :=
  let d := PreFrg.operand_version (PreRename.selected frame) in
  PreFrg.version_expr d = u /\
  (forall q, PreFrg.version_point c d = Some q -> dominates (Pre.pg c) q n) /\
  (PreRename.available frame = true -> exists q, PreFrg.version_point c d = Some q).

Definition scope_sound n (frames : PreRename.scope B E U) : Prop :=
  forall u, frame_sound u n (PreRename.top c frames u).

(** Full frame meaning supplies expression and definition provenance without any output premise. *)
Theorem frame_laws_sound (g : PreFrg.frg B BE E U) :
  forall u n frame, frame_laws g u n frame -> frame_sound u n frame.
Proof.
  intros u n frame [Hexpr [Hreal Hmeaning]].
  unfold frame_sound; split; [exact Hexpr|].
  destruct (PreFrg.version_point c (PreFrg.operand_version (PreRename.selected frame)))
    as [q|] eqn:Hpoint.
  - destruct Hmeaning as [Hnearest Havailable].
    destruct Hnearest as [_ [_ [p [Hp [Hdom Hminimal]]]]].
    assert (p = q) by congruence; subst p.
    split.
    + intros other Hother; inversion Hother; subst other; exact Hdom.
    + intros _; exists q; reflexivity.
  - destruct Hmeaning as [_ [Hfalse Hnone]]; split.
    + intros q Hq; discriminate.
    + intro Htrue; congruence.
Qed.

(** Definition provenance remains valid at every dominated point. *)
Theorem frame_sound_monotone :
  forall u n target frame, dominates (Pre.pg c) n target ->
    frame_sound u n frame -> frame_sound u target frame.
Proof.
  intros u n target frame Hdom [Hexpr [Hpoint Havailable]].
  split; [exact Hexpr|]; split; [|exact Havailable].
  intros q Hq; eapply dominates_trans; [apply Hpoint; exact Hq|exact Hdom].
Qed.

(** An unavailable frame excludes every dominating graph definition of its expression. *)
Theorem unavailable_frame_excludes (g : PreFrg.frg B BE E U) :
  forall u n frame, frame_laws g u n frame ->
    PreFrg.operand_version (PreRename.selected frame) = PreFrg.Unavailable u ->
    no_reaching_version g u n.
Proof.
  intros u n frame [_ [_ Hmeaning]] Hmissing.
  rewrite Hmissing, PreFrg.version_point_equation in Hmeaning.
  exact (proj2 (proj2 Hmeaning)).
Qed.

End Coverage.

End PreCoverage.
