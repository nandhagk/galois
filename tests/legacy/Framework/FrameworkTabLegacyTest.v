(** * Actual legacy IFDS result correspondence

    The legacy finite presentation is built from the modern graph and its actual exploded flows.
    For example, both completed engines agree inside a pending call of the taint fixture.
    Builds on: FrameworkTabReach and the public legacy IFDS exactness theorem. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkIfds FrameworkIde FrameworkStack FrameworkTabulate
  FrameworkTabValues FrameworkTabJumpProgress FrameworkTabValueProgress FrameworkTabReach.
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabSoundTest.
From GaloisLegacy.Collections Require CollectionsEncoding.
From GaloisLegacy.Analyses Require AnalysesInterprocedural.
Import List.ListNotations.

Module Old := AnalysesInterprocedural.

Module TabLegacy.

Definition action {P} (kind : Icfg.kind P) :=
  match kind with
  | Icfg.Internal => Old.IpInternal
  | Icfg.Call p => Old.IpCall p
  | Icfg.Return p => Old.IpReturn p
  end.

(** Each legacy edge contains precisely the supported input facts and their actual flow outputs. *)
Definition edge {N E P D} (I : Ifds.t N E P D) e :=
  Old.IpEdge
    (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e)
    (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e)
    (action (Icfg.edge_kind (Ifds.icfg I) e))
    (flat_map (fun x => map (fun y => (x, y)) (Ifds.flow I e x)) (Jump.fact_domain I)).

(** The adapter keeps supplied nodes and facts and maps every listed modern edge occurrence. *)
Definition problem {N E P D} (I : Ifds.t N E P D) sites :=
  Old.IpProblem (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg I)))) sites (Ifds.facts I)
    (map (edge I) (Cfg.edges (Icfg.cfg (Ifds.icfg I)))).

Local Lemma domain_spec {N E P D} (I : Ifds.t N E P D) x :
  In x (Jump.fact_domain I) <-> Ifds.fact_supported I x.
Proof.
  destruct x as [d|].
  - change (In (Some d) (None :: map (@Some D) (Ifds.facts I)) <-> In d (Ifds.facts I)).
    split.
    + intros [Hbad|Hin]; [discriminate|]; apply in_map_iff in Hin.
      destruct Hin as [a [Heq Ha]]; injection Heq as Heq; subst a; exact Ha.
    + intro Hd; right; apply in_map; exact Hd.
  - split; [intro Hin; exact Logic.I|intro Htrue; left; reflexivity].
Qed.

Local Lemma pairs_spec {N E P D} (I : Ifds.t N E P D) e x y :
  In (x, y) (Old.ip_pairs (edge I e)) <->
    Ifds.fact_supported I x /\ In y (Ifds.flow I e x).
Proof.
  unfold edge; cbn [Old.ip_pairs]; rewrite in_flat_map; split.
  - intros [a [Ha Hin]]; apply in_map_iff in Hin; destruct Hin as [b [Heq Hb]].
    injection Heq as Hx Hy; subst a b; split; [apply domain_spec; exact Ha|exact Hb].
  - intros [Hx Hy]; exists x; split; [apply domain_spec; exact Hx|apply in_map; exact Hy].
Qed.

Local Lemma step_forward {N E P D} (I : Ifds.t N E P D) sites c e next :
  Ifds.fact_supported I (snd (fst c)) -> Stack.step I c e next ->
  Old.ip_step (problem I sites) c (edge I e) next.
Proof.
  intros Hsupported Hstep.
  destruct Hstep as [e x y stack He Hkind Hflow|
    e p x y stack He Hkind Hflow|e p x y stack He Hkind Hflow].
  - apply (Old.ip_step_internal (problem I sites) (edge I e) x y stack).
    + apply in_map; exact He.
    + change (action (Icfg.edge_kind (Ifds.icfg I) e) = Old.IpInternal).
      rewrite Hkind; reflexivity.
    + apply pairs_spec; split; assumption.
  - apply (Old.ip_step_call (problem I sites) (edge I e) p x y stack).
    + apply in_map; exact He.
    + change (action (Icfg.edge_kind (Ifds.icfg I) e) = Old.IpCall p).
      rewrite Hkind; reflexivity.
    + apply pairs_spec; split; assumption.
  - apply (Old.ip_step_return (problem I sites) (edge I e) p x y stack).
    + apply in_map; exact He.
    + change (action (Icfg.edge_kind (Ifds.icfg I) e) = Old.IpReturn p).
      rewrite Hkind; reflexivity.
    + apply pairs_spec; split; assumption.
Qed.

Local Lemma step_supported {N E P D} (I : Ifds.t N E P D) c e next :
  Ifds.flow_closed I -> Ifds.fact_supported I (snd (fst c)) ->
  Stack.step I c e next -> Ifds.fact_supported I (snd (fst next)).
Proof.
  intros Hclosed Hsupported Hstep.
  destruct Hstep as [e x y stack He Hkind Hflow|
    e p x y stack He Hkind Hflow|e p x y stack He Hkind Hflow];
    eapply Hclosed; eassumption.
Qed.

Local Lemma path_forward {N E P D} (I : Ifds.t N E P D) sites c next :
  Ifds.flow_closed I -> Ifds.fact_supported I (snd (fst c)) ->
  Stack.path I c next -> Old.ip_path (problem I sites) c next.
Proof.
  intros Hclosed Hsupported Hpath; revert Hsupported.
  induction Hpath as [c|c e mid next Hstep Hpath IH]; intro Hsupported.
  - apply Old.ip_path_refl.
  - eapply Old.ip_path_step.
    + exact (step_forward I sites c e mid Hsupported Hstep).
    + apply IH; apply (step_supported I c e mid); assumption.
Qed.

Local Lemma step_backward {N E P D} (I : Ifds.t N E P D) sites c old next :
  Old.ip_step (problem I sites) c old next -> exists e, Stack.step I c e next.
Proof.
  intro Hstep.
  destruct Hstep as [old x y stack He Hkind Hflow|
    old p x y stack He Hkind Hflow|old p x y stack He Hkind Hflow].
  all: apply in_map_iff in He; destruct He as [e [Heq He]]; subst old;
    apply pairs_spec in Hflow; destruct Hflow as [Hsupported Hflow]; exists e.
  - apply (Stack.internal I e x y stack); try assumption.
    change (action (Icfg.edge_kind (Ifds.icfg I) e) = Old.IpInternal) in Hkind.
    destruct (Icfg.edge_kind (Ifds.icfg I) e); cbn [action] in Hkind; congruence.
  - apply (Stack.call I e p x y stack); try assumption.
    change (action (Icfg.edge_kind (Ifds.icfg I) e) = Old.IpCall p) in Hkind.
    destruct (Icfg.edge_kind (Ifds.icfg I) e); cbn [action] in Hkind; congruence.
  - apply (Stack.return_ I e p x y stack); try assumption.
    change (action (Icfg.edge_kind (Ifds.icfg I) e) = Old.IpReturn p) in Hkind.
    destruct (Icfg.edge_kind (Ifds.icfg I) e); cbn [action] in Hkind; congruence.
Qed.

Local Lemma path_backward {N E P D} (I : Ifds.t N E P D) sites c next :
  Old.ip_path (problem I sites) c next -> Stack.path I c next.
Proof.
  intro Hpath; induction Hpath as [c|c old mid next Hstep Hpath IH].
  - apply Stack.refl.
  - destruct (step_backward I sites c old mid Hstep) as [e Hactual].
    eapply Stack.next; eassumption.
Qed.

(** The constructed adapter has the same supported original executions in both directions. *)
Theorem paths_agree {N E P D} (I : Ifds.t N E P D) sites c next :
  Ifds.flow_closed I -> Ifds.fact_supported I (snd (fst c)) ->
  (Stack.path I c next <-> Old.ip_path (problem I sites) c next).
Proof.
  intros Hclosed Hsupported; split.
  - apply path_forward; assumption.
  - apply path_backward.
Qed.

(** Actual constructed modern completion agrees with the legacy solver on its finite lawful domain. *)
Theorem completed_results_agree {N E P D} (I : Ifds.t N E P D) sites start
    (EN : CollectionsEncoding.encoding N) (EP : CollectionsEncoding.encoding P)
    (ED : CollectionsEncoding.encoding D) :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg I))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg I))) ->
  encoding_laws (Ifds.fact_enc I) -> encoding_laws (Icfg.site_enc (Ifds.icfg I)) ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg I))) ->
  Ifds.flow_closed I -> Ifds.seed_supported I start ->
  Old.ip_problem_wf (problem I sites) ->
  In (fst start) (Old.ip_nodes (problem I sites)) ->
  exists jumps values,
    TabJumpProgress.complete (TabValues.reach_ide I) (fst start) bool_height =
      Tab.Certified jumps /\
    TabValueProgress.complete (TabValues.reach_ide I) (proj1_sig jumps) start true bool_height =
      TabValues.Certified values /\
    forall n d, TabValues.lookup (TabValues.reach_ide I) (proj1_sig values) (n, d) =
      Old.ifds_solve EN EP ED (problem I sites) (fst start) (snd start) n d.
Proof.
  intros HN HE HD HS HG Hclosed Hsupported Hlegacy Hstart.
  destruct (TabReach.complete_exact I start HN HE HD HS HG Hclosed Hsupported) as
    [jumps [values [Hjump [Hvalue [Hbalanced Hprefix]]]]].
  exists jumps, values; split; [exact Hjump|]; split; [exact Hvalue|].
  intros n d.
  assert (Hsame :
    TabValues.lookup (TabValues.reach_ide I) (proj1_sig values) (n, d) = true <->
    Old.ifds_solve EN EP ED (problem I sites) (fst start) (snd start) n d = true).
  { rewrite (Hprefix n d).
    rewrite (Old.ifds_solve_exact EN EP ED (problem I sites)
      (fst start) (snd start) Hlegacy Hstart Hsupported n d).
    split; intros [stack Hpath]; exists stack.
    - apply path_forward; assumption.
    - apply (path_backward I sites); exact Hpath. }
  destruct (TabValues.lookup (TabValues.reach_ide I) (proj1_sig values) (n, d)),
    (Old.ifds_solve EN EP ED (problem I sites) (fst start) (snd start) n d);
    try reflexivity.
  - pose proof (proj1 Hsame eq_refl); discriminate.
  - pose proof (proj2 Hsame eq_refl); discriminate.
Qed.

End TabLegacy.
