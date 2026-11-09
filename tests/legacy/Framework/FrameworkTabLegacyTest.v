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
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabSoundTest
  FrameworkTabulateTest FrameworkTabReachTest.
From GaloisLegacy.Collections Require CollectionsEncoding.
From GaloisLegacy.Order Require OrderLattice OrderBasic.
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

(** Modern graph closure and legacy site and zero-flow duties establish adapter validity. *)
Theorem problem_wf {N E P D} (I : Ifds.t N E P D) sites :
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg I))) ->
  NoDup sites -> NoDup (Ifds.facts I) -> Ifds.flow_closed I ->
  (forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
    In None (Ifds.flow I e None)) ->
  (forall e, In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
    match Icfg.edge_kind (Ifds.icfg I) e with
    | Icfg.Internal => True
    | Icfg.Call p | Icfg.Return p => In p sites
    end) ->
  Old.ip_problem_wf (problem I sites).
Proof.
  intros HG Hsites Hfacts Hclosed Hzero Hkind.
  split; [exact (nodes_nodup HG)|].
  split; [exact Hsites|]; split; [exact Hfacts|].
  intros old Hold; apply in_map_iff in Hold; destruct Hold as [e [Heq He]]; subst old.
  apply Cfg.edges_spec in He; destruct He as [n [Hn He]].
  assert (Hlisted : In e (Cfg.edges (Icfg.cfg (Ifds.icfg I)))).
  { apply Cfg.edges_spec; exists n; split; assumption. }
  split.
  - change (In (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e)
      (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg I))))).
    rewrite (out_source HG n e He); exact Hn.
  - split; [exact (out_target_in HG n e Hn He)|].
    split; [apply pairs_spec; split; [exact Logic.I|apply Hzero; exact Hlisted]|].
    split.
    + specialize (Hkind e Hlisted); unfold edge; cbn [Old.ip_action].
      destruct (Icfg.edge_kind (Ifds.icfg I) e); exact Hkind.
    + intros x y Hpair; apply pairs_spec in Hpair; destruct Hpair as [Hx Hy].
      split; [exact Hx|exact (Hclosed e x y Hlisted Hx Hy)].
Qed.

(** Constructed modern completion agrees with the legacy solver on its finite lawful domain. *)
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

Definition legacy_reached (I : Ifds.t nat nat nat unit) sites n d :=
  Old.ifds_solve CollectionsEncoding.nat_encoding CollectionsEncoding.nat_encoding
    CollectionsEncoding.unit_encoding (problem I sites) 0 None n d.

Example taint_adapter_is_lawful : Old.ip_problem_wf (problem taint [7]).
Proof.
  apply problem_wf.
  - exact taint_graph_wf.
  - constructor; [intro Hbad; inversion Hbad|constructor].
  - constructor; [intro Hbad; inversion Hbad|constructor].
  - exact taint_flow_closed.
  - intros e He; change (In e [0; 1; 2]) in He.
    destruct He as [He|[He|[He|He]]]; try contradiction; subst e;
      vm_compute; auto.
  - intros e He; change (In e [0; 1; 2]) in He.
    destruct He as [He|[He|[He|He]]]; try contradiction; subst e;
      vm_compute; auto.
Qed.

(** The actual legacy result theorem applies to the completed two-phase taint engine. *)
Example actual_taint_results_agree :
  exists jumps values,
    TabJumpProgress.complete (TabValues.reach_ide taint) 0 bool_height =
      Tab.Certified jumps /\
    TabValueProgress.complete (TabValues.reach_ide taint) (proj1_sig jumps)
      (0, None) true bool_height = TabValues.Certified values /\
    forall n d, TabValues.lookup (TabValues.reach_ide taint) (proj1_sig values) (n, d) =
      legacy_reached taint [7] n d.
Proof.
  unfold legacy_reached.
  apply (completed_results_agree taint [7] (0, None)
    CollectionsEncoding.nat_encoding CollectionsEncoding.nat_encoding
    CollectionsEncoding.unit_encoding).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact nat_encoding_laws.
  - exact taint_graph_wf.
  - exact taint_flow_closed.
  - exact Logic.I.
  - exact taint_adapter_is_lawful.
  - left; reflexivity.
Qed.

Local Lemma taint_queries_agree n d :
  reached taint n d = Some (legacy_reached taint [7] n d).
Proof.
  destruct actual_taint_results_agree as [jumps [values [Hjump [Hvalue Hagree]]]].
  unfold reached; rewrite Hjump, Hvalue, Hagree; reflexivity.
Qed.

Example pending_call_results_agree :
  (reached taint 2 (Some tt), legacy_reached taint [7] 2 (Some tt)) = (Some true, true).
Proof.
  pose proof (taint_queries_agree 2 (Some tt)) as Hagree.
  rewrite pending_call_is_reached in Hagree.
  injection Hagree as Hold; rewrite <- Hold, pending_call_is_reached; reflexivity.
Qed.

Example unlisted_destination_results_agree :
  (reached taint 99 None, legacy_reached taint [7] 99 None) = (Some false, false).
Proof.
  assert (Hnew : reached taint 99 None = Some false) by (vm_compute; reflexivity).
  pose proof (taint_queries_agree 99 None) as Hagree.
  rewrite Hnew in Hagree; injection Hagree as Hold.
  rewrite Hnew, <- Hold; reflexivity.
Qed.

Example seed_results_agree :
  (reached taint 0 None, legacy_reached taint [7] 0 None) = (Some true, true).
Proof.
  assert (Hnew : reached taint 0 None = Some true) by (vm_compute; reflexivity).
  pose proof (taint_queries_agree 0 None) as Hagree.
  rewrite Hnew in Hagree; injection Hagree as Hold.
  rewrite Hnew, <- Hold; reflexivity.
Qed.

End TabLegacy.

Module TabLegacyIde.

(** The finite Boolean identity fragment is distributive and retains every matched execution. *)
Definition problem {N E P D} (I : Ifds.t N E P D) sites :=
  Old.IdeProblem (TabLegacy.problem I sites) OrderBasic.bool_lattice [false; true]
    (fun _ _ _ value => value).

Local Lemma problem_laws {N E P D} (I : Ifds.t N E P D) sites :
  Old.ip_problem_wf (TabLegacy.problem I sites) -> Old.ide_laws (problem I sites).
Proof.
  intro Hwf; constructor.
  - exact Hwf.
  - intros []; [right; left; reflexivity|left; reflexivity].
  - exact OrderBasic.bool_laws.
  - exact OrderBasic.bool_lub.
  - intros edge x y a b Hedge Hpair; split; destruct a, b; reflexivity.
Qed.

Local Lemma path_weighted {N E P D} (I : Ifds.t N E P D) sites c next value :
  Old.ip_path (TabLegacy.problem I sites) c next ->
  Old.ide_path (problem I sites) c value next value.
Proof.
  intro Hpath; induction Hpath as [c|c edge mid next Hstep Hpath IH].
  - apply Old.ide_path_refl.
  - destruct c as [[n x] stack], mid as [[n' y] stack'].
    eapply Old.ide_path_step; [exact Hstep|exact IH].
Qed.

(** Actual finite IDE execution agrees with actual IFDS execution on the identity fragment. *)
Theorem old_results_agree {N E P D} (I : Ifds.t N E P D) sites start
    (EN : CollectionsEncoding.encoding N) (EP : CollectionsEncoding.encoding P)
    (ED : CollectionsEncoding.encoding D) :
  Old.ip_problem_wf (TabLegacy.problem I sites) ->
  In (fst start) (Old.ip_nodes (TabLegacy.problem I sites)) ->
  Ifds.fact_supported I (snd start) ->
  forall n d,
    Old.ide_solve EN EP ED CollectionsEncoding.bool_encoding
      (problem I sites) (fst start) (snd start) true n d =
    Old.ifds_solve EN EP ED (TabLegacy.problem I sites) (fst start) (snd start) n d.
Proof.
  intros Hwf Hstart Hseed n d.
  destruct (Old.ide_solve_exact EN EP ED CollectionsEncoding.bool_encoding (problem I sites)
    (fst start) (snd start) true (problem_laws I sites Hwf) Hstart Hseed n d)
    as [Hupper Hleast].
  destruct (Old.ifds_solve EN EP ED (TabLegacy.problem I sites)
    (fst start) (snd start) n d) eqn:Hreachable.
  - apply (proj1 (Old.ifds_solve_exact EN EP ED (TabLegacy.problem I sites)
      (fst start) (snd start) Hwf Hstart Hseed n d)) in Hreachable.
    destruct Hreachable as [stack Hpath].
    pose proof (Hupper stack true (path_weighted I sites _ _ true Hpath)) as Hbound.
    change (implb true (Old.ide_solve EN EP ED CollectionsEncoding.bool_encoding
      (problem I sites) (fst start) (snd start) true n d) = true) in Hbound.
    exact Hbound.
  - assert (Hnone : forall stack b,
      Old.ide_path (problem I sites) (fst start, snd start, []) true (n, d, stack) b ->
      OrderLattice.leb OrderBasic.bool_lattice b false = true).
    { intros stack b Hpath.
      pose proof (Old.ide_path_graph _ _ _ _ _ Hpath) as Hgraph.
      assert (Htrue : Old.ifds_solve EN EP ED (TabLegacy.problem I sites)
        (fst start) (snd start) n d = true).
      { apply (proj2 (Old.ifds_solve_exact EN EP ED (TabLegacy.problem I sites)
          (fst start) (snd start) Hwf Hstart Hseed n d)).
        exists stack; exact Hgraph. }
      rewrite Hreachable in Htrue; discriminate. }
    specialize (Hleast false Hnone).
    change (implb (Old.ide_solve EN EP ED CollectionsEncoding.bool_encoding
      (problem I sites) (fst start) (snd start) true n d) false = true) in Hleast.
    destruct (Old.ide_solve EN EP ED CollectionsEncoding.bool_encoding
      (problem I sites) (fst start) (snd start) true n d); [discriminate|reflexivity].
Qed.

(** Constructed modern values agree with actual legacy IDE on the Boolean identity fragment. *)
Theorem completed_results_agree {N E P D} (I : Ifds.t N E P D) sites start
    (EN : CollectionsEncoding.encoding N) (EP : CollectionsEncoding.encoding P)
    (ED : CollectionsEncoding.encoding D) :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg I))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg I))) ->
  encoding_laws (Ifds.fact_enc I) -> encoding_laws (Icfg.site_enc (Ifds.icfg I)) ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg I))) ->
  Ifds.flow_closed I -> Ifds.seed_supported I start ->
  Old.ip_problem_wf (TabLegacy.problem I sites) ->
  In (fst start) (Old.ip_nodes (TabLegacy.problem I sites)) ->
  exists jumps values,
    TabJumpProgress.complete (TabValues.reach_ide I) (fst start) bool_height =
      Tab.Certified jumps /\
    TabValueProgress.complete (TabValues.reach_ide I) (proj1_sig jumps) start true bool_height =
      TabValues.Certified values /\
    forall n d, TabValues.lookup (TabValues.reach_ide I) (proj1_sig values) (n, d) =
      Old.ide_solve EN EP ED CollectionsEncoding.bool_encoding
        (problem I sites) (fst start) (snd start) true n d.
Proof.
  intros HN HE HD HS HG Hclosed Hseed Hlegacy Hstart.
  destruct (TabLegacy.completed_results_agree I sites start EN EP ED
    HN HE HD HS HG Hclosed Hseed Hlegacy Hstart) as
    [jumps [values [Hjump [Hvalue Hagree]]]].
  exists jumps, values; split; [exact Hjump|]; split; [exact Hvalue|].
  intros n d; rewrite Hagree, (old_results_agree I sites start EN EP ED
    Hlegacy Hstart Hseed n d); reflexivity.
Qed.

Definition taint_result n d :=
  Old.ide_solve CollectionsEncoding.nat_encoding CollectionsEncoding.nat_encoding
    CollectionsEncoding.unit_encoding CollectionsEncoding.bool_encoding
    (problem taint [7]) 0 None true n d.

Local Lemma taint_agrees n d : reached taint n d = Some (taint_result n d).
Proof.
  assert (Hsame : taint_result n d = TabLegacy.legacy_reached taint [7] n d).
  { apply (old_results_agree taint [7] (0, None)
      CollectionsEncoding.nat_encoding CollectionsEncoding.nat_encoding
      CollectionsEncoding.unit_encoding).
    - exact TabLegacy.taint_adapter_is_lawful.
    - left; reflexivity.
    - exact Logic.I. }
  destruct TabLegacy.actual_taint_results_agree as [jumps [values [Hjump [Hvalue Hagree]]]].
  unfold reached; rewrite Hjump, Hvalue, Hagree, Hsame; reflexivity.
Qed.

Example finite_ide_pending_call :
  (reached taint 2 (Some tt), taint_result 2 (Some tt)) = (Some true, true).
Proof.
  pose proof (taint_agrees 2 (Some tt)) as Hsame.
  rewrite pending_call_is_reached in Hsame; injection Hsame as Hold.
  rewrite pending_call_is_reached, <- Hold; reflexivity.
Qed.

Example finite_ide_unlisted_destination :
  (reached taint 99 None, taint_result 99 None) = (Some false, false).
Proof.
  assert (Hnew : reached taint 99 None = Some false) by (vm_compute; reflexivity).
  pose proof (taint_agrees 99 None) as Hsame; rewrite Hnew in Hsame.
  injection Hsame as Hold; rewrite Hnew, <- Hold; reflexivity.
Qed.

End TabLegacyIde.
