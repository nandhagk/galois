(** * Induction over matched Stack paths

    Candidate summary predicates are propagated through the suspended frames of Stack.path.
    For example, a return uses the same call edge that introduced its pending frame.
    Builds on: FrameworkStack and the finite fact-flow support contract. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseRel.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkStack FrameworkIde.
Import List.ListNotations.

Module TabPaths.

Definition vertex N D := (N * option D)%type.

Definition source {N E P D} (I : Ifds.t N E P D) e d : vertex N D :=
  (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, d).

Definition target {N E P D} (I : Ifds.t N E P D) e d : vertex N D :=
  (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e, d).

Definition roots {N E P D A F} (I : Ide.t N E P D A F) start :=
  Cost.value (Jump.roots_c I start (Jump.arcs I)).

(** Root observations retain the initial facts and the actual exploded call targets. *)
Theorem roots_value {N E P D A F} (I : Ide.t N E P D A F) start :
  roots I start =
    map (fun d => (start, d)) (Jump.fact_domain (Ide.ifds I)) ++
    filter_map (fun a =>
      match Jump.kind a with
      | Icfg.Call _ => Some (Jump.target a)
      | _ => None
      end) (Jump.arcs I).
Proof.
  apply Jump.roots_c_value.
Qed.

(** Every prepared exploded call contributes its own callee-entry root. *)
Theorem call_target_root {N E P D A F} (I : Ide.t N E P D A F) start a p :
  In a (Jump.arcs I) -> Jump.kind a = Icfg.Call p ->
  In (Jump.target a) (roots I start).
Proof.
  intros Ha Hkind; unfold roots; rewrite Jump.roots_c_value.
  apply in_app_iff; right; apply filter_map_spec.
  exists a; split; [exact Ha|]; rewrite Hkind; reflexivity.
Qed.

(** Every entry root has an identity row, including unreachable callee entries. *)
Theorem root_identity {N E P D A F} (I : Ide.t N E P D A F) start J r :
  jump_post I start J -> In r (roots I start) ->
  leb (Micro.lat (Ide.micro I)) (Micro.id (Ide.micro I)) (J (r, r)) = true.
Proof.
  intros Hpost Hr; unfold roots in Hr; rewrite Jump.roots_c_value in Hr.
  apply in_app_iff in Hr; destruct Hr as [Hseed|Hcall].
  - apply (Hpost (Jump.Seed r)); apply Jump.rows_spec; left.
    exists r; auto.
  - apply filter_map_spec in Hcall; destruct Hcall as [a [Ha Htarget]].
    destruct (Jump.kind a) as [|p|p] eqn:Hkind; try discriminate.
    injection Htarget as Heq; subst r.
    apply (Hpost (Jump.Call a)); apply Jump.rows_spec; right; left.
    exists a, p; auto.
Qed.

(** A label retains the actual edge, input/output facts, stack kind and symbolic weight. *)
Definition label {N E P D A F} (I : Ide.t N E P D A F) e x y :=
  Jump.Arc e (source (Ide.ifds I) e x) (target (Ide.ifds I) e y)
    (Icfg.edge_kind (Ifds.icfg (Ide.ifds I)) e) (Ide.weight I e x y).

(** A label's kind is the actual kind of its own edge occurrence. *)
Theorem label_kind {N E P D A F} (I : Ide.t N E P D A F) e x y :
  Jump.kind (label I e x y) = Icfg.edge_kind (Ifds.icfg (Ide.ifds I)) e.
Proof.
  reflexivity.
Qed.

(** Every actual supported exploded flow alternative has its canonical prepared label. *)
Theorem label_member {N E P D A F} (I : Ide.t N E P D A F) e x y :
  In e (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  Ifds.fact_supported (Ide.ifds I) x -> In y (Ifds.flow (Ide.ifds I) e x) ->
  In (label I e x y) (Jump.arcs I).
Proof.
  intros He Hx Hy; rewrite Jump.arcs_equation; apply in_flat_map.
  exists e; split; [exact He|]; apply in_flat_map.
  exists x; split.
  - destruct x as [x|].
    + right; apply in_map; exact Hx.
    + left; reflexivity.
  - apply in_map; exact Hy.
Qed.

(** An annotation labels the same Stack.step with its own edge and its actual facts. *)
Definition annotation {N E P D A F} (I : Ide.t N E P D A F)
    (c : Stack.config N D P) (a : Jump.arc N E P D F) (next : Stack.config N D P) :=
  Stack.step (Ide.ifds I) c (Jump.edge a) next /\
  a = label I (Jump.edge a) (snd (fst c)) (snd (fst next)).

(** An annotated trace is the generic labelled refinement of the existing Stack.step. *)
Definition trace {N E P D A F} (I : Ide.t N E P D A F) :=
  Rel.lpath (annotation I).

(** Annotated endpoints and the actual Stack.step impose the label's precise stack action. *)
Theorem annotation_shape {N E P D A F} (I : Ide.t N E P D A F) c a next :
  annotation I c a next ->
  Jump.source a = fst c /\ Jump.target a = fst next /\
    match Jump.kind a with
    | Icfg.Internal => snd next = snd c
    | Icfg.Call p => snd next = p :: snd c
    | Icfg.Return p => snd c = p :: snd next
    end.
Proof.
  intros [Hstep Hlabel].
  destruct Hstep as [e x y stack He Hkind Hflow|
    e p x y stack He Hkind Hflow|e p x y stack He Hkind Hflow];
    cbn [fst snd] in *; split.
  all: try (rewrite Hlabel; reflexivity).
  all: split; [rewrite Hlabel; reflexivity|].
  all: rewrite Hlabel, label_kind, Hkind; reflexivity.
Qed.

(** Actual annotations propagate finite fact support through the original flow-closure duty. *)
Theorem annotation_supported {N E P D A F} (I : Ide.t N E P D A F) c a next :
  Ifds.flow_closed (Ide.ifds I) ->
  Ifds.fact_supported (Ide.ifds I) (snd (fst c)) ->
  annotation I c a next ->
  Ifds.fact_supported (Ide.ifds I) (snd (fst next)).
Proof.
  intros Hclosed Hsupported [Hstep Hlabel].
  destruct Hstep as [e x y stack He Hkind Hflow|
    e p x y stack He Hkind Hflow|e p x y stack He Hkind Hflow];
    cbn [fst snd] in *; eapply Hclosed; eassumption.
Qed.

(** Erasing labels projects to the original Stack.path, including the same push/pop steps. *)
Theorem trace_project {N E P D A F} (I : Ide.t N E P D A F) c as_ next :
  trace I c as_ next -> Stack.path (Ide.ifds I) c next.
Proof.
  intro Htrace; induction Htrace as [c|c a mid as_ next [Hstep Hlabel] Htrace IH].
  - apply Stack.refl.
  - eapply Stack.next; [exact Hstep|exact IH].
Qed.

Local Lemma step_annotate {N E P D A F} (I : Ide.t N E P D A F) c e next :
  Ifds.flow_closed (Ide.ifds I) ->
  Ifds.fact_supported (Ide.ifds I) (snd (fst c)) ->
  Stack.step (Ide.ifds I) c e next ->
  annotation I c (label I e (snd (fst c)) (snd (fst next))) next /\
  In (label I e (snd (fst c)) (snd (fst next))) (Jump.arcs I) /\
  Ifds.fact_supported (Ide.ifds I) (snd (fst next)).
Proof.
  intros Hclosed Hsupported Hstep; split.
  - split; [exact Hstep|reflexivity].
  - destruct Hstep as [e x y stack He Hkind Hflow|
      e p x y stack He Hkind Hflow|e p x y stack He Hkind Hflow];
      cbn [fst snd] in *; split.
    all: try (apply label_member; assumption).
    all: eapply Hclosed; eassumption.
Qed.

(** Every original supported path has annotations of that same execution in the prepared arcs. *)
Theorem trace_complete {N E P D A F} (I : Ide.t N E P D A F) c next :
  Ifds.flow_closed (Ide.ifds I) ->
  Ifds.fact_supported (Ide.ifds I) (snd (fst c)) ->
  Stack.path (Ide.ifds I) c next ->
  exists as_, trace I c as_ next /\ Forall (fun a => In a (Jump.arcs I)) as_.
Proof.
  intros Hclosed Hsupported Hpath; revert Hsupported.
  induction Hpath as [c|c e mid next Hstep Hpath IH]; intro Hsupported.
  - exists []; split; constructor.
  - destruct (step_annotate I c e mid Hclosed Hsupported Hstep) as
      [Hannotation [Harc Hnext]].
    destruct (IH Hnext) as [as_ [Htrace Hmembers]].
    exists (label I e (snd (fst c)) (snd (fst mid)) :: as_); split.
    + econstructor; eassumption.
    + constructor; assumption.
Qed.

(** Listed semantic edges have both endpoints in a lawful graph's node inventory. *)
Theorem listed_endpoints {N E P D} (I : Ifds.t N E P D) e :
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg I))) ->
  In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
  In (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e)
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg I)))) /\
  In (Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg I))) e)
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg I)))).
Proof.
  intros HG He; apply Cfg.edges_spec in He; destruct He as [n [Hn Hout]]; split.
  - rewrite (out_source HG n e Hout); exact Hn.
  - apply (out_target_in HG n e Hn Hout).
Qed.

(** Actual prepared arc endpoints are listed vertices under graph and finite flow closure. *)
Theorem arc_vertices {N E P D A F} (I : Ide.t N E P D A F) a :
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  Ifds.flow_closed (Ide.ifds I) -> In a (Jump.arcs I) ->
  In (Jump.source a) (IdeValue.vertices I) /\ In (Jump.target a) (IdeValue.vertices I).
Proof.
  intros HG Hclosed Ha; rewrite Jump.arcs_equation in Ha; apply in_flat_map in Ha.
  destruct Ha as [e [He Ha]]; apply in_flat_map in Ha.
  destruct Ha as [x [Hx Ha]]; apply in_map_iff in Ha.
  destruct Ha as [y [Heq Hy]]; subst a.
  pose proof (listed_endpoints (Ide.ifds I) e HG He) as [Hsource Htarget].
  assert (Hinput : Ifds.fact_supported (Ide.ifds I) x).
  { destruct x as [x|]; [|exact Logic.I].
    destruct Hx as [Hbad|Hin]; [discriminate|].
    apply in_map_iff in Hin; destruct Hin as [d [Heq Hd]].
    injection Heq as Heq; subst d; exact Hd. }
  pose proof (Hclosed e x y He Hinput Hy) as Houtput.
  split; apply IdeValue.vertices_spec; split; try assumption.
  destruct y as [y|].
  - right; apply in_map; exact Houtput.
  - left; reflexivity.
Qed.

(** A nonempty annotated execution derives its final inventory membership from its actual steps. *)
Theorem trace_nonempty_vertices {N E P D A F} (I : Ide.t N E P D A F) c as_ next :
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  Ifds.flow_closed (Ide.ifds I) -> trace I c as_ next ->
  Forall (fun a => In a (Jump.arcs I)) as_ -> as_ <> [] ->
  In (fst next) (IdeValue.vertices I).
Proof.
  intros HG Hclosed Htrace; induction Htrace as [c|c a mid rest next Hstep Htrace IH];
    intros Hmembers Hnonempty.
  - exfalso; apply Hnonempty; reflexivity.
  - inversion Hmembers as [|a' rest' Ha Hrest]; subst a' rest'.
    destruct rest as [|b rest].
    + assert (Hsame : mid = next) by (inversion Htrace; reflexivity); subst next.
      destruct (annotation_shape I c a mid Hstep) as [Hsource [Htarget Hstack]].
      rewrite <- Htarget; exact (proj2 (arc_vertices I a HG Hclosed Ha)).
    + apply IH; [exact Hrest|discriminate].
Qed.

(** This proof invariant evaluates an arbitrary candidate at the actual suspended frames. *)
Local Fixpoint frames {N E P D} (I : Ifds.t N E P D)
    (R : vertex N D -> Prop) (Q : vertex N D -> vertex N D -> Prop)
    root v (stack : list P) : Prop :=
  match stack with
  | [] => R root /\ Q root v
  | p :: rest =>
    exists call x y,
      In call (Cfg.edges (Icfg.cfg (Ifds.icfg I))) /\
      Icfg.edge_kind (Ifds.icfg I) call = Icfg.Call p /\
      In y (Ifds.flow I call x) /\
      Ifds.fact_supported I x /\
      frames I R Q root (source I call x) rest /\
      R (target I call y) /\ Q (target I call y) v
  end.

Local Lemma frames_extend {N E P D} (I : Ifds.t N E P D) R Q root u v stack :
  (forall r, R r -> Q r u -> Q r v) ->
  frames I R Q root u stack -> frames I R Q root v stack.
Proof.
  intros Hextend Hframes; destruct stack as [|p rest]; cbn [frames] in *.
  - destruct Hframes as [Hr Hq]; split; [exact Hr|apply Hextend; assumption].
  - destruct Hframes as [call [x [y [He [Hkind [Hflow [Hx [Houter [Hr Hq]]]]]]]]].
    exists call, x, y; repeat split; try assumption.
    apply Hextend; assumption.
Qed.

Section Candidate.
Context {N E P D} (I : Ifds.t N E P D).
Context (R : vertex N D -> Prop) (Q : vertex N D -> vertex N D -> Prop).
Context (Hflow : Ifds.flow_closed I).
Context (Hseed : forall r, R r -> Q r r).
Context (Hcall_root : forall e p x y,
  In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
  Icfg.edge_kind (Ifds.icfg I) e = Icfg.Call p ->
  Ifds.fact_supported I x -> In y (Ifds.flow I e x) -> R (target I e y)).
Context (Hinternal : forall r e x y,
  R r -> Ifds.fact_supported I x -> Q r (source I e x) ->
  In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
  Icfg.edge_kind (Ifds.icfg I) e = Icfg.Internal ->
  In y (Ifds.flow I e x) -> Q r (target I e y)).
Context (Hreturn : forall r call ret p x entry exit y,
  R r -> Ifds.fact_supported I x -> Q r (source I call x) ->
  In call (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
  Icfg.edge_kind (Ifds.icfg I) call = Icfg.Call p ->
  In entry (Ifds.flow I call x) ->
  Ifds.fact_supported I exit ->
  Q (target I call entry) (source I ret exit) ->
  In ret (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
  Icfg.edge_kind (Ifds.icfg I) ret = Icfg.Return p ->
  In y (Ifds.flow I ret exit) -> Q r (target I ret y)).

Local Lemma step_frames root c e c' :
  Ifds.fact_supported I (snd (fst c)) ->
  frames I R Q root (fst c) (snd c) ->
  Stack.step I c e c' ->
  Ifds.fact_supported I (snd (fst c')) /\ frames I R Q root (fst c') (snd c').
Proof.
  intros Hsupported Hframes Hstep.
  destruct Hstep as [e x y stack He Hkind Hxy|
    e p x y stack He Hkind Hxy|e p x y stack He Hkind Hxy];
    cbn [fst snd] in *; split; try (eapply Hflow; eassumption).
  - eapply frames_extend; [|exact Hframes].
    intros r Hr Hq; apply Hinternal with (x := x); assumption.
  - cbn [frames]; exists e, x, y; repeat split; try assumption.
    + eapply Hcall_root; eassumption.
    + apply Hseed; eapply Hcall_root; eassumption.
  - cbn [frames] in Hframes.
    destruct Hframes as
      [call [a [entry [Hcall [Hcallkind [Hentry [Ha [Houter [Hr Hq]]]]]]]]].
    eapply frames_extend; [|exact Houter].
    intros r Hroot Hbefore; apply (Hreturn r call e p a entry x y); assumption.
Qed.

Local Lemma path_frames root c c' :
  Stack.path I c c' ->
  Ifds.fact_supported I (snd (fst c)) ->
  frames I R Q root (fst c) (snd c) ->
  Ifds.fact_supported I (snd (fst c')) /\ frames I R Q root (fst c') (snd c').
Proof.
  intro Hpath; induction Hpath as [c|c e next last Hstep Hpath IH];
    intros Hsupported Hframes.
  - split; assumption.
  - destruct (step_frames root c e next Hsupported Hframes Hstep) as [Hnext Hframe].
    apply IH; assumption.
Qed.

(** Every balanced Stack path is admitted by a candidate closed under matched summary rules. *)
Theorem balanced_induction root n d :
  R root -> Ifds.seed_supported I root ->
  Stack.balanced I (fst root) (snd root) n d ->
  Q root (n, d).
Proof.
  destruct root as [r x].
  intros Hroot Hsupported Hpath.
  pose proof (path_frames (r, x) _ _ Hpath Hsupported
    (conj Hroot (Hseed (r, x) Hroot))) as Hfinal.
  exact (proj2 (proj2 Hfinal)).
Qed.

Local Lemma frames_prefix (V : vertex N D -> Prop) root v stack :
  (forall r v, Q r v -> V r -> V v) ->
  (forall e p x y,
    In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
    Icfg.edge_kind (Ifds.icfg I) e = Icfg.Call p ->
    Ifds.fact_supported I x -> In y (Ifds.flow I e x) ->
    V (source I e x) -> V (target I e y)) ->
  V root -> frames I R Q root v stack -> V v.
Proof.
  intros Hsummary Henter Hroot; revert v.
  induction stack as [|p stack IH]; intros v Hframes; cbn [frames] in Hframes.
  - apply (Hsummary root v); [exact (proj2 Hframes)|exact Hroot].
  - destruct Hframes as
      [call [x [y [He [Hkind [Hflowxy [Hx [Houter [Hr Hq]]]]]]]]].
    apply (Hsummary (target I call y) v Hq).
    apply (Henter call p x y); try assumption.
    apply IH; exact Houter.
Qed.

(** Prefix closure covers endpoints inside pending calls of the same Stack path. *)
Theorem prefix_induction (V : vertex N D -> Prop) root n d stack :
  R root -> Ifds.seed_supported I root -> V root ->
  (forall r v, Q r v -> V r -> V v) ->
  (forall e p x y,
    In e (Cfg.edges (Icfg.cfg (Ifds.icfg I))) ->
    Icfg.edge_kind (Ifds.icfg I) e = Icfg.Call p ->
    Ifds.fact_supported I x -> In y (Ifds.flow I e x) ->
    V (source I e x) -> V (target I e y)) ->
  Stack.path I (fst root, snd root, []) (n, d, stack) -> V (n, d).
Proof.
  destruct root as [r x].
  intros Hroot Hsupported Hinitial Hsummary Henter Hpath.
  pose proof (path_frames (r, x) _ _ Hpath Hsupported
    (conj Hroot (Hseed (r, x) Hroot))) as Hfinal.
  apply (frames_prefix V (r, x) (n, d) stack Hsummary Henter Hinitial).
  exact (proj2 Hfinal).
Qed.

End Candidate.

End TabPaths.
