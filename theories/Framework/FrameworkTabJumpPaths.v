(** * Symbolic bounds along the same matched execution

    A semantic frame invariant carries the bound for each suspended caller segment.
    For example, a return composes the current segment with the call stored by its own frame.
    Builds on: FrameworkTabPaths, FrameworkTabWeight and the ground jump rows. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseRel.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkStack
  FrameworkTabPaths FrameworkTabWeight.
Import List.ListNotations.

Module TabJumpPaths.

(** Semantic frames retain the caller entry, preceding segment weight and actual call label. *)
Record frame (N E P D F : Type) := Frame {
  outer : N * option D;
  before : F;
  call : Jump.arc N E P D F
}.
Arguments Frame {N E P D F}.
Arguments outer {N E P D F}.
Arguments before {N E P D F}.
Arguments call {N E P D F}.

(** This is a pure semantic interpretation of suspended weights, outside executable algorithms. *)
Fixpoint plug {N E P D A F} (M : Micro.t A F)
    (fs : list (frame N E P D F)) f :=
  match fs with
  | [] => f
  | fr :: rest => plug M rest
      (Micro.compose M f (Micro.compose M (Jump.weight (call fr)) (before fr)))
  end.

Local Lemma plug_mono {N E P D A F} (LA : lattice A) (M : Micro.t A F)
    (HM : micro_laws LA M) (fs : list (frame N E P D F)) f g :
  leb (Micro.lat M) f g = true ->
  leb (Micro.lat M) (plug M fs f) (plug M fs g) = true.
Proof.
  revert f g; induction fs as [|fr fs IH]; intros f g Hfg; cbn [plug].
  - exact Hfg.
  - apply IH, (compose_mono _ _ HM); [exact Hfg|apply leb_refl; exact (lat_ok _ _ HM)].
Qed.

Local Lemma plug_compose {N E P D A F} (LA : lattice A) (M : Micro.t A F)
    (HM : micro_laws LA M) (HW : TabWeight.laws M)
    (fs : list (frame N E P D F)) f g :
  equivalent (Micro.lat M) (plug M fs (Micro.compose M f g))
    (Micro.compose M f (plug M fs g)).
Proof.
  revert f g; induction fs as [|fr fs IH]; intros f g; cbn [plug].
  - split; apply leb_refl; exact (lat_ok _ _ HM).
  - destruct (TabWeight.associative HW f g
      (Micro.compose M (Jump.weight (call fr)) (before fr))) as [Hassoc Hreverse].
    destruct (IH f (Micro.compose M g
      (Micro.compose M (Jump.weight (call fr)) (before fr)))) as [Hforward Hback].
    split.
    + eapply leb_trans; [exact (lat_ok _ _ HM)| |exact Hforward].
      apply (plug_mono LA M HM); exact Hassoc.
    + eapply leb_trans; [exact (lat_ok _ _ HM)|exact Hback|].
      apply (plug_mono LA M HM); exact Hreverse.
Qed.

(** Saved bounds refer to the same call sites and entry facts as the semantic stack. *)
Local Fixpoint saved {N E P D A F} (I : Ide.t N E P D A F) start J origin current
    (fs : list (frame N E P D F)) (stack : list P) : Prop :=
  match fs with
  | [] => stack = [] /\ current = origin
  | fr :: rest =>
    exists p tail,
      stack = p :: tail /\ Jump.kind (call fr) = Icfg.Call p /\
      current = Jump.target (call fr) /\
      In (outer fr) (TabPaths.roots I start) /\ In (call fr) (Jump.arcs I) /\
      leb (Micro.lat (Ide.micro I)) (before fr) (J (outer fr, Jump.source (call fr))) = true /\
      saved I start J origin (outer fr) rest tail
  end.

(** A marker bounds the actual accumulated weight through the current suspended segments. *)
Local Definition marker {N E P D A F} (I : Ide.t N E P D A F) start J
    origin (c : Stack.config N D P) total :=
  exists current f fs,
    In current (TabPaths.roots I start) /\
    Ifds.fact_supported (Ide.ifds I) (snd (fst c)) /\
    leb (Micro.lat (Ide.micro I)) f (J (current, fst c)) = true /\
    saved I start J origin current fs (snd c) /\
    leb (Micro.lat (Ide.micro I)) total (plug (Ide.micro I) fs f) = true.

Section Soundness.
Context {N E P D A F} (I : Ide.t N E P D A F)
  (start : N) (J : jkey N D -> F) (origin : N * option D).
Context (HM : micro_laws (Ide.values I) (Ide.micro I)).
Context (HW : TabWeight.laws (Ide.micro I)).
Context (Hclosed : Ifds.flow_closed (Ide.ifds I)).
Context (Hpost : jump_post I start J).

Local Lemma marker_internal c a next total :
  marker I start J origin c total ->
  TabPaths.annotation I c a next -> In a (Jump.arcs I) ->
  Jump.kind a = Icfg.Internal ->
  marker I start J origin next (Micro.compose (Ide.micro I) (Jump.weight a) total).
Proof.
  intros [current [f [fs [Hroot [Hsupported [Hf [Hsaved Htotal]]]]]]]
    Hannotation Ha Hkind.
  destruct (TabPaths.annotation_shape I c a next Hannotation) as [Hsource [Htarget Hstack]].
  pose proof (TabPaths.annotation_supported I c a next Hclosed Hsupported Hannotation)
    as Hnext.
  rewrite Hkind in Hstack; rewrite <- Hsource in Hf.
  exists current, (Micro.compose (Ide.micro I) (Jump.weight a) f), fs.
  split; [exact Hroot|]; split; [exact Hnext|]; split.
  - rewrite <- Htarget.
    eapply leb_trans; [exact (lat_ok _ _ HM)| |].
    + apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|exact Hf].
    + apply (Hpost (Jump.Path current a)), Jump.rows_spec; right; right; left.
      exists current, a; repeat split; assumption || reflexivity.
  - split; [rewrite Hstack; exact Hsaved|].
    eapply leb_trans; [exact (lat_ok _ _ HM)| |].
    + apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|exact Htotal].
    + exact (proj2 (plug_compose (Ide.values I) (Ide.micro I) HM HW fs
        (Jump.weight a) f)).
Qed.

Local Lemma marker_call c a next total p :
  marker I start J origin c total ->
  TabPaths.annotation I c a next -> In a (Jump.arcs I) ->
  Jump.kind a = Icfg.Call p ->
  marker I start J origin next (Micro.compose (Ide.micro I) (Jump.weight a) total).
Proof.
  intros [current [f [fs [Hroot [Hsupported [Hf [Hsaved Htotal]]]]]]]
    Hannotation Ha Hkind.
  destruct (TabPaths.annotation_shape I c a next Hannotation) as [Hsource [Htarget Hstack]].
  pose proof (TabPaths.annotation_supported I c a next Hclosed Hsupported Hannotation)
    as Hnext.
  rewrite Hkind in Hstack; rewrite <- Hsource in Hf.
  assert (Hentry : In (Jump.target a) (TabPaths.roots I start)).
  { apply TabPaths.call_target_root with (p := p); assumption. }
  exists (Jump.target a), (Micro.id (Ide.micro I)), (Frame current f a :: fs).
  split; [exact Hentry|]; split; [exact Hnext|]; split.
  - rewrite <- Htarget; exact (TabPaths.root_identity I start J (Jump.target a) Hpost Hentry).
  - split.
    + cbn [saved]; exists p, (snd c); repeat split; assumption || reflexivity.
    + cbn [plug before call].
      eapply leb_trans; [exact (lat_ok _ _ HM)| |].
      * apply (compose_mono _ _ HM);
          [apply leb_refl; exact (lat_ok _ _ HM)|exact Htotal].
      * eapply leb_trans; [exact (lat_ok _ _ HM)| |].
        -- exact (proj2 (plug_compose (Ide.values I) (Ide.micro I) HM HW fs
             (Jump.weight a) f)).
        -- apply (plug_mono (Ide.values I) (Ide.micro I) HM).
           exact (proj2 (TabWeight.unit_left HW
             (Micro.compose (Ide.micro I) (Jump.weight a) f))).
Qed.

Local Lemma return_segment_bound fr a f p :
  In (outer fr) (TabPaths.roots I start) -> In (call fr) (Jump.arcs I) ->
  In a (Jump.arcs I) -> Jump.kind (call fr) = Icfg.Call p ->
  Jump.kind a = Icfg.Return p ->
  leb (Micro.lat (Ide.micro I)) f (J (Jump.target (call fr), Jump.source a)) = true ->
  leb (Micro.lat (Ide.micro I)) (before fr) (J (outer fr, Jump.source (call fr))) = true ->
  leb (Micro.lat (Ide.micro I))
    (Micro.compose (Ide.micro I) (Jump.weight a)
      (Micro.compose (Ide.micro I) f
        (Micro.compose (Ide.micro I) (Jump.weight (call fr)) (before fr))))
    (J (outer fr, Jump.target a)) = true.
Proof.
  intros Houter Hcall Ha Hcallkind Hkind Hf Hbefore.
  eapply leb_trans; [exact (lat_ok _ _ HM)| |].
  - apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|].
    apply (compose_mono _ _ HM); [exact Hf|].
    apply (compose_mono _ _ HM); [apply leb_refl; exact (lat_ok _ _ HM)|exact Hbefore].
  - apply (Hpost (Jump.Return (outer fr) (call fr) a)), Jump.rows_spec.
    right; right; right.
    exists (outer fr), (call fr), a; repeat split; try assumption; try reflexivity.
    rewrite Jump.matches_c_value, Hcallkind, Hkind; apply eqb_refl.
Qed.

Local Lemma marker_return c a next total p :
  marker I start J origin c total ->
  TabPaths.annotation I c a next -> In a (Jump.arcs I) ->
  Jump.kind a = Icfg.Return p ->
  marker I start J origin next (Micro.compose (Ide.micro I) (Jump.weight a) total).
Proof.
  intros [current [f [fs [Hroot [Hsupported [Hf [Hsaved Htotal]]]]]]]
    Hannotation Ha Hkind.
  destruct (TabPaths.annotation_shape I c a next Hannotation) as [Hsource [Htarget Hstack]].
  pose proof (TabPaths.annotation_supported I c a next Hclosed Hsupported Hannotation)
    as Hnext.
  rewrite Hkind in Hstack; rewrite <- Hsource in Hf.
  destruct fs as [|fr rest].
  - cbn [saved] in Hsaved; destruct Hsaved as [Hempty Hcurrent].
    rewrite Hstack in Hempty; discriminate.
  - cbn [saved] in Hsaved.
    destruct Hsaved as
      [q [tail [Hstackcall [Hcallkind [Hcurrent [Houter [Hcall [Hbefore Hrest]]]]]]]].
    rewrite Hstack in Hstackcall; injection Hstackcall as Hsite Htail.
    subst q tail current.
    exists (outer fr),
      (Micro.compose (Ide.micro I) (Jump.weight a)
        (Micro.compose (Ide.micro I) f
          (Micro.compose (Ide.micro I) (Jump.weight (call fr)) (before fr)))), rest.
    split; [exact Houter|]; split; [exact Hnext|]; split.
    + rewrite <- Htarget; apply (return_segment_bound fr a f p); assumption.
    + split; [exact Hrest|].
      cbn [plug] in Htotal.
      eapply leb_trans; [exact (lat_ok _ _ HM)| |].
      * apply (compose_mono _ _ HM);
          [apply leb_refl; exact (lat_ok _ _ HM)|exact Htotal].
      * exact (proj2 (plug_compose (Ide.values I) (Ide.micro I) HM HW rest
          (Jump.weight a) (Micro.compose (Ide.micro I) f
            (Micro.compose (Ide.micro I) (Jump.weight (call fr)) (before fr))))).
Qed.

Local Lemma marker_step c a next total :
  marker I start J origin c total ->
  TabPaths.annotation I c a next -> In a (Jump.arcs I) ->
  marker I start J origin next (Micro.compose (Ide.micro I) (Jump.weight a) total).
Proof.
  intros Hmarker Hannotation Ha.
  destruct (Jump.kind a) as [|p|p] eqn:Hkind.
  - apply (marker_internal c a next total); assumption.
  - apply (marker_call c a next total p); assumption.
  - apply (marker_return c a next total p); assumption.
Qed.

Local Lemma trace_marker c as_ next :
  TabPaths.trace I c as_ next -> Forall (fun a => In a (Jump.arcs I)) as_ ->
  forall total, marker I start J origin c total ->
    marker I start J origin next (TabWeight.fold (Ide.micro I) as_ total).
Proof.
  intro Htrace; induction Htrace as [c|c a mid as_ next Hstep Htrace IH];
    intros Hmembers total Hmarker.
  - exact Hmarker.
  - inversion Hmembers as [|a' rest Ha Hrest]; subst a' rest.
    rewrite TabWeight.fold_equation; apply IH; [exact Hrest|].
    apply marker_step with (c := c); assumption.
Qed.

Local Lemma marker_initial :
  In origin (TabPaths.roots I start) -> Ifds.seed_supported (Ide.ifds I) origin ->
  marker I start J origin (fst origin, snd origin, []) (Micro.id (Ide.micro I)).
Proof.
  intros Hroot Hsupported; destruct origin as [r x].
  exists (r, x), (Micro.id (Ide.micro I)), []; split; [exact Hroot|].
  split; [exact Hsupported|]; split.
  - apply TabPaths.root_identity with (start := start); assumption.
  - split; [split; reflexivity|apply leb_refl; exact (lat_ok _ _ HM)].
Qed.

(** Every balanced annotated execution is bounded in symbolic function order. *)
Theorem balanced_trace_sound n d as_ :
  In origin (TabPaths.roots I start) -> Ifds.seed_supported (Ide.ifds I) origin ->
  TabPaths.trace I (fst origin, snd origin, []) as_ (n, d, []) ->
  Forall (fun a => In a (Jump.arcs I)) as_ ->
  leb (Micro.lat (Ide.micro I)) (TabWeight.weight I as_) (J (origin, (n, d))) = true.
Proof.
  intros Hroot Hsupported Htrace Hmembers.
  pose proof (marker_initial Hroot Hsupported) as Hinitial.
  pose proof (trace_marker _ _ _ Htrace Hmembers _ Hinitial) as Hfinal.
  destruct Hfinal as [current [f [fs [Hentry [Hfact [Hf [Hsaved Htotal]]]]]]].
  destruct fs as [|fr rest].
  - cbn [saved fst snd] in Hsaved; destruct Hsaved as [Hempty Hcurrent]; subst current.
    rewrite TabWeight.weight_fold.
    eapply leb_trans; [exact (lat_ok _ _ HM)|exact Htotal|exact Hf].
  - cbn [saved fst snd] in Hsaved.
    destruct Hsaved as [p [tail [Hbad Hrest]]]; discriminate Hbad.
Qed.

(** Original balanced paths receive annotations and the bound for that same execution. *)
Theorem balanced_path_sound n d :
  In origin (TabPaths.roots I start) -> Ifds.seed_supported (Ide.ifds I) origin ->
  Stack.balanced (Ide.ifds I) (fst origin) (snd origin) n d ->
  exists as_, TabPaths.trace I (fst origin, snd origin, []) as_ (n, d, []) /\
    Forall (fun a => In a (Jump.arcs I)) as_ /\
    leb (Micro.lat (Ide.micro I)) (TabWeight.weight I as_) (J (origin, (n, d))) = true.
Proof.
  intros Hroot Hsupported Hpath.
  destruct (TabPaths.trace_complete I (fst origin, snd origin, []) (n, d, [])
    Hclosed Hsupported Hpath) as
    [as_ [Htrace Hmembers]].
  exists as_; split; [exact Htrace|]; split; [exact Hmembers|].
  apply balanced_trace_sound; assumption.
Qed.

Section Values.
Context (jump_c : jkey N D -> Cost.t F) (a0 : A) (sigma : (N * option D) -> A).
Context (Hread : forall k, Cost.value (jump_c k) = J k).
Context (HN : encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))).
Context (HE : encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))).
Context (HD : encoding_laws (Ifds.fact_enc (Ide.ifds I))).
Context (HL : lattice_laws (Ide.values I)).
Context (Hstart : fst origin = start).
Context (Hvalues : post_solution (Ide.values I)
  (Analysis.system (value_analysis I jump_c origin a0)) sigma).
Context (Hsources : forall a, In a (Jump.arcs I) -> In (Jump.source a) (IdeValue.vertices I)).

Local Lemma summary_value current v f b :
  In current (TabPaths.roots I start) -> In v (IdeValue.vertices I) ->
  leb (Micro.lat (Ide.micro I)) f (J (current, v)) = true ->
  leb (Ide.values I) b (sigma current) = true ->
  leb (Ide.values I) (Micro.apply (Ide.micro I) f b) (sigma v) = true.
Proof.
  intros Hroot Hv Hf Hb.
  pose proof (proj1 (value_analysis_post_solution_iff I jump_c origin a0 sigma HN HE HD)
    Hvalues) as Hrows.
  destruct Hrows as [Hseed [Hjumps Hcalls]]; rewrite Hstart in Hjumps.
  eapply leb_trans; [exact HL|apply (apply_mono _ _ HM); exact Hb|].
  eapply leb_trans; [exact HL|apply (apply_order HM); exact Hf|].
  specialize (Hjumps current v Hroot Hv); rewrite Hread in Hjumps; exact Hjumps.
Qed.

Local Lemma call_value a p b :
  In a (Jump.arcs I) -> Jump.kind a = Icfg.Call p ->
  leb (Ide.values I) b (sigma (Jump.source a)) = true ->
  leb (Ide.values I) (Micro.apply (Ide.micro I) (Jump.weight a) b)
    (sigma (Jump.target a)) = true.
Proof.
  intros Ha Hkind Hb.
  pose proof (proj1 (value_analysis_post_solution_iff I jump_c origin a0 sigma HN HE HD)
    Hvalues) as Hrows.
  eapply leb_trans; [exact HL|apply (apply_mono _ _ HM); exact Hb|].
  apply (proj2 (proj2 Hrows) a p Ha Hkind).
Qed.

Local Lemma plug_apply (fs : list (frame N E P D F)) f g :
  leb (Ide.values I)
    (Micro.apply (Ide.micro I) (plug (Ide.micro I) fs (Micro.compose (Ide.micro I) f g)) a0)
    (Micro.apply (Ide.micro I) f
      (Micro.apply (Ide.micro I) (plug (Ide.micro I) fs g) a0)) = true.
Proof.
  eapply leb_trans; [exact HL| |].
  - apply (apply_order HM).
    exact (proj1 (plug_compose (Ide.values I) (Ide.micro I) HM HW fs f g)).
  - exact (proj1 (compose_apply _ _ HM f (plug (Ide.micro I) fs g) a0)).
Qed.

Local Lemma saved_value fs current stack f v :
  saved I start J origin current fs stack ->
  In current (TabPaths.roots I start) -> In v (IdeValue.vertices I) ->
  leb (Micro.lat (Ide.micro I)) f (J (current, v)) = true ->
  leb (Ide.values I) (Micro.apply (Ide.micro I) (plug (Ide.micro I) fs f) a0)
    (sigma v) = true.
Proof.
  revert current stack f v; induction fs as [|fr fs IH]; intros current stack f v
    Hsaved Hroot Hv Hf; cbn [saved] in Hsaved.
  - destruct Hsaved as [Hempty Hcurrent]; subst current.
    apply summary_value with (current := origin); try assumption.
    exact (proj1 (proj1 (value_analysis_post_solution_iff I jump_c origin a0 sigma HN HE HD)
      Hvalues)).
  - destruct Hsaved as
      [p [tail [Hstack [Hkind [Hcurrent [Houter [Hcall [Hbefore Hrest]]]]]]]].
    subst current; cbn [plug].
    eapply leb_trans; [exact HL|exact (plug_apply fs f
      (Micro.compose (Ide.micro I) (Jump.weight (call fr)) (before fr)))|].
    apply summary_value with (current := Jump.target (call fr)); try assumption.
    eapply leb_trans; [exact HL|exact (plug_apply fs (Jump.weight (call fr)) (before fr))|].
    apply call_value with (p := p); try assumption.
    apply (IH (outer fr) tail (before fr) (Jump.source (call fr)));
      try assumption.
    apply Hsources; exact Hcall.
Qed.

(** Every marked prefix is value-sound through its actual suspended callers. *)
Local Lemma marker_value c total :
  marker I start J origin c total -> In (fst c) (IdeValue.vertices I) ->
  leb (Ide.values I) (Micro.apply (Ide.micro I) total a0) (sigma (fst c)) = true.
Proof.
  intros [current [f [fs [Hroot [Hsupported [Hf [Hsaved Htotal]]]]]]] Hv.
  eapply leb_trans; [exact HL|apply (apply_order HM); exact Htotal|].
  apply (saved_value fs current (snd c) f (fst c)); assumption.
Qed.

(** Annotated prefixes are sound without requiring their pending calls to return. *)
Theorem prefix_trace_sound n d stack as_ :
  In origin (TabPaths.roots I start) -> Ifds.seed_supported (Ide.ifds I) origin ->
  TabPaths.trace I (fst origin, snd origin, []) as_ (n, d, stack) ->
  Forall (fun a => In a (Jump.arcs I)) as_ ->
  In (n, d) (IdeValue.vertices I) ->
  leb (Ide.values I) (Micro.apply (Ide.micro I) (TabWeight.weight I as_) a0)
    (sigma (n, d)) = true.
Proof.
  intros Hroot Hsupported Htrace Hmembers Hv; rewrite TabWeight.weight_fold.
  pose proof (trace_marker _ _ _ Htrace Hmembers _ (marker_initial Hroot Hsupported)) as Hmarker.
  apply (marker_value (n, d, stack) _ Hmarker); exact Hv.
Qed.

End Values.

(** Original arbitrary prefixes are value-sound, including an unlisted zero-step seed. *)
Theorem prefix_path_sound (jump_c : jkey N D -> Cost.t F) a0 sigma :
  (forall k, Cost.value (jump_c k) = J k) ->
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Ide.values I) -> fst origin = start ->
  post_solution (Ide.values I) (Analysis.system (value_analysis I jump_c origin a0)) sigma ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  In origin (TabPaths.roots I start) -> Ifds.seed_supported (Ide.ifds I) origin ->
  forall n d stack, Stack.path (Ide.ifds I) (fst origin, snd origin, []) (n, d, stack) ->
    exists as_, TabPaths.trace I (fst origin, snd origin, []) as_ (n, d, stack) /\
      Forall (fun a => In a (Jump.arcs I)) as_ /\
      leb (Ide.values I) (Micro.apply (Ide.micro I) (TabWeight.weight I as_) a0)
        (sigma (n, d)) = true.
Proof.
  intros Hread HN HE HD HL Hstart Hvalues HG Hroot Hsupported n d stack Hpath.
  destruct (TabPaths.trace_complete I (fst origin, snd origin, []) (n, d, stack)
    Hclosed Hsupported Hpath) as [as_ [Htrace Hmembers]].
  exists as_; split; [exact Htrace|]; split; [exact Hmembers|].
  destruct as_ as [|a rest].
  - assert (Hsame : (fst origin, snd origin, []) = (n, d, stack)).
    { inversion Htrace; reflexivity. }
    injection Hsame as Hn Hd Hstack.
    assert (Hvertex : (n, d) = origin).
    { destruct origin as [r x]; cbn [fst snd] in Hn, Hd; subst n d; reflexivity. }
    rewrite TabWeight.weight_nil, Hvertex.
    eapply leb_trans; [exact HL|exact (proj1 (id_apply _ _ HM a0))|].
    exact (proj1 (proj1 (value_analysis_post_solution_iff I jump_c origin a0 sigma HN HE HD)
      Hvalues)).
  - apply (prefix_trace_sound jump_c a0 sigma Hread HN HE HD HL Hstart Hvalues
      (fun call Hcall => proj1 (TabPaths.arc_vertices I call HG Hclosed Hcall))
      n d stack (a :: rest)).
    + exact Hroot.
    + exact Hsupported.
    + exact Htrace.
    + exact Hmembers.
    + exact (TabPaths.trace_nonempty_vertices I _ _ _ HG Hclosed Htrace Hmembers
        ltac:(discriminate)).
Qed.

End Soundness.

End TabJumpPaths.
