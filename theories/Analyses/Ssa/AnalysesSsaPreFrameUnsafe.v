(** * Exact unsafe marks in the actual scoped walk

    Unsafe seeds record nearest unused phis observed at exits or unmatched killing instructions.
    For example, a join phi with no real use is marked when its block reaches an exit.
    Builds on: AnalysesSsaPreFrameWalk, AnalysesSsaPreFrameInvariant and the actual cache equations. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIntern BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep AnalysesSsaPreFrameEnd
  AnalysesSsaPreFrameCache AnalysesSsaPreFrameInvariant AnalysesSsaPreFrameDominance
  AnalysesSsaPreFrameTables AnalysesSsaPreFrameWalk AnalysesSsaPreFrameHistory AnalysesSsaPreFrameVisit.
Import List.ListNotations.

Module PreFrameUnsafe.

(** A history accumulates exactly the events contributed by its executed local steps. *)
Theorem history_membership {S L} (step : S -> L -> S -> Prop) (member : S -> Prop)
    (event : L -> Prop) :
  forall source labels target, PreFrameStep.history step source labels target ->
  (forall before label after, In label labels -> step before label after ->
    (member after <-> member before \/ event label)) ->
    (member target <-> member source \/ exists label, In label labels /\ event label).
Proof.
  intros source labels target Hhistory; induction Hhistory as
    [source|source label next rest target Hexecuted Hhistory IH]; intro Hstep.
  - split; [auto|intros [Hmember|[label [[] Hevent]]]; exact Hmember].
  - rewrite (IH (fun before edge after Hin Hlocal => Hstep before edge after (or_intror Hin) Hlocal)).
    rewrite (Hstep _ _ _ (or_introl eq_refl) Hexecuted); cbn [In].
    split.
    + intros [[Hmember|Hevent]|[edge [Hin Hevent]]].
      * now left.
      * right; exists label; auto.
      * right; exists edge; auto.
    + intros [Hmember|[edge [[<-|Hin] Hevent]]].
      * now left; left.
      * now left; right.
      * right; exists edge; auto.
Qed.

Section Events.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Context {g : PreFrg.frg B BE E U}.
Hypothesis Hlaw : Pre.laws c.
Hypothesis Hdata : PreFrameCache.placement_laws c data.
Hypothesis Hversions :
  forall d, In d (PreFrg.versions g) -> PreFrameInvariant.source_version c d.
Let index := PreRename.prepare c data.
Let bank := PreFrameCache.names c data.
Let points := Pre.points (Pre.input c).

(** An unused phi is nearest at this point and has no dominating real occurrence. *)
Definition phi_unused n b u : Prop :=
  PreRename.nearest_version c g u n (PreFrg.Phi b u) /\
    PreRename.no_dominating_real_use c g n (PreFrg.Phi b u).

(** Unsafe observations are explicit exits, terminal points or unmatched outgoing kills. *)
Definition unsafe_event n u : Prop :=
  Pre.exit_point c n = true \/ Graph.out (Pre.pg c) n = [] \/
    exists e, In e (Graph.out (Pre.pg c) n) /\
      Pre.killed c e u = true /\ Pre.recomputed c e <> Some u.

(** An instruction contributes its source kill and its target exit observation. *)
Definition instruction_event e b u : Prop :=
  (Pre.killed c e u = true /\ Pre.recomputed c e <> Some u /\
    phi_unused (Graph.source (Pre.pg c) e) b u) \/
  ((Pre.exit_point c (Graph.target (Pre.pg c) e) = true \/
    Graph.out (Pre.pg c) (Graph.target (Pre.pg c) e) = []) /\
    phi_unused (Graph.target (Pre.pg c) e) b u).

(** A block contributes the unsafe observations at its own listed points. *)
Definition block_event owner b u : Prop :=
  exists n, In n (SsaPoints.points_in_block points owner) /\
    phi_unused n b u /\ unsafe_event n u.

(** Mark membership observes the actual accumulator's unsafe index. *)
Definition marked (acc : PreRename.accumulator B BE E U) b u :=
  FinSet.mem (PreFrg.phi_encoding c) (b, u) (PreRename.unsafe_index acc) = true.

Local Lemma unused_family {n b u} :
  phi_unused n b u -> PreFamily.in_family c u /\ Pre.pure c u = true.
Proof.
  intros [[Hd Hrest] Hnone].
  exact (conj (proj1 (Hversions _ Hd)) (proj1 (proj2 (Hversions _ Hd)))).
Qed.

Local Lemma frame_phi_exact {n b u frame} :
  In n (Graph.nodes (Pre.pg c)) -> PreCoverage.frame_laws c g u n frame ->
    (PreRename.selected frame = PreFrg.Operand (PreFrg.Phi b u) false <-> phi_unused n b u).
Proof.
  intros Hn Hframe; pose proof (proj2 (proj2 Hframe)) as Hmeaning; split.
  - intro Heq; unfold phi_unused.
    rewrite Heq in Hmeaning; rewrite PreFrg.version_point_equation in Hmeaning.
    split; [exact (proj1 Hmeaning)|].
    intros e Hget Hdom.
    pose proof (proj1 (proj2 Hframe)) as Hreal; rewrite Heq in Hreal.
    pose proof (proj2 Hreal (ex_intro _ e (conj Hget Hdom))) as Htrue; discriminate.
  - intros [Hnearest Hnone].
    destruct (PreFrg.version_point c (PreFrg.operand_version (PreRename.selected frame)))
      as [q|] eqn:Hpoint.
    + assert (Hversion : PreFrg.operand_version (PreRename.selected frame) = PreFrg.Phi b u).
      { apply (PreRename.nearest_version_unique c g Hlaw) with (u := u) (n := n).
        - intros d Hd; exact (proj2 (proj2 (Hversions d Hd))).
        - exact (Pre.reachable_points c (Pre.graphs c Hlaw) n Hn).
        - exact (proj1 Hmeaning).
        - exact Hnearest. }
      assert (Hreal : PreFrg.real_use (PreRename.selected frame) = false).
      { destruct (PreFrg.real_use (PreRename.selected frame)) eqn:Hreal; [|reflexivity].
        destruct (proj1 (proj1 (proj2 Hframe)) Hreal) as [e [Hget Hdom]].
        rewrite Hversion in Hget; exfalso; exact (Hnone e Hget Hdom). }
      destruct (PreRename.selected frame) as [d real]; cbn in Hversion, Hreal; subst; reflexivity.
    + destruct Hmeaning as [Hmissing [Hfalse Habsent]].
      destruct Hnearest as [Hd [Hu [q [Hq [Hdom Hnearest]]]]].
      exfalso; exact (Habsent _ q Hd Hu Hq Hdom).
Qed.

Local Lemma named_top {frames id u} :
  PreFrameInvariant.scope_source c data frames -> Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    PreRename.top_id frames id u = PreRename.top c frames u.
Proof.
  intros Hsource Hid; symmetry; apply PreFrameCache.top_id_agrees.
  rewrite (PreFrameInvariant.scope_symbols c data frames Hsource); exact Hid.
Qed.

Local Lemma mark_exact frames acc key b u :
  PreFrameEnd.accumulator_wf c acc ->
    (marked (PreRename.mark c frames acc key) b u <->
      marked acc b u \/
      PreRename.selected (PreRename.top_id frames (fst key) (snd key)) =
        PreFrg.Operand (PreFrg.Phi b u) false).
Proof.
  intro Hwf; unfold marked; rewrite PreRename.mark_equation.
  destruct (PreRename.selected (PreRename.top_id frames (fst key) (snd key))) as [d real].
  destruct d as [v|v|e v|owner v], real; cbn [PreRename.unsafe_index];
    try (split; [auto|intros [Hmark|Hbad]; [exact Hmark|discriminate]]).
  rewrite FinSet.mem_add by exact (proj2 (proj2 (proj2 Hwf))).
  rewrite orb_true_iff, (eqb_true_iff _ (PreFrg.phi_encoding_laws c Hlaw)).
  split.
  - intros [Heq|Hmark]; [right; inversion Heq; reflexivity|now left].
  - intros [Hmark|Heq]; [now right|left; inversion Heq; reflexivity].
Qed.

Local Lemma marks_exact frames :
  forall keys acc b u, PreFrameEnd.accumulator_wf c acc ->
    (marked (fold_left (PreRename.mark c frames) keys acc) b u <-> marked acc b u \/
      exists key, In key keys /\ PreRename.selected
        (PreRename.top_id frames (fst key) (snd key)) = PreFrg.Operand (PreFrg.Phi b u) false).
Proof.
  intro keys; induction keys as [|key rest IH]; intros acc b u Hwf.
  - cbn [fold_left]; split; [auto|intros [Hmark|[key [[] Htop]]]; exact Hmark].
  - cbn [fold_left]; rewrite IH, mark_exact by
      (assumption || apply PreFrameEnd.mark_wf; exact Hwf).
    split.
    + intros [[Hmark|Htop]|[other [Hin Htop]]].
      * now left.
      * right; exists key; split; [now left|exact Htop].
      * right; exists other; split; [now right|exact Htop].
    + intros [Hmark|[other [[<-|Hin] Htop]]].
      * now left; left.
      * now left; right.
      * right; exists other; auto.
Qed.

(** Exit marking adds precisely the nearest unused phi frames at that same point. *)
Theorem exit_exact n frames acc b u :
  In n (Graph.nodes (Pre.pg c)) -> PreFrameInvariant.scope_source c data frames ->
  PreFrameEnd.accumulator_wf c acc -> PreCoverage.scope_laws c g n frames ->
    (marked (snd (PreRename.mark_exit c index n (frames, acc))) b u <->
      marked acc b u \/ ((Pre.exit_point c n = true \/ Graph.out (Pre.pg c) n = []) /\
        phi_unused n b u)).
Proof.
  intros Hn Hsource Hwf Hscope; rewrite PreRename.mark_exit_equation.
  assert (Hexits := PreFrameCache.exits_exact c data Hlaw n).
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index)) eqn:Hexit.
  - cbn [snd]; rewrite marks_exact by exact Hwf; split.
    + intros [Hmark|[[id v] [Hin Htop]]]; [now left|].
      apply (PreFrameCache.family_ids_exact c data Hlaw) in Hin.
      destruct (proj1 (PreFrameCache.names_domain c data Hlaw Hdata v) (ex_intro _ id Hin))
        as [Hfamily Hpure].
      cbn [fst snd] in Htop.
      rewrite (named_top Hsource Hin) in Htop.
      pose proof (proj1 (Hscope v Hfamily Hpure)) as Hexpr.
      rewrite Htop in Hexpr; cbn [PreFrg.operand_version PreFrg.version_expr] in Hexpr; subst v.
      right; split; [apply Hexits in Hexit; exact (proj2 Hexit)|].
      apply (frame_phi_exact Hn (Hscope u Hfamily Hpure)); exact Htop.
    + intros [Hmark|[Hending Hphi]]; [now left|].
      destruct (unused_family Hphi) as [Hfamily Hpure].
      destruct (proj2 (PreFrameCache.names_domain c data Hlaw Hdata u) (conj Hfamily Hpure))
        as [id Hid].
      right; exists (id, u); split.
      * apply (PreFrameCache.family_ids_exact c data Hlaw); exact Hid.
      * cbn [fst snd]; rewrite (named_top Hsource Hid).
        apply (frame_phi_exact Hn (Hscope u Hfamily Hpure)); exact Hphi.
  - cbn [snd]; split; [auto|intros [Hmark|[Hending Hphi]]; [exact Hmark|]].
    assert (Htrue : FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index) = true).
    { apply Hexits; auto. }
    congruence.
Qed.

Local Lemma instance_different e id u :
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
  ((match PreRename.evaluation (PreFrameCache.event_description c bank e) with
    | None => false
    | Some current => eqb positive_encoding (fst current) id
    end) = false <-> Pre.recomputed c e <> Some u).
Proof.
  intro Hid; destruct (PreRename.evaluation (PreFrameCache.event_description c bank e))
    as [[other v]|] eqn:Hinstance.
  - destruct (proj1 (PreFrameCache.evaluation_exact c bank e) Hinstance)
      as [Hcomputed [Hpure Hfind]].
    cbn [fst]; rewrite (eqb_false_iff _ positive_encoding_laws).
    split; intros Hne Heq; apply Hne.
    + assert (Hv : v = u) by congruence; subst v; congruence.
    + subst other.
      pose proof (Intern.key_of_find _ _ _ _ (PreFrameCache.names_wf c data Hlaw) Hid).
      pose proof (Intern.key_of_find _ _ _ _ (PreFrameCache.names_wf c data Hlaw) Hfind).
      assert (Hv : v = u) by congruence; congruence.
  - split; [|intros _; reflexivity]; intros _ Hcomputed.
    destruct (proj1 (PreFrameCache.names_domain c data Hlaw Hdata u) (ex_intro _ id Hid))
      as [Hfamily Hpure].
    destruct (PreFrameCache.evaluation_available c data Hlaw Hdata e u Hcomputed Hpure)
      as [found [Heval Hfind]]; fold bank in Heval; congruence.
Qed.

Local Lemma alter_selected instance frames acc id v u :
  PreFrameInvariant.scope_source c data frames ->
  Intern.find (Pre.eu (Pre.keys c)) v bank = Some id ->
    PreRename.selected (PreRename.top c
      (fst (PreRename.alter c instance (frames, acc) (id, v))) u) =
      PreRename.selected (PreRename.top c frames u).
Proof.
  intros Hframes Hid; rewrite (PreFrameInvariant.alter_top c data Hlaw Hframes Hid u).
  destruct (eqb (Pre.eu (Pre.keys c)) u v); reflexivity.
Qed.

Local Lemma alters_exact e :
  forall changes frames acc b u,
    Forall (fun key => Intern.find (Pre.eu (Pre.keys c)) (snd key) bank = Some (fst key)) changes ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    (marked (snd (fold_left (PreRename.alter c
      (PreRename.evaluation (PreFrameCache.event_description c bank e))) changes (frames, acc))) b u
      <-> marked acc b u \/ exists v id, In (id, v) changes /\
        Pre.recomputed c e <> Some v /\
        PreRename.selected (PreRename.top c frames v) = PreFrg.Operand (PreFrg.Phi b u) false).
Proof.
  intro changes; induction changes as [|[id v] rest IH]; intros frames acc b u Hchanges Hframes Hwf.
  - cbn [fold_left snd]; split; [auto|intros [Hmark|[v [id [[] Hrest]]]]; exact Hmark].
  - inversion Hchanges as [|key tail Hid Hrest]; subst key tail; cbn [fst snd] in Hid.
    pose proof (PreFrameInvariant.alter_source c data Hlaw frames acc
      (PreRename.evaluation (PreFrameCache.event_description c bank e)) id v Hframes Hid) as Hnew.
    pose proof (PreFrameEnd.alter_wf c (work := (frames, acc))
      (instance := PreRename.evaluation (PreFrameCache.event_description c bank e))
      (key := (id, v)) Hwf) as Hnew_wf.
    cbn [fold_left]; rewrite PreRename.alter_equation in Hnew, Hnew_wf |- *.
    cbn [fst snd] in Hnew, Hnew_wf |- *.
    rewrite IH by assumption.
    set (same := match PreRename.evaluation (PreFrameCache.event_description c bank e) with
      | None => false
      | Some current => eqb positive_encoding (fst current) id
      end).
    assert (Hone : marked
      (if same then acc else PreRename.mark c frames acc (id, v)) b u <->
      marked acc b u \/ (Pre.recomputed c e <> Some v /\
        PreRename.selected (PreRename.top c frames v) = PreFrg.Operand (PreFrg.Phi b u) false)).
    { pose proof (instance_different e id v Hid) as Hsame; fold same in Hsame.
      destruct same eqn:Hflag.
      - split; [auto|intros [Hmark|[Hne Htop]]; [exact Hmark|]].
        apply Hsame in Hne; discriminate.
      - rewrite mark_exact by exact Hwf; cbn [fst snd]; rewrite (named_top Hframes Hid).
        assert (Hdifferent : Pre.recomputed c e <> Some v) by (apply Hsame; reflexivity).
        tauto. }
    rewrite Hone.
    assert (Hselected : forall value, PreRename.selected
      (PreRename.top c (PreRename.store frames id
        (PreRename.Frame (PreRename.selected (PreRename.top_id frames id v)) false)) value) =
      PreRename.selected (PreRename.top c frames value)).
    { intro value; pose proof (alter_selected
        (PreRename.evaluation (PreFrameCache.event_description c bank e))
        frames acc id v value Hframes Hid) as Hselected.
      rewrite PreRename.alter_equation in Hselected; exact Hselected. }
    split.
    + intros [[Hmark|[Hne Htop]]|[value [other [Hin [Hne Htop]]]]].
      * now left.
      * right; exists v, id; split; [now left|auto].
      * right; exists value, other; rewrite Hselected in Htop; split; [now right|auto].
    + intros [Hmark|[value [other [[Heq|Hin] [Hne Htop]]]]].
      * now left; left.
      * inversion Heq; subst other value; left; right; auto.
      * right; exists value, other; rewrite Hselected; auto.
Qed.

Local Lemma event_names e id v :
  PreRename.evaluation (PreFrameCache.event_description c bank e) = Some (id, v) ->
    Intern.find (Pre.eu (Pre.keys c)) v bank = Some id.
Proof.
  intro Hinstance; apply PreFrameCache.evaluation_exact in Hinstance; tauto.
Qed.

Local Lemma occurrence_unsafe e instance frames acc :
  PreRename.unsafe_index (snd (fst (PreRename.occurrence c e instance (frames, acc)))) =
    PreRename.unsafe_index acc.
Proof.
  rewrite PreRename.occurrence_equation; destruct instance as [[id v]|]; [|reflexivity].
  cbn zeta; destruct (PreRename.frame_reuse c (PreRename.top_id frames id v) v); reflexivity.
Qed.

Local Lemma occurrence_other e frames acc v :
  PreFrameInvariant.scope_source c data frames -> Pre.recomputed c e <> Some v ->
    PreRename.selected (PreRename.top c (fst (fst (PreRename.occurrence c e
      (PreRename.evaluation (PreFrameCache.event_description c bank e)) (frames, acc)))) v) =
    PreRename.selected (PreRename.top c frames v).
Proof.
  intros Hsource Hne.
  rewrite (PreFrameInvariant.occurrence_top c data Hlaw frames acc e _
    Hsource (event_names e) v).
  destruct (PreRename.evaluation (PreFrameCache.event_description c bank e))
    as [[id value]|] eqn:Hinstance; [|reflexivity].
  pose proof (proj1 (proj1 (PreFrameCache.evaluation_exact c bank e) Hinstance)) as Hcomputed.
  assert (Hdifferent : eqb (Pre.eu (Pre.keys c)) v value = false).
  { apply (eqb_false_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))).
    intro Heq; subst value; contradiction. }
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id value) value);
    rewrite ?Hdifferent; reflexivity.
Qed.

(** Actual killing lists mark precisely unused source phis not recomputed by this instruction. *)
Theorem kills_exact e frames acc b u :
  In e (Cfg.edges (Pre.point_cfg c)) -> PreFrameInvariant.scope_source c data frames ->
  PreFrameEnd.accumulator_wf c acc ->
  PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) frames ->
    (marked (snd (fold_left (PreRename.alter c
      (PreRename.evaluation (PreFrameCache.event_description c bank e)))
      (PreRename.alterations (PreFrameCache.event_description c bank e))
      (fst (PreRename.occurrence c e
        (PreRename.evaluation (PreFrameCache.event_description c bank e)) (frames, acc))))) b u <->
      marked acc b u \/ (Pre.killed c e u = true /\ Pre.recomputed c e <> Some u /\
        phi_unused (Graph.source (Pre.pg c) e) b u)).
Proof.
  intros He Hsource Hwf Hscope.
  set (observed := fst (PreRename.occurrence c e
    (PreRename.evaluation (PreFrameCache.event_description c bank e)) (frames, acc))).
  assert (Hobserved : PreFrameInvariant.scope_source c data (fst observed)).
  { exact (PreFrameInvariant.occurrence_source c data Hlaw frames acc e _
      Hsource (event_names e)). }
  assert (Hobserved_wf : PreFrameEnd.accumulator_wf c (snd observed)).
  { apply PreFrameEnd.occurrence_wf; exact Hwf. }
  assert (Hchanges : Forall (fun key => Intern.find (Pre.eu (Pre.keys c)) (snd key) bank =
    Some (fst key)) (PreRename.alterations (PreFrameCache.event_description c bank e))).
  { apply Forall_forall; intros [id v] Hin; cbn [fst snd].
    apply (PreFrameCache.event_alterations c bank e Hlaw) in Hin; tauto. }
  pose proof (alters_exact e _ (fst observed) (snd observed) b u
    Hchanges Hobserved Hobserved_wf) as Hchanges_exact.
  rewrite <- surjective_pairing in Hchanges_exact.
  rewrite Hchanges_exact; unfold observed at 1; unfold marked at 1; rewrite occurrence_unsafe.
  fold (marked acc b u); split.
  - intros [Hmark|[v [id [Hin [Hne Htop]]]]]; [now left|].
    apply (PreFrameCache.event_alterations c bank e Hlaw) in Hin; destruct Hin as [Hkill Hid].
    unfold observed in Htop; rewrite (occurrence_other e frames acc v Hsource Hne) in Htop.
    destruct (proj1 (PreFrameCache.names_domain c data Hlaw Hdata v) (ex_intro _ id Hid))
      as [Hfamily Hpure].
    pose proof (proj1 (Hscope v Hfamily Hpure)) as Hexpr; rewrite Htop in Hexpr.
    cbn [PreFrg.operand_version PreFrg.version_expr] in Hexpr; subst v.
    right; split; [exact Hkill|]; split; [exact Hne|].
    apply (frame_phi_exact (proj1 (PreCoverage.listed_edge_out c Hlaw He))
      (Hscope u Hfamily Hpure)); exact Htop.
  - intros [Hmark|[Hkill [Hne Hphi]]]; [now left|].
    destruct (unused_family Hphi) as [Hfamily Hpure].
    destruct (proj2 (PreFrameCache.names_domain c data Hlaw Hdata u) (conj Hfamily Hpure))
      as [id Hid].
    right; exists u, id; split.
    + apply (PreFrameCache.event_alterations c bank e Hlaw); auto.
    + split; [exact Hne|]; unfold observed.
      rewrite (occurrence_other e frames acc u Hsource Hne).
      apply (frame_phi_exact (proj1 (PreCoverage.listed_edge_out c Hlaw He))
        (Hscope u Hfamily Hpure)); exact Hphi.
Qed.

(** Instruction marking adds exactly its unmatched source kill and its target exit events. *)
Theorem instruction_exact owner e frames acc b u :
  In owner (Graph.nodes (Pre.bg c)) ->
  In e (SsaPoints.instruction_edges points owner) ->
  PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
  PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) frames ->
  PreCoverage.scope_laws c g (Graph.target (Pre.pg c) e)
    (fst (PreRename.instruction c index owner (SsaPoints.parameter_edge points owner)
      (frames, acc) e)) ->
    (marked (snd (PreRename.instruction c index owner (SsaPoints.parameter_edge points owner)
      (frames, acc) e)) b u <-> marked acc b u \/ instruction_event e b u).
Proof.
  intros Howner Hin Hsource Hwf Hscope Hafter.
  pose proof (PreCoverage.instruction_edge_listed c Hlaw Howner Hin) as He.
  pose proof (PreFrameCache.event_lookup c data Hlaw e He) as Hlookup; fold index bank in Hlookup.
  pose proof (kills_exact e frames acc b u He Hsource Hwf Hscope) as Hkills.
  pose proof (PreFrameInvariant.instruction_source c data Hlaw Hdata owner
    (SsaPoints.parameter_edge points owner) (frames, acc) e Hsource)
    as Htarget_source.
  fold index in Htarget_source.
  rewrite PreRename.instruction_equation, Hlookup in Hafter, Htarget_source |- *.
  rewrite (PreFrameCache.event_endpoint c bank e) in Hafter, Htarget_source |- *.
  destruct (PreRename.occurrence c e (PreRename.evaluation
    (PreFrameCache.event_description c bank e)) (frames, acc)) as [[observed output] fresh]
    eqn:Hobserved.
  cbn [fst snd] in Hkills, Hafter, Htarget_source |- *.
  assert (Haltered_wf : PreFrameEnd.accumulator_wf c
    (snd (fold_left (PreRename.alter c
      (PreRename.evaluation (PreFrameCache.event_description c bank e)))
      (PreRename.alterations (PreFrameCache.event_description c bank e)) (observed, output)))).
  { apply (PreFrameStep.fold_preserves _ (fun work => PreFrameEnd.accumulator_wf c (snd work))).
    - intros work key Hwork; apply PreFrameEnd.alter_wf; exact Hwork.
    - pose proof (PreFrameEnd.occurrence_wf c (e := e) (work := (frames, acc))
        (instance := PreRename.evaluation (PreFrameCache.event_description c bank e)) Hwf) as Hnew.
      rewrite Hobserved in Hnew; exact Hnew. }
  destruct (fold_left (PreRename.alter c
    (PreRename.evaluation (PreFrameCache.event_description c bank e)))
    (PreRename.alterations (PreFrameCache.event_description c bank e)) (observed, output))
    as [changed altered] eqn:Haltered.
  cbn [fst snd] in Hkills, Hafter, Htarget_source, Haltered_wf |- *.
  unfold index in Hafter, Htarget_source.
  rewrite PreFrameInvariant.mark_exit_scope in Hafter, Htarget_source.
  cbn [fst] in Hafter, Htarget_source; fold index in Hafter, Htarget_source.
  assert (Htarget : In (Graph.target (Pre.pg c) e) (Graph.nodes (Pre.pg c))).
  { destruct (PreCoverage.listed_edge_out c Hlaw He) as [Hstart Hout].
    exact (out_target_in (points_graph_wf (Pre.point_laws c (Pre.graphs c Hlaw)))
      _ e Hstart Hout). }
  rewrite (exit_exact _ _ altered b u Htarget Htarget_source Haltered_wf Hafter), Hkills.
  unfold instruction_event; tauto.
Qed.

Local Lemma chain_point_cases {ns es first n} :
  point_chain (Pre.pg c) ns es -> nth_error ns 0 = Some first -> In n ns ->
    n = first \/ exists e, In e es /\ Graph.target (Pre.pg c) e = n.
Proof.
  intro Hchain; revert first; induction Hchain as
    [point|point next ns edge es Hedge Htarget Hchain IH]; intros first Hfirst Hin;
    cbn [nth_error] in Hfirst; inversion Hfirst; subst first.
  - destruct Hin as [<-|[]]; now left.
  - destruct Hin as [<-|Hin]; [now left|].
    destruct (IH next eq_refl Hin) as [Heq|[e [He Hn]]].
    + right; exists edge; split; [now left|congruence].
    + right; exists e; split; [now right|exact Hn].
Qed.

Local Lemma block_events owner first b u :
  In owner (Graph.nodes (Pre.bg c)) ->
  nth_error (SsaPoints.points_in_block points owner) 0 = Some first ->
    (((Pre.exit_point c first = true \/ Graph.out (Pre.pg c) first = []) /\
       phi_unused first b u) \/
      exists e, In e (SsaPoints.instruction_edges points owner) /\ instruction_event e b u) <->
    block_event owner b u.
Proof.
  intros Howner Hfirst; pose proof (Pre.point_laws c (Pre.graphs c Hlaw)) as Hp.
  pose proof (points_ordered Hp owner Howner) as Hchain; split.
  - intros [[Hending Hphi]|[e [Hin [[Hkill [Hne Hphi]]|[Hending Hphi]]]]].
    + exists first; split; [exact (nth_error_In _ _ Hfirst)|]; unfold unsafe_event; tauto.
    + exists (Graph.source (Pre.pg c) e); split.
      * destruct (PreFrg.chain_source _ Hchain Hin) as [n [Hn Hout]].
        pose proof (out_source (points_graph_wf Hp) _ e Hout) as Hstart.
        change (Graph.source (Pre.pg c) e = n) in Hstart; rewrite Hstart; exact Hn.
      * split; [exact Hphi|]; right; right; exists e; split; [|auto].
        exact (proj2 (PreCoverage.listed_edge_out c Hlaw
          (PreCoverage.instruction_edge_listed c Hlaw Howner Hin))).
    + exists (Graph.target (Pre.pg c) e); split.
      * apply PreFrg.tail_member; exact (PreFrg.chain_target _ Hchain Hin).
      * unfold unsafe_event; tauto.
  - intros [n [Hn [Hphi Hevent]]]; destruct Hevent as [Hexit|[Hout|[e [He [Hkill Hne]]]]].
    + destruct (chain_point_cases Hchain Hfirst Hn) as [<-|[e [Hin Htarget]]]; [left; auto|].
      right; exists e; split; [exact Hin|]; right; rewrite Htarget; auto.
    + destruct (chain_point_cases Hchain Hfirst Hn) as [<-|[e [Hin Htarget]]]; [left; auto|].
      right; exists e; split; [exact Hin|]; right; rewrite Htarget; auto.
    + assert (Hlisted : In n (Graph.nodes (Pre.pg c))).
      { apply (points_covered Hp); exists owner; auto. }
      assert (Hedge : In e (Cfg.edges (Pre.point_cfg c))).
      { apply Cfg.edges_spec; exists n; auto. }
      pose proof (PreCoverage.kill_internal c Hlaw (proj1 (unused_family Hphi)) Hedge Hkill)
        as Hinternal.
      pose proof (instruction_edges_complete Hp n e Hlisted He Hinternal) as Hin.
      rewrite (points_owner Hp owner n Howner Hn) in Hin.
      right; exists e; split; [exact Hin|]; left.
      pose proof (out_source (points_graph_wf Hp) n e He) as Hstart.
      change (Graph.source (Pre.pg c) e = n) in Hstart; rewrite Hstart; auto.
Qed.

Variable final : PreRename.accumulator B BE E U.
Hypothesis Htransfer :
  forall frames acc b e, In b (Graph.nodes (Pre.bg c)) ->
    In e (SsaPoints.instruction_edges points b) ->
    PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
    PreFrameTables.stamp c e acc = (None, false) ->
    PreFrameTables.stamp c e final = PreFrameTables.stamp c e
      (snd (PreRename.instruction c index b (SsaPoints.parameter_edge points b) (frames, acc) e)) ->
    PreCoverage.scope_laws c g (Graph.source (Pre.pg c) e) frames ->
    PreCoverage.scope_laws c g (Graph.target (Pre.pg c) e)
      (fst (PreRename.instruction c index b (SsaPoints.parameter_edge points b) (frames, acc) e)).

(** Each processed block adds precisely the unused-phi events at its own ordered points. *)
Theorem block_exact owner first frames acc b u :
  In owner (Graph.nodes (Pre.bg c)) ->
  nth_error (SsaPoints.points_in_block points owner) 0 = Some first ->
  PreFrameInvariant.scope_source c data frames -> PreFrameEnd.accumulator_wf c acc ->
  PreCoverage.scope_laws c g first frames ->
  PreFrameTables.unwritten c (SsaPoints.instruction_edges points owner) acc ->
  (forall e, In e (SsaPoints.instruction_edges points owner) ->
    PreFrameTables.stamp c e final =
      PreFrameTables.stamp c e (snd (PreRename.block c index owner frames acc))) ->
    (marked (snd (PreRename.block c index owner frames acc)) b u <->
      marked acc b u \/ block_event owner b u).
Proof.
  intros Howner Hfirst Hsource Hwf Hscope Hunwritten Htable.
  pose proof (PreFrameWalk.block_history c data final Hlaw Hdata Htransfer owner first frames acc
    Howner Hfirst Hsource Hwf Hscope Hunwritten Htable) as Hhistory.
  set (entered := match SsaPoints.points_in_block points owner with
    | [] => (frames, acc)
    | point :: _ => PreRename.mark_exit c index point (frames, acc)
    end) in *.
  assert (Hlocal : forall before e after,
    In e (SsaPoints.instruction_edges points owner) ->
    PreFrameWalk.instruction_step c data (g := g) final owner before e after ->
    (marked (snd after) b u <-> marked (snd before) b u \/ instruction_event e b u)).
  { intros [input output] e after Hin [Hinput [Houtput [Hmeaning [[Hbefore Hpacket] ->]]]].
    apply (instruction_exact owner e input output b u Howner).
    - exact Hin.
    - exact Hinput.
    - exact Houtput.
    - exact Hmeaning.
    - apply (Htransfer input output owner e Howner); assumption. }
  assert (Hmembership : marked
    (snd (fold_left (PreRename.instruction c index owner (SsaPoints.parameter_edge points owner))
      (SsaPoints.instruction_edges points owner) entered)) b u <->
    marked (snd entered) b u \/ exists e, In e (SsaPoints.instruction_edges points owner) /\
      instruction_event e b u).
  { exact (history_membership _ (fun work => marked (snd work) b u) _ _ _ _ Hhistory Hlocal). }
  rewrite PreRename.block_equation; fold entered; cbn [snd].
  rewrite (PreFrameStep.fold_observation _ (fun output => marked output b u)).
  2: { intros output pair; unfold marked; rewrite PreRename.select_argument_equation; reflexivity. }
  fold points index entered.
  rewrite Hmembership.
  assert (Hentered : entered = PreRename.mark_exit c index first (frames, acc)).
  { unfold entered; destruct (SsaPoints.points_in_block points owner); cbn in Hfirst;
      [discriminate|inversion Hfirst; reflexivity]. }
  assert (Hlisted : In first (Graph.nodes (Pre.pg c))).
  { apply (points_covered (Pre.point_laws c (Pre.graphs c Hlaw))); exists owner; split;
      [exact Howner|exact (nth_error_In _ _ Hfirst)]. }
  rewrite Hentered, (exit_exact first frames acc b u Hlisted Hsource Hwf Hscope).
  rewrite <- (block_events owner first b u Howner Hfirst); tauto.
Qed.

(** Accumulated unsafe marks are exactly events in already visited named blocks. *)
Definition seen_exact (current : PreRename.work B BE E U) : Prop :=
  forall b u, marked (PreRename.output current) b u <->
    exists id owner, Prepared.name_of (Pre.blocks c) id = Some owner /\
      In owner (Graph.nodes (Pre.bg c)) /\
      FinSet.mem positive_encoding id (PreRename.visited current) = true /\ block_event owner b u.

Local Lemma initial_exact : seen_exact (PreRename.initial index).
Proof.
  intros b u; unfold marked; rewrite PreRename.initial_equation.
  cbn [PreRename.output PreRename.visited PreRename.empty_accumulator PreRename.unsafe_index].
  rewrite FinSet.mem_empty; split; [discriminate|].
  intros [id [owner [Hname [Howner [Hseen Hevent]]]]]; rewrite FinSet.mem_empty in Hseen; discriminate.
Qed.

Local Lemma step_exact {current next result budget} :
  PreFrameWalk.walk_scope c data (g := g) current ->
  PreRename.step c index current = inl next ->
  runs (PreRename.step_c c index) budget next result ->
  final = PreFrameTables.output_of result ->
  seen_exact current -> seen_exact next.
Proof.
  intros [Hdomains [Howned Htasks]] Hstep Hsuffix Hfinal Hindex.
  pose proof Hstep as Hraw; rewrite PreRename.step_equation in Hstep.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [discriminate|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current)) eqn:Hseen.
  - inversion Hstep; subst next; exact Hindex.
  - pose proof (proj2 Hdomains) as Hpending_domains; rewrite Hpending in Hpending_domains.
    inversion Hpending_domains as [|pair tail Hdomain Htail]; subst pair tail.
    destruct Hdomain as [owner [first [Hname [Howner [Hfirst [Hsource Hpoint]]]]]].
    cbn [fst snd] in Hname, Hsource.
    rewrite Hname in Hstep; inversion Hstep; subst next.
    assert (Hlocal : forall b u,
      marked (snd (PreRename.block c index owner frames (PreRename.output current))) b u <->
      marked (PreRename.output current) b u \/ block_event owner b u).
    { intros b u; apply (block_exact owner first frames _ b u Howner Hfirst Hsource
        (PreFrameTables.owned_output_wf c current Howned)).
      - inversion Htasks as [|pair tail Htask Hrest]; subst pair tail.
        exact (Htask owner first Hname Howner Hfirst).
      - intros e He; exact (PreFrameTables.unvisited_unwritten c Hlaw Howned Hname Hseen e He).
      - intros e He; rewrite Hfinal.
        exact (PreFrameTables.block_table_final c Hlaw index current Howned _ result budget
          id frames rest owner Hpending Hseen Hname Hraw Hsuffix e He). }
    intros b u.
    change (marked (snd (PreRename.block c index owner frames (PreRename.output current))) b u <->
      exists other block, Prepared.name_of (Pre.blocks c) other = Some block /\
        In block (Graph.nodes (Pre.bg c)) /\
        FinSet.mem positive_encoding other
          (FinSet.add positive_encoding id (PreRename.visited current)) = true /\ block_event block b u).
    rewrite (Hlocal b u), (Hindex b u); split.
    + intros [[other [block [Hblock [Hb [Hmem Hevent]]]]]|Hevent].
      * exists other, block; split; [exact Hblock|]; split; [exact Hb|]; split; [|exact Hevent].
        rewrite FinSet.mem_add by exact (PreFrameTables.owned_seen_wf c current Howned).
        rewrite Hmem, orb_true_r; reflexivity.
      * exists id, owner; split; [exact Hname|]; split; [exact Howner|]; split; [|exact Hevent].
        rewrite FinSet.mem_add by exact (PreFrameTables.owned_seen_wf c current Howned).
        rewrite eqb_refl; reflexivity.
    + intros [other [block [Hblock [Hb [Hmem Hevent]]]]].
      rewrite FinSet.mem_add in Hmem by exact (PreFrameTables.owned_seen_wf c current Howned).
      apply orb_true_iff in Hmem; destruct Hmem as [Hsame|Hmem].
      * apply (eqb_true_iff _ positive_encoding_laws) in Hsame; subst other.
        assert (Hsame : block = owner) by congruence; subst block; now right.
      * left; exists other, block; auto.
Qed.

(** A stopped result retains the last checked state and its exact visited-event inventory. *)
Definition result_exact (result : PreRename.work B BE E U + PreRename.stopped B BE E U) : Prop :=
  match result with
  | inl current => seen_exact current /\ PreFrameVisit.visit_laws c data current
  | inr stopped => exists current, seen_exact current /\ PreFrameVisit.visit_laws c data current /\
      PreRename.step c index current = inr stopped
  end.

Local Lemma history_exact :
  forall source labels target,
    PreFrameStep.history (PreFrameWalk.checked_step c data (g := g)) source labels target ->
    final = PreFrameTables.output_of target ->
  forall current, source = inl current -> seen_exact current ->
    PreFrameVisit.visit_laws c data current -> result_exact target.
Proof.
  intros source labels target Hhistory; induction Hhistory as
    [source|source label next rest target Hstep Hhistory IH];
    intros Hfinal current Hsource Hindex Hvisit.
  - subst source; exact (conj Hindex Hvisit).
  - destruct Hstep as [executed [Hexecuted [Hscope Hstep]]].
    assert (Heq : executed = current) by congruence; subst executed.
    destruct next as [next|stopped].
    + apply (IH Hfinal next eq_refl).
      * exact (step_exact Hscope Hstep
          (PreFrameHistory.checked_runs c data _ _ _ Hhistory next eq_refl) Hfinal Hindex).
      * exact (PreFrameVisit.step_visit_laws c data Hlaw _ _ Hvisit Hstep).
    + assert (Htarget : target = inr stopped).
      { inversion Hhistory as [|start edge finish tail result Hbad Hrest]; [reflexivity|].
        destruct Hbad as [work [Hbad Hother]]; discriminate. }
      subst target; exists current; auto.
Qed.

(** A completed checked execution records exactly all unsafe events in the original point graph. *)
Theorem run_exact {labels target} :
  PreFrameStep.history (PreFrameWalk.checked_step c data (g := g))
    (inl (PreRename.initial index)) labels target ->
  final = PreFrameTables.output_of target ->
  (match target with
  | inl _ => False
  | inr stopped => PreRename.stop_status stopped = PreFrg.Completed
  end) ->
  forall b u, (marked final b u <->
    exists n, In n (Graph.nodes (Pre.pg c)) /\ phi_unused n b u /\ unsafe_event n u).
Proof.
  intros Hhistory Hfinal Hcompleted b u.
  pose proof (history_exact _ _ _ Hhistory Hfinal _ eq_refl initial_exact
    (PreFrameVisit.initial_visit_laws c data)) as Hresult.
  destruct target as [remaining|stopped]; [contradiction|].
  destruct Hresult as [current [Hindex [Hvisit Hstop]]].
  destruct (PreFrameVisit.completed_stop_empty c data current stopped Hstop Hcompleted)
    as [Hempty Houtput].
  rewrite Hfinal; cbn [PreFrameTables.output_of]; rewrite Houtput, (Hindex b u); split.
  - intros [id [owner [Hname [Howner [Hseen [n [Hn [Hphi Hevent]]]]]]]].
    exists n; split; [|auto].
    apply (points_covered (Pre.point_laws c (Pre.graphs c Hlaw))); exists owner; auto.
  - intros [n [Hn [Hphi Hevent]]].
    destruct (proj1 (points_covered (Pre.point_laws c (Pre.graphs c Hlaw)) n) Hn)
      as [owner [Howner Hmember]].
    pose proof (proj2 (proj2 (Pre.blocks_ready c (Pre.graphs c Hlaw)))) as Hp.
    assert (Hb : In owner (Graph.nodes (Prepared.graph (Pre.blocks c)))).
    { rewrite (Pre.blocks_source c (Pre.graphs c Hlaw)); exact Howner. }
    destruct (proj1 (Prepared.ids_domain _ Hp owner) Hb) as [id Hid].
    exists id, owner; split; [exact (Prepared.name_of_id_of _ _ _ Hp Hid)|].
    split; [exact Howner|]; split.
    + exact (PreFrameVisit.completed_blocks_seen c data Hlaw current Hvisit Hempty owner id Howner Hid).
    + exists n; auto.
Qed.

End Events.

End PreFrameUnsafe.
