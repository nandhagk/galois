(** * Source provenance maintained by scoped renaming

    Dense frames retain the expression, source definition and availability distinction that
    their actual update installed. For example, clearing availability never invents a definition.
    Builds on: AnalysesSsaPreFrameCache, AnalysesSsaPreFrameStep and CostLoop. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphModel GraphPrepared.
From Galois.Program Require Import ProgramCfg ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily
  AnalysesSsaPreFrg AnalysesSsaPreRename AnalysesSsaPreFrameCache AnalysesSsaPreFrameStep.
Import List.ListNotations.

Module PreFrameInvariant.

Section Provenance.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.
Variable data : @PreFrg.phi_data B U.
Hypothesis Hlaw : Pre.laws c.
Hypothesis Hdata : PreFrameCache.placement_laws c data.
Let bank := PreFrameCache.names c data.
Let index := PreRename.prepare c data.

(** Source versions have an eligible expression and the static domain of their actual origin. *)
Definition source_version (d : PreFrg.version B E U) : Prop :=
  PreFamily.in_family c (PreFrg.version_expr d) /\
  Pre.pure c (PreFrg.version_expr d) = true /\ PreFrg.definition_domain c d.

(** A frame retains a source version of its queried expression; unavailable sentinels stay invalid. *)
Definition frame_source u (frame : PreRename.frame B E U) : Prop :=
  PreFrg.version_expr (PreFrg.operand_version (PreRename.selected frame)) = u /\
  source_version (PreFrg.operand_version (PreRename.selected frame)) /\
  (PreRename.available frame = true ->
    PreFrg.operand_version (PreRename.selected frame) <> PreFrg.Unavailable u).

(** All named frames share the prepared symbol table and retain source-origin provenance. *)
Record scope_source (frames : PreRename.scope B E U) : Prop := ScopeSource {
  scope_representation : PreFrameCache.scope_wf c frames;
  scope_symbols : PreRename.symbols frames = bank;
  scope_frames : forall u id, Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    frame_source u (PreRename.top c frames u)
}.

Local Lemma named_eligible {u id} :
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    PreFamily.in_family c u /\ Pre.pure c u = true.
Proof.
  intro Hid; apply (proj1 (PreFrameCache.names_domain c data Hlaw Hdata u)).
  now exists id.
Qed.

Local Lemma fresh_source {e u id} :
  In e (Cfg.edges (Pre.point_cfg c)) -> Pre.recomputed c e = Some u ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id -> source_version (PreFrg.Fresh e u).
Proof.
  intros He Hcomputed Hid; destruct (named_eligible Hid) as [Hfamily Hpure].
  unfold source_version; cbn [PreFrg.version_expr PreFrg.definition_domain]; auto.
Qed.

Local Lemma phi_source {b u id} :
  PreFrg.phi_needed c u b ->
  Intern.find (Pre.eu (Pre.keys c)) u bank = Some id -> source_version (PreFrg.Phi b u).
Proof.
  intros Hphi Hid; destruct (named_eligible Hid) as [Hfamily Hpure].
  unfold source_version; cbn [PreFrg.version_expr PreFrg.definition_domain]; auto.
Qed.

(** Prepared entry frames establish the source invariant before any block is processed. *)
Theorem entry_source : scope_source (PreRename.entry_scope index).
Proof.
  constructor.
  - apply PreFrameCache.entry_scope_wf; exact Hlaw.
  - apply PreFrameCache.entry_symbols.
  - intros u id Hid.
    unfold index.
    rewrite (PreFrameCache.cached_entry c data _ (PreFrameCache.prepare_laws c data)).
    rewrite PreFrameCache.initial_top; [|exact Hlaw|].
    + rewrite PreRename.initial_frame_equation.
      destruct (named_eligible Hid) as [Hfamily Hpure].
      destruct (Pre.initial c u) eqn:Hinitial; unfold frame_source, source_version;
        cbn [PreRename.selected PreRename.available PreFrg.operand_version
          PreFrg.version_expr PreFrg.definition_domain]; intuition discriminate.
    + apply (proj2 (PreFrameCache.eligible_exact c data Hdata u)); exact (named_eligible Hid).
Qed.

(** Installing one named source frame preserves every other expression's source provenance. *)
Theorem store_source :
  forall frames, scope_source frames ->
  forall u id frame, Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    frame_source u frame -> scope_source (PreRename.store frames id frame).
Proof.
  intros frames Hframes u id frame Hid Hframe; constructor.
  - apply PreFrameCache.store_wf; exact (scope_representation _ Hframes).
  - rewrite PreRename.store_equation; exact (scope_symbols _ Hframes).
  - intros v other Hv; rewrite (PreFrameCache.top_store c Hlaw frames u id frame).
    + destruct (eqb (Pre.eu (Pre.keys c)) v u) eqn:Hsame.
      * apply (eqb_true_iff _ (Pre.eu_laws c (Pre.graphs c Hlaw))) in Hsame.
        subst v; exact Hframe.
      * exact (scope_frames _ Hframes v other Hv).
    + exact (scope_representation _ Hframes).
    + rewrite (scope_symbols _ Hframes); exact Hid.
Qed.

Local Lemma dense_frame_source {frames u id} :
  scope_source frames -> Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    frame_source u (PreRename.top_id frames id u).
Proof.
  intros Hframes Hid.
  rewrite <- (PreFrameCache.top_id_agrees c (frames := frames) (u := u) (id := id)).
  - exact (scope_frames _ Hframes u id Hid).
  - rewrite (scope_symbols _ Hframes); exact Hid.
Qed.

Local Lemma reused_frame_source {u frame} :
  frame_source u frame -> PreRename.available frame = true ->
    frame_source u (PreRename.Frame
      (PreFrg.Operand (PreFrg.operand_version (PreRename.selected frame)) true) true).
Proof.
  intros [Hexpr [Hsource Havailable]] Hreuse.
  unfold frame_source; cbn [PreRename.selected PreRename.available PreFrg.operand_version].
  auto.
Qed.

Local Lemma reuse_available frame u :
  PreRename.frame_reuse c frame u = true -> PreRename.available frame = true.
Proof.
  unfold PreRename.frame_reuse; destruct (PreRename.available frame); [reflexivity|discriminate].
Qed.

(** Occurrence selection changes a frame only to the same available source version. *)
Theorem occurrence_source :
  forall frames acc e instance, scope_source frames ->
    (forall id u, instance = Some (id, u) ->
      Intern.find (Pre.eu (Pre.keys c)) u bank = Some id) ->
    scope_source (fst (fst (PreRename.occurrence c e instance (frames, acc)))).
Proof.
  intros frames acc e instance Hframes Hinstance; rewrite PreRename.occurrence_equation.
  destruct instance as [[id u]|]; [|exact Hframes].
  cbn zeta; destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u) eqn:Hreuse;
    cbn [fst]; [|exact Hframes].
  apply (store_source frames Hframes u id); [apply Hinstance; reflexivity|].
  apply reused_frame_source.
  - exact (dense_frame_source Hframes (Hinstance id u eq_refl)).
  - exact (reuse_available _ _ Hreuse).
Qed.

(** Invalidation preserves the source identity while clearing only availability. *)
Theorem alter_source :
  forall frames acc instance id u, scope_source frames ->
    Intern.find (Pre.eu (Pre.keys c)) u bank = Some id ->
    scope_source (fst (PreRename.alter c instance (frames, acc) (id, u))).
Proof.
  intros frames acc instance id u Hframes Hid; rewrite PreRename.alter_equation.
  cbn [fst snd]; apply (store_source frames Hframes u id); [exact Hid|].
  destruct (dense_frame_source Hframes Hid) as [Hexpr [Hsource Havailable]].
  unfold frame_source; cbn [PreRename.selected PreRename.available].
  split; [exact Hexpr|]; split; [exact Hsource|discriminate].
Qed.

Local Lemma phi_bucket_source {b block id u} :
  In (block, (id, u))
    (Index.find (Pre.eb (Pre.keys c)) b (PreRename.phi_definitions index)) ->
    block = b /\ PreFrg.phi_needed c u b /\
      Intern.find (Pre.eu (Pre.keys c)) u bank = Some id.
Proof.
  intro Hin.
  unfold index in Hin.
  rewrite (PreFrameCache.cached_phi_definitions c data _ (PreFrameCache.prepare_laws c data)),
    Index.find_group_by, filter_In in Hin.
  destruct Hin as [Hin Hsame]; cbn [fst] in Hsame.
  apply (eqb_true_iff _ (Pre.eb_laws c (Pre.graphs c Hlaw))) in Hsame; subst block.
  split; [reflexivity|].
  exact (proj1 (PreFrameCache.phi_pairs_exact c data Hlaw Hdata b id u) Hin).
Qed.

(** Phi installation takes its source and dense identity from the actual block bucket. *)
Theorem install_phi_source :
  forall b frames pair, scope_source frames ->
    In pair (Index.find (Pre.eb (Pre.keys c)) b (PreRename.phi_definitions index)) ->
    scope_source (PreRename.install_phi b frames pair).
Proof.
  intros b frames [block [id u]] Hframes Hin.
  destruct (phi_bucket_source Hin) as [Hblock [Hphi Hid]].
  rewrite PreRename.install_phi_equation; cbn [fst snd].
  apply (store_source frames Hframes u id); [exact Hid|].
  unfold frame_source; cbn [PreRename.selected PreRename.available
    PreFrg.operand_version PreFrg.version_expr].
  split; [reflexivity|]; split; [exact (phi_source Hphi Hid)|discriminate].
Qed.

Local Lemma fold_phi_source b :
  forall pairs frames, Forall
    (fun pair => In pair
      (Index.find (Pre.eb (Pre.keys c)) b (PreRename.phi_definitions index))) pairs ->
    scope_source frames -> scope_source (fold_left (PreRename.install_phi b) pairs frames).
Proof.
  intros pairs frames Hpairs; revert frames.
  induction Hpairs as [|pair rest Hpair Hrest IH]; intros frames Hframes; cbn [fold_left].
  - exact Hframes.
  - apply IH; apply install_phi_source; assumption.
Qed.

(** Definition installation records actual fresh sources and then the exact prepared phi bucket. *)
Theorem definitions_source :
  forall b parameter e fresh frames, scope_source frames ->
    (forall id u, fresh = Some (id, u) ->
      In e (Cfg.edges (Pre.point_cfg c)) /\ Pre.recomputed c e = Some u /\
        Intern.find (Pre.eu (Pre.keys c)) u bank = Some id) ->
    scope_source (PreRename.definitions c index b parameter e fresh frames).
Proof.
  intros b parameter e fresh frames Hframes Hfresh; rewrite PreRename.definitions_equation.
  assert (Hnew : scope_source (match fresh with
    | None => frames
    | Some (id, u) => PreRename.store frames id
        (PreRename.Frame (PreFrg.Operand (PreFrg.Fresh e u) true) true)
    end)).
  { destruct fresh as [[id u]|]; [|exact Hframes].
    destruct (Hfresh id u eq_refl) as [He [Hcomputed Hid]].
    apply (store_source frames Hframes u id); [exact Hid|].
    unfold frame_source; cbn [PreRename.selected PreRename.available
      PreFrg.operand_version PreFrg.version_expr].
    split; [reflexivity|]; split; [exact (fresh_source He Hcomputed Hid)|discriminate]. }
  destruct (eqb (Pre.ee (Pre.keys c)) e parameter); [|exact Hnew].
  apply fold_phi_source; [apply Forall_forall; auto|exact Hnew].
Qed.

(** Exit marking cannot change the current scope, even when it adds unsafe events. *)
Theorem mark_exit_scope n work :
  fst (PreRename.mark_exit c index n work) = fst work.
Proof.
  rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index));
    reflexivity.
Qed.

Local Lemma occurrence_fresh {e instance work id u} :
  snd (PreRename.occurrence c e instance work) = Some (id, u) ->
    instance = Some (id, u).
Proof.
  rewrite PreRename.occurrence_equation; destruct instance as [[key value]|]; [|discriminate].
  destruct work as [frames acc]; cbn zeta.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames key value) value);
    cbn [snd]; [discriminate|congruence].
Qed.

Local Lemma fold_alter_source instance :
  forall changes work,
    Forall (fun pair => Intern.find (Pre.eu (Pre.keys c)) (snd pair) bank = Some (fst pair))
      changes ->
    scope_source (fst work) ->
    scope_source (fst (fold_left (PreRename.alter c instance) changes work)).
Proof.
  intros changes work Hchanges; revert work.
  induction Hchanges as [|[id u] rest Hid Hrest IH]; intros [frames acc] Hframes;
    cbn [fold_left fst snd] in *.
  - exact Hframes.
  - apply IH; apply alter_source; assumption.
Qed.

(** Each actual prepared instruction retains the shared symbol table and source frame domains. *)
Theorem instruction_source b parameter work e :
  scope_source (fst work) ->
    scope_source (fst (PreRename.instruction c index b parameter work e)).
Proof.
  intro Hframes; rewrite PreRename.instruction_equation.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index))
    as [info|] eqn:Hinfo; [|exact Hframes].
  destruct (PreFrameCache.event_lookup_domain c data Hlaw e info Hinfo) as [He Hdescription].
  subst info; rewrite mark_exit_scope; cbn [fst].
  set (instance := PreRename.evaluation (PreFrameCache.event_description c bank e)).
  assert (Hinstance : forall id u, instance = Some (id, u) ->
    Pre.recomputed c e = Some u /\ Intern.find (Pre.eu (Pre.keys c)) u bank = Some id).
  { intros id u Hvalue; apply PreFrameCache.evaluation_exact in Hvalue; tauto. }
  set (observed := PreRename.occurrence c e instance work).
  assert (Hobserved : scope_source (fst (fst observed))).
  { destruct work as [frames acc]; apply occurrence_source; [exact Hframes|].
    intros id u Hvalue; exact (proj2 (Hinstance id u Hvalue)). }
  apply definitions_source.
  - apply fold_alter_source; [|exact Hobserved].
    apply Forall_forall; intros [id u] Hin; cbn [fst snd].
    apply (PreFrameCache.event_alterations c bank e Hlaw) in Hin; exact (proj2 Hin).
  - intros id u Hfresh.
    apply occurrence_fresh in Hfresh.
    destruct (Hinstance id u Hfresh) as [Hcomputed Hid]; auto.
Qed.

Local Lemma fold_instruction_source b parameter :
  forall es work, scope_source (fst work) ->
    scope_source (fst (fold_left (PreRename.instruction c index b parameter) es work)).
Proof.
  intro es; induction es as [|e rest IH]; intros work Hwork; cbn [fold_left].
  - exact Hwork.
  - apply IH; apply instruction_source; exact Hwork.
Qed.

(** Ordered block processing and outgoing argument selection retain the final scope provenance. *)
Theorem block_source b frames acc :
  scope_source frames -> scope_source (fst (PreRename.block c index b frames acc)).
Proof.
  intro Hframes; rewrite PreRename.block_equation; cbn [fst].
  apply fold_instruction_source.
  destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b) as [|first rest];
    [exact Hframes|rewrite mark_exit_scope; exact Hframes].
Qed.

(** Pending dominator tasks contain only scopes obtained from prepared entry or source updates. *)
Definition tasks_source (current : PreRename.work B BE E U) : Prop :=
  Forall (fun pair => scope_source (snd pair)) (PreRename.pending current).

Local Lemma initial_tasks_source : tasks_source (PreRename.initial index).
Proof.
  unfold tasks_source; rewrite PreRename.initial_equation; cbn [PreRename.pending].
  apply Forall_forall; intros [id frames] Hin; apply in_map_iff in Hin.
  destruct Hin as [root [Heq Hroot]]; inversion Heq; subst frames; exact entry_source.
Qed.

Local Lemma step_tasks_source current :
  tasks_source current ->
    match PreRename.step c index current with
    | inl next => tasks_source next
    | inr _ => True
    end.
Proof.
  intro Htasks; rewrite PreRename.step_equation.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [exact I|].
  unfold tasks_source in Htasks; rewrite Hpending in Htasks.
  inversion Htasks as [|pair tail Hframes Hrest]; subst pair tail; cbn [snd] in Hframes.
  destruct (FinSet.mem positive_encoding id (PreRename.visited current));
    [exact Hrest|].
  destruct (Prepared.name_of (Pre.blocks c) id) as [b|]; [|exact I].
  unfold tasks_source; cbn [PreRename.pending]; apply Forall_app; split; [|exact Hrest].
  apply Forall_forall; intros [child child_frames] Hin; apply in_map_iff in Hin.
  destruct Hin as [pair [Heq Hpair]]; inversion Heq; subst child_frames.
  apply block_source; exact Hframes.
Qed.

(** Every continuing actual binary-driver state retains the pending-scope source invariant. *)
Theorem runs_tasks_source :
  forall budget current result, runs (PreRename.step_c c index) budget current result ->
    tasks_source current ->
    match result with inl next => tasks_source next | inr _ => True end.
Proof.
  intros budget current result Hrun; induction Hrun as [current|
    budget current final Hstop|budget current next result Hstep Hrun IH]; intro Htasks.
  - exact Htasks.
  - exact I.
  - apply IH; pose proof (step_tasks_source current Htasks) as Hnext.
    unfold PreRename.step in Hnext; rewrite Hstep in Hnext; exact Hnext.
Qed.

(** Occurrence answers denote a real pure recomputation and a nonsentinel source version. *)
Definition occurrence_source_at e d : Prop :=
  In e (Cfg.edges (Pre.point_cfg c)) /\
  exists u, Pre.recomputed c e = Some u /\ Pre.pure c u = true /\
    PreFrg.version_expr d = u /\ source_version d /\ d <> PreFrg.Unavailable u.

(** The output records only source-backed occurrences and actually created fresh origins. *)
Record output_source (acc : PreRename.accumulator B BE E U) : Prop := OutputSource {
  source_occurrences_wf : Map.wf (Pre.ee (Pre.keys c)) (PreRename.occurrence_index acc);
  source_occurrences : forall e d,
    Map.get (Pre.ee (Pre.keys c)) e (PreRename.occurrence_index acc) = Some d ->
      occurrence_source_at e d;
  source_created : forall d, In d (PreRename.created acc) ->
    source_version d /\ exists e u, d = PreFrg.Fresh e u
}.

Local Lemma empty_output_source : output_source PreRename.empty_accumulator.
Proof.
  constructor.
  - apply Map.wf_empty.
  - intros e d Hget.
    cbn [PreRename.occurrence_index PreRename.empty_accumulator] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros d [].
Qed.

Local Lemma output_set_source acc e d fresh :
  output_source acc -> occurrence_source_at e d ->
  (fresh = true -> exists u, d = PreFrg.Fresh e u) ->
  output_source (PreRename.Accumulator
    (Map.set (Pre.ee (Pre.keys c)) e d (PreRename.occurrence_index acc))
    (if fresh then FinSet.add (Pre.ee (Pre.keys c)) e (PreRename.fresh_index acc)
      else PreRename.fresh_index acc)
    (PreRename.link_index acc) (PreRename.unsafe_index acc)
    (if fresh then d :: PreRename.created acc else PreRename.created acc)).
Proof.
  intros Hacc Hd Hfresh; constructor.
  - apply Map.wf_set; exact (source_occurrences_wf _ Hacc).
  - intros other result Hget; cbn [PreRename.occurrence_index] in Hget.
    rewrite Map.get_set in Hget by exact (source_occurrences_wf _ Hacc).
    destruct (eqb (Pre.ee (Pre.keys c)) other e) eqn:Hsame.
    + apply (eqb_true_iff _ (Pre.ee_laws c (Pre.graphs c Hlaw))) in Hsame.
      inversion Hget; subst other result; exact Hd.
    + exact (source_occurrences _ Hacc other result Hget).
  - intros result Hin; cbn [PreRename.created] in Hin.
    destruct fresh; [destruct Hin as [<-|Hin]|].
    + destruct Hd as [He [u [Hcomputed [Hpure [Hexpr [Hsource Hnonempty]]]]]].
      split; [exact Hsource|].
      destruct (Hfresh eq_refl) as [value Hvalue]; exists e, value; exact Hvalue.
    + exact (source_created _ Hacc result Hin).
    + exact (source_created _ Hacc result Hin).
Qed.

(** Reuse and fresh selection both retain the exact source recomputation in the occurrence map. *)
Theorem occurrence_output_source :
  forall frames acc e instance, scope_source frames -> output_source acc ->
    In e (Cfg.edges (Pre.point_cfg c)) ->
    (forall id u, instance = Some (id, u) ->
      Pre.recomputed c e = Some u /\ Intern.find (Pre.eu (Pre.keys c)) u bank = Some id) ->
    output_source (snd (fst (PreRename.occurrence c e instance (frames, acc)))).
Proof.
  intros frames acc e instance Hframes Hacc He Hinstance.
  rewrite PreRename.occurrence_equation; destruct instance as [[id u]|]; [|exact Hacc].
  destruct (Hinstance id u eq_refl) as [Hcomputed Hid].
  destruct (named_eligible Hid) as [Hfamily Hpure]; cbn zeta.
  destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u) eqn:Hreuse; cbn [fst snd].
  - apply (output_set_source acc e _ false); [exact Hacc| |discriminate].
    destruct (dense_frame_source Hframes Hid) as [Hexpr [Hsource Hnonempty]].
    split; [exact He|]; exists u.
    split; [exact Hcomputed|]; split; [exact Hpure|]; split; [exact Hexpr|].
    split; [exact Hsource|].
    apply Hnonempty; exact (reuse_available _ _ Hreuse).
  - apply (output_set_source acc e _ true); [exact Hacc| |exists u; reflexivity].
    split; [exact He|]; exists u; split; [exact Hcomputed|]; split; [exact Hpure|].
    split; [reflexivity|]; split; [exact (fresh_source He Hcomputed Hid)|discriminate].
Qed.

Local Lemma mark_output_source frames acc key :
  output_source acc -> output_source (PreRename.mark c frames acc key).
Proof.
  intro Hacc; rewrite PreRename.mark_equation.
  destruct (PreRename.selected (PreRename.top_id frames (fst key) (snd key))) as [d real].
  destruct d, real; try exact Hacc.
  destruct Hacc; constructor; assumption.
Qed.

Local Lemma mark_exit_output_source n work :
  output_source (snd work) -> output_source (snd (PreRename.mark_exit c index n work)).
Proof.
  intro Hacc; rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index)); [|exact Hacc].
  cbn [snd]; apply (PreFrameStep.fold_preserves _ output_source); [|exact Hacc].
  intros current pair Hcurrent; apply mark_output_source; exact Hcurrent.
Qed.

Local Lemma alter_output_source instance work key :
  output_source (snd work) -> output_source (snd (PreRename.alter c instance work key)).
Proof.
  intro Hacc; rewrite PreRename.alter_equation; destruct work as [frames acc].
  destruct instance as [current|]; cbn [snd].
  - destruct (eqb positive_encoding (fst current) (fst key));
      [exact Hacc|apply mark_output_source; exact Hacc].
  - apply mark_output_source; exact Hacc.
Qed.

(** A local instruction preserves both scope source provenance and accumulated occurrence sources. *)
Theorem instruction_output_source b parameter work e :
  scope_source (fst work) -> output_source (snd work) ->
    output_source (snd (PreRename.instruction c index b parameter work e)).
Proof.
  intros Hframes Hacc; rewrite PreRename.instruction_equation.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index)) as [info|] eqn:Hinfo;
    [|exact Hacc].
  destruct (PreFrameCache.event_lookup_domain c data Hlaw e info Hinfo) as [He Hdescription].
  subst info; apply mark_exit_output_source; cbn [snd].
  apply (PreFrameStep.fold_preserves _ (fun work => output_source (snd work))).
  - intros current key Hcurrent; apply alter_output_source; exact Hcurrent.
  - destruct work as [frames acc]; apply occurrence_output_source; try assumption.
    intros id u Hvalue; apply PreFrameCache.evaluation_exact in Hvalue; tauto.
Qed.

Local Lemma fold_body_source b parameter :
  forall es work, scope_source (fst work) -> output_source (snd work) ->
    scope_source (fst (fold_left (PreRename.instruction c index b parameter) es work)) /\
    output_source (snd (fold_left (PreRename.instruction c index b parameter) es work)).
Proof.
  intro es; induction es as [|e rest IH]; intros work Hframes Hacc; cbn [fold_left].
  - auto.
  - apply IH; [apply instruction_source|apply instruction_output_source]; assumption.
Qed.

Local Lemma argument_output_source frames acc arg :
  output_source acc -> output_source (PreRename.select_argument c frames acc arg).
Proof.
  intro Hacc; rewrite PreRename.select_argument_equation.
  destruct Hacc; constructor; assumption.
Qed.

(** The actual ordered block preserves every occurrence/created-source observation. *)
Theorem block_output_source b frames acc :
  scope_source frames -> output_source acc ->
    output_source (snd (PreRename.block c index b frames acc)).
Proof.
  intros Hframes Hacc; rewrite PreRename.block_equation.
  set (entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
    | [] => (frames, acc)
    | first :: _ => PreRename.mark_exit c index first (frames, acc)
    end).
  assert (Hentered : scope_source (fst entered) /\ output_source (snd entered)).
  { unfold entered; destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b).
    - auto.
    - split; [rewrite mark_exit_scope; exact Hframes|].
      apply mark_exit_output_source; exact Hacc. }
  pose proof (fold_body_source b (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b)
    (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered
    (proj1 Hentered) (proj2 Hentered)) as Hbody.
  cbn [snd]; apply (PreFrameStep.fold_preserves _ output_source); [|exact (proj2 Hbody)].
  intros current pair Hcurrent; apply argument_output_source; exact Hcurrent.
Qed.

(** The whole walk combines immutable pending-scope provenance with monotone source observations. *)
Definition walk_source (current : PreRename.work B BE E U) : Prop :=
  tasks_source current /\ output_source (PreRename.output current).

Definition result_source (result : PreRename.work B BE E U + PreRename.stopped B BE E U) :=
  match result with
  | inl current => walk_source current
  | inr final => output_source (PreRename.stop_output final)
  end.

Local Lemma step_source current :
  walk_source current -> result_source (PreRename.step c index current).
Proof.
  intros [Htasks Hacc]; pose proof (step_tasks_source current Htasks) as Hnext.
  rewrite PreRename.step_equation in Hnext |- *.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending; [exact Hacc|].
  destruct (FinSet.mem positive_encoding id (PreRename.visited current));
    [split; assumption|].
  destruct (Prepared.name_of (Pre.blocks c) id) as [b|]; [|exact Hacc].
  split; [exact Hnext|].
  apply block_output_source; [|exact Hacc].
  unfold tasks_source in Htasks; rewrite Hpending in Htasks.
  inversion Htasks; assumption.
Qed.

Local Lemma runs_source :
  forall budget current result, runs (PreRename.step_c c index) budget current result ->
    walk_source current -> result_source result.
Proof.
  intros budget current result Hrun; induction Hrun as [current|
    budget current final Hstop|budget current next result Hstep Hrun IH]; intro Hcurrent.
  - exact Hcurrent.
  - pose proof (step_source current Hcurrent) as Hfinal.
    unfold PreRename.step in Hfinal; rewrite Hstop in Hfinal; exact Hfinal.
  - apply IH; pose proof (step_source current Hcurrent) as Hnext.
    unfold PreRename.step in Hnext; rewrite Hstep in Hnext; exact Hnext.
Qed.

(** Every actual run, including partial outcomes, contains only source-backed occurrences/creations. *)
Theorem run_output_source :
  output_source (PreRename.stop_output (PreRename.run c index)).
Proof.
  pose proof (runs_source _ _ _ (iterate_value (PreRename.step_c c index)
    (PreRename.walk_budget index) (PreRename.initial index))) as Hrun.
  assert (Hinitial : walk_source (PreRename.initial index)).
  { split; [exact initial_tasks_source|].
    rewrite PreRename.initial_equation; exact empty_output_source. }
  specialize (Hrun Hinitial); rewrite PreRename.run_equation.
  destruct (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
    (PreRename.initial index))); [exact (proj2 Hrun)|exact Hrun].
Qed.

End Provenance.

End PreFrameInvariant.
