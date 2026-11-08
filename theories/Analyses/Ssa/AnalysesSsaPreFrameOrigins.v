(** * Created-version membership through saved scopes

    Every selected fresh version comes from the growing list of actual creations.
    For example, a saved parent scope remains valid after a sibling creates another version.
    Builds on: AnalysesSsaPreRename, AnalysesSsaPreFrameCache and CostLoop. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseIntern.
From Galois.Graph Require Import GraphPrepared.
From Galois.Program Require Import ProgramSsaPoints.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreFrameCache AnalysesSsaPreFrameStep.
Import List.ListNotations.

Module PreFrameOrigins.

Section Origins.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

(** A fresh origin must occur in the actual creation list while other origins need no allocation. *)
Definition origin (known : list (PreFrg.version B E U)) d : Prop :=
  match d with PreFrg.Fresh _ _ => In d known | _ => True end.

(** Dense scope bindings can refer only to fresh versions already created by the same walk. *)
Record scope_origins known (frames : PreRename.scope B E U) : Prop := ScopeOrigins {
  origins_bindings_wf : Map.wf positive_encoding (PreRename.bindings frames);
  origins_frames : forall id u,
    origin known (PreFrg.operand_version (PreRename.selected (PreRename.top_id frames id u)))
}.

(** Both accumulated occurrence and incoming-operand selections retain allocated fresh origins. *)
Record output_origins (acc : PreRename.accumulator B BE E U) : Prop := OutputOrigins {
  origins_occurrences_wf : Map.wf (Pre.ee (Pre.keys c)) (PreRename.occurrence_index acc);
  origins_links_wf : Map.wf (PreFrg.link_encoding c) (PreRename.link_index acc);
  origins_occurrences : forall e d,
    Map.get (Pre.ee (Pre.keys c)) e (PreRename.occurrence_index acc) = Some d ->
      origin (PreRename.created acc) d;
  origins_links : forall key op,
    Map.get (PreFrg.link_encoding c) key (PreRename.link_index acc) = Some op ->
      origin (PreRename.created acc) (PreFrg.operand_version op)
}.

Definition local_origins (work : PreRename.scope B E U * PreRename.accumulator B BE E U) :=
  scope_origins (PreRename.created (snd work)) (fst work) /\ output_origins (snd work).

Local Lemma origin_weaken {before after d} :
  incl before after -> origin before d -> origin after d.
Proof.
  intros Hle Hd; destruct d; try exact I; apply Hle; exact Hd.
Qed.

(** Saved scopes remain valid when later instructions extend the global creation list. *)
Theorem scope_weaken {before after frames} :
  incl before after -> scope_origins before frames -> scope_origins after frames.
Proof.
  intros Hle Hframes; constructor.
  - exact (origins_bindings_wf _ _ Hframes).
  - intros id u; apply (origin_weaken Hle); exact (origins_frames _ _ Hframes id u).
Qed.

Local Lemma store_origins {known frames id frame} :
  scope_origins known frames ->
  origin known (PreFrg.operand_version (PreRename.selected frame)) ->
    scope_origins known (PreRename.store frames id frame).
Proof.
  intros Hframes Hframe; constructor.
  - rewrite PreRename.store_equation; apply Map.wf_set; exact (origins_bindings_wf _ _ Hframes).
  - intros query u; rewrite PreRename.top_id_equation, PreRename.store_equation,
      Map.find_or_equation; cbn [PreRename.bindings].
    rewrite Map.get_set by exact (origins_bindings_wf _ _ Hframes).
    destruct (eqb positive_encoding query id); [exact Hframe|].
    rewrite <- Map.find_or_equation, <- PreRename.top_id_equation.
    exact (origins_frames _ _ Hframes query u).
Qed.

Local Lemma assigned_property {X Y} (enc : encoding X) (pairs : list (X * Y)) (P : Y -> Prop) :
  Forall (fun pair => P (snd pair)) pairs ->
  forall x y, Map.get enc x (Map.of_list enc pairs) = Some y -> P y.
Proof.
  intros Hpairs x y; rewrite Map.of_list_get.
  assert (Hfold : forall rest old, Forall (fun pair => P (snd pair)) rest ->
    (forall value, old = Some value -> P value) ->
    fold_left (fun acc pair => if eqb enc x (fst pair) then Some (snd pair) else acc)
      rest old = Some y -> P y).
  { intros rest; induction rest as [|[key value] rest IH]; intros old Hrest Hold Hresult.
    - apply Hold; exact Hresult.
    - inversion Hrest as [|pair tail Hvalue Htail]; subst pair tail.
      cbn [fold_left fst snd] in Hresult.
      destruct (eqb enc x key).
      + apply (IH (Some value) Htail);
          [intros value' Heq; inversion Heq; subst; exact Hvalue|exact Hresult].
      + exact (IH _ Htail Hold Hresult). }
  apply (Hfold pairs None Hpairs); intros value Hfalse; discriminate.
Qed.

(** Entry preparation installs only initial values or unavailable sentinels in every dense binding. *)
Theorem initial_scope_origins family :
  scope_origins [] (PreRename.initial_scope c family).
Proof.
  constructor.
  - rewrite PreRename.initial_scope_equation; apply Map.wf_of_list.
  - intros id u; rewrite PreRename.initial_scope_equation, PreRename.top_id_equation,
      Map.find_or_equation; cbn [PreRename.bindings].
    set (pairs := map (fun pair => (fst pair, PreRename.initial_frame c (snd pair)))
      (Map.elements (Intern.inverse (Intern.of_list (Pre.eu (Pre.keys c)) family)))).
    destruct (Map.get positive_encoding id (Map.of_list positive_encoding pairs))
      as [frame|] eqn:Hget; [|exact I].
    apply (assigned_property positive_encoding pairs
      (fun frame => origin [] (PreFrg.operand_version (PreRename.selected frame)))) in Hget.
    + exact Hget.
    + unfold pairs; apply Forall_forall; intros [key frame'] Hin.
      apply in_map_iff in Hin; destruct Hin as [[other value] [Heq Hin]].
      inversion Heq; subst frame'; rewrite PreRename.initial_frame_equation.
      destruct (Pre.initial c value); exact I.
Qed.

Local Lemma empty_output_origins : output_origins PreRename.empty_accumulator.
Proof.
  constructor; try apply Map.wf_empty.
  - intros e d Hget; cbn [PreRename.empty_accumulator PreRename.occurrence_index] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros key op Hget; cbn [PreRename.empty_accumulator PreRename.link_index] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
Qed.

Local Lemma mark_origins frames acc key :
  output_origins acc -> output_origins (PreRename.mark c frames acc key) /\
    PreRename.created (PreRename.mark c frames acc key) = PreRename.created acc.
Proof.
  intro Hacc; rewrite PreRename.mark_equation.
  destruct (PreRename.selected (PreRename.top_id frames (fst key) (snd key))) as [d real].
  destruct d, real; split; try exact Hacc; try reflexivity.
  destruct Hacc; constructor; assumption.
Qed.

Local Lemma fold_mark_origins frames :
  forall keys acc, output_origins acc ->
    output_origins (fold_left (PreRename.mark c frames) keys acc) /\
      PreRename.created (fold_left (PreRename.mark c frames) keys acc) = PreRename.created acc.
Proof.
  intro keys; induction keys as [|key rest IH]; intros acc Hacc; [auto|].
  cbn [fold_left]; destruct (mark_origins frames acc key Hacc) as [Hmark Heq].
  destruct (IH _ Hmark) as [Hfinal Hcreated]; split; [exact Hfinal|congruence].
Qed.

Local Lemma mark_exit_origins index n work :
  local_origins work ->
    local_origins (PreRename.mark_exit c index n work) /\
      PreRename.created (snd (PreRename.mark_exit c index n work)) =
        PreRename.created (snd work).
Proof.
  intros [Hframes Hacc]; rewrite PreRename.mark_exit_equation.
  destruct (FinSet.mem (Pre.en (Pre.keys c)) n (PreRename.exit_points index)).
  2: { split; [split; assumption|reflexivity]. }
  destruct (fold_mark_origins (fst work) (PreRename.family_ids index) (snd work) Hacc)
    as [Hfinal Heq].
  split; [split|exact Heq].
  - cbn [fst snd]; rewrite Heq; exact Hframes.
  - exact Hfinal.
Qed.

Local Lemma set_occurrence_origins acc e d known :
  output_origins acc -> incl (PreRename.created acc) known -> origin known d ->
    output_origins (PreRename.Accumulator
      (Map.set (Pre.ee (Pre.keys c)) e d (PreRename.occurrence_index acc))
      (PreRename.fresh_index acc) (PreRename.link_index acc) (PreRename.unsafe_index acc) known).
Proof.
  intros Hacc Hle Hd; constructor.
  - apply Map.wf_set; exact (origins_occurrences_wf _ Hacc).
  - exact (origins_links_wf _ Hacc).
  - intros query value Hget; cbn [PreRename.occurrence_index] in Hget.
    rewrite Map.get_set in Hget by exact (origins_occurrences_wf _ Hacc).
    destruct (eqb (Pre.ee (Pre.keys c)) query e).
    + inversion Hget; subst value; exact Hd.
    + apply (origin_weaken Hle); exact (origins_occurrences _ Hacc query value Hget).
  - intros key op Hget; apply (origin_weaken Hle); exact (origins_links _ Hacc key op Hget).
Qed.

(** Actual occurrence selection preserves origins and exposes the created fresh token for definitions. *)
Theorem occurrence_origins :
  forall e {instance work}, local_origins work ->
    let result := PreRename.occurrence c e instance work in
    local_origins (fst result) /\
    incl (PreRename.created (snd work)) (PreRename.created (snd (fst result))) /\
    forall id u, snd result = Some (id, u) ->
      In (PreFrg.Fresh e u) (PreRename.created (snd (fst result))).
Proof.
  intros e instance [frames acc] [Hframes Hacc]; rewrite PreRename.occurrence_equation.
  destruct instance as [[id u]|].
  2: { split; [split; assumption|split; [apply incl_refl|discriminate]]. }
  cbn zeta; destruct (PreRename.frame_reuse c (PreRename.top_id frames id u) u);
    cbn [fst snd].
  - split; [split|split; [apply incl_refl|discriminate]].
    + apply store_origins; [exact Hframes|exact (origins_frames _ _ Hframes id u)].
    + apply set_occurrence_origins; [exact Hacc|apply incl_refl|].
      exact (origins_frames _ _ Hframes id u).
  - assert (Hle : incl (PreRename.created acc) (PreFrg.Fresh e u :: PreRename.created acc)).
    { intros d Hd; now right. }
    split; [split|split].
    + exact (scope_weaken Hle Hframes).
    + pose proof (set_occurrence_origins acc e (PreFrg.Fresh e u) _ Hacc Hle
        (or_introl eq_refl)) as Hnew.
      destruct Hnew; constructor; assumption.
    + exact Hle.
    + intros other value Heq; inversion Heq; subst other value; now left.
Qed.

Local Lemma alter_origins instance work key :
  local_origins work ->
    local_origins (PreRename.alter c instance work key) /\
      PreRename.created (snd (PreRename.alter c instance work key)) =
        PreRename.created (snd work).
Proof.
  intros Hwork; destruct work as [frames acc]; destruct Hwork as [Hframes Hacc].
  rewrite PreRename.alter_equation; cbn [fst snd].
  assert (Hstore : scope_origins (PreRename.created acc)
    (PreRename.store frames (fst key)
      (PreRename.Frame (PreRename.selected (PreRename.top_id frames (fst key) (snd key))) false))).
  { apply store_origins; [exact Hframes|exact (origins_frames _ _ Hframes (fst key) (snd key))]. }
  destruct instance as [current|].
  - destruct (eqb positive_encoding (fst current) (fst key)).
    + split; [split; assumption|reflexivity].
    + destruct (mark_origins frames acc key Hacc) as [Hmark Heq].
      split; [split|exact Heq]; [cbn [fst snd]; rewrite Heq; exact Hstore|exact Hmark].
  - destruct (mark_origins frames acc key Hacc) as [Hmark Heq].
    split; [split|exact Heq]; [cbn [fst snd]; rewrite Heq; exact Hstore|exact Hmark].
Qed.

Local Lemma fold_alter_origins instance :
  forall keys work, local_origins work ->
    local_origins (fold_left (PreRename.alter c instance) keys work) /\
      PreRename.created (snd (fold_left (PreRename.alter c instance) keys work)) =
        PreRename.created (snd work).
Proof.
  intro keys; induction keys as [|key rest IH]; intros work Hwork; [auto|].
  cbn [fold_left]; destruct (alter_origins instance work key Hwork) as [Halter Heq].
  destruct (IH _ Halter) as [Hfinal Hcreated]; split; [exact Hfinal|congruence].
Qed.

Local Lemma definitions_origins index b parameter e fresh frames known :
  scope_origins known frames ->
  (forall id u, fresh = Some (id, u) -> In (PreFrg.Fresh e u) known) ->
    scope_origins known (PreRename.definitions c index b parameter e fresh frames).
Proof.
  intros Hframes Hfresh; rewrite PreRename.definitions_equation.
  assert (Hnew : scope_origins known (match fresh with
    | None => frames
    | Some (id, u) => PreRename.store frames id
        (PreRename.Frame (PreFrg.Operand (PreFrg.Fresh e u) true) true)
    end)).
  { destruct fresh as [[id u]|]; [|exact Hframes].
    apply store_origins; [exact Hframes|apply (Hfresh id u eq_refl)]. }
  destruct (eqb (Pre.ee (Pre.keys c)) e parameter); [|exact Hnew].
  apply (PreFrameStep.fold_preserves _ (scope_origins known)); [|exact Hnew].
  intros current pair Hcurrent; rewrite PreRename.install_phi_equation.
  apply store_origins; [exact Hcurrent|exact I].
Qed.

Local Lemma instruction_origins index b parameter work e :
  local_origins work ->
    local_origins (PreRename.instruction c index b parameter work e) /\
    incl (PreRename.created (snd work))
      (PreRename.created (snd (PreRename.instruction c index b parameter work e))).
Proof.
  intro Hwork; rewrite PreRename.instruction_equation.
  destruct (Map.get (Pre.ee (Pre.keys c)) e (PreRename.events index)) as [info|];
    [|split; [exact Hwork|apply incl_refl]].
  destruct (occurrence_origins e (instance := PreRename.evaluation info) (work := work) Hwork)
    as [Hobserved [Hle Hfresh]].
  destruct (fold_alter_origins (PreRename.evaluation info) (PreRename.alterations info)
    (fst (PreRename.occurrence c e (PreRename.evaluation info) work)) Hobserved)
    as [[Hframes Hacc] Hcreated].
  assert (Hdefinitions : local_origins
    (PreRename.definitions c index b parameter e
      (snd (PreRename.occurrence c e (PreRename.evaluation info) work))
      (fst (fold_left (PreRename.alter c (PreRename.evaluation info)) (PreRename.alterations info)
        (fst (PreRename.occurrence c e (PreRename.evaluation info) work)))),
      snd (fold_left (PreRename.alter c (PreRename.evaluation info)) (PreRename.alterations info)
        (fst (PreRename.occurrence c e (PreRename.evaluation info) work))))).
  { split; [|exact Hacc]; apply definitions_origins; [exact Hframes|].
    intros id u Htoken; cbn [snd]; rewrite Hcreated; exact (Hfresh id u Htoken). }
  destruct (mark_exit_origins index (PreRename.endpoint info) _ Hdefinitions) as [Hfinal Hexit].
  cbn zeta; split; [exact Hfinal|]; rewrite Hexit; cbn [snd]; rewrite Hcreated; exact Hle.
Qed.

Local Lemma fold_instruction_origins index b parameter :
  forall es work, local_origins work ->
    local_origins (fold_left (PreRename.instruction c index b parameter) es work) /\
    incl (PreRename.created (snd work))
      (PreRename.created (snd (fold_left (PreRename.instruction c index b parameter) es work))).
Proof.
  intro es; induction es as [|e rest IH]; intros work Hwork; cbn [fold_left].
  - split; [exact Hwork|apply incl_refl].
  - destruct (instruction_origins index b parameter work e Hwork) as [Hnext Hle].
    destruct (IH _ Hnext) as [Hfinal Htail]; split; [exact Hfinal|].
    intros d Hd; apply Htail; apply Hle; exact Hd.
Qed.

Local Lemma argument_origins frames acc arg :
  scope_origins (PreRename.created acc) frames -> output_origins acc ->
    output_origins (PreRename.select_argument c frames acc arg) /\
    PreRename.created (PreRename.select_argument c frames acc arg) = PreRename.created acc.
Proof.
  intros Hframes Hacc; rewrite PreRename.select_argument_equation; cbn zeta.
  set (frame := match PreRename.argument_id arg with
    | None => PreRename.missing (PreRename.argument_input arg)
    | Some id => PreRename.top_id frames id (PreRename.argument_input arg)
    end).
  assert (Hframe : origin (PreRename.created acc)
    (PreFrg.operand_version (PreRename.selected frame))).
  { unfold frame; destruct (PreRename.argument_id arg) as [id|]; [|exact I].
    exact (origins_frames _ _ Hframes id (PreRename.argument_input arg)). }
  set (operand := if PreRename.available frame then
    if eqb (Pre.eu (Pre.keys c)) (PreFrg.version_expr
      (PreFrg.operand_version (PreRename.selected frame))) (PreRename.argument_input arg)
    then PreRename.selected frame else PreFrg.Operand (PreFrg.Unavailable
      (PreRename.argument_input arg)) false
    else PreFrg.Operand (PreFrg.Unavailable (PreRename.argument_input arg)) false).
  assert (Hoperand : origin (PreRename.created acc) (PreFrg.operand_version operand)).
  { unfold operand; destruct (PreRename.available frame); [|exact I].
    destruct (eqb (Pre.eu (Pre.keys c)) (PreFrg.version_expr
      (PreFrg.operand_version (PreRename.selected frame))) (PreRename.argument_input arg));
      [exact Hframe|exact I]. }
  split; [constructor|reflexivity].
  - exact (origins_occurrences_wf _ Hacc).
  - apply Map.wf_set; exact (origins_links_wf _ Hacc).
  - exact (origins_occurrences _ Hacc).
  - intros key op Hget; cbn [PreRename.link_index] in Hget.
    rewrite Map.get_set in Hget by exact (origins_links_wf _ Hacc).
    fold frame in Hget.
    destruct (eqb (PreFrg.link_encoding c) key
      (PreRename.argument_phi arg, PreRename.argument_edge arg)).
    + assert (Hselected : op = operand).
      { inversion Hget; unfold operand; destruct (PreRename.available frame); reflexivity. }
      subst op; exact Hoperand.
    + exact (origins_links _ Hacc key op Hget).
Qed.

Local Lemma fold_argument_origins frames :
  forall (args : list (B * PreRename.argument B BE U)) acc,
    scope_origins (PreRename.created acc) frames -> output_origins acc ->
    output_origins (fold_left
      (fun current pair => PreRename.select_argument c frames current (snd pair)) args acc) /\
    PreRename.created (fold_left
      (fun current pair => PreRename.select_argument c frames current (snd pair)) args acc) =
      PreRename.created acc.
Proof.
  intro args; induction args as [|pair rest IH]; intros acc Hframes Hacc; [auto|].
  cbn [fold_left]; destruct (argument_origins frames acc (snd pair) Hframes Hacc) as [Hnext Heq].
  assert (Hnext_frames : scope_origins
    (PreRename.created (PreRename.select_argument c frames acc (snd pair))) frames).
  { rewrite Heq; exact Hframes. }
  destruct (IH _ Hnext_frames Hnext) as [Hfinal Hcreated]; split; [exact Hfinal|congruence].
Qed.

(** A whole block preserves selection origins and only extends the actual creation list. *)
Theorem block_origins :
  forall {index b frames acc}, local_origins (frames, acc) ->
    local_origins (PreRename.block c index b frames acc) /\
    incl (PreRename.created acc) (PreRename.created (snd (PreRename.block c index b frames acc))).
Proof.
  intros index b frames acc Hwork; rewrite PreRename.block_equation.
  set (entered := match SsaPoints.points_in_block (Pre.points (Pre.input c)) b with
    | [] => (frames, acc)
    | first :: _ => PreRename.mark_exit c index first (frames, acc)
    end).
  assert (Hentered : local_origins entered /\
    PreRename.created (snd entered) = PreRename.created acc).
  { unfold entered; destruct (SsaPoints.points_in_block (Pre.points (Pre.input c)) b);
      [split; [exact Hwork|reflexivity]|apply mark_exit_origins; exact Hwork]. }
  set (body := fold_left (PreRename.instruction c index b
    (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b))
    (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered).
  destruct (fold_instruction_origins index b
    (SsaPoints.parameter_edge (Pre.points (Pre.input c)) b)
    (SsaPoints.instruction_edges (Pre.points (Pre.input c)) b) entered (proj1 Hentered))
    as [[Hframes Hacc] Hle].
  fold body in Hframes, Hacc, Hle |- *.
  destruct (fold_argument_origins (fst body)
    (Index.find (Pre.eb (Pre.keys c)) b (PreRename.arguments index)) (snd body) Hframes Hacc)
    as [Hfinal Hcreated].
  set (final_acc := fold_left
    (fun current pair => PreRename.select_argument c (fst body) current (snd pair))
    (Index.find (Pre.eb (Pre.keys c)) b (PreRename.arguments index)) (snd body)) in *.
  change (local_origins (fst body, final_acc) /\
    incl (PreRename.created acc) (PreRename.created final_acc)).
  split; [split|].
  - change (scope_origins (PreRename.created final_acc) (fst body)).
    rewrite Hcreated; exact Hframes.
  - exact Hfinal.
  - rewrite Hcreated, <- (proj2 Hentered); exact Hle.
Qed.

(** Every saved task is checked against the current global creation list. *)
Definition walk_origins (current : PreRename.work B BE E U) : Prop :=
  output_origins (PreRename.output current) /\
  Forall (fun pair => scope_origins (PreRename.created (PreRename.output current)) (snd pair))
    (PreRename.pending current).

Definition result_output (result : PreRename.work B BE E U + PreRename.stopped B BE E U) :=
  match result with
  | inl current => PreRename.output current
  | inr final => PreRename.stop_output final
  end.

Definition result_origins (result : PreRename.work B BE E U + PreRename.stopped B BE E U) :=
  match result with
  | inl current => walk_origins current
  | inr final => output_origins (PreRename.stop_output final)
  end.

Local Lemma step_origins index current :
  walk_origins current ->
    result_origins (PreRename.step c index current) /\
    incl (PreRename.created (PreRename.output current))
      (PreRename.created (result_output (PreRename.step c index current))).
Proof.
  intros [Hacc Htasks]; rewrite PreRename.step_equation.
  destruct (PreRename.pending current) as [|[id frames] rest] eqn:Hpending.
  - split; [exact Hacc|apply incl_refl].
  - inversion Htasks as [|pair tail Hframes Hrest]; subst pair tail.
    destruct (FinSet.mem positive_encoding id (PreRename.visited current)).
    + split; [split; assumption|apply incl_refl].
    + destruct (Prepared.name_of (Pre.blocks c) id) as [b|];
        [|split; [exact Hacc|apply incl_refl]].
      destruct (block_origins (index := index) (b := b) (frames := frames)
        (acc := PreRename.output current) (conj Hframes Hacc))
        as [[Hscope Hfinal] Hle].
      split; [split; [exact Hfinal|]|exact Hle].
      apply Forall_app; split.
      * apply Forall_forall; intros [child scope] Hin; apply in_map_iff in Hin.
        destruct Hin as [edge [Heq Hedge]]; inversion Heq; subst scope; exact Hscope.
      * apply Forall_forall; intros pair Hin; apply (scope_weaken Hle).
        exact (proj1 (Forall_forall _ _) Hrest pair Hin).
Qed.

(** The actual fuel-driver history preserves origins and monotonicity for all raw outcomes. *)
Theorem runs_origins :
  forall {index budget current result}, runs (PreRename.step_c c index) budget current result ->
    walk_origins current -> result_origins result /\
      incl (PreRename.created (PreRename.output current)) (PreRename.created (result_output result)).
Proof.
  intros index budget current result Hrun; induction Hrun as [current|
    budget current final Hstop|budget current next result Hstep Hrun IH]; intro Hcurrent.
  - split; [exact Hcurrent|apply incl_refl].
  - pose proof (step_origins index current Hcurrent) as Hfinal.
    unfold PreRename.step in Hfinal; rewrite Hstop in Hfinal; exact Hfinal.
  - destruct (step_origins index current Hcurrent) as [Hnext Hfirst].
    unfold PreRename.step in Hnext, Hfirst; rewrite Hstep in Hnext, Hfirst.
    destruct (IH Hnext) as [Hfinal Hlast]; split; [exact Hfinal|].
    intros d Hd; apply Hlast; apply Hfirst; exact Hd.
Qed.

(** A prepared entry scope proves origin accounting for the same actual run and all saved scopes. *)
Theorem run_prepared_origins data :
  output_origins (PreRename.stop_output (PreRename.run c (PreRename.prepare c data))).
Proof.
  set (index := PreRename.prepare c data).
  assert (Hinitial : walk_origins (PreRename.initial index)).
  { split; rewrite PreRename.initial_equation; cbn [PreRename.output PreRename.pending].
    - exact empty_output_origins.
    - apply Forall_forall; intros [id frames] Hin; apply in_map_iff in Hin.
      destruct Hin as [root [Heq Hroot]]; inversion Heq; subst frames.
      change (scope_origins [] (PreRename.entry_scope index)).
      unfold index; rewrite (PreFrameCache.cached_entry c data _ (PreFrameCache.prepare_laws c data)).
      exact (initial_scope_origins _). }
  pose proof (proj1 (runs_origins (iterate_value (PreRename.step_c c index)
    (PreRename.walk_budget index) (PreRename.initial index)) Hinitial)) as Hrun.
  rewrite PreRename.run_equation.
  destruct (Cost.value (iterate (PreRename.step_c c index) (PreRename.walk_budget index)
    (PreRename.initial index))); [exact (proj1 Hrun)|exact Hrun].
Qed.

End Origins.

End PreFrameOrigins.
