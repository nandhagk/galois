(** * Expression definition origins and source identity

    Version points distinguish the entry from completed instruction and parameter edges.
    For example, an unavailable sentinel has no definition point.
    Builds on: AnalysesSsaPreFrg and AnalysesSsaPreContextTest. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom
  GraphFrontierSpec.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily AnalysesSsaPreFrg.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest.
Import List.ListNotations.

Example version_encoding_client : encoding_laws (PreFrg.version_encoding One.ctx).
Proof.
  exact (PreFrg.version_encoding_laws One.ctx One.laws).
Qed.

Example unavailable_has_no_point :
  PreFrg.version_point One.ctx (PreFrg.Unavailable tt) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example initial_has_entry_point :
  PreFrg.version_point One.ctx (PreFrg.Initial tt) = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_has_target_point :
  PreFrg.version_point One.ctx (PreFrg.Fresh tt tt) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example phi_has_parameter_target :
  PreFrg.version_point One.ctx (PreFrg.Phi tt tt) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example prepared_definition_entry :
  PreFrg.defs One.ctx (PreFrg.definition_index One.ctx [tt]) tt = [tt].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_definition_index :
  PreFrg.defs One.ctx (PreFrg.definition_index One.ctx []) tt = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_definition_values_retained :
  PreFrg.defs Parallel.ctx (PreFrg.definition_index Parallel.ctx [false; false]) false =
    [false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

(** The prepared bucket denotes the same source relation on the actual inhabited model. *)
Example prepared_definition_client :
  forall b, In b (PreFrg.defs One.ctx (PreFrg.definition_index One.ctx [tt]) tt) <->
    PreFrg.definition_block One.ctx tt b.
Proof.
  apply (PreFrg.defs_exact One.ctx [tt] tt One.laws); now left.
Qed.

Example singleton_frontier_row : PreFrg.frontier_row One.ctx tt = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_cached_frontier :
  PreFrg.cached_row One.ctx (PreFrg.frontier_rows One.ctx) tt = [].
Proof.
  vm_compute; reflexivity.
Qed.

(** Cached singleton-IDF lookup consumes the supplied exact block tree through its public contract. *)
Example cached_frontier_client :
  forall b, In b (PreFrg.cached_row One.ctx (PreFrg.frontier_rows One.ctx) tt) <->
    in_idf One.bg [tt] b.
Proof.
  apply (PreFrg.cached_row_exact One.ctx One.laws).
Qed.

(** The static definition identity theorem applies without assuming any built-graph result. *)
Example definition_identity_client :
  forall d other q, PreFrg.definition_domain One.ctx d ->
    PreFrg.definition_domain One.ctx other -> PreFrg.version_expr d = PreFrg.version_expr other ->
    PreFrg.version_point One.ctx d = Some q -> PreFrg.version_point One.ctx other = Some q ->
    d = other.
Proof.
  exact (PreFrg.definition_points_unique One.ctx One.laws).
Qed.

Example distinct_origins :
  @PreFrg.Initial unit unit unit tt <> PreFrg.Unavailable tt.
Proof.
  vm_compute; discriminate.
Qed.

Module Diamond.

Inductive block := Entry | Left | Right | Join.
Inductive block_edge := EL | ER | LJ | RJ.
Inductive stage := Before | Body | After.
Inductive edge := Bind (b : block) | Real (b : block) | Cross (be : block_edge).

Definition block_enc := of_pure (fun b =>
  match b with Entry => 1 | Left => 2 | Right => 3 | Join => 4 end)%positive.
Definition be_enc := of_pure (fun be =>
  match be with EL => 1 | ER => 2 | LJ => 3 | RJ => 4 end)%positive.
Definition stage_enc := of_pure (fun s =>
  match s with Before => 1 | Body => 2 | After => 3 end)%positive.
Definition point_enc := pair_encoding block_enc stage_enc.
Definition edge_codes := sum_encoding block_enc (sum_encoding block_enc be_enc).
Definition edge_key e :=
  match e with Bind b => inl b | Real b => inr (inl b) | Cross be => inr (inr be) end.
Definition edge_enc := Encoding (fun e => Cost.bind Cost.step (fun _ => encode_c edge_codes (edge_key e))).

Example block_enc_laws : encoding_laws block_enc.
Proof.
  constructor; intros [] [] H; vm_compute in H; congruence.
Qed.

Example be_enc_laws : encoding_laws be_enc.
Proof.
  constructor; intros [] [] H; vm_compute in H; congruence.
Qed.

Example stage_enc_laws : encoding_laws stage_enc.
Proof.
  constructor; intros [] [] H; vm_compute in H; congruence.
Qed.

Example point_enc_laws : encoding_laws point_enc.
Proof.
  apply pair_encoding_laws; [exact block_enc_laws|exact stage_enc_laws].
Qed.

Example edge_enc_laws : encoding_laws edge_enc.
Proof.
  assert (Hcodes : encoding_laws edge_codes).
  { apply sum_encoding_laws; [exact block_enc_laws|].
    apply sum_encoding_laws; [exact block_enc_laws|exact be_enc_laws]. }
  constructor; intros e other H.
  change (encode edge_codes (edge_key e) = encode edge_codes (edge_key other)) in H.
  apply (encode_injective Hcodes) in H; destruct e, other; cbn [edge_key] in H;
    inversion H; reflexivity.
Qed.

Definition bg : Graph.t block block_edge :=
  Graph.of_pure [Entry] [Entry; Left; Right; Join]
    (fun b => match b with Entry => [EL; ER] | Left => [LJ] | Right => [RJ] | Join => [] end)
    (fun be => match be with EL | ER => Entry | LJ => Left | RJ => Right end)
    (fun be => match be with EL => Left | ER => Right | LJ | RJ => Join end).
Definition pg : Graph.t (block * stage) edge :=
  Graph.of_pure [(Entry, Before)]
    [(Entry, Before); (Entry, Body); (Entry, After); (Left, Before); (Left, Body); (Left, After);
     (Right, Before); (Right, Body); (Right, After); (Join, Before); (Join, Body); (Join, After)]
    (fun n => let '(b, s) := n in
      match s with
      | Before => [Bind b]
      | Body => [Real b]
      | After => match b with Entry => [Cross EL; Cross ER] | Left => [Cross LJ]
          | Right => [Cross RJ] | Join => [] end
      end)
    (fun e => match e with Bind b => (b, Before) | Real b => (b, Body)
      | Cross be => (Graph.source bg be, After) end)
    (fun e => match e with Bind b => (b, Body) | Real b => (b, After)
      | Cross be => (Graph.target bg be, Before) end).
Definition bc := Cfg.Make bg block_enc be_enc.
Definition pc := Cfg.Make pg point_enc edge_enc.
Definition vars := Vars.of_pure pc unit_encoding (fun _ => []) (fun _ => []) (fun _ => []).
Definition points :=
  SsaPoints.of_pure vars bc (fun b => [(b, Before); (b, Body); (b, After)])
    (fun b => [Bind b; Real b]) Bind fst
    (fun e => match e with Cross be => Some be | _ => None end)
    (fun _ => []) (fun _ => []) (fun _ => None).
Definition ssa : Ssa.t block block_edge unit unit unit :=
  Ssa.of_pure bc unit_encoding [] (fun _ => Arbitrary) (fun _ => Entry)
    (fun _ => []) (fun _ => []) (fun _ => []).
Definition occurrence e :=
  match e with Real Left | Real Join => Some tt | _ => None end.
Definition expr :=
  Bitvector.of_pure pc unit_encoding [tt] Forward
    (fun e => match occurrence e with Some u => [u] | None => [] end)
    (fun _ => []) (fun _ => None).
Definition client : Pre.client block block_edge (block * stage) edge unit unit unit nat unit :=
  Pre.Client points ssa expr
    (Cost.lift (fun _ => 1%N) (fun _ => true)) (Cost.lift (fun _ => 1%N) occurrence) [tt] []
    (Cost.lift (fun _ => 1%N) (fun _ => 1%positive))
    (Cost.lift (fun _ => 1%N) (fun _ => [])) (fun _ _ => Some 0)
    (fun _ => Cost.lift (fun _ => 1%N) (fun _ => Some tt))
    (Cost.lift (fun _ => 1%N) (fun _ => false))
    (Cost.lift (fun _ => 1%N) (fun n =>
      match n with (Join, After) => true | _ => false end)).
Definition blocks := Prepared.prepare block_enc bg.
Definition point_graph := Prepared.prepare point_enc pg.
Definition parents := Map.of_list positive_encoding [(2, 1); (3, 1); (4, 1)]%positive.
Definition tree := DomCheck.of_parents blocks parents.
Definition ctx := Pre.Context client
  (Pre.Encs block_enc be_enc point_enc edge_enc unit_encoding unit_encoding) blocks point_graph tree.

Example blocks_wf : graph_wf bg.
Proof.
  constructor.
  - vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros [] H; vm_compute in H |- *; intuition congruence.
  - intros [] [] H; vm_compute in H |- *; intuition congruence.
  - intros [] [] _ H; vm_compute in H |- *; intuition congruence.
Qed.

Example points_wf : graph_wf pg.
Proof.
  constructor.
  - vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros [b s] H; destruct b, s; vm_compute in H |- *; intuition congruence.
  - intros [b s] e H; destruct b, s; destruct e as [b'|b'|be];
      try destruct b'; try destruct be; vm_compute in H |- *; intuition congruence.
  - intros [b s] e _ H; destruct b, s; destruct e as [b'|b'|be];
      try destruct b'; try destruct be; vm_compute in H |- *; intuition congruence.
Qed.

Example blocks_ready : Prepared.ready blocks.
Proof.
  apply Prepared.prepare_ready; [exact block_enc_laws|exact blocks_wf|].
  intros []; vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
Qed.

Example points_ready : Prepared.ready point_graph.
Proof.
  apply Prepared.prepare_ready; [exact point_enc_laws|exact points_wf|].
  intros [b s]; destruct b, s; vm_compute;
    repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
Qed.

Example accepted_tree : DomCheck.check blocks parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example tree_exact : Dom.exact blocks tree.
Proof.
  apply DomCheck.check_sound; [exact blocks_ready|apply Map.wf_of_list|exact accepted_tree].
Qed.

Example point_laws : ssa_point_laws points.
Proof.
  constructor.
  - exact points_wf.
  - intros [b s]; destruct b, s; vm_compute;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - exact blocks_wf.
  - intros []; vm_compute;
      repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros [b s]; split; intros _.
    + exists b; destruct b, s; vm_compute; tauto.
    + destruct b, s; vm_compute; tauto.
  - intros b; vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil.
  - intros b [owner s] _ H; vm_compute in H |- *; intuition congruence.
  - intros b _; discriminate.
  - intros b _; apply (point_chain_step (b, Before) (b, Body) [(b, After)] (Bind b) [Real b]).
    + now left.
    + reflexivity.
    + apply (point_chain_step (b, Body) (b, After) [] (Real b) []); [now left|reflexivity|constructor].
  - intros b e _ H; destruct e as [owner|owner|be]; vm_compute in H |- *; intuition congruence.
  - intros [b s] e _ Hout Hinternal; destruct b, s; destruct e as [owner|owner|be];
      try destruct owner; try destruct be; vm_compute in Hout, Hinternal |- *; intuition congruence.
  - intros b _; reflexivity.
  - intros b [] _; vm_compute; tauto.
  - intros [b s] e _ H; destruct b, s; destruct e as [owner|owner|be];
      try destruct owner; try destruct be; vm_compute in H |- *; intuition congruence.
  - intros [] _; reflexivity.
  - intros n e be _ _ _ [] H; contradiction.
  - intros be _; exists (Graph.source bg be, After), (Cross be).
    destruct be; vm_compute; tauto.
  - intros e other be _ _ H Hother; destruct e, other; vm_compute in H, Hother; congruence.
Qed.

Example strict_points : reachable_point_ssa points.
Proof.
  constructor.
  - exists (Entry, Before); reflexivity.
  - intros n [] _ [Huse|[e [_ Huse]]]; vm_compute in Huse; contradiction.
  - intros n e [] _ _ Hdef; vm_compute in Hdef; contradiction.
  - intros [] n e Hhome; discriminate.
Qed.

Lemma after_before b :
  reachable pg (b, Before) -> reachable pg (b, After).
Proof.
  intro H; exact (@reachable_step _ _ pg (Real b)
    (@reachable_step _ _ pg (Bind b) H (or_introl eq_refl)) (or_introl eq_refl)).
Qed.

Lemma left_before : reachable pg (Left, Before).
Proof.
  exact (@reachable_step _ _ pg (Cross EL)
    (after_before Entry (@reachable_entry _ _ pg (Entry, Before) (or_introl eq_refl)))
    (or_introl eq_refl)).
Qed.

Example before_reachable : forall b, reachable pg (b, Before).
Proof.
  intros [].
  - apply reachable_entry; now left.
  - exact left_before.
  - exact (@reachable_step _ _ pg (Cross ER)
      (after_before Entry (@reachable_entry _ _ pg (Entry, Before) (or_introl eq_refl)))
      (or_intror (or_introl eq_refl))).
  - exact (@reachable_step _ _ pg (Cross LJ) (after_before Left left_before) (or_introl eq_refl)).
Qed.

Example points_reachable : forall n, reachable pg n.
Proof.
  intros [b []].
  - apply before_reachable.
  - exact (@reachable_step _ _ pg (Bind b) (before_reachable b) (or_introl eq_refl)).
  - apply after_before, before_reachable.
Qed.

Example shapes : Pre.shape_laws ctx.
Proof.
  constructor.
  - intro b; constructor.
  - intros e [] _; now left.
  - intros [] H; discriminate.
  - intros [] _ [] H; contradiction.
  - intros [] [] _ _ _ _; reflexivity.
  - intros [] [] _ _ _; reflexivity.
  - intros be [] _ _; exists tt; reflexivity.
  - intros be [] [] _ _; reflexivity.
  - intros be [] [] _ _ _; reflexivity.
  - intros be [] [] _ _; reflexivity.
Qed.

Example graphs : Pre.graph_laws ctx.
Proof.
  constructor.
  - exact block_enc_laws.
  - exact be_enc_laws.
  - exact point_enc_laws.
  - exact edge_enc_laws.
  - exact unit_encoding_laws.
  - exact unit_encoding_laws.
  - exact point_laws.
  - exact strict_points.
  - reflexivity.
  - reflexivity.
  - apply Prepared.prepare_graph.
  - apply Prepared.prepare_graph.
  - exact blocks_ready.
  - exact points_ready.
  - exact tree_exact.
  - intros [] _.
    + apply reachable_entry; now left.
    + exact (@reachable_step _ _ bg EL (@reachable_entry _ _ bg Entry (or_introl eq_refl))
        (or_introl eq_refl)).
    + exact (@reachable_step _ _ bg ER (@reachable_entry _ _ bg Entry (or_introl eq_refl))
        (or_intror (or_introl eq_refl))).
    + exact (@reachable_step _ _ bg LJ
        (@reachable_step _ _ bg EL (@reachable_entry _ _ bg Entry (or_introl eq_refl))
          (or_introl eq_refl)) (or_introl eq_refl)).
  - intros n _; apply points_reachable.
  - exists Entry, (Entry, Before); repeat split; reflexivity.
  - intros b be Hb He; destruct b, be; vm_compute in Hb |- *; intuition congruence.
Qed.

Example kills : Pre.kill_laws ctx.
Proof.
  constructor.
  - intros e [] _ _ H; vm_compute in H; discriminate.
  - intros e [] _ H; contradiction.
  - intros e be _ _; reflexivity.
  - intros e [] H; destruct e as [b|b|be]; try destruct b; vm_compute in H |- *;
      try discriminate.
    all: split; [reflexivity|intros owner Heq; discriminate].
Qed.

Example runtime : Pre.runtime_laws ctx.
Proof.
  constructor; intros; reflexivity.
Qed.

Example laws : Pre.laws ctx.
Proof.
  exact (Pre.Laws ctx shapes graphs kills runtime).
Qed.

(** The actual product-closure producer emits the join phi and excludes the entry phi. *)
Example join_phi :
  match PreFrg.phi_sites ctx with
  | inl _ => False
  | inr data =>
    FinSet.mem (PreFrg.phi_encoding ctx) (Join, tt) (PreFrg.sites data) = true /\
    FinSet.mem (PreFrg.phi_encoding ctx) (Entry, tt) (PreFrg.sites data) = false
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The computed diamond is a client of the general four-clause phi exactness theorem. *)
Example phi_exact_client :
  exists data, PreFrg.phi_sites ctx = inr data /\
    forall u b, FinSet.mem (PreFrg.phi_encoding ctx) (b, u) (PreFrg.sites data) = true <->
      PreFrg.phi_needed ctx u b.
Proof.
  destruct (PreFrg.phi_sites_exact ctx laws) as [data [Hdata [_ [_ Hexact]]]].
  exists data; auto.
Qed.

End Diamond.
