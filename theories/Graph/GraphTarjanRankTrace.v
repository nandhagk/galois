(** * Actual trace preservation of emitted-edge ranks

    Frontier and examined-edge invariants close every emitted component before its owner is assigned.
    For example, all actual admitted arcs leave an emitted owner for an equal or earlier owner.
    Builds on: GraphTarjanTrace, GraphTarjanClosed and the complete actual Search root trace. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchExact GraphTarjan GraphTarjanState GraphTarjanBookkeeping
  GraphTarjanLow GraphTarjanTrace GraphTarjanFrontier GraphTarjanExamined GraphTarjanClosed.
Import List.ListNotations.

Module TarjanRankTrace.

(** The actual prefix carries frontier, examined occurrences and emitted ranks on the same core. *)
Record invariant {V E} (p : Prepared.t V E) scope roots (w : SearchRun.work E)
    (s : Tarjan.state) : Prop := Invariant {
  prefix : TarjanTrace.invariant p scope roots w s;
  frontier : TarjanFrontier.frontier (map fst (fst w)) s;
  examined : TarjanExamined.examined p scope (fst w) s;
  rank : TarjanClosed.output_rank p scope s
}.

(** Initial actual state has no open frontier, pending arcs or emitted owners. *)
Theorem initial_invariant {V E} (p : Prepared.t V E) scope roots :
  invariant p scope roots ([], @SearchRun.initial E) Tarjan.initial.
Proof.
  constructor.
  - apply TarjanTrace.initial_invariant.
  - apply TarjanFrontier.initial_frontier.
  - apply TarjanExamined.initial_examined.
  - apply TarjanClosed.initial_rank.
Qed.

Local Lemma tree_fresh {V E} (p : Prepared.t V E) scope roots w s u v :
  TarjanTrace.invariant p scope roots w s ->
  SearchRun.edge_color (snd w) u v Search.Tree ->
    Map.get positive_encoding v (Tarjan.disc s) = None.
Proof.
  intros HI Hcolor. apply (TarjanTrace.fresh_discovery p scope roots w s v HI).
  apply (proj1 (SearchInvariant.tree_is_white (snd w) u v)).
  now apply SearchRun.color_edge_kind.
Qed.

Local Lemma seen_number {V E} (p : Prepared.t V E) scope roots w s u v k :
  TarjanTrace.invariant p scope roots w s ->
  SearchRun.edge_color (snd w) u v k -> k <> Search.Tree ->
    exists d, Map.get positive_encoding v (Tarjan.disc s) = Some d.
Proof.
  intros HI Hcolor Hnot.
  pose proof (SearchRun.color_edge_kind _ _ _ _ Hcolor) as Hkind.
  assert (Hseen : FinSet.mem positive_encoding v (SearchRun.seen (snd w)) = true).
  { destruct (FinSet.mem positive_encoding v (SearchRun.seen (snd w))) eqn:Hseen;
      [reflexivity|].
    assert (Htree : SearchRun.edge_kind (snd w) u v = Search.Tree) by
      (apply (proj2 (SearchInvariant.tree_is_white (snd w) u v)); exact Hseen).
    congruence. }
  apply (SearchInvariant.seen_discovered _
    (TarjanTrace.representation _ _ _ _ (TarjanTrace.search _ _ _ _ _ HI))) in Hseen.
  rewrite (proj1 (TarjanTrace.discovery _ _ _ _ _ HI)).
  apply (proj2 (SearchInvariant.numbering_domain _ _ _
    (SearchInvariant.pre_numbering _
      (TarjanTrace.history _ _ _ _ (TarjanTrace.search _ _ _ _ _ HI))) v)).
  exact Hseen.
Qed.

(** Each actual event block preserves the open low-link frontier on the same remaining stack. *)
Theorem step_frontier {V E} (p : Prepared.t V E) scope roots w here next s :
  invariant p scope roots w s -> SearchRun.trace_step p scope w here next ->
  TarjanFrontier.frontier (map fst (fst next)) (SearchRun.apply_events Tarjan.visitor here s).
Proof.
  intros HI Htrace.
  pose proof (prefix _ _ _ _ _ HI) as HP.
  pose proof (TarjanLow.book _ _ _ _ (TarjanTrace.low _ _ _ _ _ HP)) as Hbook.
  pose proof (TarjanLow.numbers _ _ _ _ (TarjanTrace.low _ _ _ _ _ HP)) as Hnumbers.
  pose proof (frontier _ _ _ _ _ HI) as HF.
  destruct Htrace as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot].
  - change (TarjanFrontier.frontier (map fst rest)
      (Tarjan.exit u (match rest with [] => None | (parent, _) :: _ => Some parent end) s)).
    destruct rest as [|[parent es] rest];
      exact (TarjanFrontier.exit_frontier u _ s Hbook Hnumbers HF).
  - exact HF.
  - exact HF.
  - change (TarjanFrontier.frontier (v :: u :: map fst rest) (Tarjan.enter v s)).
    apply TarjanFrontier.enter_frontier; [exact Hbook|exact Hnumbers|exact HF|].
    exact (tree_fresh p scope roots _ s u v HP Hcolor).
  - change (TarjanFrontier.frontier (u :: map fst rest) (Tarjan.edge u v k s)).
    exact (TarjanFrontier.edge_frontier u _ s v k Hbook Hnumbers HF).
Qed.

(** Each actual occurrence is either retained unread or receives its scoped processed bound. *)
Theorem step_examined {V E} (p : Prepared.t V E) scope roots w here next s :
  Prepared.ready p -> invariant p scope roots w s ->
  SearchRun.trace_step p scope w here next ->
  TarjanExamined.examined p scope (fst next) (SearchRun.apply_events Tarjan.visitor here s).
Proof.
  intros Hready HI Htrace.
  pose proof (prefix _ _ _ _ _ HI) as HP.
  pose proof (TarjanTrace.low _ _ _ _ _ HP) as HL.
  pose proof (TarjanLow.book _ _ _ _ HL) as Hbook.
  pose proof (examined _ _ _ _ _ HI) as HE.
  destruct Htrace as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot].
  - change (TarjanExamined.examined p scope rest
      (Tarjan.exit u (match rest with [] => None | (parent, _) :: _ => Some parent end) s)).
    exact (TarjanExamined.exit_examined p scope u (map fst rest) s rest _ Hbook HE).
  - exact (TarjanExamined.skip_rejected p scope s u e v pending rest HE Hscope).
  - exact (TarjanExamined.skip_unknown p scope s u e v pending rest Hready HE Hname).
  - change (TarjanExamined.examined p scope
      ((v, Prepared.succ_edges p v) :: (u, pending) :: rest) (Tarjan.enter v s)).
    exact (TarjanExamined.enter_edge_examined p scope u (map fst rest) s e v pending rest
      Hready HL HE (tree_fresh p scope roots _ s u v HP Hcolor)).
  - destruct (seen_number p scope roots _ s u v k HP Hcolor Hnot) as [d Hd].
    change (TarjanExamined.examined p scope ((u, pending) :: rest) (Tarjan.edge u v k s)).
    exact (TarjanExamined.edge_examined p scope u (map fst rest) s e v pending rest k d
      Hbook HE Hd Hnot).
Qed.

(** Actual exit uses its own frontier and unread occurrences to preserve emitted owner ranks. *)
Theorem step_rank {V E} (p : Prepared.t V E) scope roots w here next s :
  invariant p scope roots w s -> SearchRun.trace_step p scope w here next ->
    TarjanClosed.output_rank p scope (SearchRun.apply_events Tarjan.visitor here s).
Proof.
  intros HI Htrace.
  pose proof (TarjanTrace.low _ _ _ _ _ (prefix _ _ _ _ _ HI)) as HL.
  pose proof (frontier _ _ _ _ _ HI) as HF.
  pose proof (examined _ _ _ _ _ HI) as HE.
  pose proof (rank _ _ _ _ _ HI) as HR.
  destruct Htrace as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot].
  - change (TarjanClosed.output_rank p scope
      (Tarjan.exit u (match rest with [] => None | (parent, _) :: _ => Some parent end) s)).
    exact (TarjanClosed.exit_rank p scope u rest s _ HL HF HE HR).
  - exact HR.
  - exact HR.
  - change (TarjanClosed.output_rank p scope (Tarjan.enter v s)).
    exact (TarjanClosed.enter_rank p scope s v HR).
  - change (TarjanClosed.output_rank p scope (Tarjan.edge u v k s)).
    exact (TarjanClosed.edge_rank p scope s u v k HR).
Qed.

(** The full actual-prefix invariant is preserved without a desired final-result premise. *)
Theorem step_invariant {V E} (p : Prepared.t V E) scope roots w here next s :
  Prepared.ready p -> invariant p scope roots w s ->
  SearchRun.trace_step p scope w here next ->
    invariant p scope roots next (SearchRun.apply_events Tarjan.visitor here s).
Proof.
  intros Hready HI Htrace. constructor.
  - exact (TarjanTrace.step_invariant p scope roots w here next s Hready
      (prefix _ _ _ _ _ HI) Htrace).
  - exact (step_frontier p scope roots w here next s HI Htrace).
  - exact (step_examined p scope roots w here next s Hready HI Htrace).
  - exact (step_rank p scope roots w here next s HI Htrace).
Qed.

(** Actual segments compose the same ordered event blocks and visitor states. *)
Theorem segment_invariant {V E} (p : Prepared.t V E) scope roots w evs final s :
  Prepared.ready p -> SearchRun.trace_segment p scope w evs final ->
  invariant p scope roots w s ->
    invariant p scope roots final (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intros Hready Htrace. revert s.
  induction Htrace as [w|w here next later final Hstep Htail IH]; intros s HI; [exact HI|].
  rewrite SearchRun.apply_events_app. apply IH.
  exact (step_invariant p scope roots w here next s Hready HI Hstep).
Qed.

(** Fresh actual root entry preserves all closure invariants from the drained preceding boundary. *)
Theorem root_start {V E} (p : Prepared.t V E) scope roots c s v name :
  Prepared.ready p -> invariant p scope roots ([], c) s -> In v roots ->
  Scope.admits scope v = true -> FinSet.mem positive_encoding v (SearchRun.seen c) = false ->
  Prepared.name_of p v = Some name ->
    invariant p scope roots ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)
      (Tarjan.enter v s).
Proof.
  intros Hready HI Hroot Hallowed Hwhite Hname.
  pose proof (prefix _ _ _ _ _ HI) as HP.
  pose proof (TarjanTrace.low _ _ _ _ _ HP) as HL.
  pose proof (TarjanLow.book _ _ _ _ HL) as Hbook.
  pose proof (TarjanTrace.fresh_discovery p scope roots _ s v HP Hwhite) as Hfresh.
  constructor.
  - exact (TarjanTrace.root_start p scope roots c s v name Hready HP Hroot Hallowed Hwhite Hname).
  - exact (TarjanFrontier.enter_frontier [] s v Hbook (TarjanLow.numbers _ _ _ _ HL)
      (frontier _ _ _ _ _ HI) Hfresh).
  - exact (TarjanExamined.enter_examined p scope [] [] s v Hready Hbook
      (examined _ _ _ _ _ HI) Hfresh).
  - exact (TarjanClosed.enter_rank p scope s v (rank _ _ _ _ _ HI)).
Qed.

(** A complete actual root trace preserves the owner-rank and emitted-edge closure invariant. *)
Theorem root_invariant {V E} (p : Prepared.t V E) scope roots c v evs final s :
  Prepared.ready p -> SearchRun.trace_root p scope c v evs final ->
  invariant p scope roots ([], c) s -> In v roots ->
    invariant p scope roots ([], final) (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intros Hready Htrace HI Hroot.
  destruct Htrace as [c v Hscope|c v Hscope Hseen|c v Hscope Hseen Hname|
    c v name evs final Hscope Hseen Hname Hsegment]; try exact HI.
  change (invariant p scope roots ([], final)
    (SearchRun.apply_events Tarjan.visitor evs (Tarjan.enter v s))).
  apply (segment_invariant p scope roots _ _ _ _ Hready Hsegment).
  exact (root_start p scope roots c s v name Hready HI Hroot Hscope Hseen Hname).
Qed.

(** All supplied occurrences compose their actual complete-root closure proofs in order. *)
Theorem roots_invariant {V E} (p : Prepared.t V E) scope roots todo c evs final s :
  Prepared.ready p -> SearchRun.trace_roots p scope todo c evs final ->
  invariant p scope roots ([], c) s -> incl todo roots ->
    invariant p scope roots ([], final) (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intros Hready Htrace. revert s.
  induction Htrace as [c|v rest c here next later final Hroot Htail IH];
    intros s HI Hincl; [exact HI|].
  rewrite SearchRun.apply_events_app. apply IH.
  - exact (root_invariant p scope roots c v here next s Hready Hroot HI
      (Hincl v (or_introl eq_refl))).
  - intros x Hx. apply Hincl. now right.
Qed.

(** The actual final core and actual visitor state satisfy the complete emitted-edge rank invariant. *)
Theorem actual_invariant {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  exists final,
    SearchRun.dfs p scope roots = SearchRun.result final /\
    invariant p scope roots ([], final)
      (snd (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))).
Proof.
  intro Hready. destruct (SearchExact.events_wf p scope roots Hready)
    as [final [Hresult Htrace]].
  exists final. split; [exact Hresult|]. rewrite SearchRun.run_events.
  apply (roots_invariant p scope roots roots SearchRun.initial _ final Tarjan.initial Hready Htrace).
  - apply initial_invariant.
  - intros x Hx. exact Hx.
Qed.

(** Every actual admitted arc from an emitted owner reaches an actual no-greater component owner. *)
Theorem actual_output_rank {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  TarjanClosed.output_rank p scope
    (snd (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))).
Proof.
  intro Hready. destruct (actual_invariant p scope roots Hready) as [final [_ HI]].
  exact (rank _ _ _ _ _ HI).
Qed.

End TarjanRankTrace.
