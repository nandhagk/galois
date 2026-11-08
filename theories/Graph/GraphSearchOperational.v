(** * Operational admission and fresh entry

    Search event blocks retain admission and fresh discovery without graph laws.
    For example, an insufficient prepared budget can leave frames open without repeating entry.
    Builds on: GraphSearch, GraphSearchInvariant and GraphSearchOrder. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchOrder.
Import List.ListNotations.

Module SearchOperational.

(** Every entry is admitted and fresh in the core reconstructed from the same event prefix. *)
Inductive events {E} (scope : Scope.t) :
    SearchRun.core E -> list (Search.event E) -> SearchRun.core E -> Prop :=
  | events_nil : forall c, events scope c [] c
  | events_cons : forall c ev rest final,
      (match ev with
      | Search.Enter v _ =>
        Scope.admits scope v = true /\ ~ In v (SearchRun.pre_rev c)
      | _ => True
      end) ->
      events scope (SearchRun.core_event c ev) rest final ->
      events scope c (ev :: rest) final.

(** Adjacent operational event blocks compose without a fuel-adequacy premise. *)
Theorem events_app {E} scope (c middle final : SearchRun.core E) first last :
  events scope c first middle -> events scope middle last final ->
    events scope c (first ++ last) final.
Proof.
  intros Hfirst Hlast. induction Hfirst; cbn [app]; [exact Hlast|].
  econstructor; eauto.
Qed.

Local Lemma trace_step_events {V E} (p : Prepared.t V E) scope w here next :
  SearchInvariant.representation (snd w) ->
  SearchRun.trace_step p scope w here next ->
    events scope (snd w) here (snd next).
Proof.
  intros Hrep Hstep. destruct Hstep as [u rest c|u e v pending rest c Hscope|
    u e v pending rest c Hscope Hname|u e v pending rest c name Hscope Hname Hcolor|
    u e v pending rest c name k Hscope Hname Hcolor Hnot]; cbn [snd].
  - econstructor; [exact I|]. rewrite SearchRun.core_event_equation. constructor.
  - constructor.
  - constructor.
  - econstructor; [exact I|]. rewrite SearchRun.core_event_equation.
    econstructor.
    + split; [exact Hscope|]. intro Hin.
      apply (SearchInvariant.seen_discovered _ Hrep) in Hin.
      pose proof (proj1 (SearchInvariant.tree_is_white c u v)
        (SearchRun.color_edge_kind c u v Search.Tree Hcolor)) as Hwhite.
      change (FinSet.mem positive_encoding v (SearchRun.seen c) = true) in Hin.
      rewrite Hwhite in Hin. discriminate.
    + rewrite SearchRun.core_event_equation. constructor.
  - econstructor; [exact I|]. rewrite SearchRun.core_event_equation. constructor.
Qed.

(** Every actual segment has fresh admitted entries, including segments stopped by short fuel. *)
Theorem trace_segment_events {V E} (p : Prepared.t V E) scope w evs final :
  SearchInvariant.representation (snd w) ->
  SearchRun.trace_segment p scope w evs final ->
    events scope (snd w) evs (snd final).
Proof.
  intros Hrep Hsegment. revert Hrep.
  induction Hsegment as [w|w here next later final Hstep Hlater IH]; intro Hrep.
  - constructor.
  - eapply events_app; [exact (trace_step_events p scope w here next Hrep Hstep)|].
    apply IH.
    pose proof (SearchInvariant.transition_representation p scope w Hrep) as Hnext.
    rewrite (SearchOrder.trace_step_equation p scope w here next Hstep) in Hnext.
    exact Hnext.
Qed.

(** A supplied root occurrence generates a fresh admitted event block on arbitrary prepared data. *)
Theorem root_events {V E} (p : Prepared.t V E) scope c v :
  SearchInvariant.representation c ->
  events scope c (snd (SearchRun.reference_root p scope c v))
    (fst (SearchRun.reference_root p scope c v)).
Proof.
  intro Hrep. rewrite SearchRun.reference_root_equation.
  destruct (Scope.admits scope v) eqn:Hscope; [|constructor].
  destruct (FinSet.mem positive_encoding v (SearchRun.seen c)) eqn:Hfresh;
    [constructor|].
  destruct (Prepared.name_of p v) as [name|]; [|constructor].
  pose proof (trace_segment_events p scope
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)
    _ _ (SearchInvariant.discover_representation c v None Hrep Hfresh)
    (SearchRun.reference_loop_trace p scope (Pos.to_nat (Prepared.fuel p))
      ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c))) as Hloop.
  destruct (SearchRun.reference_loop p scope (Pos.to_nat (Prepared.fuel p))
    ([(v, Prepared.succ_edges p v)], SearchRun.discover v None c)) as [w evs].
  cbn [fst snd] in Hloop |- *. econstructor.
  - split; [exact Hscope|]. intro Hin.
    apply (SearchInvariant.seen_discovered _ Hrep) in Hin. congruence.
  - rewrite SearchRun.core_event_equation. exact Hloop.
Qed.

(** Ordered supplied root occurrences retain operational entry evidence without readiness. *)
Theorem roots_events {V E} (p : Prepared.t V E) scope roots c :
  SearchInvariant.representation c ->
  events scope c (snd (SearchRun.reference_roots p scope roots c))
    (fst (SearchRun.reference_roots p scope roots c)).
Proof.
  revert c. induction roots as [|v rest IH]; intros c Hrep.
  - rewrite SearchRun.reference_roots_equation. constructor.
  - rewrite SearchRun.reference_roots_equation.
    pose proof (root_events p scope c v Hrep) as Hroot.
    pose proof (SearchInvariant.root_representation p scope c v Hrep) as Hnext.
    destruct (SearchRun.reference_root p scope c v) as [next here].
    cbn [fst snd] in Hroot, Hnext.
    pose proof (IH next Hnext) as Htail.
    destruct (SearchRun.reference_roots p scope rest next) as [final later].
    cbn [fst snd] in Htail |- *. eapply events_app; eassumption.
Qed.

(** Every core in an operational trace contains only admitted discoveries if its input does. *)
Theorem events_admitted {E} scope (c final : SearchRun.core E) evs :
  events scope c evs final ->
  Forall (fun v => Scope.admits scope v = true) (SearchRun.pre_rev c) ->
  Forall (fun v => Scope.admits scope v = true) (SearchRun.pre_rev final).
Proof.
  intro Hevents. induction Hevents as [c|c ev rest final Hentry Htail IH]; intro Hall.
  - exact Hall.
  - apply IH. rewrite SearchRun.core_event_equation.
    destruct ev as [v via|e u v k|v parent].
    + rewrite SearchRun.discover_equation. cbn [SearchRun.pre_rev].
      constructor; [exact (proj1 Hentry)|exact Hall].
    + exact Hall.
    + rewrite SearchRun.finish_equation. exact Hall.
Qed.

End SearchOperational.
