(** * Unconditional component support

    Emitted components contain distinct admitted IDs even when preparation laws do not hold.
    For example, short fuel can omit components without making an emitted member inadmissible.
    Builds on: GraphSearchOperational, GraphTarjanState and GraphTarjanBookkeeping. *)

From Stdlib Require Import List Bool PArith Permutation.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchInvariant GraphSearchOperational GraphSccSpec GraphTarjan GraphTarjanState
  GraphTarjanBookkeeping GraphTarjanPartition.
Import List.ListNotations.

Module TarjanOperational.

Definition support s := Tarjan.stack s ++ concat (Tarjan.emitted_rev s).

(** Pending and emitted IDs are distinct and come from the same reconstructed discovery prefix. *)
Definition supported {E} (c : SearchRun.core E) s :=
  NoDup (support s) /\ incl (support s) (SearchRun.pre_rev c).

Local Lemma lower_support v n s : support (Tarjan.lower v n s) = support s.
Proof.
  rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); reflexivity.
Qed.

Local Lemma edge_support u v k s : support (Tarjan.edge u v k s) = support s.
Proof.
  rewrite Tarjan.edge_equation. destruct k; try reflexivity.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try reflexivity.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try reflexivity.
  all: apply lower_support.
Qed.

Local Lemma emit_support root s : Permutation (support s) (support (Tarjan.emit root s)).
Proof.
  pose proof (TarjanStateFacts.pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  rewrite Tarjan.emit_equation. unfold support. cbn [Tarjan.stack Tarjan.emitted_rev concat].
  rewrite Hsplit at 1. rewrite !app_assoc.
  apply Permutation_app_tail, Permutation_app_comm.
Qed.

Local Lemma exit_support v parent s :
  Permutation (support s) (support (Tarjan.exit v parent s)).
Proof.
  rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|];
    try reflexivity.
  destruct (Pos.eqb l d); [apply emit_support|].
  destruct parent; [rewrite lower_support|]; reflexivity.
Qed.

Local Lemma supported_permutation {E} (c : SearchRun.core E) s next :
  Permutation (support s) (support next) -> supported c s -> supported c next.
Proof.
  intros Hperm [Hnodup Hincl]. split.
  - exact (Permutation_NoDup Hperm Hnodup).
  - intros v Hv. apply Hincl. eapply Permutation_in; [apply Permutation_sym, Hperm|exact Hv].
Qed.

Local Lemma apply_supported {E} scope (c : SearchRun.core E) ev s :
  (match ev with
  | Search.Enter v _ => Scope.admits scope v = true /\ ~ In v (SearchRun.pre_rev c)
  | _ => True
  end) ->
  supported c s ->
  supported (SearchRun.core_event c ev) (Visitor.apply Tarjan.visitor ev s).
Proof.
  intros Hentry Hsupport. rewrite Tarjan.apply_equation, SearchRun.core_event_equation.
  destruct ev as [v via|e u v k|v parent].
  - rewrite Tarjan.enter_equation, SearchRun.discover_equation.
    destruct Hsupport as [Hnodup Hincl]. split.
    + change (NoDup (v :: support s)). constructor; [|exact Hnodup].
      intro Hin. exact (proj2 Hentry (Hincl v Hin)).
    + intros x [<-|Hin]; [now left|right; exact (Hincl x Hin)].
  - unfold supported. rewrite edge_support. exact Hsupport.
  - rewrite SearchRun.finish_equation.
    exact (supported_permutation c s _ (exit_support v parent s) Hsupport).
Qed.

(** Fresh operational events maintain duplicate-free pending and emitted support. *)
Theorem events_supported {E} scope (c final : SearchRun.core E) evs s :
  SearchOperational.events scope c evs final -> supported c s ->
    supported final (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  intro Hevents. revert s.
  induction Hevents as [c|c ev rest final Hentry Htail IH]; intros s Hsupport.
  - rewrite SearchRun.apply_events_nil. exact Hsupport.
  - rewrite SearchRun.apply_events_cons. apply IH.
    exact (apply_supported scope c ev s Hentry Hsupport).
Qed.

Local Lemma initial_supported {E} : supported (@SearchRun.initial E) Tarjan.initial.
Proof.
  split; [constructor|intros v Hin; contradiction].
Qed.

(** Arbitrary prepared records produce duplicate-free emitted members and admit every such member. *)
Theorem partition_support {V E} (p : Prepared.t V E) scope roots :
  NoDup (concat (Scc.components (Tarjan.compute p scope roots))) /\
  forall v, In v (concat (Scc.components (Tarjan.compute p scope roots))) ->
    Scope.admits scope v = true.
Proof.
  pose proof (SearchOperational.roots_events p scope roots SearchRun.initial
    SearchInvariant.initial_representation) as Hevents.
  pose proof (events_supported scope _ _ _ _ Hevents initial_supported) as Hsupport.
  pose proof (SearchOperational.events_admitted scope _ _ _ Hevents
    (Forall_nil _)) as Hadmitted.
  rewrite Tarjan.compute_equation, SearchRun.run_equation.
  destruct (SearchRun.reference_roots p scope roots SearchRun.initial) as [final evs].
  cbn [fst snd] in Hsupport, Hadmitted |- *.
  rewrite Tarjan.result_equation. cbn [Scc.components].
  destruct Hsupport as [Hnodup Hincl].
  unfold support in Hnodup, Hincl.
  split.
  - apply (Permutation_NoDup (TarjanPartition.concat_rev_permutation _)).
    exact (proj2 (TarjanBook.nodup_parts _ _ Hnodup)).
  - intros v Hv.
    apply (proj1 (TarjanPartition.concat_rev_members _ v)) in Hv.
    apply Forall_forall with (x := v) in Hadmitted; [exact Hadmitted|].
    apply Hincl, in_or_app. now right.
Qed.

(** Every emitted component is duplicate-free and every member satisfies its actual scope predicate. *)
Theorem component_support {V E} (p : Prepared.t V E) scope roots c :
  In c (Scc.components (Tarjan.compute p scope roots)) ->
  NoDup c /\ forall v, In v c -> Scope.admits scope v = true.
Proof.
  intro Hc. destruct (partition_support p scope roots) as [Hnodup Hadmitted].
  split.
  - apply in_split in Hc. destruct Hc as [first [last Hsplit]].
    rewrite Hsplit, concat_app in Hnodup. cbn [concat] in Hnodup.
    apply TarjanBook.nodup_parts in Hnodup.
    exact (proj1 (TarjanBook.nodup_parts _ _ (proj2 Hnodup))).
  - intros v Hv. apply Hadmitted, in_concat. exists c. auto.
Qed.

End TarjanOperational.
