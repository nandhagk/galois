(** * Memo execution tree adequacy

    Memo trees have unique observable endpoints and bounded branch overhead.
    For example, a completed hit returns its stored roots without spending credit.
    Builds on: source-shaped memo rules and binary natural arithmetic. *)

From Stdlib Require Import List NArith Lia.
From Galois.Collections Require Import CollectionsMap CollectionsFinSet.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteAdequacy.
Import List.ListNotations.

(** * Tree structure and occurrence counts *)

Scheme audit_memo_tree_mutual := Induction for audit_memo_tree Sort Prop
with audit_memo_children_mutual := Induction for audit_memo_children Sort Prop.

Combined Scheme audit_memo_mutual from audit_memo_tree_mutual, audit_memo_children_mutual.

(** Successor occurrence counts compose in the same order as execution traces. *)
Lemma audit_memo_occurrences_app N E CV CK NE (left right : list (audit_memo_event N E CV CK NE)) :
  audit_memo_successor_occurrences (left ++ right) =
    audit_memo_successor_occurrences left + audit_memo_successor_occurrences right.
Proof.
  induction left as [|event rest IH]; cbn; [reflexivity|].
  destruct event; cbn; rewrite IH; lia.
Qed.

(** * Totality and determinacy *)

(** Every input has the concrete producer's tree, including zero credit and malformed callbacks. *)
Theorem audit_memo_tree_total : audit_memo_tree_total_statement.
Proof.
  intros N E CV CK NE version_enc key_enc scope next active memo v fuel.
  pose proof (audit_memo_execute_tree N E CV CK NE version_enc key_enc scope next
    fuel active memo v) as Htree.
  exists (audit_memo_value (audit_memo_execute version_enc key_enc scope next fuel active memo v)),
    (audit_memo_cache (audit_memo_execute version_enc key_enc scope next fuel active memo v)),
    (audit_memo_credit (audit_memo_execute version_enc key_enc scope next fuel active memo v)),
    (audit_memo_body_events (audit_memo_execute version_enc key_enc scope next fuel active memo v)).
  exact Htree.
Qed.

(** Equal calls identify both components of their actual returned pairs. *)
Local Ltac audit_memo_identify_calls :=
  repeat match goal with
  | Hleft : ?call = (?left, ?body), Hright : ?call = (?right, ?body') |- _ =>
    let Hpair := fresh "Hpair" in
    assert (Hpair : (left, body) = (right, body')) by congruence;
    clear Hright; inversion Hpair; subst; clear Hpair
  | Hfuel : N.succ ?first = N.succ ?second |- _ =>
    apply N.succ_inj in Hfuel; subst
  end.

(** Primitive call determinacy and the child induction determine every tree endpoint and trace. *)
Lemma audit_memo_tree_unique N E CV CK NE version_enc key_enc scope next :
  (forall active memo v fuel result final remaining events,
    @audit_memo_tree N E CV CK NE version_enc key_enc scope next
      active memo v fuel result final remaining events ->
    forall result' final' remaining' events',
      audit_memo_tree version_enc key_enc scope next active memo v fuel
        result' final' remaining' events' ->
      result = result' /\ final = final' /\ remaining = remaining' /\ events = events') /\
  (forall active memo versions fuel result final remaining events,
    @audit_memo_children N E CV CK NE version_enc key_enc scope next
      active memo versions fuel result final remaining events ->
    forall result' final' remaining' events',
      audit_memo_children version_enc key_enc scope next active memo versions fuel
        result' final' remaining' events' ->
      result = result' /\ final = final' /\ remaining = remaining' /\ events = events').
Proof.
  apply audit_memo_mutual; intros;
    match goal with
    | |- _ = ?result /\ _ = ?final /\ _ = ?credit /\ _ = ?events =>
      match goal with
      | Hrun : audit_memo_tree _ _ _ _ _ _ _ _ result final credit events |- _ =>
        inversion Hrun; subst
      | Hrun : audit_memo_children _ _ _ _ _ _ _ _ result final credit events |- _ =>
        inversion Hrun; subst
      end
    end;
    try congruence; audit_memo_identify_calls; try congruence; try lia.
  all: repeat match goal with
  | IH : forall result final credit events,
      audit_memo_tree _ _ _ _ ?active ?memo ?v ?fuel result final credit events -> _,
    Hrun : audit_memo_tree _ _ _ _ ?active ?memo ?v ?fuel _ _ _ _ |- _ =>
    let Hequal := fresh "Hequal" in
    pose proof (IH _ _ _ _ Hrun) as Hequal; clear IH;
    destruct Hequal as [? [? [? ?]]]; subst
  | IH : forall result final credit events,
      audit_memo_children _ _ _ _ ?active ?memo ?vs ?fuel result final credit events -> _,
    Hrun : audit_memo_children _ _ _ _ ?active ?memo ?vs ?fuel _ _ _ _ |- _ =>
    let Hequal := fresh "Hequal" in
    pose proof (IH _ _ _ _ Hrun) as Hequal; clear IH;
    destruct Hequal as [? [? [? ?]]]; subst
  end; audit_memo_identify_calls; try congruence; repeat split; reflexivity.
Qed.

(** A fixed input has unique result, final cache, remaining credit and body trace. *)
Theorem audit_memo_tree_deterministic : audit_memo_tree_deterministic_statement.
Proof.
  intros N E CV CK NE version_enc key_enc scope next active memo v fuel
    result1 final1 remaining1 events1 result2 final2 remaining2 events2 Hfirst Hsecond.
  exact (proj1 (audit_memo_tree_unique N E CV CK NE version_enc key_enc scope next)
    active memo v fuel result1 final1 remaining1 events1 Hfirst
    result2 final2 remaining2 events2 Hsecond).
Qed.

(** * Source overhead *)

(** Remaining credit and trace overhead satisfy a common invariant for trees and child lists. *)
Lemma audit_memo_tree_control_bound N E CV CK NE version_enc key_enc scope next :
  (forall active memo v fuel result final remaining events,
    @audit_memo_tree N E CV CK NE version_enc key_enc scope next
      active memo v fuel result final remaining events ->
    2 * length events + 8 * N.to_nat remaining <=
      4 + 8 * N.to_nat fuel + 6 * audit_memo_successor_occurrences events) /\
  (forall active memo versions fuel result final remaining events,
    @audit_memo_children N E CV CK NE version_enc key_enc scope next
      active memo versions fuel result final remaining events ->
    2 * length events + 8 * N.to_nat remaining <=
      6 * length versions + 8 * N.to_nat fuel +
      6 * audit_memo_successor_occurrences events).
Proof.
  apply audit_memo_mutual; intros;
    repeat rewrite length_app;
    repeat rewrite audit_memo_occurrences_app;
    cbn [length audit_memo_successor_occurrences] in *;
    rewrite ?N2Nat.inj_succ in *; lia.
Qed.

(** Source overhead counts each expansion and each actual successor occurrence. *)
Theorem audit_memo_tree_source_bound : audit_memo_tree_source_bound_statement.
Proof.
  intros N E CV CK NE version_enc key_enc scope next active memo v fuel result final remaining
    events version_work key_work next_work Htree.
  pose proof (proj1 (audit_memo_tree_control_bound N E CV CK NE version_enc key_enc scope next)
    active memo v fuel result final remaining events Htree) as Hbound.
  unfold audit_memo_source_work; lia.
Qed.
