(** * Numbered callback adequacy

    The numbered closures retain the original callback body and label lookup work.
    For example, an absent occurrence invokes the callback on the fallback label.
    Builds on: FixpointAuditObserveNumberAdequacy and numbered callback models. *)

From Stdlib Require Import Lia.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditEncoding.
From Galois.Fixpoint Require Import FixpointSystem FixpointObserve FixpointAuditWorklistCallbacks
  FixpointAuditObserveNumber FixpointAuditObserveNumberAdequacy FixpointAuditObserveNumberCallbacks.

(** * Original callback bodies *)

(** The target closure composes one label lookup with its actual target callback body. *)
Theorem fx_observe_numbered_target_source : fx_observe_numbered_target_source_statement.
Proof.
  intros X C A B S fallback table source budget i [Htarget [_ [Htarget_bound _]]].
  pose proof (fx_observe_label_source C fallback table i) as Hlabel.
  destruct (fx_observe_label fallback table i) as [label events] eqn:Hrun.
  change (label = observation_label fallback table i /\
    audit_map_source_work audit_nat_events_work events <= fx_observe_label_budget i) in Hlabel;
    destruct Hlabel as [Heq Hwork].
  destruct (Htarget label) as [body Hbody].
  pose proof (Htarget_bound label (System.target S label) body Hbody) as Hbound.
  unfold fx_observe_numbered_target; rewrite Hrun.
  rewrite Heq in *; exists body; repeat split; try assumption; try reflexivity; lia.
Qed.

(** The RHS closure composes one label lookup with its actual RHS callback body. *)
Theorem fx_observe_numbered_rhs_source : fx_observe_numbered_rhs_source_statement.
Proof.
  intros X C A B S fallback table source budget i [_ [Hrhs [_ Hrhs_bound]]].
  pose proof (fx_observe_label_source C fallback table i) as Hlabel.
  destruct (fx_observe_label fallback table i) as [label events] eqn:Hrun.
  change (label = observation_label fallback table i /\
    audit_map_source_work audit_nat_events_work events <= fx_observe_label_budget i) in Hlabel;
    destruct Hlabel as [Heq Hwork].
  destruct (Hrhs label) as [body Hbody].
  pose proof (Hrhs_bound label (System.rhs S label) body Hbody) as Hbound.
  unfold fx_observe_numbered_rhs; rewrite Hrun.
  rewrite Heq in *; exists body; repeat split; try assumption; try reflexivity; lia.
Qed.
