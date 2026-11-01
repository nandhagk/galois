(** * Shared memory graph callback bodies

    These adapters retain every original outgoing, target and node encoder call in full preparation.
    For example, a target's returned node feeds the exact subsequent incoming-index encoder call.
    Builds on: full graph preparation and genuine external callback bodies. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Graph Require Import GraphCore GraphAuditBase.
Import List.ListNotations.

Inductive audit_snapshot_graph_body (CN OE TE : Type) : Type :=
  | AuditSnapshotNodeBody (events : list CN)
  | AuditSnapshotOutBody (events : list OE)
  | AuditSnapshotTargetBody (events : list TE).
Arguments AuditSnapshotNodeBody {CN OE TE} _.
Arguments AuditSnapshotOutBody {CN OE TE} _.
Arguments AuditSnapshotTargetBody {CN OE TE} _.

Definition audit_snapshot_graph_body_work {CN OE TE} (node_work : list CN -> nat)
    (out_work : list OE -> nat) (target_work : list TE -> nat)
    (body : audit_snapshot_graph_body CN OE TE) : nat :=
  match body with
  | AuditSnapshotNodeBody events => node_work events
  | AuditSnapshotOutBody events => out_work events
  | AuditSnapshotTargetBody events => target_work events
  end.

Definition audit_snapshot_graph_callbacks {N E CN OE TE}
    (node_enc : N -> positive * list CN) (out : N -> list E * list OE)
    (target : E -> N * list TE) :
    audit_prepare_callback_model N E (audit_snapshot_graph_body CN OE TE) :=
  @AuditPrepareCallbackModel N E (audit_snapshot_graph_body CN OE TE)
    (fun n => let '(edges, body) := out n in (edges, [AuditSnapshotOutBody body]))
    (fun e => let '(n, body) := target e in (n, [AuditSnapshotTargetBody body]))
    (fun n => let '(code, body) := node_enc n in (code, [AuditSnapshotNodeBody body])).

Fixpoint audit_snapshot_target_input_budget {N E TE} (target : E -> N * list TE)
    (node_budget : N -> nat) (target_budget : E -> nat) (edges : list E) : nat :=
  match edges with
  | [] => 0
  | e :: rest => target_budget e + node_budget (fst (target e)) +
      audit_snapshot_target_input_budget target node_budget target_budget rest
  end.

Fixpoint audit_snapshot_graph_input_budget {N E OE TE}
    (out : N -> list E * list OE) (target : E -> N * list TE)
    (node_budget out_budget : N -> nat) (target_budget : E -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | n :: rest => node_budget n + out_budget n +
      audit_snapshot_target_input_budget target node_budget target_budget (fst (out n)) +
      audit_snapshot_graph_input_budget out target node_budget out_budget target_budget rest
  end.
