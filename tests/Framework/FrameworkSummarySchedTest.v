(** * SCC summary policy cycle boundary

    A single representative of an SCC need not meet every cycle in that SCC.
    For example, two mutually recursive functions can each have a self-call.
    Builds on: FrameworkSummary and GraphModel. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCalls.
From Galois.Fixpoint Require Import FixpointAnalysis.
From Galois.Framework Require Import FrameworkSummary.
Import List.ListNotations.

Module SummarySchedBoundary.

(** Both listed functions call both functions, including themselves. *)
Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 | 1 => [0; 1] | _ => [] end)
    nat_encoding nat_encoding.

Example selected_representative :
  (Policy.widen_at (summary_policy_scc calls) 0,
   Policy.widen_at (summary_policy_scc calls) 1) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_self_edge :
  Graph.out (Calls.graph calls) 0 = [CallEdge 0 0; CallEdge 0 1].
Proof.
  vm_compute; reflexivity.
Qed.

(** The counterexample has a closed, duplicate-free, correctly sourced graph. *)
Theorem calls_wf : graph_wf (Calls.graph calls).
Proof.
  apply call_graph_wf.
  - repeat constructor; cbn; intuition discriminate.
  - intros f [<-|[]]; left; reflexivity.
  - intros f p Hsite.
    destruct f as [|[|f]]; cbn in Hsite; try contradiction;
      destruct Hsite as [<-|[]]; split; [reflexivity| |reflexivity|];
      cbn; auto.
  - intros p g Htarget.
    destruct p as [|[|p]]; cbn in Htarget; try contradiction;
      exact Htarget.
Qed.

(** Function zero has a nonempty cycle consisting of its self-call. *)
Theorem zero_cycle :
  path (Calls.graph calls) 0 [CallEdge 0 0] 0.
Proof.
  change (path (Calls.graph calls)
    (Graph.source (Calls.graph calls) (CallEdge 0 0)) [CallEdge 0 0] 0).
  constructor.
  - vm_compute; auto.
  - constructor.
Qed.

(** The actual SCC policy misses a listed cycle even on a well-formed call graph. *)
Theorem policy_scc_does_not_cut :
  ~ cycles_cut (Calls.graph calls)
      (fun f => Policy.widen_at (summary_policy_scc calls) f = true).
Proof.
  intro Hcut.
  destruct (Hcut 0 [CallEdge 0 0] (or_introl eq_refl) zero_cycle
    ltac:(discriminate)) as [Hselected|[e [Hin Hselected]]].
  - vm_compute in Hselected; discriminate.
  - destruct Hin as [<-|[]].
    vm_compute in Hselected; discriminate.
Qed.

End SummarySchedBoundary.
