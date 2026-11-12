(** * Recursive summary observations

    Two functions call each other and retain the old row order.
    For example, the all-true candidate satisfies both call rows.
    Builds on: Framework.Summary and Fixpoint.Query. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import Data.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CallsSig.
From Galois.Framework Require Import SummarySig Summary.
From Galois.Lattice Require Import LatticeSig.
Import List.ListNotations.

Module BoolOps <: LATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
End BoolOps.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Calls <: CALLS_OPS Prog NatKeyCode NatKeyCode.
  Definition functions (_ : unit) := [0; 1].
  Definition roots (_ : unit) := [0].
  Definition sites_of (_ : unit) f := match f with 0 => [0] | 1 => [1] | _ => [] end.
  Definition caller_of (_ : unit) (site : nat) := site.
  Definition resolve (_ : unit) site := match site with 0 => [1] | 1 => [0] | _ => [] end.
  Definition call_graph (_ : unit) := Digraph [] Empty.
  Definition calls p := flat_map (fun f =>
    flat_map (fun site => map (pair site) (resolve p site)) (sites_of p f)) (functions p).
End Calls.
Module Body <: BODY_OPS Prog NatKeyCode NatKeyCode BoolOps.
  Definition local (_ : unit) f := Nat.eqb f 1.
  Definition via_call (_ : unit) (_ _ : nat) (a : bool) := a.
  Definition entry (_ : unit) (_ _ : nat) := false.
End Body.
Module A := SummaryCode Prog NatKeyCode NatKeyCode Calls BoolOps Body.
Definition check (look : nat -> bool) := forallb (fun r =>
  row_ok BoolOps.leb look (A.target tt r)
    (eval_query (A.resume tt) look (S (length (A.deps tt r))) (A.start tt r))) (A.rows tt).

Example summary_row_order : A.rows tt =
  [SummaryLocal 0; SummaryLocal 1; SummaryCall 0 1; SummaryCall 1 0].
Proof. vm_compute; reflexivity. Qed.

Example summary_hand_candidate : check (fun _ => true) = true.
Proof. vm_compute; reflexivity. Qed.

Example summary_rejects_bottom : check (fun _ => false) = false.
Proof. vm_compute; reflexivity. Qed.
