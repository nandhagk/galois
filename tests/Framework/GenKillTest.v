(** * Gen/kill candidate observations

    A backward loop checks the retained liveness candidates.
    For example, removing all facts rejects the old hand candidate.
    Builds on: Framework.GenKill and Fixpoint.Query. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key TrieSet.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig GenKillSig GenKill.
Import List.ListNotations.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.
Module Loop <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0; 1; 2].
  Definition edges (_ : unit) := [0; 1; 2].
  Definition src (_ : unit) e := match e with 0 => 0 | _ => 1 end.
  Definition dst (_ : unit) e := match e with 2 => 2 | _ => 1 end.
End Loop.
Module Sets := TrieSetCode NatKeyCode.
Definition facts (xs : list nat) := fold_left (fun s x => Sets.add x s) xs Sets.empty.
Module Live <: GENKILL_OPS Prog Edge NatKeyCode Sets.
  Definition dir := Backward.
  Definition may := true.
  Definition gen (_ : unit) e := facts (match e with 1 => [0] | 2 => [1] | _ => [] end).
  Definition kill (_ : unit) e := facts (match e with 0 => [0] | _ => [] end).
  Definition init (_ : unit) := Sets.empty.
End Live.
Module Lat := GenKillMayDomainCode NatKeyCode Sets.
Module Flow := GenKillMayFlowCode Prog NatKeyCode Edge NatKeyCode Sets Live Lat.
Module System := GenKillMayCode Prog NatKeyCode Edge Loop NatKeyCode Sets Live Lat Flow.
Definition candidate n := facts (match n with 0 => [1] | 1 => [0; 1] | _ => [] end).
Definition check (look : nat -> Sets.t) := forallb (fun r =>
  row_ok Lat.leb look (System.target tt r)
    (eval_query (System.resume tt) look (S (length (System.deps tt r))) (System.start tt r)))
  (System.rows tt).

Example may_hand_candidate : check candidate = true.
Proof. vm_compute; reflexivity. Qed.

Example may_missing_uses_rejected : check (fun _ => Sets.empty) = false.
Proof. vm_compute; reflexivity. Qed.
