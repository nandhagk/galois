(** * Gen/kill candidate observations

    A backward loop checks the retained liveness candidates.
    For example, removing all facts rejects the old hand candidate.

    Groups:
    - [MayTests] The may-analysis accepts a hand candidate and rejects one with missing uses.

    Builds on: Framework.GenKill and Fixpoint.Query. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import KeySig Key TrieSet.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig GenKillSig GenKill.
Import List.ListNotations.

(** * Fixtures *)

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := nat. End Edge.

(** A CFG with three edges, whose sources and destinations form a small backward loop. *)
Module Loop <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0; 1; 2].
  Definition edges (_ : unit) := [0; 1; 2].
  Definition src (_ : unit) e := match e with 0 => 0 | _ => 1 end.
  Definition dst (_ : unit) e := match e with 2 => 2 | _ => 1 end.
End Loop.

Module Sets := TrieSetCode NatKeyCode.

(** The set of the given facts. *)
Definition facts (xs : list nat) := fold_left (fun s x => Sets.add x s) xs Sets.empty.

(** Liveness: edge 1 generates fact 0, edge 2 generates fact 1, and edge 0 kills fact 0. *)
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

(** The hand candidate that gives node 0 fact 1 and node 1 facts 0 and 1. *)
Definition candidate n := facts (match n with 0 => [1] | 1 => [0; 1] | _ => [] end).

(** Whether every row of the system accepts the candidate look. *)
Definition check (look : nat -> Sets.t) := forallb (fun r =>
  row_ok Lat.leb look (System.target tt r)
    (eval_query (System.resume tt) look (S (length (System.deps tt r))) (System.start tt r)))
  (System.rows tt).

(** * May *)

Module MayTests.

  (** The hand candidate passes every row of the liveness system. *)
  Example hand_candidate_accepted : check candidate = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A candidate with no facts at all fails some row. *)
  Example missing_uses_rejected : check (fun _ => Sets.empty) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

End MayTests.
