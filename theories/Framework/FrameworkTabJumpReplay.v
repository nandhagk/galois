(** * Coverage by actual caller and end-summary replay

    A call pass covers every recorded matching end, and an end pass covers every recorded caller.
    For example, a return discovered before its caller is replayed when that caller is installed.
    Builds on: FrameworkTabRecords and FrameworkTabJumpEffects. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabRecords FrameworkTabJumpProgress FrameworkTabJumpEffects.
Import List.ListNotations.

Module TabJumpReplay.

Section Replay.
Context {N E P D A F} (I : Ide.t N E P D A F).
Context (HK : encoding_laws (Jump.enc I)).
Context (HL : lattice_laws (Micro.lat (Ide.micro I))).

(** Registering a call replays its own actual stored matching end occurrence. *)
Theorem call_covers start root a b s :
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  TabRecords.end_at I s (Jump.target a) b ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  TabJumpEffects.frontier I (Cost.value (Tab.call_c I root a s)) (Jump.Return root a b).
Proof.
  intros Hvalid Hshape Hend Hmatch; rewrite Tab.call_equation.
  apply (TabJumpEffects.fold_hit
    (TabJumpProgress.shape I)
    (fun t => TabJumpEffects.frontier I t (Jump.Return root a b))
    (fun t kv => Tab.return_ I root a (snd kv) t)
    (Map.elements (TabRecords.ends I s (Jump.target a)))
    (encode (Tab.arc_enc I) (Tab.arc_key b), b)).
  - intros t kv Ht Hin; apply TabJumpEffects.return_shape; assumption.
  - intros t kv Ht HP Hin; apply TabJumpEffects.return_frontier; assumption.
  - intros t Ht; apply TabJumpEffects.return_covers; assumption.
  - apply (proj2 (Map.elements_spec positive_encoding positive_encoding_laws _ _ _
      (TabRecords.end_buckets_wf Hvalid (Jump.target a)))); exact Hend.
  - exact Hshape.
Qed.

(** Registering an end replays the same actual caller from that end's callee-entry bucket. *)
Theorem end_covers start root a b s :
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  TabRecords.caller_at I s root a ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  TabJumpEffects.frontier I
    (Cost.value (Tab.end_c I (Jump.target a) b s)) (Jump.Return root a b).
Proof.
  intros Hvalid Hshape Hcaller Hmatch; rewrite Tab.end_equation.
  apply (TabJumpEffects.fold_hit
    (TabJumpProgress.shape I)
    (fun t => TabJumpEffects.frontier I t (Jump.Return root a b))
    (fun t kv => Tab.return_ I (fst (snd kv)) (snd (snd kv)) b t)
    (Map.elements (TabRecords.callers I s (Jump.target a)))
    (encode (Tab.incoming_enc I) (root, Tab.arc_key a), (root, a))).
  - intros t kv Ht Hin; apply TabJumpEffects.return_shape; assumption.
  - intros t kv Ht HP Hin; apply TabJumpEffects.return_frontier; assumption.
  - intros t Ht; apply TabJumpEffects.return_covers; assumption.
  - apply (proj2 (Map.elements_spec positive_encoding positive_encoding_laws _ _ _
      (TabRecords.caller_buckets_wf Hvalid (Jump.target a)))); exact Hcaller.
  - exact Hshape.
Qed.

End Replay.

End TabJumpReplay.
