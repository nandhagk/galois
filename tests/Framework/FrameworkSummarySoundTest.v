(** * Active summaries and matched contexts

    Fixtures exercise recursive summaries, real active frames and bounded matched stacks.
    For example, an effect in function two is covered by both suspended callers.
    Builds on: FrameworkSummarySound and FixpointAnalyze. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCalls ProgramCfg
  ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis
  FixpointSolver FixpointAnalyze.
From Galois.Framework Require Import FrameworkUtil FrameworkSummary FrameworkSummarySound
  FrameworkIfds FrameworkStack.
Import List.ListNotations.

Module SummarySoundFixture.

Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1; 2] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | 2 => [2] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [2] | 2 => [1] | _ => [] end)
    nat_encoding nat_encoding.

Definition purity : Summary.spec nat nat bool :=
  Summary.Make bool_lattice (fun f => Cost.ret (Nat.eqb f 2))
    (fun _ _ a => Cost.ret a).

Definition observe {X R A} (a : Analysis.t X R A) fuel xs :=
  match analyze a fuel with
  | Outcome.Solved s => Some (map (proj1_sig s) xs)
  | _ => None
  end.

Example recursive_pair_and_caller :
  observe (summary_analysis calls purity) 8 [0; 1; 2; 3] =
    Some [true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example recursive_bottom_rejected :
  check_post bool_lattice (Analysis.system (summary_analysis calls purity))
    (fun _ => false) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition link : CallsLink.t nat nat nat :=
  CallsLink.Make
    (fun s => match s with 0 => 0 | 1 => 1 | 2 => 2 | _ => 0 end)
    (fun s => match s with 1 => [(0, 0)] | 2 => [(1, 1); (0, 0)] | _ => [] end).

Definition machine : semantics nat unit :=
  Semantics (fun s => s = 0) (fun s l t =>
    (s = 0 /\ l = [] /\ t = 1) \/
    (s = 1 /\ l = [] /\ t = 2) \/
    (s = 2 /\ l = [tt] /\ t = 2)).

(** This finite machine's pushes use exactly the listed callers, sites and targets. *)
Theorem machine_calls : calls_laws machine calls link.
Proof.
  constructor.
  - intros f p Hp; destruct f as [|[|[|f]]]; cbn in Hp; try contradiction;
      destruct Hp as [<-|[]]; reflexivity.
  - intros s Hinit; change (s = 0) in Hinit; subst s; split; [now left|reflexivity].
  - intros s Hreach f Hf; destruct s as [|[|[|s]]];
      vm_compute in Hf |- *; intuition congruence.
  - intros s l t Hreach Hstep; destruct Hstep as
      [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]].
    + right; left; exists 0; cbn; auto.
    + right; left; exists 1; cbn; auto.
    + left; split; reflexivity.
Qed.

Definition cover : SummarySound.step_cover nat unit bool :=
  SummarySound.StepCover (fun a _ l _ => a = true \/ l = []).

(** Local effects cover the real transitions and identity lifting carries that coverage outward. *)
Theorem machine_summaries : SummarySound.summary_laws machine calls link purity cover.
Proof.
  constructor.
  - intros a b Hab s l t Hreach Hstep [Ha|Hl].
    + left; destruct a, b; vm_compute in Hab, Ha |- *; congruence.
    + right; exact Hl.
  - intros s l t Hreach Hstep; destruct Hstep as
      [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]]; cbn; auto.
  - intros p g a s l t Hreach Hstep Hframe Hcover; exact Hcover.
Qed.

(** The effectful inner activation is reached by both listed pushes. *)
Theorem machine_two_reachable : reachable_state machine 2.
Proof.
  exists 0, []; split; [reflexivity|].
  change (exec machine 0 ([] ++ []) 2).
  eapply exec_step with (s' := 1).
  - left; auto.
  - change (exec machine 1 ([] ++ []) 2).
    eapply exec_step with (s' := 2); [right; left; auto|constructor].
Qed.

Example active_step_covered :
  forall f, In f [2; 1; 0] -> SummarySound.step_covers cover true 2 [tt] 2.
Proof.
  intros f Hf.
  eapply (SummarySound.sound machine calls link purity cover (fun _ => true)
    nat_encoding_laws nat_encoding_laws machine_calls machine_summaries).
  - apply check_post_sound; vm_compute; reflexivity.
  - exact machine_two_reachable.
  - right; right; auto.
  - exact Hf.
Qed.

Example contextual_outer_caller_covers_inner_step :
  SummarySound.step_covers cover true 2 [tt] 2.
Proof.
  assert (Hpost : post_solution bool_lattice
    (Analysis.system (ctx_summary_analysis calls (Ctx.call_string 2 calls) purity))
    (fun _ => true)).
  { apply check_post_sound; vm_compute; reflexivity. }
  exact (SummarySound.ctx_call_string_sound machine calls link 2 purity cover (fun _ => true)
    nat_encoding_laws nat_encoding_laws machine_calls machine_summaries Hpost
    2 [tt] 2 2 0 machine_two_reachable (or_intror (or_intror (conj eq_refl
      (conj eq_refl eq_refl)))) eq_refl).
Qed.

Definition chain : Calls.t nat nat :=
  Calls.of_pure [0; 1; 2; 3] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | 2 => [2] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [2] | 2 => [3] | _ => [] end)
    nat_encoding nat_encoding.

Definition contexts := Ctx.call_string 2 chain.

Example context_lengths :
  (existsb (fun st => Nat.eqb (length st) 0) (Ctx.contexts contexts),
   existsb (fun st => Nat.eqb (length st) 1) (Ctx.contexts contexts),
   existsb (fun st => Nat.eqb (length st) 2) (Ctx.contexts contexts),
   forallb (fun st => Nat.leb (length st) 2) (Ctx.contexts contexts)) =
    (true, true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example three_calls_truncate :
  (Ctx.init contexts 0, Ctx.enter contexts 0 1 [],
   Ctx.enter contexts 1 2 [0], Ctx.enter contexts 2 3 [1; 0]) =
    ([], Some [0], Some [1; 0], Some [2; 1]).
Proof.
  vm_compute; reflexivity.
Qed.

Example context_chain_analysis :
  observe (ctx_summary_analysis chain contexts purity) 8
    [(0, []); (1, [0]); (2, [1; 0]); (3, [2; 1])] =
    Some [true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example chain_matched_annotation :
  SummarySound.ctx_frames chain contexts 3 [2; 1]
    [(2, 2); (1, 1); (0, 0)] [[1; 0]; [0]; []].
Proof.
  eapply SummarySound.ctx_frames_push with (f := 2) (p := 2).
  - eapply SummarySound.ctx_frames_push with (f := 1) (p := 1).
    + eapply SummarySound.ctx_frames_push with (f := 0) (p := 0).
      * constructor; now left.
      * vm_compute; auto.
      * vm_compute; auto.
      * vm_compute; reflexivity.
    + vm_compute; auto.
    + vm_compute; auto.
    + vm_compute; reflexivity.
  - vm_compute; auto.
  - vm_compute; auto.
  - vm_compute; reflexivity.
Qed.

Example chain_stack_correspondence :
  [2; 1] = Stack.truncate 2 (map snd [(2, 2); (1, 1); (0, 0)]).
Proof.
  exact (SummarySound.ctx_reachable_call_string chain 2 _ _ _ _ chain_matched_annotation).
Qed.

Definition icfg : Icfg.t nat nat nat :=
  Icfg.of_pure
    (Cfg.Make (Graph.of_pure [0] [0; 1; 2; 3]
      (fun n => match n with 0 => [0] | 1 => [1] | 2 => [2] | 3 => [3; 4] | _ => [] end)
      (fun e => match e with 4 => 3 | _ => e end)
      (fun e => match e with 0 => 1 | 1 => 2 | 2 => 3 | _ => 2 end))
      nat_encoding nat_encoding)
    nat_encoding (fun e => match e with 0 => Icfg.Call 0 | 1 => Icfg.Call 1
      | 2 => Icfg.Call 2 | 4 => Icfg.Return 2 | _ => Icfg.Return 1 end).

Definition ifds : Ifds.t nat nat nat unit :=
  Ifds.of_pure icfg unit_encoding [] (fun _ _ => [None]).

Example matched_three_calls :
  Stack.path ifds (0, None, []) (3, None, [2; 1; 0]).
Proof.
  eapply Stack.next with (e := 0) (c' := (1, None, [0])).
  - apply (@Stack.call nat nat nat unit ifds 0 0 None None []); vm_compute; auto.
  - eapply Stack.next with (e := 1) (c' := (2, None, [1; 0])).
    + apply (@Stack.call nat nat nat unit ifds 1 1 None None [0]); vm_compute; auto.
    + eapply Stack.next with (e := 2) (c' := (3, None, [2; 1; 0])).
      * apply (@Stack.call nat nat nat unit ifds 2 2 None None [1; 0]); vm_compute; auto.
      * constructor.
Qed.

Example mismatched_return_rejected :
  ~ Stack.step ifds (3, None, [2; 1; 0]) 3 (2, None, [1; 0]).
Proof.
  intro Hstep.
  pose proof (SummarySound.ctx_stack_step_shape ifds _ _ _ Hstep) as Hshape.
  vm_compute in Hshape; discriminate.
Qed.

Example matched_return_restores_stack :
  Stack.path ifds (3, None, [2; 1; 0]) (2, None, [1; 0]).
Proof.
  eapply Stack.next with (e := 4) (c' := (2, None, [1; 0])).
  - apply (@Stack.return_ nat nat nat unit ifds 4 2 None None [1; 0]);
      vm_compute; intuition congruence.
  - constructor.
Qed.

Definition no_calls : Calls.t nat nat :=
  Calls.of_pure [0] [0] (fun _ => []) (fun _ => 0) (fun _ => [])
    nat_encoding nat_encoding.

Example single_function_boundary :
  observe (summary_analysis no_calls purity) 2 [0; 1] = Some [false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example insensitive_boundary :
  (observe (summary_analysis no_calls purity) 2 [0],
   observe (ctx_summary_analysis no_calls (Ctx.insensitive nat nat) purity) 2 [(0, tt)]) =
    (Some [false], Some [false]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition unsupported : Ctx.t nat nat unit :=
  Ctx.Make unit_encoding [] (fun _ => Cost.ret tt) (fun _ _ _ => Cost.ret (Some tt)).

Example call_strings_have_closed_support :
  SummarySound.ctx_support chain contexts.
Proof.
  apply SummarySound.ctx_call_string_support.
Qed.

Example finite_support_is_not_initial_membership :
  ~ SummarySound.ctx_support no_calls unsupported.
Proof.
  intro Hsupport.
  pose proof (SummarySound.ctx_initial_member Hsupport 0 (or_introl eq_refl)) as Hmember.
  exact Hmember.
Qed.

Definition unclosed : Ctx.t nat nat (list nat) :=
  Ctx.Make (FrameworkKey.list nat_encoding) [[]] (fun _ => Cost.ret [])
    (fun p _ _ => Cost.ret (Some [p])).

Example initial_membership_is_not_enter_closure :
  ~ SummarySound.ctx_support chain unclosed.
Proof.
  intro Hsupport.
  pose proof (SummarySound.ctx_enter_closed Hsupport 0 0 1 [] [0]
    (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl)
    (or_introl eq_refl) eq_refl) as Hmember.
  vm_compute in Hmember; intuition discriminate.
Qed.

End SummarySoundFixture.
