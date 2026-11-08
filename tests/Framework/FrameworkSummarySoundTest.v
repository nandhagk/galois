(** * Active summaries and matched contexts

    Fixtures exercise recursive summaries, real active frames and bounded matched stacks.
    For example, an effect in function two is covered by both suspended callers.
    Builds on: FrameworkSummarySound and FixpointAnalyze. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCalls ProgramCfg
  ProgramIcfg.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck FixpointAnalysis
  FixpointLeast FixpointSolver FixpointAnalyze.
From Galois.Framework Require Import FrameworkUtil FrameworkSummary FrameworkSummarySound
  FrameworkSummarySched FrameworkIfds FrameworkStack.
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

Module SummaryLocalClient.

Definition lat : lattice nat := simple Nat.leb 0 Nat.max.

(** Natural maxima satisfy the lattice bounds used by this client. *)
Theorem lat_laws : lattice_laws lat.
Proof.
  apply simple_laws.
  - apply Nat.leb_refl.
  - intros a b c Hab Hbc; apply Nat.leb_le in Hab, Hbc; apply Nat.leb_le; lia.
  - intro a; apply Nat.leb_le; lia.
  - intros a b; apply Nat.leb_le, Nat.le_max_l.
  - intros a b; apply Nat.leb_le, Nat.le_max_r.
Qed.

Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1; 2; 3] [0]
    (fun f => match f with 0 => [0; 3] | 1 => [1] | 2 => [2] | _ => [] end)
    (fun p => match p with 3 => 0 | _ => p end)
    (fun p => match p with 0 => [1] | 1 => [2] | 2 | 3 => [3] | _ => [] end)
    nat_encoding nat_encoding.

Definition spec : Summary.spec nat nat nat :=
  Summary.Make lat
    (fun f => Cost.ret (match f with 2 => 2 | 3 => 1 | _ => 0 end))
    (fun p g a => Cost.ret (a + S p + g)).

Definition link : CallsLink.t nat nat nat :=
  CallsLink.Make
    (fun s => match s with 0 => 0 | 1 => 1 | 2 | 4 => 2 | 3 => 3 | _ => 0 end)
    (fun s => match s with
      | 1 => [(0, 0)]
      | 2 | 4 => [(1, 1); (0, 0)]
      | 3 => [(2, 2); (1, 1); (0, 0)]
      | _ => []
      end).

Definition machine : semantics nat unit :=
  Semantics (fun s => s = 0) (fun s l t =>
    (s = 0 /\ l = [] /\ t = 1) \/
    (s = 1 /\ l = [] /\ t = 2) \/
    (s = 2 /\ l = [] /\ t = 3) \/
    (s = 3 /\ l = [] /\ t = 4) \/
    (s = 3 /\ l = [tt] /\ t = 3) \/
    (s = 4 /\ l = [tt] /\ t = 4)).

(** The client has three concrete pushes and a return that restores function two. *)
Theorem calls_ok : calls_laws machine calls link.
Proof.
  constructor.
  - intros f p Hp; destruct f as [|[|[|f]]]; vm_compute in Hp;
      intuition subst; reflexivity.
  - intros s Hinit; change (s = 0) in Hinit; subst s; split; [now left|reflexivity].
  - intros s Hreach f Hf; destruct s as [|[|[|[|[|s]]]]];
      vm_compute in Hf |- *; intuition congruence.
  - intros s l t Hreach Hstep; destruct Hstep as
      [[-> [-> ->]]|[[-> [-> ->]]|[[-> [-> ->]]|
        [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]]]]].
    + right; left; exists 0; vm_compute; auto.
    + right; left; exists 1; vm_compute; auto.
    + right; left; exists 2; vm_compute; auto.
    + right; right; exists 2, 2; split; reflexivity.
    + left; split; reflexivity.
    + left; split; reflexivity.
Qed.

Definition demand s := match s with 3 => 1 | 4 => 2 | _ => 0 end.
Definition cover : SummarySound.step_cover nat unit nat :=
  SummarySound.StepCover (fun a s _ _ => Nat.leb (demand s) a = true).

(** Nonidentity site-and-callee-sensitive lifting retains each actual step's demand bound. *)
Theorem summaries_ok : SummarySound.summary_laws machine calls link spec cover.
Proof.
  constructor.
  - intros a b Hab s l t Hreach Hstep Hcover.
    change (Nat.leb a b = true) in Hab.
    change (Nat.leb (demand s) a = true) in Hcover.
    change (Nat.leb (demand s) b = true).
    apply Nat.leb_le in Hab, Hcover; apply Nat.leb_le; lia.
  - intros s l t Hreach Hstep; destruct Hstep as
      [[-> [-> ->]]|[[-> [-> ->]]|[[-> [-> ->]]|
        [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]]]]]; reflexivity.
  - intros p g a s l t Hreach Hstep Hframe Hcover.
    change (Nat.leb (demand s) a = true) in Hcover.
    change (Nat.leb (demand s) (a + S p + g) = true).
    apply Nat.leb_le in Hcover; apply Nat.leb_le; lia.
Qed.

Definition base_context := Ctx.call_string 2 calls.

(** The syntactic root-to-three shortcut is rejected, while all concrete pushes are accepted. *)
Definition partial : Ctx.t nat nat (list nat) :=
  Ctx.Make (Ctx.ctx_enc base_context) (Ctx.contexts base_context)
    (Ctx.init_c base_context)
    (fun p g k => if Nat.eqb p 3 then Cost.ret None else Ctx.enter_c base_context p g k).

(** The supported partial policy is closed under its accepted entries. *)
Theorem partial_support : SummarySound.ctx_support calls partial.
Proof.
  constructor.
  - exact (SummarySound.ctx_initial_member (SummarySound.ctx_call_string_support calls 2)).
  - intros f p g k k' Hf Hk Hp Hg Henter.
    change (Cost.value (if Nat.eqb p 3 then Cost.ret None
      else Ctx.enter_c base_context p g k) = Some k') in Henter.
    destruct (Nat.eqb p 3); [discriminate|].
    exact (SummarySound.ctx_enter_closed (SummarySound.ctx_call_string_support calls 2)
      f p g k k' Hf Hk Hp Hg Henter).
Qed.

Definition context s :=
  match s with 1 => [0] | 2 | 4 => [1; 0] | 3 => [2; 1] | _ => [] end.
Definition saved s :=
  match s with
  | 1 => [[]]
  | 2 | 4 => [[0]; []]
  | 3 => [[1; 0]; [0]; []]
  | _ => []
  end.

(** Local annotation duties accept the actual pushes and restore the saved return context. *)
Theorem annotations_ok :
  SummarySound.ctx_annotation_laws machine calls link partial context saved.
Proof.
  constructor.
  - intros s Hinit; change (s = 0) in Hinit; subst s; split; reflexivity.
  - intros s l t Hreach Hstep; destruct Hstep as
      [[-> [-> ->]]|[[-> [-> ->]]|[[-> [-> ->]]|
        [[-> [-> ->]]|[[-> [-> ->]]|[-> [-> ->]]]]]]].
    + right; left; exists 0; vm_compute; auto.
    + right; left; exists 1; vm_compute; auto.
    + right; left; exists 2; vm_compute; auto.
    + right; right; exists 2, 2, [1; 0], [[0]; []]; repeat split; reflexivity.
    + left; repeat split; reflexivity.
    + left; repeat split; reflexivity.
Qed.

(** Each concrete state of the push-return prefix is reachable. *)
Theorem prefix_reachable n : n <= 4 -> reachable_state machine n.
Proof.
  induction n as [|n IH]; intro Hn.
  - exists 0, []; split; [reflexivity|constructor].
  - eapply (reachable_state_step machine n [] (S n)).
    + apply IH; lia.
    + destruct n as [|[|[|[|n]]]]; try lia; vm_compute; tauto.
Qed.

Definition ordinary := summary_analysis calls spec.
Definition contextual := ctx_summary_analysis calls partial spec.

(** The ordinary client really solves through the public analysis entry point. *)
Theorem ordinary_solved : exists s, analyze ordinary 8 = Outcome.Solved s.
Proof.
  assert (Htag : match analyze ordinary 8 with Outcome.Solved _ => true | _ => false end = true).
  { vm_compute; reflexivity. }
  destruct (analyze ordinary 8) as [s|have|why] eqn:Hrun;
    [exists s; reflexivity|discriminate|discriminate].
Qed.

(** The supported partial-context client also returns an actual certified solution. *)
Theorem contextual_solved : exists s, analyze contextual 8 = Outcome.Solved s.
Proof.
  assert (Htag :
    match analyze contextual 8 with Outcome.Solved _ => true | _ => false end = true).
  { vm_compute; reflexivity. }
  destruct (analyze contextual 8) as [s|have|why] eqn:Hrun;
    [exists s; reflexivity|discriminate|discriminate].
Qed.

Definition ordinary_result := solved_result (analyze ordinary 8) ordinary_solved.
Definition contextual_result := solved_result (analyze contextual 8) contextual_solved.

Example site_sensitive_results :
  (map (proj1_sig ordinary_result) [0; 1; 2; 3],
   map (proj1_sig contextual_result) [(0, []); (1, [0]); (2, [1; 0]); (3, [2; 1])]) =
    ([13; 11; 7; 1], [13; 11; 7; 1]).
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_rejects_a_listed_shortcut :
  (Ctx.enter partial 3 3 [], Ctx.enter partial 2 3 [1; 0]) = (None, Some [2; 1]).
Proof.
  vm_compute; reflexivity.
Qed.

Example lifted_active_lookup :
  SummarySound.step_covers cover (proj1_sig ordinary_result 0) 3 [tt] 3.
Proof.
  exact (SummarySound.sound machine calls link spec cover (proj1_sig ordinary_result)
    nat_encoding_laws nat_encoding_laws calls_ok summaries_ok (proj2_sig ordinary_result)
    3 [tt] 3 0 (prefix_reachable 3 ltac:(lia))
    ltac:(vm_compute; tauto) ltac:(vm_compute; tauto)).
Qed.

Example local_contextual_saved_lookup :
  SummarySound.step_covers cover (proj1_sig contextual_result (0, [])) 3 [tt] 3.
Proof.
  exact (SummarySound.ctx_sound_local machine calls link partial spec cover
    (proj1_sig contextual_result) context saved nat_encoding_laws nat_encoding_laws
    (FrameworkKey.list_laws nat_encoding nat_encoding_laws) partial_support calls_ok
    summaries_ok annotations_ok (proj2_sig contextual_result)
    3 [tt] 3 3 0 [] (prefix_reachable 3 ltac:(lia))
    ltac:(vm_compute; tauto) eq_refl eq_refl).
Qed.

Example returned_contextual_lookup :
  SummarySound.step_covers cover (proj1_sig contextual_result (2, [1; 0])) 4 [tt] 4.
Proof.
  exact (SummarySound.ctx_sound_local machine calls link partial spec cover
    (proj1_sig contextual_result) context saved nat_encoding_laws nat_encoding_laws
    (FrameworkKey.list_laws nat_encoding nat_encoding_laws) partial_support calls_ok
    summaries_ok annotations_ok (proj2_sig contextual_result)
    4 [tt] 4 0 2 [1; 0] (prefix_reachable 4 ltac:(lia))
    ltac:(vm_compute; tauto) eq_refl eq_refl).
Qed.

Example lifted_arguments_are_observable :
  (Summary.via_call spec 2 3 1, Summary.via_call spec 1 3 1,
   Summary.via_call spec 2 2 1) = (7, 6, 6).
Proof.
  vm_compute; reflexivity.
Qed.

Example accepted_call_uses_entered_lookup :
  leb lat (Summary.via_call spec 2 3 (proj1_sig contextual_result (3, [2; 1])))
    (proj1_sig contextual_result (2, [1; 0])) = true.
Proof.
  eapply (SummarySound.ctx_call_bound calls partial spec (proj1_sig contextual_result)
    nat_encoding_laws nat_encoding_laws
    (FrameworkKey.list_laws nat_encoding nat_encoding_laws) (proj2_sig contextual_result))
    with (f := 2); vm_compute; intuition congruence.
Qed.

Example rejected_entry_equation_is_bottom :
  Query.eval (System.rhs (Analysis.system contextual) (Summary.SCall 3 3, []))
    (proj1_sig contextual_result) = 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_post_equations :
  (forall f k, In f (Calls.functions calls) -> In k (Ctx.contexts partial) ->
    leb lat (Summary.local spec f) (proj1_sig contextual_result (f, k)) = true) /\
  (forall f p g k k', In f (Calls.functions calls) ->
    In p (Calls.sites_of calls f) -> In g (Calls.resolve calls p) ->
    In k (Ctx.contexts partial) -> Ctx.enter partial p g k = Some k' ->
    leb lat (Summary.via_call spec p g (proj1_sig contextual_result (g, k')))
      (proj1_sig contextual_result (Calls.caller_of calls p, k)) = true).
Proof.
  exact (proj1 (SummarySound.ctx_post_solution_iff calls partial spec
    (proj1_sig contextual_result) nat_encoding_laws nat_encoding_laws
    (FrameworkKey.list_laws nat_encoding nat_encoding_laws) lat_laws)
    (proj2_sig contextual_result)).
Qed.

(** The concrete prefix gives a root-and-call derivation in the partial context equations. *)
Theorem inner_context_reachable : SummarySound.ctx_reachable calls partial 3 [2; 1].
Proof.
  eapply SummarySound.ctx_call with (f := 2) (k := [1; 0]) (p := 2).
  - eapply SummarySound.ctx_call with (f := 1) (k := [0]) (p := 1).
    + eapply SummarySound.ctx_call with (f := 0) (k := []) (p := 0).
      * constructor; now left.
      * vm_compute; auto.
      * vm_compute; auto.
      * reflexivity.
    + vm_compute; auto.
    + vm_compute; auto.
    + reflexivity.
  - vm_compute; auto.
  - vm_compute; auto.
  - reflexivity.
Qed.

Example reachable_equation_client :
  (In 3 (Calls.roots calls) /\ [2; 1] = Ctx.init partial 3) \/
  exists caller c p, SummarySound.ctx_reachable calls partial caller c /\
    In p (Calls.sites_of calls caller) /\ In 3 (Calls.resolve calls p) /\
    Ctx.enter partial p 3 c = Some [2; 1].
Proof.
  exact (proj1 (SummarySound.ctx_reachable_equation calls partial 3 [2; 1])
    inner_context_reachable).
Qed.

Local Lemma partial_length p g k k' :
  Ctx.enter partial p g k = Some k' -> length k' <= 2.
Proof.
  change (Cost.value (if Nat.eqb p 3 then Cost.ret None
    else Ctx.enter_c base_context p g k) = Some k' -> length k' <= 2).
  destruct (Nat.eqb p 3); [discriminate|intro Henter].
  change (Ctx.enter (Ctx.call_string 2 calls) p g k = Some k') in Henter.
  rewrite SummarySound.ctx_call_string_enter in Henter; inversion Henter; subst k'.
  change (length (Stack.truncate 2 (p :: k)) <= 2).
  rewrite Stack.truncate_length; apply Nat.le_min_l.
Qed.

Example reachable_least_client :
  In 3 (Calls.functions calls) /\ length ([2; 1] : list nat) <= 2.
Proof.
  apply (SummarySound.ctx_reachable_least calls partial
    (fun f k => In f (Calls.functions calls) /\ length k <= 2)).
  - intros f Hroot; vm_compute in Hroot; destruct Hroot as [<-|[]]; vm_compute; auto.
  - intros f k p g k' Hclosed Hp Hg Henter; split.
    + destruct p as [|[|[|[|p]]]]; vm_compute in Hg |- *; intuition congruence.
    + exact (partial_length p g k k' Henter).
  - exact inner_context_reachable.
Qed.

End SummaryLocalClient.

Module SummaryInsensitiveClient.

Definition calls := SummarySoundFixture.calls.
Definition spec := SummarySoundFixture.purity.
Definition ordinary := summary_analysis calls spec.
Definition contextual := ctx_summary_analysis calls (Ctx.insensitive nat nat) spec.

(** Both recursive analyses have actual solved witnesses. *)
Theorem ordinary_solved : exists s, analyze ordinary 8 = Outcome.Solved s.
Proof.
  assert (Htag : match analyze ordinary 8 with Outcome.Solved _ => true | _ => false end = true).
  { vm_compute; reflexivity. }
  destruct (analyze ordinary 8) as [s|have|why] eqn:Hrun;
    [exists s; reflexivity|discriminate|discriminate].
Qed.

(** The second witness is obtained from the insensitive recursive run itself. *)
Theorem contextual_solved : exists s, analyze contextual 8 = Outcome.Solved s.
Proof.
  assert (Htag :
    match analyze contextual 8 with Outcome.Solved _ => true | _ => false end = true).
  { vm_compute; reflexivity. }
  destruct (analyze contextual 8) as [s|have|why] eqn:Hrun;
    [exists s; reflexivity|discriminate|discriminate].
Qed.

Definition ordinary_result := solved_result (analyze ordinary 8) ordinary_solved.
Definition contextual_result := solved_result (analyze contextual 8) contextual_solved.

(** The ordinary witness is least through the published generic analysis interface. *)
Theorem ordinary_least :
  least_solution bool_lattice (Analysis.system ordinary) (proj1_sig ordinary_result).
Proof.
  eapply analyze_least.
  - apply Summary.analysis_laws; [exact nat_encoding_laws|exact nat_encoding_laws|exact bool_laws].
  - exact bool_lub.
  - apply SummarySched.monotone;
      [exact nat_encoding_laws|exact nat_encoding_laws|exact bool_laws|].
    intros p g a b Hab; exact Hab.
  - intro f; reflexivity.
  - reflexivity.
  - apply solved_result_spec.
Qed.

(** The insensitive witness is least over the same recursive equations with unit keys. *)
Theorem contextual_least :
  least_solution bool_lattice (Analysis.system contextual) (proj1_sig contextual_result).
Proof.
  eapply analyze_least.
  - apply Summary.ctx_analysis_laws;
      [exact nat_encoding_laws|exact nat_encoding_laws|exact unit_encoding_laws|exact bool_laws].
  - exact bool_lub.
  - apply SummarySched.ctx_monotone; [exact nat_encoding_laws|exact nat_encoding_laws|
      exact unit_encoding_laws|exact bool_laws|].
    intros p g a b Hab; exact Hab.
  - intros [f []]; reflexivity.
  - reflexivity.
  - apply solved_result_spec.
Qed.

Example recursive_insensitive_equations :
  post_solution bool_lattice (Analysis.system ordinary)
    (fun f => proj1_sig contextual_result (f, tt)).
Proof.
  exact (proj1 (SummarySound.ctx_insensitive_agrees calls spec
    (proj1_sig contextual_result) nat_encoding_laws nat_encoding_laws bool_laws)
    (proj2_sig contextual_result)).
Qed.

Example recursive_insensitive_least_lookup :
  equivalent bool_lattice (proj1_sig contextual_result (1, tt)) (proj1_sig ordinary_result 1).
Proof.
  exact (SummarySound.ctx_insensitive_least_agrees calls spec
    (proj1_sig contextual_result) (proj1_sig ordinary_result)
    nat_encoding_laws nat_encoding_laws bool_laws contextual_least ordinary_least 1).
Qed.

Example recursive_insensitive_solved_lookup :
  equivalent bool_lattice (proj1_sig contextual_result (2, tt)) (proj1_sig ordinary_result 2).
Proof.
  exact (SummarySched.ctx_insensitive_results_agree calls spec 8 8
    contextual_result ordinary_result nat_encoding_laws nat_encoding_laws bool_laws bool_lub
    ltac:(intros p g a b Hab; exact Hab)
    (solved_result_spec (analyze contextual 8) contextual_solved)
    (solved_result_spec (analyze ordinary 8) ordinary_solved) 2).
Qed.

Example same_witness_observations :
  (map (proj1_sig ordinary_result) [0; 1; 2; 3],
   map (fun f => proj1_sig contextual_result (f, tt)) [0; 1; 2; 3]) =
    ([true; true; true; false], [true; true; true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

End SummaryInsensitiveClient.

Module SummaryMatchedClient.

Definition calls := SummarySoundFixture.chain.
Definition ifds := SummarySoundFixture.ifds.
Definition roots : list (Stack.config nat unit nat) := [(0, None, [])].
Definition machine := SummarySound.ctx_stack_semantics ifds roots.
Definition link : CallsLink.t (Stack.config nat unit nat) nat nat :=
  CallsLink.Make (fun c => fst (fst c)) (fun c => map (fun p => (p, p)) (snd c)).

(** The reachable stack configurations include both the inner state and its restored caller. *)
Definition domain (c : Stack.config nat unit nat) :=
  In c [(0, None, []); (1, None, [0]); (2, None, [1; 0]); (3, None, [2; 1; 0])].

Local Lemma step_domain c e d : domain c -> Stack.step ifds c e d -> domain d.
Proof.
  intros Hdomain Hstep.
  destruct Hstep as
    [e x y st He Hkind Hflow|e p x y st He Hkind Hflow|e p x y st He Hkind Hflow];
    vm_compute in He;
    destruct He as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    vm_compute in Hkind; try discriminate;
    inversion Hkind; subst;
    vm_compute in Hflow; destruct Hflow as [<-|[]];
    vm_compute in Hdomain |- *; intuition congruence.
Qed.

(** Every reachable source has one of the concrete matched stacks of the fixture. *)
Theorem reachable_domain : forall c, reachable_state machine c -> domain c.
Proof.
  apply reachable_ind.
  - intros c Hroot; destruct Hroot as [<-|[]]; left; reflexivity.
  - intros c l d Hreach IH [Hl [e Hstep]]; eapply step_domain; eassumption.
Qed.

(** The stack semantics uses a call link whose saved sites are the actual matched stack. *)
Theorem calls_ok : calls_laws machine calls link.
Proof.
  constructor.
  - intros f p Hp; destruct f as [|[|[|f]]]; vm_compute in Hp;
      intuition subst; reflexivity.
  - intros c Hroot; destruct Hroot as [<-|[]]; split; [now left|reflexivity].
  - intros c Hreach f Hf.
    pose proof (reachable_domain c Hreach) as Hdomain.
    destruct Hdomain as [<-|[<-|[<-|[<-|[]]]]];
      vm_compute in Hf |- *; intuition congruence.
  - intros c l d Hreach [Hl [e Hstep]].
    pose proof (reachable_domain c Hreach) as Hdomain.
    destruct Hstep as
      [e x y st He Hkind Hflow|e p x y st He Hkind Hflow|e p x y st He Hkind Hflow];
      vm_compute in He;
      destruct He as [<-|[<-|[<-|[<-|[<-|[]]]]]];
      vm_compute in Hkind; try discriminate; inversion Hkind; subst.
    + right; left; exists 0; vm_compute; intuition congruence.
    + right; left; exists 1; vm_compute; intuition congruence.
    + right; left; exists 2; vm_compute; intuition congruence.
    + exfalso; vm_compute in Hdomain; intuition congruence.
    + right; right; exists 2, 2; split; reflexivity.
Qed.

(** Erasing the saved caller identities gives the same concrete endpoint stack. *)
Theorem frame_sites n d st : map snd (CallsLink.frames link (n, d, st)) = st.
Proof.
  change (map snd (map (fun p => (p, p)) st) = st).
  rewrite map_map; apply map_id.
Qed.

Definition endpoint : Stack.config nat unit nat := (2, None, [1; 0]).

(** The supplied endpoint is reached by three pushes followed by the valid return. *)
Theorem matched_prefix : Stack.path ifds (0, None, []) endpoint.
Proof.
  eapply Stack.path_trans.
  - exact SummarySoundFixture.matched_three_calls.
  - exact SummarySoundFixture.matched_return_restores_stack.
Qed.

Example semantic_matched_context_at_return :
  exists k frames ks, SummarySound.ctx_frames calls (Ctx.call_string 2 calls)
    (CallsLink.here link endpoint) k frames ks /\
    map snd frames = [1; 0] /\
    SummarySound.ctx_reachable calls (Ctx.call_string 2 calls)
      (CallsLink.here link endpoint) k.
Proof.
  exact (SummarySound.ctx_matched_path ifds roots calls link (Ctx.call_string 2 calls)
    (0, None, []) 2 None [1; 0] calls_ok
    ltac:(intros p g k; eexists; apply SummarySound.ctx_call_string_enter)
    frame_sites (or_introl eq_refl) matched_prefix).
Qed.

Example semantic_matched_call_string_at_return :
  SummarySound.ctx_reachable calls (Ctx.call_string 2 calls)
    (CallsLink.here link endpoint) (Stack.truncate 2 [1; 0]).
Proof.
  exact (SummarySound.ctx_matched_call_string ifds roots calls link 2
    (0, None, []) 2 None [1; 0] calls_ok frame_sites (or_introl eq_refl) matched_prefix).
Qed.

Definition before_return : Stack.config nat unit nat := (3, None, [2; 1; 0]).

Example semantic_matched_context_before_return :
  exists k frames ks, SummarySound.ctx_frames calls (Ctx.call_string 2 calls)
    (CallsLink.here link before_return) k frames ks /\
    map snd frames = [2; 1; 0] /\
    SummarySound.ctx_reachable calls (Ctx.call_string 2 calls)
      (CallsLink.here link before_return) k.
Proof.
  exact (SummarySound.ctx_matched_path ifds roots calls link (Ctx.call_string 2 calls)
    (0, None, []) 3 None [2; 1; 0] calls_ok
    ltac:(intros p g k; eexists; apply SummarySound.ctx_call_string_enter)
    frame_sites (or_introl eq_refl) SummarySoundFixture.matched_three_calls).
Qed.

Example semantic_matched_call_string_before_return :
  SummarySound.ctx_reachable calls (Ctx.call_string 2 calls)
    (CallsLink.here link before_return) [2; 1].
Proof.
  exact (SummarySound.ctx_matched_call_string ifds roots calls link 2
    (0, None, []) 3 None [2; 1; 0] calls_ok frame_sites
    (or_introl eq_refl) SummarySoundFixture.matched_three_calls).
Qed.

Example semantic_three_push_truncation :
  Stack.truncate 2 [2; 1; 0] = [2; 1].
Proof.
  vm_compute; reflexivity.
Qed.

End SummaryMatchedClient.
