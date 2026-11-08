(** * SCC summary policy cycle boundary

    A single representative of an SCC need not meet every cycle in that SCC.
    For example, two mutually recursive functions can each have a self-call.
    Builds on: FrameworkSummary and GraphModel. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphSccSpec GraphReach.
From Galois.Program Require Import ProgramCalls.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointLeast FixpointAnalysis
  FixpointSolver FixpointKleene FixpointAnalyze.
From Galois.Framework Require Import FrameworkSummary FrameworkSummarySched FrameworkSummaryClosure.
Import List.ListNotations.

Module SummarySchedBoundary.

(** Both listed functions call both functions, including themselves. *)
Definition calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 | 1 => [0; 1] | _ => [] end)
    nat_encoding nat_encoding.

(** This predicate records the head-only policy observation checked at commit 07c2861.
    It is historical test data and is not the current computational policy. *)
Definition historical_head_only f := Nat.eqb f 1.

Example selected_representative :
  (historical_head_only 0, historical_head_only 1) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example current_all_listed :
  (Policy.widen_at (summary_policy_scc calls) 0,
   Policy.widen_at (summary_policy_scc calls) 1,
   Policy.widen_at (summary_policy_scc calls) 2) = (true, true, false).
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

(** The historical head-only policy misses a cycle on a well-formed call graph. *)
Theorem historical_policy_scc_does_not_cut :
  ~ cycles_cut (Calls.graph calls)
      (fun f => historical_head_only f = true).
Proof.
  intro Hcut.
  destruct (Hcut 0 [CallEdge 0 0] (or_introl eq_refl) zero_cycle
    ltac:(discriminate)) as [Hselected|[e [Hin Hselected]]].
  - vm_compute in Hselected; discriminate.
  - destruct Hin as [<-|[]].
    vm_compute in Hselected; discriminate.
Qed.

End SummarySchedBoundary.

Module SummarySchedFixture.

Example repaired_cycles_cut :
  cycles_cut (Calls.graph SummarySchedBoundary.calls)
    (fun f => Policy.widen_at (summary_policy_scc SummarySchedBoundary.calls) f = true).
Proof.
  apply SummarySched.policy_scc_cuts; exact nat_encoding_laws.
Qed.

Example repaired_self_cycles :
  (Policy.widen_at (summary_policy_scc SummarySchedBoundary.calls)
     (Graph.target (Calls.graph SummarySchedBoundary.calls) (CallEdge 0 0)),
   Policy.widen_at (summary_policy_scc SummarySchedBoundary.calls)
     (Graph.target (Calls.graph SummarySchedBoundary.calls) (CallEdge 1 1))) =
    (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example ordinary_mutual_cycle :
  path (Calls.graph SummarySchedBoundary.calls) 0 [CallEdge 0 1; CallEdge 1 0] 0.
Proof.
  change (path (Calls.graph SummarySchedBoundary.calls)
    (Graph.source (Calls.graph SummarySchedBoundary.calls) (CallEdge 0 1))
    [CallEdge 0 1; CallEdge 1 0] 0).
  constructor; [vm_compute; auto|].
  change (path (Calls.graph SummarySchedBoundary.calls)
    (Graph.source (Calls.graph SummarySchedBoundary.calls) (CallEdge 1 0))
    [CallEdge 1 0] 0).
  constructor; [vm_compute; auto|constructor].
Qed.

Definition recursive_calls : Calls.t nat nat :=
  Calls.of_pure [0; 1; 2] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | 2 => [2] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [2] | 2 => [1] | _ => [] end)
    nat_encoding nat_encoding.

Example callee_first_order :
  map (Policy.order (summary_policy_scc recursive_calls)) [0; 1; 2] =
    [4; 3; 3]%positive.
Proof.
  vm_compute; reflexivity.
Qed.

Example exact_prepared_reach_sets :
  map (fun f => map (fun g =>
    FinSet.mem nat_encoding g
      (SummaryClosure.row recursive_calls (Cost.value (Summary.closure_c recursive_calls)) f))
    [0; 1; 2]) [0; 1; 2] =
    [[true; true; true]; [false; true; true]; [false; true; true]].
Proof.
  vm_compute; reflexivity.
Qed.

Definition single : Calls.t nat nat :=
  Calls.of_pure [0] [0] (fun _ => []) (fun _ => 0) (fun _ => [])
    nat_encoding nat_encoding.

Example singleton_policy_boundary :
  (Policy.order (summary_policy_scc single) 0,
   Policy.widen_at (summary_policy_scc single) 0,
   Policy.widen_at (summary_policy_scc single) 1) = (2%positive, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition pair_calls : Calls.t nat nat :=
  Calls.of_pure [0; 1] [0]
    (fun f => match f with 0 => [0] | 1 => [1] | _ => [] end)
    (fun p => p)
    (fun p => match p with 0 => [1] | 1 => [0] | _ => [] end)
    nat_encoding nat_encoding.

Definition antitone : Summary.spec nat nat bool :=
  Summary.Make bool_lattice (fun _ => Cost.ret false) (fun _ _ a => Cost.ret (negb a)).

Definition first_zero : Policy.t nat :=
  Policy.Make (fun f => Cost.ret (if Nat.eqb f 0 then 1 else 2)%positive)
    (fun _ => Cost.ret false) 0 0.

Definition first_one : Policy.t nat :=
  Policy.Make (fun f => Cost.ret (if Nat.eqb f 1 then 1 else 2)%positive)
    (fun _ => Cost.ret false) 0 0.

(** This fixture engine performs policy-ordered shared raises.
    It is not an execution of analyze_ref, whose row order is fixed. *)
Definition scheduled_raises (pol : Policy.t nat) :=
  let sys := Analysis.system (summary_analysis pair_calls antitone) in
  let order := if Pos.leb (Policy.order pol 0) (Policy.order pol 1)
    then [Summary.SLocal 0; Summary.SLocal 1; Summary.SCall 0 1; Summary.SCall 1 0]
    else [Summary.SLocal 1; Summary.SLocal 0; Summary.SCall 1 0; Summary.SCall 0 1] in
  fst (Kleene.round nat_encoding bool_lattice sys order Map.empty).

Example nonmonotone_two_schedules :
  (map (lookup nat_encoding bool_lattice (scheduled_raises first_zero)) [0; 1],
   map (lookup nat_encoding bool_lattice (scheduled_raises first_one)) [0; 1]) =
    ([true; false], [false; true]).
Proof.
  vm_compute; reflexivity.
Qed.

Example both_schedules_are_checked_post_solutions :
  (check_post bool_lattice (Analysis.system (summary_analysis pair_calls antitone))
     (lookup nat_encoding bool_lattice (scheduled_raises first_zero)),
   check_post bool_lattice (Analysis.system (summary_analysis pair_calls antitone))
     (lookup nat_encoding bool_lattice (scheduled_raises first_one))) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example negation_is_not_monotone :
  ~ monotone_fun bool_lattice bool_lattice (Summary.via_call antitone 0 1).
Proof.
  intro Hmono; specialize (Hmono false true eq_refl); vm_compute in Hmono; discriminate.
Qed.

Definition observe_ref pol :=
  match analyze_ref (SummarySched.using_policy (summary_analysis pair_calls antitone) pol) 8 with
  | Outcome.Solved s => Some (map (proj1_sig s) [0; 1])
  | _ => None
  end.

Example reference_ignores_policy_order :
  (observe_ref first_zero, observe_ref first_one) =
    (Some [true; false], Some [true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

End SummarySchedFixture.

Module SummarySccClient.

Local Open Scope positive_scope.

Definition calls : Calls.t positive positive :=
  Calls.of_pure [1; 2]%positive [1]%positive
    (fun f => if Pos.eqb f 1 then [1]%positive else []) (fun _ => 1%positive)
    (fun p => if Pos.eqb p 1 then [2]%positive else []) positive_encoding positive_encoding.

(** The supplied line graph has one correctly sourced, closed call edge. *)
Theorem graph_ok : graph_wf (Calls.graph calls).
Proof.
  apply call_graph_wf.
  - repeat constructor; vm_compute; intuition discriminate.
  - intros f [<-|[]]; now left.
  - intros f p Hp.
    change (In p (if Pos.eqb f 1 then [1] else [])) in Hp.
    destruct (Pos.eqb f 1) eqn:Hf; [apply Pos.eqb_eq in Hf; subst f|contradiction].
    destruct Hp as [<-|[]]; split; [reflexivity|now left].
  - intros p g Hg.
    change (In g (if Pos.eqb p 1 then [2] else [])) in Hg.
    destruct (Pos.eqb p 1); [destruct Hg as [<-|[]]; right; now left|contradiction].
Qed.

Definition prepared := Prepared.prepare positive_encoding (Calls.graph calls).

(** Public reference preparation supplies the generic ID and adjacency laws. *)
Theorem prepared_ok : Prepared.ready prepared.
Proof.
  apply Prepared.prepare_ready; [exact positive_encoding_laws|exact graph_ok|].
  intro f; rewrite Calls.graph_out.
  change (NoDup (flat_map (fun p => map (CallEdge p)
    (if Pos.eqb p 1 then [2] else [])) (if Pos.eqb f 1 then [1] else []))).
  destruct (Pos.eqb f 1); vm_compute; repeat constructor; intuition discriminate.
Qed.

Local Lemma valid_ids u : Prepared.valid_id prepared u <-> u = 1%positive \/ u = 2%positive.
Proof.
  split.
  - intros [f [Hf Hid]].
    change (In f [1; 2]%positive) in Hf.
    destruct Hf as [<-|[<-|[]]]; vm_compute in Hid; inversion Hid; auto.
  - intros [-> | ->]; [exists 1%positive|exists 2%positive]; split; vm_compute; auto.
Qed.

Local Lemma arc_spec u e v :
  Prepared.arc prepared u e v <->
    u = 1%positive /\ e = CallEdge 1%positive 2%positive /\ v = 2%positive.
Proof.
  split.
  - intros [f [g [Hf [Hid [Htarget [Hs [Ht He]]]]]]].
    change (In f [1; 2]%positive) in Hf.
    destruct Hf as [<-|[<-|[]]]; vm_compute in He; [|contradiction].
    destruct He as [<-|[]].
    vm_compute in Ht; subst g; vm_compute in Hid, Htarget.
    repeat split; congruence.
  - intros [-> [-> ->]]; exists 1%positive, 2%positive.
    repeat split; vm_compute; auto.
Qed.

Local Lemma id_refl u :
  u = 1%positive \/ u = 2%positive ->
  Search.scoped_path prepared Reach.unrestricted u [] u.
Proof.
  intro Hu; constructor; [apply valid_ids; exact Hu|apply Reach.admits_unrestricted].
Qed.

Local Lemma path_shape u es v :
  Search.scoped_path prepared Reach.unrestricted u es v ->
  u = v \/ (u = 1%positive /\ v = 2%positive).
Proof.
  intro Hpath; induction Hpath as [u Hu Ha|u e w es v Hu Ha He Hpath IH].
  - now left.
  - apply arc_spec in He; destruct He as [-> [-> ->]].
    destruct IH as [Heq|[Hbad Hv]]; [right; auto|discriminate].
Qed.

Local Lemma reachable_ids u :
  Search.scoped_reachable prepared Reach.unrestricted [1%positive] u <->
    u = 1%positive \/ u = 2%positive.
Proof.
  split.
  - intros [r [es [[<-|[]] Hpath]]]; apply path_shape in Hpath; intuition congruence.
  - intros [-> | ->].
    + exists 1%positive, []; split; [now left|apply id_refl; now left].
    + exists 1%positive, [CallEdge 1%positive 2%positive]; split; [now left|].
      eapply Search.scoped_cons.
      * apply valid_ids; now left.
      * apply Reach.admits_unrestricted.
      * apply arc_spec; repeat split; reflexivity.
      * apply id_refl; now right.
Qed.

Local Lemma singleton_block u :
  u = 1%positive \/ u = 2%positive ->
  Scc.block prepared Reach.unrestricted [1%positive] [u].
Proof.
  intro Hu; split; [discriminate|split; [constructor; [tauto|constructor]|split]].
  - intros v [<-|[]]; apply reachable_ids; exact Hu.
  - intros v w [<-|[]]; split.
    + intros [<-|[]]; split; [apply reachable_ids; exact Hu|split];
        exists []; apply id_refl; exact Hu.
    + intros [Hreach [[es Huw] [gs Hwu]]].
      apply path_shape in Huw, Hwu; left; intuition congruence.
Qed.

Definition supplied_scc :=
  Scc.Result [[2%positive]; [1%positive]]
    (Map.of_list positive_encoding [(1%positive, 2%positive); (2%positive, 1%positive)]).

(** The hand-supplied SCC partition is exact without invoking an SCC producer. *)
Theorem supplied_scc_exact : Scc.exact prepared Reach.unrestricted [1%positive] supplied_scc.
Proof.
  constructor.
  - constructor; [apply singleton_block; now right|].
    constructor; [apply singleton_block; now left|constructor].
  - change (NoDup [2; 1]%positive).
    constructor; [cbn; intuition discriminate|].
    constructor; [cbn; tauto|constructor].
  - intro u; rewrite reachable_ids; vm_compute; intuition congruence.
  - apply Map.wf_of_list.
  - intros u i; split.
    + intro Hget.
      apply (proj2 (Map.elements_spec positive_encoding positive_encoding_laws u i _
        (Map.wf_of_list positive_encoding _))) in Hget.
      vm_compute in Hget.
      destruct Hget as [Heq|[Heq|[]]]; inversion Heq; subst u i.
      * exists [2%positive]; split; [reflexivity|now left].
      * exists [1%positive]; split; [reflexivity|now left].
    + intros [c [Hnth Hu]].
      change (nth_error [[2]; [1]]%positive (Nat.pred (Pos.to_nat i)) = Some c) in Hnth.
      destruct (Nat.pred (Pos.to_nat i)) as [|[|n]] eqn:Hi.
      * cbn in Hnth; injection Hnth as <-; destruct Hu as [<-|[]].
        assert (i = 1%positive).
        { apply Pos2Nat.inj; pose proof (Pos2Nat.is_pos i); cbn; lia. }
        subst i; vm_compute; reflexivity.
      * cbn in Hnth; injection Hnth as <-; destruct Hu as [<-|[]].
        assert (i = 2%positive).
        { apply Pos2Nat.inj; pose proof (Pos2Nat.is_pos i); cbn; lia. }
        subst i; vm_compute; reflexivity.
      * destruct n; discriminate Hnth.
  - intros u e v i j Harc Hi Hj Hneq.
    apply arc_spec in Harc; destruct Harc as [-> [-> ->]].
    vm_compute in Hi, Hj; inversion Hi; inversion Hj; subst; vm_compute; reflexivity.
Qed.

Example supplied_scc_order_client :
  (Policy.order (summary_policy_scc calls) 2 <
    Policy.order (summary_policy_scc calls) 1)%positive.
Proof.
  eapply (SummarySched.policy_scc_order calls prepared [1%positive] supplied_scc
    1%positive (CallEdge 1%positive 2%positive) 2%positive
    1%positive 2%positive 2%positive 1%positive positive_encoding_laws graph_ok
    (proj2 (proj2 prepared_ok)) (Prepared.prepare_graph _ _) supplied_scc_exact);
    vm_compute; intuition congruence.
Qed.

End SummarySccClient.

Module SummaryJoiningClient.

Definition calls := SummarySchedFixture.pair_calls.
Definition spec : Summary.spec nat nat bool :=
  Summary.Make bool_lattice (fun f => Cost.ret (Nat.eqb f 1)) (fun _ _ a => Cost.ret a).
Definition first := SummarySched.using_policy
  (summary_analysis calls spec) SummarySchedFixture.first_zero.
Definition second := SummarySched.using_policy
  (summary_analysis calls spec) SummarySchedFixture.first_one.

(** The first joining policy has an actual certified solved run. *)
Theorem first_solved : exists s, analyze first 8 = Outcome.Solved s.
Proof.
  assert (Htag : match analyze first 8 with Outcome.Solved _ => true | _ => false end = true).
  { vm_compute; reflexivity. }
  destruct (analyze first 8) as [s|have|why] eqn:Hrun;
    [exists s; reflexivity|discriminate|discriminate].
Qed.

(** The second joining policy has its own actual solved witness. *)
Theorem second_solved : exists s, analyze second 8 = Outcome.Solved s.
Proof.
  assert (Htag : match analyze second 8 with Outcome.Solved _ => true | _ => false end = true).
  { vm_compute; reflexivity. }
  destruct (analyze second 8) as [s|have|why] eqn:Hrun;
    [exists s; reflexivity|discriminate|discriminate].
Qed.

Definition first_result := solved_result (analyze first 8) first_solved.
Definition second_result := solved_result (analyze second 8) second_solved.

Example joining_policy_lookup_client :
  equivalent bool_lattice (proj1_sig first_result 0) (proj1_sig second_result 0).
Proof.
  exact (SummarySched.policy_independent calls spec SummarySchedFixture.first_zero
    SummarySchedFixture.first_one 8 8 first_result second_result
    nat_encoding_laws nat_encoding_laws bool_laws bool_lub
    ltac:(intros p g a b Hab; exact Hab) ltac:(intro f; reflexivity)
    ltac:(intro f; reflexivity) eq_refl eq_refl
    (solved_result_spec (analyze first 8) first_solved)
    (solved_result_spec (analyze second 8) second_solved) 0).
Qed.

Example selected_joining_lookups :
  (map (proj1_sig first_result) [0; 1; 2], map (proj1_sig second_result) [0; 1; 2]) =
    ([true; true; false], [true; true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

End SummaryJoiningClient.
