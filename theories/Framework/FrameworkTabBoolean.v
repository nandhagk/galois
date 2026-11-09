(** * Original-path witnesses for actual Boolean jump execution

    A true jump value has a balanced witness in the existing Stack.path semantics.
    For example, a true return contribution joins the caller path, callee path and matching return.
    Builds on: FrameworkTabRecords, FrameworkTabJumpEffects and FrameworkStack. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkStack
  FrameworkTabulate FrameworkTabPaths FrameworkTabRecords FrameworkTabJumpEffects.
Import List.ListNotations.

Module TabBoolean.

(** Reverse Boolean witnesses use these symbolic observations independently of value application. *)
Record laws {N E P D A} (I : Ide.t N E P D A bool) : Prop := {
  identity : Micro.id (Ide.micro I) = true;
  bottom : bot (Micro.lat (Ide.micro I)) = false;
  joining : forall f g, join (Micro.lat (Ide.micro I)) f g = orb f g;
  composing : forall f g, Micro.compose (Ide.micro I) f g = andb f g
}.
Arguments identity {N E P D A I}.
Arguments bottom {N E P D A I}.
Arguments joining {N E P D A I}.
Arguments composing {N E P D A I}.

(** Appending a stack suffix retains every original transition and its own edge. *)
Theorem path_suffix {N E P D} (I : Ifds.t N E P D) c next suffix :
  Stack.path I c next ->
  Stack.path I (fst c, snd c ++ suffix) (fst next, snd next ++ suffix).
Proof.
  intro Hpath; induction Hpath as [c|c e mid next Hstep Hpath IH].
  - apply Stack.refl.
  - eapply Stack.next; [|exact IH].
    destruct Hstep as [e x y stack He Hkind Hflow|
      e p x y stack He Hkind Hflow|e p x y stack He Hkind Hflow]; cbn [fst snd app].
    + apply Stack.internal; assumption.
    + apply Stack.call; assumption.
    + apply Stack.return_; assumption.
Qed.

(** Each prepared arc supplies its own actual original step and stack action. *)
Theorem arc_step {N E P D A F} (I : Ide.t N E P D A F) a :
  In a (Jump.arcs I) ->
  forall stack,
    match Jump.kind a with
    | Icfg.Internal =>
      Stack.step (Ide.ifds I) (Jump.source a, stack) (Jump.edge a) (Jump.target a, stack)
    | Icfg.Call p =>
      Stack.step (Ide.ifds I) (Jump.source a, stack) (Jump.edge a) (Jump.target a, p :: stack)
    | Icfg.Return p =>
      Stack.step (Ide.ifds I) (Jump.source a, p :: stack) (Jump.edge a) (Jump.target a, stack)
    end.
Proof.
  rewrite Jump.arcs_equation; intro Ha; apply in_flat_map in Ha.
  destruct Ha as [e [He Ha]]; apply in_flat_map in Ha.
  destruct Ha as [x [Hx Ha]]; apply in_map_iff in Ha.
  destruct Ha as [y [Heq Hy]]; subst a; intro stack.
  cbn [Jump.kind Jump.source Jump.target Jump.edge].
  destruct (Icfg.edge_kind (Ifds.icfg (Ide.ifds I)) e) as [|p|p] eqn:Hkind.
  - apply Stack.internal; assumption.
  - apply Stack.call; assumption.
  - apply Stack.return_; assumption.
Qed.

(** A true key retains a balanced witness of the same original execution. *)
Definition witnessed {N E P D A} (I : Ide.t N E P D A bool) (s : Tab.state N E P D bool) :=
  Map.wf positive_encoding (Tab.jumps s) /\
    forall root v, Jump.lookup I (Tab.jumps s) (root, v) = true ->
      Stack.path (Ide.ifds I) (root, []) (v, []).

Section Run.
Context {N E P D A} (I : Ide.t N E P D A bool) (start : N).
Context (HV : encoding_laws (IdeValue.key_enc I)) (HK : encoding_laws (Jump.enc I)).
Context (HS : encoding_laws (Icfg.site_enc (Ifds.icfg (Ide.ifds I)))).
Context (HB : laws I).

Local Lemma schedule_witnessed key s :
  witnessed I s -> witnessed I (Tab.schedule I key s).
Proof.
  intro Hwit; rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)); exact Hwit.
Qed.

Local Lemma update_witnessed root v f s :
  witnessed I s ->
  (f = true -> Stack.path (Ide.ifds I) (root, []) (v, [])) ->
  witnessed I (Tab.update I (root, v) f s).
Proof.
  intros [Hwf Hwit] Hcandidate; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) (root, v))).
  - split; assumption.
  - apply schedule_witnessed; split; [apply Map.wf_set; exact Hwf|].
    intros outer dst Htrue; cbn [Tab.jumps] in Htrue.
    rewrite TabJumpEffects.lookup_set in Htrue by exact Hwf.
    destruct (eqb (Jump.enc I) (outer, dst) (root, v)) eqn:Heq.
    + apply (eqb_true_iff (Jump.enc I) HK) in Heq.
      injection Heq as Hroot Hdst; subst outer dst.
      rewrite (joining HB) in Htrue; apply orb_true_iff in Htrue; destruct Htrue as [Hold|Hnew].
      * apply Hwit; exact Hold.
      * apply Hcandidate; exact Hnew.
    + apply Hwit; exact Htrue.
Qed.

Local Lemma return_path root a b s :
  witnessed I s -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  Jump.lookup I (Tab.jumps s) (root, Jump.source a) = true ->
  Jump.lookup I (Tab.jumps s) (Jump.target a, Jump.source b) = true ->
  Stack.path (Ide.ifds I) (root, []) (Jump.target b, []).
Proof.
  intros [Hwf Hwit] Ha Hb Hmatch Hbefore Hinside.
  rewrite Jump.matches_c_value in Hmatch.
  destruct (Jump.kind a) as [|p|p] eqn:Hcall; try discriminate.
  destruct (Jump.kind b) as [|q|q] eqn:Hreturn; try discriminate.
  apply (eqb_true_iff _ HS) in Hmatch; subst q.
  pose proof (arc_step I a Ha []) as Hpush; rewrite Hcall in Hpush.
  pose proof (arc_step I b Hb []) as Hpop; rewrite Hreturn in Hpop.
  pose proof (path_suffix (Ide.ifds I) _ _ [p] (Hwit _ _ Hinside)) as Hbody.
  cbn [fst snd app] in Hbody.
  eapply Stack.path_trans; [exact (Hwit _ _ Hbefore)|].
  eapply Stack.next; [exact Hpush|].
  eapply Stack.path_trans; [exact Hbody|].
  eapply Stack.next; [exact Hpop|apply Stack.refl].
Qed.

Local Lemma return_witnessed root a b s :
  witnessed I s -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  witnessed I (Tab.return_ I root a b s).
Proof.
  intros Hwit Ha Hb; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b))
    eqn:Hmatch; [|exact Hwit].
  apply update_witnessed; [exact Hwit|].
  rewrite !(composing HB); intro Htrue.
  apply andb_true_iff in Htrue; destruct Htrue as [Hret Hbody].
  apply andb_true_iff in Hbody; destruct Hbody as [Hinside Hpushed].
  apply andb_true_iff in Hpushed; destruct Hpushed as [Hcall Hbefore].
  apply (return_path root a b s); assumption.
Qed.

Local Lemma call_witnessed root a s :
  TabRecords.valid I start s -> witnessed I s -> In a (Jump.arcs I) ->
  witnessed I (Cost.value (Tab.call_c I root a s)).
Proof.
  intros Hvalid Hwit Ha; rewrite Tab.call_equation.
  refine (proj2 (TabJumpEffects.fold_closed (fun _ => True) (witnessed I)
    (fun t kv => Tab.return_ I root a (snd kv) t)
    (Map.elements (TabRecords.ends I s (Jump.target a)))
    (TabRecords.registered_call I root a s) _ _ Logic.I Hwit)).
  - intros t kv Ht Hin; exact Logic.I.
  - intros t [code b] Ht Hw Hin; apply return_witnessed; try assumption.
    exact (proj1 (proj2 (TabRecords.end_element I start s (Jump.target a) code b Hvalid Hin))).
Qed.

Local Lemma end_witnessed root a s :
  TabRecords.valid I start s -> witnessed I s -> In a (Jump.arcs I) ->
  witnessed I (Cost.value (Tab.end_c I root a s)).
Proof.
  intros Hvalid Hwit Ha; rewrite Tab.end_equation.
  refine (proj2 (TabJumpEffects.fold_closed (fun _ => True) (witnessed I)
    (fun t kv => Tab.return_ I (fst (snd kv)) (snd (snd kv)) a t)
    (Map.elements (TabRecords.callers I s root))
    (TabRecords.registered_end I root a s) _ _ Logic.I Hwit)).
  - intros t kv Ht Hin; exact Logic.I.
  - intros t [code [outer call]] Ht Hw Hin; apply return_witnessed; try assumption.
    exact (proj1 (proj2
      (TabRecords.caller_element I start s root code outer call Hvalid Hin))).
Qed.

Local Lemma arc_witnessed root a s :
  TabRecords.valid I start s -> witnessed I s -> In a (Jump.arcs I) ->
  witnessed I (Cost.value (Tab.arc_c I root a s)).
Proof.
  intros Hvalid Hwit Ha; rewrite Tab.arc_equation.
  destruct (Jump.kind a) as [|p|p] eqn:Hkind.
  - apply update_witnessed; [exact Hwit|].
    rewrite (composing HB); intro Htrue; apply andb_true_iff in Htrue.
    eapply Stack.path_trans; [apply (proj2 Hwit); exact (proj2 Htrue)|].
    eapply Stack.next; [|apply Stack.refl].
    pose proof (arc_step I a Ha []) as Hstep; rewrite Hkind in Hstep; exact Hstep.
  - apply call_witnessed; assumption.
  - apply end_witnessed; assumption.
Qed.

Local Lemma initial_witnessed :
  witnessed I (Tab.initial I (Tab.prepare I start)).
Proof.
  rewrite Tab.initial_equation.
  refine (proj2 (TabJumpEffects.fold_closed (fun _ => True) (witnessed I)
    (fun t root => Tab.update I (root, root) (Micro.id (Ide.micro I)) t) _ _ _ _ Logic.I _)).
  - intros t root Ht Hin; exact Logic.I.
  - intros t root Ht Hwit Hin; apply update_witnessed; [exact Hwit|].
    intro Htrue; apply Stack.refl.
  - refine (proj2 (TabJumpEffects.fold_closed (fun _ => True) (witnessed I)
      (fun t key => Tab.schedule I key t) _ _ _ _ Logic.I _)).
    + intros t key Ht Hin; exact Logic.I.
    + intros t key Ht Hwit Hin; apply schedule_witnessed; exact Hwit.
    + split; [apply Map.wf_empty|]; intros root v Htrue.
      cbn [Tab.jumps] in Htrue.
      rewrite Jump.lookup_equation, Map.find_or_equation, Map.get_empty, (bottom HB) in Htrue.
      discriminate.
Qed.

Local Lemma step_witnessed s :
  TabRecords.invariant I start s -> witnessed I s ->
  match Tab.step I (Tab.prepare I start) s with
  | inl next | inr next => witnessed I next
  end.
Proof.
  intros [Hvalid Hwork] Hwit; rewrite Tab.tabulate_equation.
  destruct (Tab.work s) as [|[root v] rest] eqn:Hlist; [exact Hwit|].
  assert (Hroot : In root (TabPaths.roots I start)).
  { apply (Hwork (root, v)); rewrite Hlist; left; reflexivity. }
  refine (proj2 (TabJumpEffects.fold_closed (TabRecords.valid I start) (witnessed I)
    (fun t a => Cost.value (Tab.arc_c I root a t)) _
    (Tab.State (Tab.jumps s) (Tab.callers s) (Tab.ends s) rest
      (FinSet.remove (Jump.enc I) (root, v) (Tab.pending s))) _ _ _ Hwit)).
  - intros t a Ht Hin; apply TabRecords.arc_valid; try assumption.
    apply TabRecords.outgoing_member with (start := start) (v := v); exact Hin.
  - intros t a Ht Hw Hin; apply arc_witnessed; try assumption.
    apply TabRecords.outgoing_member with (start := start) (v := v); exact Hin.
  - apply TabRecords.rebuild_valid; exact Hvalid.
Qed.

(** Every true raw jump has an original balanced witness, including on exhaustion. *)
Theorem raw_witnessed fuel :
  match Tab.raw I start fuel with
  | inl s | inr s => witnessed I s
  end.
Proof.
  rewrite Tab.raw_equation.
  pose proof (iterate_value (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (Tab.step_c I (Tab.prepare I start)) n s result ->
    TabRecords.invariant I start s -> witnessed I s ->
    match result with inl next | inr next => witnessed I next end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intros Hinv Hwit.
    - exact Hwit.
    - pose proof (step_witnessed s Hinv Hwit) as Hstep.
      rewrite Tab.step_c_value in Hstop; rewrite Hstop in Hstep; exact Hstep.
    - pose proof (step_witnessed s Hinv Hwit) as Hstep.
      pose proof (TabRecords.step_invariant I start HV s Hinv) as Hvalid.
      rewrite Tab.step_c_value in Hnext; rewrite Hnext in Hstep, Hvalid.
      exact (IH Hvalid Hstep). }
  exact (Hpreserved _ _ _ Hrun (TabRecords.initial_invariant I start) initial_witnessed).
Qed.

(** A certified actual Boolean jump denotes an original balanced path on its actual endpoints. *)
Theorem certified_witness fuel c root v :
  Tab.tabulate I start fuel = Tab.Certified c ->
  Jump.lookup I (proj1_sig c) (root, v) = true ->
  Stack.path (Ide.ifds I) (root, []) (v, []).
Proof.
  intros Hrun Htrue; pose proof (raw_witnessed fuel) as Hwit.
  rewrite Tab.outcome_equation in Hrun.
  destruct (Tab.raw I start fuel) as [s|s] eqn:Hraw; [discriminate|].
  apply Tab.certify_candidate in Hrun; rewrite Hrun in Htrue.
  apply (proj2 Hwit); exact Htrue.
Qed.

End Run.

End TabBoolean.
