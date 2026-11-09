(** * Closure of actual stopped symbolic jump states

    Every ground row is covered or waits for an actual pending dependency or unfinished local arc.
    For example, matching returns are replayed whichever of caller and end is visited last.
    Builds on: FrameworkTabJumpProgress, FrameworkTabJumpEffects and FrameworkTabJumpReplay. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabPaths FrameworkTabRecords FrameworkTabQueue FrameworkTabJumpProgress
  FrameworkTabJumpEffects FrameworkTabJumpReplay FrameworkTabCost FrameworkTabSound.
Import List.ListNotations.

Module TabJumpClosure.

(** An unfinished visit is represented by its actual pending key or its remaining local arc. *)
Definition waiting {N E P D F} (s : Tab.state N E P D F)
    (active : Tab.key N D) (todo : list (Jump.arc N E P D F)) root a :=
  In (root, Jump.source a) (Tab.work s) \/
    (root = fst active /\ Jump.source a = snd active /\ In a todo).

(** Closure also retains the records needed when the other dependency is visited later. *)
Record backlog {N E P D A F} (I : Ide.t N E P D A F) start s active todo : Prop := {
  identities : forall root, In root (TabPaths.roots I start) ->
    Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Seed root);
  paths : forall root a, In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
    Jump.kind a = Icfg.Internal ->
    Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Path root a) \/
      waiting s active todo root a;
  callers : forall root a p, In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
    Jump.kind a = Icfg.Call p ->
    TabRecords.caller_at I s root a \/ waiting s active todo root a;
  ends : forall root a p, In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
    Jump.kind a = Icfg.Return p ->
    TabRecords.end_at I s root a \/ waiting s active todo root a;
  returns : forall root a b, In root (TabPaths.roots I start) ->
    In a (Jump.arcs I) -> In b (Jump.arcs I) ->
    Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
    Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Return root a b) \/
      waiting s active todo root a \/ waiting s active todo (Jump.target a) b
}.
Arguments identities {N E P D A F I start s active todo}.
Arguments paths {N E P D A F I start s active todo}.
Arguments callers {N E P D A F I start s active todo}.
Arguments ends {N E P D A F I start s active todo}.
Arguments returns {N E P D A F I start s active todo}.

Local Lemma waiting_grows {N E P D F} (s t : Tab.state N E P D F) active todo root a :
  incl (Tab.work s) (Tab.work t) ->
  waiting s active todo root a -> waiting t active todo root a.
Proof.
  intros Hwork [Hpending|Hlocal]; [left; apply Hwork; exact Hpending|right; exact Hlocal].
Qed.

Local Lemma waiting_drop {N E P D F} (s : Tab.state N E P D F) active head todo root a :
  waiting s active (head :: todo) root a ->
  waiting s active todo root a \/ (root = fst active /\ a = head).
Proof.
  intros [Hpending|[Hroot [Hsource [Heq|Hin]]]].
  - left; left; exact Hpending.
  - right; split; [exact Hroot|symmetry; exact Heq].
  - left; right; repeat split; assumption.
Qed.

Local Lemma path_frontier {N E P D A F} (I : Ide.t N E P D A F) s active todo root a :
  TabJumpEffects.frontier I s (Jump.Path root a) ->
  Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Path root a) \/
    waiting s active todo root a.
Proof.
  intros [Hrow|[key [[Heq|Hbad] Hwork]]].
  - left; exact Hrow.
  - subst key; right; left; exact Hwork.
  - inversion Hbad.
Qed.

Local Lemma return_frontier {N E P D A F} (I : Ide.t N E P D A F) s active todo root a b :
  TabJumpEffects.frontier I s (Jump.Return root a b) ->
  Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Return root a b) \/
    waiting s active todo root a \/ waiting s active todo (Jump.target a) b.
Proof.
  intros [Hrow|[key [[Heq|[Heq|Hbad]] Hwork]]].
  - left; exact Hrow.
  - subst key; right; left; left; exact Hwork.
  - subst key; right; right; left; exact Hwork.
  - inversion Hbad.
Qed.

Local Lemma match_kinds {N E P D A F} (I : Ide.t N E P D A F)
    (a b : Jump.arc N E P D F) :
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  exists p q, Jump.kind a = Icfg.Call p /\ Jump.kind b = Icfg.Return q.
Proof.
  rewrite Jump.matches_c_value; destruct (Jump.kind a) as [|p|p] eqn:Ha;
    destruct (Jump.kind b) as [|q|q] eqn:Hb; try discriminate.
  intro Hmatch; exists p, q; split; reflexivity.
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (start : N).
Context (HV : encoding_laws (IdeValue.key_enc I)) (HK : encoding_laws (Jump.enc I)).
Context (HA : encoding_laws (Tab.arc_enc I)) (HI : encoding_laws (Tab.incoming_enc I)).
Context (HL : lattice_laws (Micro.lat (Ide.micro I))).

Local Lemma arc_good root a s :
  TabRecords.valid I start s /\ TabJumpProgress.shape I s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  TabRecords.valid I start (Cost.value (Tab.arc_c I root a s)) /\
    TabJumpProgress.shape I (Cost.value (Tab.arc_c I root a s)).
Proof.
  intros [Hvalid Hshape] Hroot Ha; split.
  - apply TabRecords.arc_valid; assumption.
  - eapply TabJumpEffects.arc_shape; eassumption.
Qed.

Local Lemma arc_identities root a s :
  TabJumpProgress.shape I s ->
  (forall r, In r (TabPaths.roots I start) ->
    Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Seed r)) ->
  forall r, In r (TabPaths.roots I start) ->
    Jump.holds I (Jump.lookup I (Tab.jumps (Cost.value (Tab.arc_c I root a s)))) (Jump.Seed r).
Proof.
  intros Hshape Hseed r Hr.
  assert (Hfrontier : TabJumpEffects.frontier I
    (Cost.value (Tab.arc_c I root a s)) (Jump.Seed r)).
  { eapply TabJumpEffects.arc_frontier; try eassumption; left; apply Hseed; exact Hr. }
  destruct Hfrontier as [Hrow|[key [Hbad Hwork]]]; [exact Hrow|inversion Hbad].
Qed.

Local Lemma call_hit s active head todo a b :
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  backlog I start s active (head :: todo) ->
  In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  a = head ->
  Jump.holds I (Jump.lookup I (Tab.jumps (Cost.value (Tab.arc_c I (fst active) head s))))
      (Jump.Return (fst active) a b) \/
    waiting (Cost.value (Tab.arc_c I (fst active) head s)) active todo (fst active) a \/
    waiting (Cost.value (Tab.arc_c I (fst active) head s)) active todo (Jump.target a) b.
Proof.
  intros Hvalid Hshape Hback Ha Hb Hmatch Heq; subst head.
  destruct (match_kinds I a b Hmatch) as [p [q [Hcall Hreturn]]].
  assert (Hr : In (Jump.target a) (TabPaths.roots I start)).
  { apply (TabPaths.call_target_root I start a p); assumption. }
  destruct (ends Hback _ _ q Hr Hb Hreturn) as [Hend|Hwait].
  - apply return_frontier; rewrite Tab.arc_equation, Hcall.
    eapply TabJumpReplay.call_covers; eassumption.
  - destruct (waiting_drop s active a todo (Jump.target a) b Hwait) as [Hwait'|[Hr' Heq]].
    + right; right; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|].
      exact Hwait'.
    + subst b; rewrite Hcall in Hreturn; discriminate.
Qed.

Local Lemma end_hit s active head todo root a b :
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  backlog I start s active (head :: todo) ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
  Jump.target a = fst active -> b = head ->
  Jump.holds I (Jump.lookup I (Tab.jumps (Cost.value (Tab.arc_c I (fst active) head s))))
      (Jump.Return root a b) \/
    waiting (Cost.value (Tab.arc_c I (fst active) head s)) active todo root a \/
    waiting (Cost.value (Tab.arc_c I (fst active) head s)) active todo (Jump.target a) b.
Proof.
  intros Hvalid Hshape Hback Hr Ha Hb Hmatch Hentry Heq; subst head.
  destruct (match_kinds I a b Hmatch) as [p [q [Hcall Hreturn]]].
  destruct (callers Hback _ _ p Hr Ha Hcall) as [Hcaller|Hwait].
  - apply return_frontier; rewrite Tab.arc_equation, Hreturn, <- Hentry.
    eapply TabJumpReplay.end_covers; eassumption.
  - destruct (waiting_drop s active b todo root a Hwait) as [Hwait'|[Hr' Heq]].
    + right; left; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|].
      exact Hwait'.
    + subst a; rewrite Hcall in Hreturn; discriminate.
Qed.

Local Lemma arc_returns s active head todo :
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  backlog I start s active (head :: todo) ->
  forall root a b, In root (TabPaths.roots I start) ->
    In a (Jump.arcs I) -> In b (Jump.arcs I) ->
    Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) = true ->
    Jump.holds I (Jump.lookup I (Tab.jumps (Cost.value (Tab.arc_c I (fst active) head s))))
        (Jump.Return root a b) \/
      waiting (Cost.value (Tab.arc_c I (fst active) head s)) active todo root a \/
      waiting (Cost.value (Tab.arc_c I (fst active) head s)) active todo (Jump.target a) b.
Proof.
  intros Hvalid Hshape Hback root a b Hr Ha Hb Hmatch.
  destruct (returns Hback root a b Hr Ha Hb Hmatch) as [Hrow|[Hcall|Hend]].
  - apply return_frontier; eapply TabJumpEffects.arc_frontier; try eassumption; left; exact Hrow.
  - destruct (waiting_drop s active head todo root a Hcall) as [Hwait|[Heq Hhit]].
    + right; left; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|].
      exact Hwait.
    + subst root; apply call_hit; assumption.
  - destruct (waiting_drop s active head todo (Jump.target a) b Hend) as [Hwait|[Heq Hhit]].
    + right; right; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|].
      exact Hwait.
    + apply end_hit; assumption.
Qed.

Local Lemma arc_backlog s active head todo :
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  In head (Jump.arcs I) -> backlog I start s active (head :: todo) ->
  backlog I start (Cost.value (Tab.arc_c I (fst active) head s)) active todo.
Proof.
  intros Hvalid Hshape Hhead Hback; constructor.
  - apply arc_identities; [exact Hshape|exact (identities Hback)].
  - intros root a Hr Ha Hkind; destruct (paths Hback root a Hr Ha Hkind) as [Hrow|Hwait].
    + apply path_frontier; eapply TabJumpEffects.arc_frontier; try eassumption; left; exact Hrow.
    + destruct (waiting_drop s active head todo root a Hwait) as [Hwait'|[Heq Hhit]].
      * right; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|exact Hwait'].
      * subst root head; apply path_frontier; rewrite Tab.arc_equation, Hkind.
        eapply TabJumpEffects.path_covers; eassumption.
  - intros root a p Hr Ha Hkind; destruct (callers Hback root a p Hr Ha Hkind) as [Hold|Hwait].
    + left; eapply TabRecords.arc_keeps_caller; eassumption.
    + destruct (waiting_drop s active head todo root a Hwait) as [Hwait'|[Heq Hhit]].
      * right; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|exact Hwait'].
      * subst root head; left; rewrite Tab.arc_equation, Hkind.
        apply TabRecords.call_installs with (start := start); exact Hvalid.
  - intros root a p Hr Ha Hkind; destruct (ends Hback root a p Hr Ha Hkind) as [Hold|Hwait].
    + left; eapply TabRecords.arc_keeps_end; eassumption.
    + destruct (waiting_drop s active head todo root a Hwait) as [Hwait'|[Heq Hhit]].
      * right; eapply waiting_grows; [eapply TabJumpEffects.arc_work; eassumption|exact Hwait'].
      * subst root head; left; rewrite Tab.arc_equation, Hkind.
        apply TabRecords.end_installs with (start := start); exact Hvalid.
  - apply arc_returns; assumption.
Qed.

Local Lemma fold_backlog todo active s :
  In (fst active) (TabPaths.roots I start) ->
  (forall a, In a todo -> In a (Jump.arcs I)) ->
  TabRecords.valid I start s -> TabJumpProgress.shape I s ->
  backlog I start s active todo ->
  backlog I start
    (fold_left (fun t a => Cost.value (Tab.arc_c I (fst active) a t)) todo s) active [].
Proof.
  revert s; induction todo as [|a todo IH]; intros s Hr Harcs Hvalid Hshape Hback;
    cbn [fold_left]; [exact Hback|].
  destruct (arc_good (fst active) a s (conj Hvalid Hshape) Hr
    (Harcs a (or_introl eq_refl))) as [Hnext Hnextshape].
  apply IH; try assumption.
  - intros b Hb; apply Harcs; right; exact Hb.
  - apply arc_backlog; try assumption; apply Harcs; left; reflexivity.
Qed.

Local Lemma backlog_transport s t active todo next rest :
  Tab.jumps t = Tab.jumps s -> TabRecords.same s t ->
  (forall root a, In a (Jump.arcs I) ->
    waiting s active todo root a -> waiting t next rest root a) ->
  backlog I start s active todo -> backlog I start t next rest.
Proof.
  intros Hjumps Hsame Hwait Hback; constructor.
  - intros root Hr; rewrite Hjumps; exact (identities Hback root Hr).
  - intros root a Hr Ha Hkind; destruct (paths Hback root a Hr Ha Hkind) as [Hrow|Hw].
    + left; rewrite Hjumps; exact Hrow.
    + right; apply Hwait; assumption.
  - intros root a p Hr Ha Hkind; destruct (callers Hback root a p Hr Ha Hkind) as [Hget|Hw].
    + left; eapply TabRecords.same_caller; eassumption.
    + right; apply Hwait; assumption.
  - intros root a p Hr Ha Hkind; destruct (ends Hback root a p Hr Ha Hkind) as [Hget|Hw].
    + left; eapply TabRecords.same_end; eassumption.
    + right; apply Hwait; assumption.
  - intros root a b Hr Ha Hb Hmatch.
    destruct (returns Hback root a b Hr Ha Hb Hmatch) as [Hrow|[Hw|Hw]].
    + left; rewrite Hjumps; exact Hrow.
    + right; left; apply Hwait; assumption.
    + right; right; apply Hwait; assumption.
Qed.

Local Lemma schedule_all keys s :
  TabJumpProgress.shape I s ->
  let final := fold_left (fun t key => Tab.schedule I key t) keys s in
  TabJumpProgress.shape I final /\ incl (Tab.work s) (Tab.work final) /\
    (forall key, In key keys -> In key (Tab.work final)).
Proof.
  revert s; induction keys as [|key keys IH]; intros s Hshape; cbn [fold_left].
  - split; [exact Hshape|]; split; [intros k Hk; exact Hk|intros k Hk; inversion Hk].
  - pose proof (TabJumpEffects.schedule_work I key s (proj2 Hshape)) as [Hgrow Hkey].
    assert (Hnext : TabJumpProgress.shape I (Tab.schedule I key s)).
    { eapply TabJumpEffects.schedule_shape; eassumption. }
    destruct (IH _ Hnext) as [Hfinal [Htail Hkeys]]; split; [exact Hfinal|]; split.
    + intros k Hk; apply Htail, Hgrow; exact Hk.
    + intros k [Heq|Hk]; [subst k; apply Htail; exact Hkey|apply Hkeys; exact Hk].
Qed.

Local Lemma update_seed key f s root :
  TabJumpProgress.shape I s ->
  Jump.holds I (Jump.lookup I (Tab.jumps s)) (Jump.Seed root) ->
  Jump.holds I (Jump.lookup I (Tab.jumps (Tab.update I key f s))) (Jump.Seed root).
Proof.
  intros Hshape Hseed.
  assert (Hfrontier : TabJumpEffects.frontier I (Tab.update I key f s) (Jump.Seed root)).
  { eapply TabJumpEffects.update_frontier; try eassumption; left; exact Hseed. }
  destruct Hfrontier as [Hrow|[reader [Hbad Hwork]]]; [exact Hrow|inversion Hbad].
Qed.

Local Lemma initial_backlog active :
  backlog I start (Tab.initial I (Tab.prepare I start)) active [].
Proof.
  set (p := Tab.prepare I start).
  set (scheduled := fold_left (fun t key => Tab.schedule I key t) (Tab.inventory p)
    (Tab.State Map.empty Map.empty Map.empty [] FinSet.empty)).
  pose proof (schedule_all (Tab.inventory p)
    (Tab.State Map.empty Map.empty Map.empty [] FinSet.empty)
    (conj (Map.wf_empty positive_encoding) (TabQueue.empty_coherent (Jump.enc I))))
    as [Hscheduled [Hempty Hkeys]].
  fold scheduled in Hscheduled, Hkeys.
  assert (Hinit : Tab.initial I p = fold_left
    (fun t root => Tab.update I (root, root) (Micro.id (Ide.micro I)) t)
    (Tab.roots p) scheduled) by (apply Tab.initial_equation).
  assert (Hwork : incl (Tab.inventory p) (Tab.work (Tab.initial I p))).
  { rewrite Hinit.
    pose proof (TabJumpEffects.fold_closed (TabJumpProgress.shape I)
      (fun t => incl (Tab.work scheduled) (Tab.work t))
      (fun t root => Tab.update I (root, root) (Micro.id (Ide.micro I)) t)
      (Tab.roots p) scheduled) as Hfold.
    destruct (Hfold
      (fun t root Ht Hin => TabJumpEffects.update_shape I HK _ _ _ Ht)
      (fun t root Ht Hincluded Hin key Hkey =>
        proj1 (proj2 (TabJumpEffects.update_effects I _ _ t HK HL Ht)) key
          (Hincluded key Hkey)) Hscheduled (fun key Hkey => Hkey)) as [Hshape Hincluded].
    intros key Hkey; apply Hincluded, Hkeys; exact Hkey. }
  assert (Hseed : forall root, In root (TabPaths.roots I start) ->
    Jump.holds I (Jump.lookup I (Tab.jumps (Tab.initial I p))) (Jump.Seed root)).
  { intros root Hr; rewrite Hinit.
    apply (TabJumpEffects.fold_hit (TabJumpProgress.shape I)
      (fun t => Jump.holds I (Jump.lookup I (Tab.jumps t)) (Jump.Seed root))
      (fun t r => Tab.update I (r, r) (Micro.id (Ide.micro I)) t)
      (Tab.roots p) root scheduled).
    - intros t r Ht Hin; eapply TabJumpEffects.update_shape; eassumption.
    - intros t r Ht HP Hin; apply update_seed; assumption.
    - intros t Ht; exact (proj2 (proj2 (proj2
        (TabJumpEffects.update_effects I _ _ t HK HL Ht)))).
    - unfold p; rewrite Tab.prepare_equation; exact Hr.
    - exact Hscheduled. }
  assert (Hwaiting : forall root a, In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
    waiting (Tab.initial I p) active [] root a).
  { intros root a Hr Ha; left; apply Hwork; unfold p.
    rewrite Tab.prepare_equation; cbn [Tab.inventory]; apply in_flat_map.
    exists root; split; [exact Hr|]; apply in_map_iff; exists (Jump.source a).
    split; [reflexivity|right; apply in_flat_map; exists a].
    split; [exact Ha|left; reflexivity]. }
  constructor.
  - exact Hseed.
  - intros root a Hr Ha Hkind; right; apply Hwaiting; assumption.
  - intros root a q Hr Ha Hkind; right; apply Hwaiting; assumption.
  - intros root a q Hr Ha Hkind; right; apply Hwaiting; assumption.
  - intros root a b Hr Ha Hb Hmatch; right; left; apply Hwaiting; assumption.
Qed.

Local Lemma step_backlog s active :
  TabJumpProgress.invariant I start s -> backlog I start s active [] ->
  match Tab.step I (Tab.prepare I start) s with
  | inl next | inr next => backlog I start next active []
  end.
Proof.
  intros [Hvalid [[Hwf Hqueue] [Hwork Hstored]]] Hback; rewrite Tab.tabulate_equation.
  destruct (Tab.work s) as [|[root v] rest] eqn:Hlist; [exact Hback|].
  set (out := Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start))).
  set (popped := Tab.State (Tab.jumps s) (Tab.callers s) (Tab.ends s) rest
    (FinSet.remove (Jump.enc I) (root, v) (Tab.pending s))).
  assert (Hroot : In root (TabPaths.roots I start)).
  { apply (TabRecords.inventory_root I start (root, v)), Hwork; left; reflexivity. }
  assert (Hpopped : backlog I start popped (root, v) out).
  { eapply (backlog_transport s popped active [] (root, v) out);
      [reflexivity|split; reflexivity| |exact Hback].
    intros r a Ha [Hpending|[Hr [Hv Hbad]]]; [|inversion Hbad].
    rewrite Hlist in Hpending; destruct Hpending as [Heq|Hin]; [|left; exact Hin].
    right; injection Heq as Hr Hv; cbn [fst snd].
    split; [congruence|]; split; [congruence|].
    unfold out; rewrite Tab.prepare_equation; cbn [Tab.outgoing].
    rewrite Index.find_group_by; apply filter_In; split.
    - exact Ha.
    - cbn beta; apply (proj2 (eqb_true_iff (IdeValue.key_enc I) HV _ _)); congruence. }
  assert (Hlocal : backlog I start
    (fold_left (fun t a => Cost.value (Tab.arc_c I root a t)) out popped) (root, v) []).
  { apply (fold_backlog out (root, v) popped).
    - exact Hroot.
    - intros a Ha; apply TabRecords.outgoing_member with (start := start) (v := v); exact Ha.
    - apply TabRecords.rebuild_valid; exact Hvalid.
    - split; [exact Hwf|apply TabQueue.pop_coherent; assumption].
    - exact Hpopped. }
  eapply (backlog_transport
    (fold_left (fun t a => Cost.value (Tab.arc_c I root a t)) out popped)
    (fold_left (fun t a => Cost.value (Tab.arc_c I root a t)) out popped)
    (root, v) [] active []);
    [reflexivity|split; reflexivity| |exact Hlocal].
  intros r a Ha [Hpending|[Hr [Hv Hbad]]]; [left; exact Hpending|inversion Hbad].
Qed.

(** Every actual raw state retains ground closure and record completeness up to pending keys. *)
Theorem raw_backlog fuel active :
  match Tab.raw I start fuel with
  | inl s | inr s => backlog I start s active []
  end.
Proof.
  rewrite Tab.raw_equation.
  pose proof (iterate_value (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (Tab.step_c I (Tab.prepare I start)) n s result ->
    TabJumpProgress.invariant I start s -> backlog I start s active [] ->
    match result with inl next | inr next => backlog I start next active [] end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intros Hinv Hback.
    - exact Hback.
    - pose proof (step_backlog s active Hinv Hback) as Hstep.
      rewrite Tab.step_c_value in Hstop; rewrite Hstop in Hstep; exact Hstep.
    - pose proof (step_backlog s active Hinv Hback) as Hstep.
      pose proof (TabJumpProgress.step_invariant I start HV HK s Hinv) as Hnextinv.
      rewrite Tab.step_c_value in Hnext; rewrite Hnext in Hstep, Hnextinv.
      exact (IH Hnextinv Hstep). }
  exact (Hpreserved _ _ _ Hrun
    (TabJumpProgress.initial_invariant I start HK) (initial_backlog active)).
Qed.

Local Lemma raw_stopped_empty fuel stopped :
  Tab.raw I start fuel = inr stopped -> Tab.work stopped = [].
Proof.
  rewrite Tab.raw_equation; intro Hresult.
  destruct (iterate_inr_stops (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start)) stopped Hresult) as
    [used [last [Hused [Hprefix Hstop]]]].
  rewrite Tab.step_c_value, Tab.tabulate_equation in Hstop.
  destruct (Tab.work last) as [|[root v] rest] eqn:Hwork; [|discriminate].
  injection Hstop as Hsame; subst stopped; exact Hwork.
Qed.

(** Every stopped raw jump map satisfies the original unconditional ground rows before checking. *)
Theorem stopped_post fuel stopped :
  Tab.raw I start fuel = inr stopped -> jump_post I start (Jump.lookup I (Tab.jumps stopped)).
Proof.
  intro Hrun.
  pose proof (raw_backlog fuel ((start, None), (start, None))) as Hback.
  rewrite Hrun in Hback.
  pose proof (raw_stopped_empty fuel stopped Hrun) as Hempty.
  assert (Hnowait : forall root a, ~ waiting stopped ((start, None), (start, None)) [] root a).
  { intros root a [Hpending|[Hr [Hv Hbad]]].
    - rewrite Hempty in Hpending; inversion Hpending.
    - inversion Hbad. }
  intros row Hrow; apply Jump.rows_spec in Hrow.
  destruct Hrow as [[root [Hr Heq]]|[[a [p [Ha [Hkind Heq]]]]|
    [[root [a [Hr [Ha [Hkind Heq]]]]]|[root [a [b [Hr [Ha [Hb [Hmatch Heq]]]]]]]]]];
    subst row.
  - apply (identities Hback); unfold TabPaths.roots; rewrite Jump.roots_c_value.
    apply in_or_app; left; exact Hr.
  - change (Jump.holds I (Jump.lookup I (Tab.jumps stopped)) (Jump.Seed (Jump.target a))).
    apply (identities Hback), (TabPaths.call_target_root I start a p); assumption.
  - destruct (paths Hback root a Hr Ha Hkind) as [Hcovered|Hwait];
      [exact Hcovered|exfalso; exact (Hnowait root a Hwait)].
  - destruct (returns Hback root a b Hr Ha Hb Hmatch) as [Hcovered|[Hwait|Hwait]];
      [exact Hcovered|exfalso; exact (Hnowait root a Hwait)|
        exfalso; exact (Hnowait (Jump.target a) b Hwait)].
Qed.

(** The charged checker accepts every stopped raw jump candidate on the stated local law domain. *)
Theorem stopped_checked fuel stopped :
  Tab.raw I start fuel = inr stopped -> check_jumps I start (Tab.jumps stopped) = true.
Proof.
  intro Hrun; apply check_jumps_iff; apply stopped_post with (fuel := fuel); exact Hrun.
Qed.

(** Every stopped run has installed all actual caller and end occurrences in their own buckets. *)
Theorem stopped_records fuel stopped :
  Tab.raw I start fuel = inr stopped ->
  forall root a, In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
    (forall p, Jump.kind a = Icfg.Call p -> TabRecords.caller_at I stopped root a) /\
    (forall p, Jump.kind a = Icfg.Return p -> TabRecords.end_at I stopped root a).
Proof.
  intros Hrun root a Hr Ha.
  pose proof (raw_backlog fuel ((start, None), (start, None))) as Hback.
  rewrite Hrun in Hback.
  pose proof (raw_stopped_empty fuel stopped Hrun) as Hempty.
  assert (Hnowait : ~ waiting stopped ((start, None), (start, None)) [] root a).
  { intros [Hpending|[Hroot [Hsource Hbad]]].
    - rewrite Hempty in Hpending; inversion Hpending.
    - inversion Hbad. }
  split; intros p Hkind.
  - destruct (callers Hback root a p Hr Ha Hkind) as [Hrecord|Hwait];
      [exact Hrecord|exfalso; exact (Hnowait Hwait)].
  - destruct (ends Hback root a p Hr Ha Hkind) as [Hrecord|Hwait];
      [exact Hrecord|exfalso; exact (Hnowait Hwait)].
Qed.

End Run.

(** Numeric height completion reaches a certificate without a success or postcondition premise. *)
Theorem complete_certified {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  encoding_laws (Tab.arc_enc I) -> encoding_laws (Tab.incoming_enc I) ->
  lattice_laws (Micro.lat (Ide.micro I)) ->
  exists c, TabJumpProgress.complete I start H = Tab.Certified c.
Proof.
  intros HV HK HA HI HL.
  destruct (TabJumpProgress.complete_raw_stops I start H HV HK HL) as
    [stopped [Hraw Hempty]].
  pose proof Hraw as Hrun; rewrite TabJumpProgress.complete_raw_equation in Hrun.
  pose proof (stopped_post I start HV HK HA HI HL _ stopped Hrun) as Hpost.
  destruct (Tab.certify_accepts I start stopped Hpost) as [c Hcertified].
  exists c; rewrite TabJumpProgress.complete_equation, Hraw; exact Hcertified.
Qed.

(** Constructed-height jump completion is least among the original ground-row post-solutions. *)
Theorem complete_least {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) J :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  encoding_laws (Tab.arc_enc I) -> encoding_laws (Tab.incoming_enc I) ->
  micro_laws (Ide.values I) (Ide.micro I) -> jump_post I start J ->
  exists c, TabJumpProgress.complete I start H = Tab.Certified c /\
    forall key, leb (Micro.lat (Ide.micro I)) (Jump.lookup I (proj1_sig c) key) (J key) = true.
Proof.
  intros HV HK HA HI HM Hpost.
  destruct (complete_certified I start H HV HK HA HI (lat_ok _ _ HM)) as [c Hrun].
  exists c; split; [exact Hrun|].
  apply (TabSound.tabulate_jump_least I start
    (TabCost.rank_fuel (Tab.prepare I start) (bound H)) c J HK HM).
  - rewrite <- TabJumpProgress.complete_agrees; exact Hrun.
  - exact Hpost.
Qed.

End TabJumpClosure.
