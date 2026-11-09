(** * Boolean exactness against original balanced paths and arbitrary prefixes

    Actual true jump and value bindings retain witnesses in the existing Stack.path semantics.
    For example, a true value inside a pending call has a witness with that call still on its stack.
    Builds on: FrameworkTabBoolean, FrameworkTabSound and FrameworkTabValues. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkStack FrameworkTabulate FrameworkTabValues FrameworkTabWeight FrameworkTabPaths
  FrameworkTabRecords FrameworkTabBoolean FrameworkTabJumpEffects FrameworkTabSound FrameworkTabCost
  FrameworkTabJumpProgress FrameworkTabJumpClosure FrameworkTabValueProgress
  FrameworkTabValueClosure.
Import List.ListNotations.

Module TabReach.

(** The original IFDS Boolean micro dictionary inhabits the reverse-witness law domain. *)
Theorem boolean_laws {N E P D} (I : Ifds.t N E P D) : TabBoolean.laws (Ifds.as_ide I).
Proof.
  constructor; reflexivity.
Qed.

(** The informative prefix adapter has the same Boolean jump operations. *)
Theorem reach_laws {N E P D} (I : Ifds.t N E P D) : TabBoolean.laws (TabValues.reach_ide I).
Proof.
  constructor; reflexivity.
Qed.

(** Boolean prefix weights satisfy the separate symbolic unit and associativity duties. *)
Theorem reach_weight_laws : TabWeight.laws TabValues.reach_micro.
Proof.
  constructor.
  - intros []; split; reflexivity.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
Qed.

(** The original IFDS Boolean jump is true exactly for an original supported balanced path. *)
Theorem ifds_balanced_exact {N E P D} (I : Ifds.t N E P D) start fuel c root n d :
  encoding_laws (IdeValue.key_enc (Ifds.as_ide I)) ->
  encoding_laws (Jump.enc (Ifds.as_ide I)) ->
  encoding_laws (Icfg.site_enc (Ifds.icfg I)) ->
  Ifds.flow_closed I -> Ifds.seed_supported I root ->
  In root (TabPaths.roots (Ifds.as_ide I) start) ->
  Tab.tabulate (Ifds.as_ide I) start fuel = Tab.Certified c ->
  (Jump.lookup (Ifds.as_ide I) (proj1_sig c) (root, (n, d)) = true <->
    Stack.balanced I (fst root) (snd root) n d).
Proof.
  intros HV HK HS Hflow Hseed Hr Hrun; split.
  - intro Htrue.
    pose proof (TabBoolean.certified_witness (Ifds.as_ide I) start HV HK HS
      (boolean_laws I) fuel c root (n, d) Hrun Htrue) as Hpath.
    destruct root; exact Hpath.
  - apply (TabSound.ifds_post_balanced I start
      (Jump.lookup (Ifds.as_ide I) (proj1_sig c)) root n d Hflow Hseed Hr).
    exact (proj2_sig c).
Qed.

Section Prefix.
Context {N E P D} (ip : Ifds.t N E P D).
Let I := TabValues.reach_ide ip.
Context (J : Map.t positive bool) (start : N * option D).
Context (HV : encoding_laws (IdeValue.key_enc I)).
Context (HJ : forall root v, Jump.lookup I J (root, v) = true ->
  Stack.path ip (root, []) (v, [])).

(** Every true value keeps the actual pending stack of an original prefix. *)
Definition witnessed (s : TabValues.state N D bool) :=
  Map.wf (IdeValue.key_enc I) (TabValues.values s) /\
    forall v, TabValues.lookup I (TabValues.values s) v = true ->
      exists stack, Stack.path ip (start, []) (v, stack).

Local Lemma schedule_witnessed v s :
  witnessed s -> witnessed (Cost.value (TabValues.schedule_c I v s)).
Proof.
  intro Hwit; rewrite TabValues.schedule_equation.
  destruct (FinSet.mem (IdeValue.key_enc I) v (TabValues.pending s)); exact Hwit.
Qed.

Local Lemma update_witnessed v candidate s :
  witnessed s -> (candidate = true -> exists stack, Stack.path ip (start, []) (v, stack)) ->
  witnessed (Cost.value (TabValues.update_c I v candidate s)).
Proof.
  intros [Hwf Hwit] Hcandidate; rewrite TabValues.update_equation.
  destruct (leb (Ide.values I) candidate (TabValues.lookup I (TabValues.values s) v)).
  - split; assumption.
  - apply schedule_witnessed; split; [apply Map.wf_set; exact Hwf|].
    intros q Htrue; cbn [TabValues.values] in Htrue.
    rewrite TabValues.lookup_equation, Map.find_or_equation, Map.get_set in Htrue by exact Hwf.
    destruct (eqb (IdeValue.key_enc I) q v) eqn:Heq.
    + apply (eqb_true_iff _ HV) in Heq; subst q.
      assert (Hor : orb (TabValues.lookup I (TabValues.values s) v) candidate = true)
        by exact Htrue.
      apply orb_true_iff in Hor; destruct Hor as [Hold|Hnew].
      * apply Hwit; exact Hold.
      * apply Hcandidate; exact Hnew.
    + apply Hwit; exact Htrue.
Qed.

Local Lemma transition_witness a s :
  In a (TabValues.transitions I J start) -> witnessed s ->
  Micro.apply (Ide.micro I) (snd a)
    (TabValues.lookup I (TabValues.values s) (fst (fst a))) = true ->
  exists stack, Stack.path ip (start, []) (snd (fst a), stack).
Proof.
  intros Ha [Hwf Hwit] Htrue.
  assert (Hboth : snd a = true /\
    TabValues.lookup I (TabValues.values s) (fst (fst a)) = true).
  { apply andb_true_iff; exact Htrue. }
  destruct Hboth as [Hweight Hbefore].
  apply TabValues.transitions_spec in Ha.
  destruct Ha as [[root [dst [Hr [Hdst Heq]]]]|[call [p [Hcall [Hkind Heq]]]]]; subst a;
    cbn [fst snd] in *.
  - destruct (Hwit root Hbefore) as [stack Hprefix]; exists stack.
    eapply Stack.path_trans; [exact Hprefix|].
    pose proof (TabBoolean.path_suffix ip _ _ stack (HJ root dst Hweight)) as Hbody.
    cbn [fst snd app] in Hbody; exact Hbody.
  - destruct (Hwit (Jump.source call) Hbefore) as [stack Hprefix]; exists (p :: stack).
    eapply Stack.path_trans; [exact Hprefix|].
    eapply Stack.next; [|apply Stack.refl].
    pose proof (TabBoolean.arc_step I call Hcall stack) as Hstep.
    rewrite Hkind in Hstep; exact Hstep.
Qed.

Local Lemma arc_witnessed a s :
  In a (TabValues.transitions I J start) -> witnessed s ->
  witnessed (Cost.value (TabValues.arc_c I a s)).
Proof.
  intros Ha Hwit; rewrite TabValues.arc_equation.
  apply update_witnessed; [exact Hwit|].
  apply transition_witness; assumption.
Qed.

Local Lemma initial_witnessed :
  witnessed (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start true)).
Proof.
  rewrite TabValues.initial_equation; apply update_witnessed.
  - refine (proj2 (TabJumpEffects.fold_closed (fun _ => True) witnessed
      (fun t v => Cost.value (TabValues.schedule_c I v t)) _ _ _ _ Logic.I _)).
    + intros t v Ht Hin; exact Logic.I.
    + intros t v Ht Hwit Hin; apply schedule_witnessed; exact Hwit.
    + split; [apply Map.wf_empty|]; intros v Htrue.
      cbn [TabValues.values] in Htrue.
      rewrite TabValues.lookup_equation, Map.find_or_equation, Map.get_empty in Htrue.
      discriminate.
  - intros Htrue; exists []; apply Stack.refl.
Qed.

Local Lemma step_witnessed s :
  witnessed s ->
  match Cost.value (TabValues.step_c I (TabValues.prepare I J start) s) with
  | inl next | inr next => witnessed next
  end.
Proof.
  intro Hwit; rewrite TabValues.step_equation.
  destruct (TabValues.work s) as [|v rest] eqn:Hlist; [exact Hwit|].
  refine (proj2 (TabJumpEffects.fold_closed (fun _ => True) witnessed
    (fun t a => Cost.value (TabValues.arc_c I a t)) _
    (TabValues.State (TabValues.values s) rest
      (FinSet.remove (IdeValue.key_enc I) v (TabValues.pending s))) _ _ Logic.I Hwit)).
  - intros t a Ht Hin; exact Logic.I.
  - intros t a Ht Hw Hin; apply arc_witnessed; [|exact Hw].
    rewrite TabValues.prepare_equation in Hin; cbn [TabValues.outgoing] in Hin.
    rewrite Index.find_group_by in Hin; apply filter_In in Hin; exact (proj1 Hin).
Qed.

(** Every true raw value is an original path prefix even if the actual value run exhausts fuel. *)
Theorem raw_witnessed fuel :
  match TabValues.raw I J start true fuel with
  | inl s | inr s => witnessed s
  end.
Proof.
  rewrite TabValues.raw_equation.
  pose proof (iterate_value (TabValues.step_c I (TabValues.prepare I J start)) fuel
    (Cost.value (TabValues.initial_c I (TabValues.prepare I J start) start true))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (TabValues.step_c I (TabValues.prepare I J start)) n s result -> witnessed s ->
    match result with inl next | inr next => witnessed next end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intro Hwit.
    - exact Hwit.
    - pose proof (step_witnessed s Hwit) as Hstep; rewrite Hstop in Hstep; exact Hstep.
    - pose proof (step_witnessed s Hwit) as Hstep; rewrite Hnext in Hstep; exact (IH Hstep). }
  exact (Hpreserved _ _ _ Hrun initial_witnessed).
Qed.

(** A true certified informative value has an original prefix witness and its pending stack. *)
Theorem certified_witness fuel c v :
  TabValues.tabulate_values I J start true fuel = TabValues.Certified c ->
  TabValues.lookup I (proj1_sig c) v = true ->
  exists stack, Stack.path ip (start, []) (v, stack).
Proof.
  intros Hrun Htrue; pose proof (raw_witnessed fuel) as Hwit.
  rewrite TabValues.outcome_equation in Hrun.
  destruct (TabValues.raw I J start true fuel) as [s|s] eqn:Hraw; [discriminate|].
  apply TabValues.certify_candidate in Hrun; rewrite Hrun in Htrue.
  apply (proj2 Hwit); exact Htrue.
Qed.

End Prefix.

(** Each actual prepared informative IFDS arc retains its constant true Boolean weight. *)
Theorem arc_weight {N E P D} (ip : Ifds.t N E P D) a :
  In a (Jump.arcs (TabValues.reach_ide ip)) -> Jump.weight a = true.
Proof.
  intro Ha; rewrite (TabRecords.arc_canonical (TabValues.reach_ide ip) a Ha); reflexivity.
Qed.

(** The chronological weight of an actual IFDS annotation list is true, including the empty path. *)
Theorem trace_weight {N E P D} (ip : Ifds.t N E P D) as_ :
  Forall (fun a => In a (Jump.arcs (TabValues.reach_ide ip))) as_ ->
  TabWeight.weight (TabValues.reach_ide ip) as_ = true.
Proof.
  rewrite TabWeight.weight_fold.
  change (Forall (fun a => In a (Jump.arcs (TabValues.reach_ide ip))) as_ ->
    TabWeight.fold TabValues.reach_micro as_ true = true).
  intro Hmembers; induction Hmembers as [|a rest Ha Hrest IH].
  - reflexivity.
  - rewrite TabWeight.fold_equation, (arc_weight ip a Ha); exact IH.
Qed.

(** Informative Boolean jumps have balanced exactness for the original Stack semantics. *)
Theorem balanced_exact {N E P D} (ip : Ifds.t N E P D) start fuel c root n d :
  encoding_laws (IdeValue.key_enc (TabValues.reach_ide ip)) ->
  encoding_laws (Jump.enc (TabValues.reach_ide ip)) ->
  encoding_laws (Icfg.site_enc (Ifds.icfg ip)) ->
  Ifds.flow_closed ip -> Ifds.seed_supported ip root ->
  In root (TabPaths.roots (TabValues.reach_ide ip) start) ->
  Tab.tabulate (TabValues.reach_ide ip) start fuel = Tab.Certified c ->
  (Jump.lookup (TabValues.reach_ide ip) (proj1_sig c) (root, (n, d)) = true <->
    Stack.balanced ip (fst root) (snd root) n d).
Proof.
  intros HV HK HS Hflow Hseed Hr Hrun; split.
  - intro Htrue.
    pose proof (TabBoolean.certified_witness (TabValues.reach_ide ip) start HV HK HS
      (reach_laws ip) fuel c root (n, d) Hrun Htrue) as Hpath.
    destruct root; exact Hpath.
  - intro Hpath.
    destruct (TabSound.tabulate_jump_sound (TabValues.reach_ide ip) start fuel c root n d
      TabValues.reach_micro_laws reach_weight_laws Hflow Hseed Hr Hrun Hpath) as
      [as_ [Htrace [Hmembers Hbound]]].
    rewrite (trace_weight ip as_ Hmembers) in Hbound; exact Hbound.
Qed.

(** Informative certified values are true exactly at original prefixes with any pending stack. *)
Theorem prefix_exact {N E P D} (ip : Ifds.t N E P D)
    start jump_fuel value_fuel jumps values n d :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg ip))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg ip))) ->
  encoding_laws (Ifds.fact_enc ip) -> encoding_laws (Icfg.site_enc (Ifds.icfg ip)) ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg ip))) ->
  Ifds.flow_closed ip -> Ifds.seed_supported ip start ->
  Tab.tabulate (TabValues.reach_ide ip) (fst start) jump_fuel = Tab.Certified jumps ->
  TabValues.tabulate_values (TabValues.reach_ide ip) (proj1_sig jumps) start true value_fuel =
    TabValues.Certified values ->
  (TabValues.lookup (TabValues.reach_ide ip) (proj1_sig values) (n, d) = true <->
    exists stack, Stack.path ip (fst start, snd start, []) (n, d, stack)).
Proof.
  intros HN HE HD HS HG Hflow Hseed Hjump Hvalue.
  assert (HV : encoding_laws (IdeValue.key_enc (TabValues.reach_ide ip))).
  { apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD]. }
  assert (HK : encoding_laws (Jump.enc (TabValues.reach_ide ip))).
  { apply jkey_enc_laws; assumption. }
  split.
  - intro Htrue.
    destruct (certified_witness ip (proj1_sig jumps) start HV
      (fun root v Htrue => TabBoolean.certified_witness
        (TabValues.reach_ide ip) (fst start) HV HK HS
        (reach_laws ip) jump_fuel jumps root v Hjump Htrue)
      value_fuel values (n, d) Hvalue Htrue) as [stack Hpath].
    exists stack; destruct start; exact Hpath.
  - intros [stack Hpath].
    destruct (TabSound.tabulate_values_sound (TabValues.reach_ide ip) start true
      jump_fuel value_fuel jumps values n d stack HN HE HD bool_laws
      TabValues.reach_micro_laws reach_weight_laws HG Hflow Hseed Hjump Hvalue Hpath) as
      [as_ [Htrace [Hmembers Hbound]]].
    rewrite (trace_weight ip as_ Hmembers) in Hbound; exact Hbound.
Qed.

(** The same actual IFDS run has balanced jump exactness and arbitrary-prefix value exactness. *)
Theorem ifds_exact {N E P D} (ip : Ifds.t N E P D)
    start jump_fuel value_fuel jumps values :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg ip))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg ip))) ->
  encoding_laws (Ifds.fact_enc ip) -> encoding_laws (Icfg.site_enc (Ifds.icfg ip)) ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg ip))) ->
  Ifds.flow_closed ip -> Ifds.seed_supported ip start ->
  Tab.tabulate (TabValues.reach_ide ip) (fst start) jump_fuel = Tab.Certified jumps ->
  TabValues.tabulate_values (TabValues.reach_ide ip) (proj1_sig jumps) start true value_fuel =
    TabValues.Certified values ->
  (forall root n d, Ifds.seed_supported ip root ->
    In root (TabPaths.roots (TabValues.reach_ide ip) (fst start)) ->
    (Jump.lookup (TabValues.reach_ide ip) (proj1_sig jumps) (root, (n, d)) = true <->
      Stack.balanced ip (fst root) (snd root) n d)) /\
  (forall n d, TabValues.lookup (TabValues.reach_ide ip) (proj1_sig values) (n, d) = true <->
    exists stack, Stack.path ip (fst start, snd start, []) (n, d, stack)).
Proof.
  intros HN HE HD HS HG Hflow Hseed Hjump Hvalue; split.
  - intros root n d Hr Hroot.
    apply (balanced_exact ip (fst start) jump_fuel jumps root n d); try assumption.
    + apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD].
    + apply jkey_enc_laws; assumption.
  - intros n d; apply (prefix_exact ip start jump_fuel value_fuel jumps values n d);
      assumption.
Qed.

(** Constructed Boolean-height runs certify both phases and establish original-path exactness. *)
Theorem complete_exact {N E P D} (ip : Ifds.t N E P D) start :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg ip))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg ip))) ->
  encoding_laws (Ifds.fact_enc ip) -> encoding_laws (Icfg.site_enc (Ifds.icfg ip)) ->
  graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg ip))) ->
  Ifds.flow_closed ip -> Ifds.seed_supported ip start ->
  exists jumps values,
    TabJumpProgress.complete (TabValues.reach_ide ip) (fst start) bool_height =
      Tab.Certified jumps /\
    TabValueProgress.complete (TabValues.reach_ide ip) (proj1_sig jumps) start true bool_height =
      TabValues.Certified values /\
    (forall root n d, Ifds.seed_supported ip root ->
      In root (TabPaths.roots (TabValues.reach_ide ip) (fst start)) ->
      (Jump.lookup (TabValues.reach_ide ip) (proj1_sig jumps) (root, (n, d)) = true <->
        Stack.balanced ip (fst root) (snd root) n d)) /\
    (forall n d, TabValues.lookup (TabValues.reach_ide ip) (proj1_sig values) (n, d) = true <->
      exists stack, Stack.path ip (fst start, snd start, []) (n, d, stack)).
Proof.
  intros HN HE HD HS HG Hflow Hseed.
  assert (HV : encoding_laws (IdeValue.key_enc (TabValues.reach_ide ip))).
  { apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD]. }
  assert (HK : encoding_laws (Jump.enc (TabValues.reach_ide ip))).
  { apply jkey_enc_laws; assumption. }
  assert (HA : encoding_laws (Tab.arc_enc (TabValues.reach_ide ip))).
  { apply Tab.arc_enc_laws; assumption. }
  assert (HI : encoding_laws (Tab.incoming_enc (TabValues.reach_ide ip))).
  { apply Tab.incoming_enc_laws; assumption. }
  destruct (TabJumpClosure.complete_certified (TabValues.reach_ide ip) (fst start)
    bool_height HV HK HA HI bool_laws) as [jumps Hjump].
  destruct (TabValueClosure.complete_certified (TabValues.reach_ide ip) (proj1_sig jumps)
    start true bool_height HN HE HD bool_laws) as [values Hvalue].
  exists jumps, values; split; [exact Hjump|]; split; [exact Hvalue|].
  rewrite TabJumpProgress.complete_agrees in Hjump.
  rewrite TabValueProgress.complete_agrees in Hvalue.
  apply (ifds_exact ip start
    (TabCost.rank_fuel (Tab.prepare (TabValues.reach_ide ip) (fst start)) (bound bool_height))
    (TabCost.inventory_fuel
      (TabValues.inventory (TabValues.prepare (TabValues.reach_ide ip) (proj1_sig jumps) start))
      (bound bool_height)) jumps values); assumption.
Qed.

End TabReach.
