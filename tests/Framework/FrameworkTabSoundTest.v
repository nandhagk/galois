(** * Symbolic law boundaries

    Application laws on a unit carrier do not imply symbolic unit or associativity.
    For example, a monotone constant composition satisfies every Micro application law.
    Builds on: FrameworkTabWeight and FrameworkMicro. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis FixpointCheck.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabWeight FrameworkTabulate FrameworkTabSound FrameworkStack FrameworkTabPaths
  FrameworkTabValues FrameworkTabValueSound FrameworkTabValueProgress.
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabulateTest.
Import List.ListNotations.

Definition nonstrict_micro : Micro.t unit bool :=
  Micro.of_pure true (fun _ _ => true) (fun _ _ => tt) bool_lattice.

(** The existing law record permits non-strict composition on a finite Boolean carrier. *)
Theorem nonstrict_micro_laws : micro_laws unit_lattice nonstrict_micro.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_lub.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
  - intros [] [] [] _; reflexivity.
  - intros [] [] [] _; reflexivity.
  - intros [] [] [] [] _ _; reflexivity.
  - intros [] [] []; split; reflexivity.
Qed.

Example absent_paths_can_have_nonbottom_contributions :
  Micro.compose nonstrict_micro false (bot (Micro.lat nonstrict_micro)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Application equivalence alone cannot prove symbolic right identity in function order. *)
Theorem application_identity_does_not_reflect_symbolic_identity :
  ~ TabWeight.laws nonstrict_micro.
Proof.
  intro Hlaws.
  destruct (TabWeight.unit_right Hlaws false) as [Hbound _].
  discriminate Hbound.
Qed.

Inductive three := Low | Middle | High.

Definition three_le (x y : three) :=
  match x, y with
  | Low, _ | _, High | Middle, Middle => true
  | _, _ => false
  end.

Definition three_join (x y : three) :=
  match x, y with
  | High, _ | _, High => High
  | Middle, _ | _, Middle => Middle
  | _, _ => Low
  end.

Definition three_next (x : three) :=
  match x with
  | Low => Middle
  | _ => High
  end.

Definition nonassoc_micro : Micro.t unit three :=
  Micro.of_pure Low (fun f g => three_join f (three_next g))
    (fun _ _ => tt) (simple three_le Low three_join).

(** Monotone composition on a finite three-element chain can violate symbolic associativity. *)
Theorem nonassoc_micro_laws : micro_laws unit_lattice nonassoc_micro.
Proof.
  constructor.
  - apply simple_laws.
    + intros []; reflexivity.
    + intros [] [] []; cbn; congruence.
    + intros []; reflexivity.
    + intros [] []; reflexivity.
    + intros [] []; reflexivity.
  - constructor; intros [] [] []; cbn; congruence.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
  - intros [] [] [] _; reflexivity.
  - intros [] [] [] _; reflexivity.
  - intros [] [] [] []; cbn; congruence.
  - intros [] [] []; split; reflexivity.
Qed.

Example symbolic_associativity_fails :
  (Micro.compose nonassoc_micro (Micro.compose nonassoc_micro Low Low) Low,
   Micro.compose nonassoc_micro Low (Micro.compose nonassoc_micro Low Low)) =
    (Middle, High).
Proof.
  vm_compute; reflexivity.
Qed.

(** Boolean IFDS discharges the separate symbolic algebra duties. *)
Example ifds_symbolic_laws : TabWeight.laws Micro.boolean.
Proof.
  exact TabWeight.boolean_laws.
Qed.

(** Every actual intermediate taint map is below the checked hand-written comparison solution. *)
Example taint_intermediate_least fuel :
  match Tab.raw ifds_ide 0 fuel with
  | inl s | inr s => TabSound.bounded ifds_ide (Jump.lookup ifds_ide taint_jump) s
  end.
Proof.
  apply TabSound.raw_bounded.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact micro_boolean_laws.
  - apply check_jumps_sound; exact taint_jump_accepts.
Qed.

(** The importing leastness client discharges the real algebra and encoding duties. *)
Example taint_certified_least fuel c :
  Tab.tabulate ifds_ide 0 fuel = Tab.Certified c ->
  forall k, leb (Micro.lat (Ide.micro ifds_ide))
    (Jump.lookup ifds_ide (proj1_sig c) k) (Jump.lookup ifds_ide taint_jump k) = true.
Proof.
  intro Hrun; apply TabSound.tabulate_jump_least with (start := 0) (fuel := fuel).
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact micro_boolean_laws.
  - exact Hrun.
  - apply check_jumps_sound; exact taint_jump_accepts.
Qed.

(** The taint client's declared finite support is closed for every actual flow output. *)
Theorem taint_flow_closed : Ifds.flow_closed taint.
Proof.
  intros e x [[]|] He Hx Hflow.
  - exact (or_introl eq_refl).
  - exact Logic.I.
Qed.

(** Every balanced path of the actual taint client is covered by a certified tabulator result. *)
Example actual_taint_balanced_sound fuel c n d :
  Tab.tabulate ifds_ide 0 fuel = Tab.Certified c ->
  Stack.balanced taint 0 None n d ->
  Jump.lookup ifds_ide (proj1_sig c) ((0, None), (n, d)) = true.
Proof.
  intros Hrun Hpath.
  apply (TabSound.ifds_post_balanced taint 0
    (Jump.lookup ifds_ide (proj1_sig c)) (0, None) n d).
  - exact taint_flow_closed.
  - exact Logic.I.
  - apply TabSound.supported_start_root; exact Logic.I.
  - apply TabSound.tabulate_jump_post with (fuel := fuel); exact Hrun.
  - exact Hpath.
Qed.

(** The original supported execution receives labels of its own steps and prepared flow pairs. *)
Example taint_original_path_gets_annotations :
  exists as_,
    TabPaths.trace ifds_ide (0, None, []) as_ (3, Some tt, []) /\
    Forall (fun a => In a (Jump.arcs ifds_ide)) as_.
Proof.
  apply TabPaths.trace_complete.
  - exact taint_flow_closed.
  - exact Logic.I.
  - exact matched_path.
Qed.

(** Importing weight clients use symbolic algebra duties without inspecting the carrier. *)
Example ifds_trace_weight_composes xs ys :
  equivalent (Micro.lat (Ide.micro ifds_ide)) (TabWeight.weight ifds_ide (xs ++ ys))
    (Micro.compose (Ide.micro ifds_ide)
      (TabWeight.weight ifds_ide ys) (TabWeight.weight ifds_ide xs)).
Proof.
  apply TabWeight.weight_app; [exact micro_boolean_laws|exact TabWeight.boolean_laws].
Qed.

(** The actual tabulator's symbolic-weight theorem retains the original matched execution. *)
Example actual_taint_symbolic_weight_sound fuel c n d :
  Tab.tabulate ifds_ide 0 fuel = Tab.Certified c ->
  Stack.balanced taint 0 None n d ->
  exists as_, TabPaths.trace ifds_ide (0, None, []) as_ (n, d, []) /\
    Forall (fun a => In a (Jump.arcs ifds_ide)) as_ /\
    leb (Micro.lat (Ide.micro ifds_ide)) (TabWeight.weight ifds_ide as_)
      (Jump.lookup ifds_ide (proj1_sig c) ((0, None), (n, d))) = true.
Proof.
  intros Hrun Hpath.
  apply (TabSound.tabulate_jump_sound ifds_ide 0 fuel c (0, None) n d).
  - exact micro_boolean_laws.
  - exact TabWeight.boolean_laws.
  - exact taint_flow_closed.
  - exact Logic.I.
  - apply TabSound.supported_start_root; exact Logic.I.
  - exact Hrun.
  - exact Hpath.
Qed.

Definition prefix_comparison (v : nat * option unit) :=
  match v with
  | (0, None) | (1, None) | (2, _) | (3, _) => true
  | _ => false
  end.

Example prefix_comparison_accepts :
  check_post bool_lattice
    (Analysis.system (value_analysis (TabValues.reach_ide taint)
      (Jump.lookup_c (TabValues.reach_ide taint) taint_jump) (0, None) true))
    prefix_comparison = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Actual raw prefix maps retain leastness even when the supplied fuel is exhausted. *)
Example prefix_raw_values_least fuel :
  match TabValues.raw (TabValues.reach_ide taint) taint_jump (0, None) true fuel with
  | inl s | inr s => TabValueSound.bounded (TabValues.reach_ide taint) prefix_comparison s
  end.
Proof.
  apply TabValueSound.raw_bounded.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
  - exact bool_lub.
  - exact TabValues.reach_micro_laws.
  - apply check_post_sound; exact prefix_comparison_accepts.
Qed.

(** Certified prefix results use explicit value lub duties and an actual checked comparison. *)
Example prefix_certified_values_least fuel c :
  TabValues.tabulate_values (TabValues.reach_ide taint) taint_jump (0, None) true fuel =
    TabValues.Certified c ->
  forall v, leb bool_lattice
    (TabValues.lookup (TabValues.reach_ide taint) (proj1_sig c) v)
    (prefix_comparison v) = true.
Proof.
  intro Hrun; apply (TabSound.tabulate_values_least (TabValues.reach_ide taint)
    taint_jump (0, None) true fuel c prefix_comparison).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
  - exact bool_lub.
  - exact TabValues.reach_micro_laws.
  - exact Hrun.
  - apply check_post_sound; exact prefix_comparison_accepts.
Qed.

(** The informative Boolean value adapter has the same symbolic monoid laws as IFDS. *)
Theorem reach_weight_laws : TabWeight.laws TabValues.reach_micro.
Proof.
  constructor.
  - intros []; split; reflexivity.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
Qed.

(** The concrete taint presentation has lawful listed endpoints. *)
Theorem taint_graph_wf : graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg taint))).
Proof.
  assert (Hout : forall n, Graph.out (Cfg.graph (Icfg.cfg (Ifds.icfg taint))) n =
    match n with 0 => [0] | 1 => [1] | 2 => [2] | _ => [] end).
  { intro n; apply Graph.of_pure_out. }
  assert (Hsource : forall e,
    Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg taint))) e = e).
  { intro e; apply Graph.of_pure_source. }
  assert (Htarget : forall e,
    Graph.target (Cfg.graph (Icfg.cfg (Ifds.icfg taint))) e = S e).
  { intro e; apply Graph.of_pure_target. }
  constructor.
  - repeat constructor; cbn [In]; intuition discriminate.
  - intros n Hin; vm_compute in Hin; destruct Hin as [Heq|Hbad]; [subst n|contradiction].
    vm_compute; auto.
  - intros n e He; rewrite Hout in He; destruct n as [|[|[|n]]];
      cbn [In] in He; try contradiction.
    all: destruct He as [Heq|Hbad]; [subst e; rewrite Hsource; reflexivity|contradiction].
  - intros n e Hn He; rewrite Hout in He; destruct n as [|[|[|n]]];
      cbn [In] in He; try contradiction.
    all: destruct He as [Heq|Hbad];
      [subst e; rewrite Htarget; vm_compute; auto|contradiction].
Qed.

(** Both actual certified phases cover the weight of every original prefix with any pending stack. *)
Example actual_prefix_value_sound jump_fuel value_fuel jumps values n d stack :
  Tab.tabulate (TabValues.reach_ide taint) 0 jump_fuel = Tab.Certified jumps ->
  TabValues.tabulate_values (TabValues.reach_ide taint) (proj1_sig jumps)
    (0, None) true value_fuel = TabValues.Certified values ->
  Stack.path taint (0, None, []) (n, d, stack) ->
  exists as_, TabPaths.trace (TabValues.reach_ide taint) (0, None, []) as_ (n, d, stack) /\
    Forall (fun a => In a (Jump.arcs (TabValues.reach_ide taint))) as_ /\
    leb bool_lattice (Micro.apply TabValues.reach_micro
      (TabWeight.weight (TabValues.reach_ide taint) as_) true)
      (TabValues.lookup (TabValues.reach_ide taint) (proj1_sig values) (n, d)) = true.
Proof.
  intros Hjump Hvalue Hpath.
  apply (TabSound.tabulate_values_sound (TabValues.reach_ide taint) (0, None) true
    jump_fuel value_fuel jumps values n d stack).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
  - exact TabValues.reach_micro_laws.
  - exact reach_weight_laws.
  - exact taint_graph_wf.
  - exact taint_flow_closed.
  - exact Logic.I.
  - exact Hjump.
  - exact Hvalue.
  - exact Hpath.
Qed.

(** Empty graph inventories satisfy the graph laws without admitting an edge. *)
Theorem empty_graph_wf : graph_wf (Cfg.graph (Icfg.cfg (Ifds.icfg empty_ifds))).
Proof.
  constructor.
  - constructor.
  - intros n Hin; vm_compute in Hin; contradiction.
  - intros n e Hin; vm_compute in Hin; contradiction.
  - intros n e Hn Hin; vm_compute in Hn; contradiction.
Qed.

(** The empty fixture's flow callback produces no unsupported output. *)
Theorem empty_flow_closed : Ifds.flow_closed empty_ifds.
Proof.
  intros e x y He Hx Hflow; vm_compute in Hflow; contradiction.
Qed.

(** An unlisted public seed is covered at its actual zero-step execution by the seed row. *)
Example unlisted_zero_step_value_sound jump_fuel value_fuel jumps values :
  Tab.tabulate (TabValues.reach_ide empty_ifds) 99 jump_fuel = Tab.Certified jumps ->
  TabValues.tabulate_values (TabValues.reach_ide empty_ifds) (proj1_sig jumps)
    (99, None) true value_fuel = TabValues.Certified values ->
  exists as_,
    TabPaths.trace (TabValues.reach_ide empty_ifds) (99, None, []) as_ (99, None, []) /\
    Forall (fun a => In a (Jump.arcs (TabValues.reach_ide empty_ifds))) as_ /\
    leb bool_lattice
      (Micro.apply TabValues.reach_micro
        (TabWeight.weight (TabValues.reach_ide empty_ifds) as_) true)
      (TabValues.lookup (TabValues.reach_ide empty_ifds) (proj1_sig values) (99, None)) = true.
Proof.
  intros Hjump Hvalue.
  apply (TabSound.tabulate_values_sound (TabValues.reach_ide empty_ifds) (99, None) true
    jump_fuel value_fuel jumps values 99 None []).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_laws.
  - exact TabValues.reach_micro_laws.
  - exact reach_weight_laws.
  - exact empty_graph_wf.
  - exact empty_flow_closed.
  - exact Logic.I.
  - exact Hjump.
  - exact Hvalue.
  - apply Stack.refl.
Qed.

(** Actual value runs maintain finite endpoint support and an exact duplicate-free pending queue. *)
Example actual_value_queue_and_keys fuel :
  match TabValues.raw (TabValues.reach_ide taint) taint_jump (0, None) true fuel with
  | inl s | inr s => TabValueProgress.invariant (TabValues.reach_ide taint)
      (TabValues.prepare (TabValues.reach_ide taint) taint_jump (0, None)) s
  end.
Proof.
  apply TabValueProgress.raw_invariant.
  apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
  apply FrameworkKey.option_laws; exact unit_encoding_laws.
Qed.
