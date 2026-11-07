(** * Producer-independent strict SSA fixtures

    A hand-written diamond SSA presentation uses a checked candidate dominator tree.
    For example, edge one to two dominates the left arm and does not dominate the join.
    Builds on: ProgramStrict, ProgramEdgeProjection and GraphFixtures. *)

From Stdlib Require Import List Arith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphFrontierSpec
  GraphCheckDom GraphFixtures.
From Galois.Program Require Import ProgramSemantics ProgramCfg ProgramLink ProgramSsa
  ProgramStrict ProgramEdgeProjection.
Import List.ListNotations.

Definition diamond_cfg : Cfg.t nat (nat * nat) :=
  Cfg.Make (Prepared.graph Fixtures.Diamond.prepared) nat_encoding
    (codec_enc (pair_codec nat_codec nat_codec)).

Definition diamond_ssa : Ssa.t nat (nat * nat) nat unit unit :=
  Ssa.of_pure diamond_cfg nat_encoding [0; 1]
    (fun x => if Nat.eqb x 0 then Op tt [] else
      if Nat.eqb x 1 then Param 4 0 else Arbitrary)
    (fun x => if Nat.eqb x 0 then 1 else 4)
    (fun b => if Nat.eqb b 4 then [1] else [])
    (fun _ => [0])
    (fun e => if Nat.eqb (fst e) 1 then [(tt, [0])] else []).

Definition diamond_context :=
  make_dom_context Fixtures.Diamond.prepared Fixtures.Diamond.tree.

Example accepts_supplied_parents :
  DomCheck.check Fixtures.Diamond.prepared Fixtures.Diamond.parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example rejects_wrong_parents :
  DomCheck.check Fixtures.Diamond.prepared Fixtures.Line.parents = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_left_arm : dominating_edges_in diamond_context 2 = [(1, 2)].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_join : dominating_edges_in diamond_context 4 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_entry : dominating_edges_in diamond_context 1 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_unknown : dominating_edges_in diamond_context 9 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_guard : Ssa.guards diamond_ssa (1, 2) = [(tt, [0])].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_parameter : Ssa.def diamond_ssa 1 = Param 4 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_semantic_dominance :
  edge_dominates (Prepared.graph Fixtures.Diamond.prepared) (1, 2) 2.
Proof.
  eapply dominating_edges_in_sound.
  - exact Fixtures.Diamond.fixture_ready.
  - exact Fixtures.Diamond.tree_exact.
  - change (In (1, 2) (dominating_edges_in diamond_context 2)).
    rewrite diamond_left_arm; left; reflexivity.
Qed.

Example line_ancestor_order :
  dominating_edges_in (make_dom_context Fixtures.Line.prepared Fixtures.Line.tree) 4 =
    [(1, 2); (2, 3); (3, 4)].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_preheader_edge :
  dominating_edges_in
    (make_dom_context Fixtures.NestedLoop.prepared Fixtures.NestedLoop.tree) 3 =
    [(1, 2); (2, 3)].
Proof.
  vm_compute; reflexivity.
Qed.

Definition diamond_machine : semantics nat unit :=
  Semantics (fun s => s = 1)
    (fun s l t => l = [] /\ In (s, t) [(1, 2); (1, 3); (2, 4); (3, 4)]).

Definition diamond_link : Link.t nat unit nat (nat * nat) :=
  Link.Make (fun s => s) (fun s _ t e => e = (s, t)) (fun _ _ _ => False).

Definition diamond_values : SsaLink.t nat unit nat (nat * nat) nat nat :=
  SsaLink.Make diamond_link (fun _ x => if Nat.eqb x 0 then Some 7 else None).

Definition evaluate (_ : unit) (args : list nat) :=
  match args with [] => Some 7 | _ => None end.

Definition holds (_ : unit) (args : list nat) := args = [7].

Example diamond_link_laws :
  link_laws diamond_machine (Cfg.graph diamond_cfg) diamond_link.
Proof.
  constructor.
  - exact (proj1 Fixtures.Diamond.fixture_ready).
  - intros s ->; vm_compute; left; reflexivity.
  - intros s l t _ Hstep; right; exists (s, t); reflexivity.
  - intros e s l t _ [-> Hedge] ->.
    vm_compute in Hedge; destruct Hedge as [Heq|[Heq|[Heq|[Heq|Hbad]]]];
      [| | | |contradiction]; inversion Heq; subst; vm_compute; tauto.
  - intros s l t _ _ Hbad; contradiction.
Qed.

Example diamond_ssa_laws :
  ssa_laws diamond_machine diamond_ssa diamond_values evaluate holds.
Proof.
  constructor.
  - exact diamond_link_laws.
  - intros [|[|x]] b i Hdef; cbn in Hdef; try discriminate.
    injection Hdef as <- <-; reflexivity.
  - intros e s l t _ _ Htaken g ys Hguard.
    change (In (g, ys) (if Nat.eqb (fst e) 1 then [(tt, [0])] else [])) in Hguard.
    destruct (Nat.eqb (fst e) 1); [|contradiction].
    destruct Hguard as [Heq|Hbad]; [inversion Heq; subst|contradiction].
    exists [7]; split; [constructor; [reflexivity|constructor]|reflexivity].
  - intros e s l t _ _ Htaken g ys x o args Hguard Hin Hdef.
    change (In (g, ys) (if Nat.eqb (fst e) 1 then [(tt, [0])] else [])) in Hguard.
    destruct (Nat.eqb (fst e) 1); [|contradiction].
    destruct Hguard as [Heq|Hbad]; [inversion Heq; subst|contradiction].
    destruct Hin as [<-|Hbad]; [|contradiction].
    cbn in Hdef; injection Hdef as <- <-.
    exists [], 7; split; [constructor|split; reflexivity].
  - intros x c s l t _ _ Hvalue; left; exact Hvalue.
  - intros s [|x] c _ Hvalue; [left; reflexivity|discriminate].
Qed.

Example diamond_strict_laws : strict_ssa_laws diamond_machine diamond_ssa diamond_values.
Proof.
  constructor.
  - intros x s l t _ _ _ Hchange; exfalso; apply Hchange; reflexivity.
  - intros e x s l t _ _ _ Hchange; exfalso; apply Hchange; reflexivity.
  - intros x s l t _ _ _ _; reflexivity.
  - intros e x s l t _ _ _ _; reflexivity.
  - intros e g ys x _ Hguard Hin.
    change (In (g, ys) (if Nat.eqb (fst e) 1 then [(tt, [0])] else [])) in Hguard.
    destruct (Nat.eqb (fst e) 1); [|contradiction].
    destruct Hguard as [Heq|Hbad]; [inversion Heq; subst|contradiction].
    destruct Hin as [<-|Hbad]; [|contradiction].
    intros s es Hentry Hpath; vm_compute in Hentry.
    destruct Hentry as [<-|Hbad]; [left; reflexivity|contradiction].
  - intros [|[|x]] o args y Hdef Hin; cbn in Hdef; try discriminate.
    injection Hdef as <- <-; contradiction.
Qed.

Example dominated_guard_instance :
  (forall g ys, In (g, ys) (Ssa.guards diamond_ssa (1, 2)) ->
    exists cs, Forall2 (fun y c => SsaLink.val diamond_values 2 y = Some c) ys cs /\
      holds g cs) /\
  guard_ops_consistent diamond_ssa diamond_values evaluate 2 (1, 2).
Proof.
  eapply dominated_guard_holds.
  - exact diamond_ssa_laws.
  - exact diamond_strict_laws.
  - exists 1, []; split; [reflexivity|].
    apply exec_one; split; [reflexivity|left; reflexivity].
  - exact diamond_semantic_dominance.
Qed.

Definition repeated_graph : Graph.t nat unit :=
  Graph.of_pure [1] [1; 2] (fun n => if Nat.eqb n 1 then [tt; tt] else [])
    (fun _ => 1) (fun _ => 2).

Example repeated_graph_wf : graph_wf repeated_graph.
Proof.
  constructor.
  - repeat constructor; cbn; intuition congruence.
  - intros n [<-|Hbad]; [left; reflexivity|contradiction].
  - intros n e Hin; unfold repeated_graph in Hin; rewrite Graph.of_pure_out in Hin.
    destruct (Nat.eqb n 1) eqn:Hsame; [|contradiction].
    apply Nat.eqb_eq in Hsame; subst n; reflexivity.
  - intros n e _ Hin; right; left; reflexivity.
Qed.

Definition repeated_prepared :=
  Prepared.prepare nat_encoding (EdgeProjection.occurrence_graph repeated_graph).

Example repeated_ready : Prepared.ready repeated_prepared.
Proof.
  apply Prepared.prepare_ready; [exact nat_encoding_laws| |].
  - apply EdgeProjection.occurrence_graph_wf; exact repeated_graph_wf.
  - intro n; rewrite EdgeProjection.occurrence_out; apply EdgeProjection.occurrences_nodup.
Qed.

Definition repeated_parents := Map.of_list positive_encoding [(2, 1)]%positive.
Definition repeated_tree := DomCheck.of_parents repeated_prepared repeated_parents.

Example repeated_tree_exact : Dom.exact repeated_prepared repeated_tree.
Proof.
  apply DomCheck.check_sound; [exact repeated_ready|apply Map.wf_of_list|].
  vm_compute; reflexivity.
Qed.

Example repeated_source_cells :
  Graph.out (Prepared.graph repeated_prepared) 1 = [(tt, 0); (tt, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_query_is_conservative :
  dominating_edges_projected
    (make_occurrence_dom_context nat_encoding repeated_graph repeated_tree) 2 = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_walk_boundary :
  Cost.value (dom_walk_step_c diamond_context (None, [])) = inr [] /\
  Cost.ticks (dom_walk_step_c diamond_context (None, [])) = 0%N.
Proof.
  vm_compute; split; reflexivity.
Qed.
