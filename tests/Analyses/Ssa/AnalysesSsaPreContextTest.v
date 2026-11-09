(** * Inhabited PRE contexts and simultaneous assignments

    The single-block model inhabits every structural context law.
    For example, its two ordered instruction points have no SSA operands or expression kills.
    Builds on: AnalysesSsaPreContext, GraphCheckDom and ProgramSsaPoints. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom.
From Galois.Program Require Import ProgramCfg ProgramSsa ProgramSsaPoints.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext.
Import List.ListNotations.

Module One.

Definition bg : Graph.t unit unit :=
  Graph.of_pure [tt] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt).
Definition pg : Graph.t bool unit :=
  Graph.of_pure [false] [false; true] (fun n => if n then [] else [tt])
    (fun _ => false) (fun _ => true).
Definition bc := Cfg.Make bg unit_encoding unit_encoding.
Definition pc := Cfg.Make pg bool_encoding unit_encoding.
Definition vars := Vars.of_pure pc unit_encoding (fun _ => []) (fun _ => []) (fun _ => []).
Definition points :=
  SsaPoints.of_pure vars bc (fun _ => [false; true]) (fun _ => [tt]) (fun _ => tt)
    (fun _ => tt) (fun _ => None) (fun _ => []) (fun _ => []) (fun _ => None).
Definition ssa : Ssa.t unit unit unit unit unit :=
  Ssa.of_pure bc unit_encoding [] (fun _ => Arbitrary) (fun _ => tt)
    (fun _ => []) (fun _ => []) (fun _ => []).
Definition expr :=
  Bitvector.of_pure pc unit_encoding [tt] Forward (fun _ => []) (fun _ => []) (fun _ => None).
Definition client : Pre.client unit unit bool unit unit unit unit nat unit :=
  Pre.Client points ssa expr
    (Cost.lift (fun _ => 1%N) (fun _ => true))
    (Cost.lift (fun _ => 1%N) (fun _ => None)) [tt] []
    (Cost.lift (fun _ => 1%N) (fun _ => 1%positive))
    (Cost.lift (fun _ => 1%N) (fun _ => []))
    (fun _ _ => Some 0)
    (fun _ => Cost.lift (fun _ => 1%N) (fun _ => Some tt))
    (Cost.lift (fun _ => 1%N) (fun _ => true))
    (Cost.lift (fun _ => 1%N) (fun _ => false)).
Definition blocks := Prepared.prepare unit_encoding bg.
Definition point_graph := Prepared.prepare bool_encoding pg.
Definition parents : Map.t positive positive := Map.empty.
Definition tree := DomCheck.of_parents blocks parents.
Definition ctx :=
  Pre.Context client
    (Pre.Encs unit_encoding unit_encoding bool_encoding unit_encoding unit_encoding unit_encoding)
    blocks point_graph tree.

Example blocks_wf : graph_wf bg.
Proof.
  constructor.
  - vm_compute; constructor; [tauto|constructor].
  - intros [] H; exact H.
  - intros [] [] H; vm_compute in H; contradiction.
  - intros [] [] _ H; vm_compute in H; contradiction.
Qed.

Example points_wf : graph_wf pg.
Proof.
  constructor.
  - vm_compute; constructor; [intros [Hsame|[]]; discriminate Hsame|].
    constructor; [tauto|constructor].
  - intros [] H; vm_compute in H |- *; intuition discriminate.
  - intros [] [] H; vm_compute in H |- *; intuition discriminate.
  - intros [] [] _ H; vm_compute in H |- *; intuition discriminate.
Qed.

Example blocks_ready : Prepared.ready blocks.
Proof.
  apply Prepared.prepare_ready; [exact unit_encoding_laws|exact blocks_wf|].
  intros []; vm_compute; constructor.
Qed.

Example points_ready : Prepared.ready point_graph.
Proof.
  apply Prepared.prepare_ready; [exact bool_encoding_laws|exact points_wf|].
  intros []; vm_compute; repeat constructor; tauto.
Qed.

Example accepted_tree : DomCheck.check blocks parents = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example tree_exact : Dom.exact blocks tree.
Proof.
  apply DomCheck.check_sound; [exact blocks_ready|apply Map.wf_empty|exact accepted_tree].
Qed.

Example point_laws : ssa_point_laws points.
Proof.
  constructor.
  - exact points_wf.
  - intros []; vm_compute; repeat constructor; tauto.
  - exact blocks_wf.
  - intros []; vm_compute; constructor.
  - intros []; vm_compute; split.
    all: intros _; try tauto; exists tt; tauto.
  - intros []; vm_compute; constructor; [intros [Hsame|[]]; discriminate Hsame|].
    constructor; [tauto|constructor].
  - intros [] [] _ _; reflexivity.
  - intros []; vm_compute; discriminate.
  - intros [] _.
    apply (point_chain_step false true [] tt []); [vm_compute; now left|reflexivity|constructor].
  - intros [] [] _ _; reflexivity.
  - intros [] [] _ H _; vm_compute in H |- *; intuition discriminate.
  - intros [] _; reflexivity.
  - intros [] [] _; vm_compute; tauto.
  - intros [] [] _ _; reflexivity.
  - intros [] H; vm_compute in H; contradiction.
  - intros [] [] [] _ _ H; discriminate.
  - intros [] H; vm_compute in H; contradiction.
  - intros [] [] [] _ _ _ _; reflexivity.
Qed.

Example strict_points : reachable_point_ssa points.
Proof.
  constructor.
  - exists false; reflexivity.
  - intros [] [] _ [Huse|[[] [_ Huse]]]; vm_compute in Huse; contradiction.
  - intros [] [] [] _ _ Hdef; vm_compute in Hdef; contradiction.
  - intros [] [] [] Hhome; discriminate.
Qed.

Example shapes : Pre.shape_laws ctx.
Proof.
  constructor.
  - intros []; constructor.
  - intros [] [] H; discriminate.
  - intros [] _; apply Pre.family_seed; now left.
  - intros [] _ [] H; contradiction.
  - intros [] [] _ _ _ _; reflexivity.
  - intros [] [] _ _ _; reflexivity.
  - intros [] [] H; vm_compute in H; contradiction.
  - intros [] [] [] _ _; reflexivity.
  - intros [] [] [] _ _ _; reflexivity.
  - intros [] [] [] _ _; reflexivity.
Qed.

Example point_reachable : forall n, reachable pg n.
Proof.
  intros [].
  - exact (@reachable_step bool unit pg tt
      (@reachable_entry bool unit pg false (or_introl eq_refl)) (or_introl eq_refl)).
  - apply reachable_entry; now left.
Qed.

Example graphs : Pre.graph_laws ctx.
Proof.
  constructor.
  - exact unit_encoding_laws.
  - exact unit_encoding_laws.
  - exact bool_encoding_laws.
  - exact unit_encoding_laws.
  - exact unit_encoding_laws.
  - exact unit_encoding_laws.
  - exact point_laws.
  - exact strict_points.
  - reflexivity.
  - reflexivity.
  - apply Prepared.prepare_graph.
  - apply Prepared.prepare_graph.
  - exact blocks_ready.
  - exact points_ready.
  - exact tree_exact.
  - intros [] _; apply reachable_entry; now left.
  - intros n _; apply point_reachable.
  - exists tt, false; repeat split; reflexivity.
  - intros [] [] _ H; vm_compute in H; contradiction.
Qed.

Example kills : Pre.kill_laws ctx.
Proof.
  constructor.
  - intros [] [] _ _ H; vm_compute in H; discriminate.
  - intros [] [] _ H; contradiction.
  - intros [] [] _ _; reflexivity.
  - intros [] [] H; discriminate.
Qed.

Example runtime : Pre.runtime_laws ctx.
Proof.
  constructor.
  - intros [] env1 env2 _; reflexivity.
  - intros [] [] [] env _ _ _; reflexivity.
Qed.

(** This finite model proves that the bundled lawful-input domain is inhabited. *)
Example laws : Pre.laws ctx.
Proof.
  exact (Pre.Laws ctx shapes graphs kills runtime).
Qed.

Definition bad_parents := Map.of_list positive_encoding [(1, 1)]%positive.

Example rejected_tree : DomCheck.check blocks bad_parents = false.
Proof.
  vm_compute; reflexivity.
Qed.

End One.

Module Parallel.

Definition bg : Graph.t bool bool :=
  Graph.of_pure [false] [false; true] (fun b => if b then [] else [false; true])
    (fun _ => false) (fun _ => true).
Definition bc := Cfg.Make bg bool_encoding bool_encoding.
Definition vars := Vars.of_pure bc bool_encoding (fun _ => []) (fun _ => []) (fun _ => []).
Definition points :=
  SsaPoints.of_pure vars bc (fun b => [b]) (fun _ => []) (fun _ => false)
    (fun b => b) (@Some bool)
    (fun _ => [false; true]) (fun be => if be then [true; false] else [false; true])
    (fun _ => None).
Definition ssa : Ssa.t bool bool bool unit unit :=
  Ssa.of_pure bc bool_encoding [false; true] (fun _ => Arbitrary) (fun _ => false)
    (fun _ => [false; true]) (fun be => if be then [true; false] else [false; true])
    (fun _ => []).
Definition expr :=
  Bitvector.of_pure bc bool_encoding [false; true] Forward
    (fun _ => []) (fun _ => []) (fun _ => None).
Definition client : Pre.client bool bool bool bool bool unit unit bool bool :=
  Pre.Client points ssa expr
    (Cost.lift (fun _ => 1%N) (fun _ => true))
    (Cost.lift (fun _ => 1%N) (fun _ => None)) [false; false] [false; true]
    (Cost.lift (fun _ => 1%N) (fun _ => 1%positive))
    (Cost.lift (fun _ => 1%N) (fun u => [u]))
    (fun u env => env u)
    (fun be => Cost.lift (fun _ => 1%N) (fun u => Some (if be then negb u else u)))
    (Cost.lift (fun _ => 1%N) (fun _ => false))
    (Cost.lift (fun _ => 1%N) (fun _ => false)).
Definition prepared := Prepared.prepare bool_encoding bg.
Definition ctx :=
  Pre.Context client
    (Pre.Encs bool_encoding bool_encoding bool_encoding bool_encoding bool_encoding bool_encoding)
    prepared prepared (Dom.Tree Map.empty Map.empty Map.empty).

Example separate_parallel_assignments :
  Pre.phi_operand ctx false false = false /\ Pre.phi_operand ctx true false = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example simultaneous_exchange :
  Pre.phi_env ctx true (@Some bool) false = Some true /\
  Pre.phi_env ctx true (@Some bool) true = Some false.
Proof.
  vm_compute; split; reflexivity.
Qed.

End Parallel.
