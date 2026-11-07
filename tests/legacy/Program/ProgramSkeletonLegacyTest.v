(** * Structured graph differential fixtures

    Both graph implementations are observed before any sorting or deduplication.
    For example, repeated switch labels retain their separate edge occurrences.
    Builds on: ProgramSkeletonTest and legacy ViewsStructured. *)

From Stdlib Require Import List.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSkeleton ProgramSkeletonCfg.
From Galois.Tests.Program Require Import ProgramSkeletonTest.
From GaloisLegacy.Graph Require GraphCore.
From GaloisLegacy.Views Require ViewsSkeleton ViewsStructured.
Import List.ListNotations.

Module OldSyntax := ViewsSkeleton.
Module Old := ViewsStructured.

Fixpoint legacy_stmt (s : Skeleton.stmt nat bool) : OldSyntax.Skeleton.stmt nat bool :=
  match s with
  | Skeleton.Atom a => OldSyntax.Skeleton.Atom a
  | Skeleton.Seq a b => OldSyntax.Skeleton.Seq (legacy_stmt a) (legacy_stmt b)
  | Skeleton.If g a b => OldSyntax.Skeleton.If g (legacy_stmt a) (legacy_stmt b)
  | Skeleton.Block a => OldSyntax.Skeleton.Block (legacy_stmt a)
  | Skeleton.Loop a => OldSyntax.Skeleton.Loop (legacy_stmt a)
  | Skeleton.Jump n => OldSyntax.Skeleton.Jump n
  | Skeleton.JumpIf g n => OldSyntax.Skeleton.JumpIf g n
  | Skeleton.JumpTable g ns n => OldSyntax.Skeleton.JumpTable g ns n
  end.

Definition point_observation v :=
  let position_observation := map
    (fun d => match d with DFirst => 0 | DSecond => 1 | DBody => 2 end) in
  match v with
  | PEntry p => (true, position_observation p)
  | PExit p => (false, position_observation p)
  end.

Definition legacy_point_observation v :=
  let position_observation := map
    (fun d => match d with
    | OldSyntax.DFirst => 0
    | OldSyntax.DSecond => 1
    | OldSyntax.DBody => 2
    end) in
  match v with
  | Old.PEntry p => (true, position_observation p)
  | Old.PExit p => (false, position_observation p)
  end.

Definition new_observation (s : Skeleton.stmt nat bool) :=
  let g := Cfg.graph (skeleton_cfg s) in
  map (fun e => (point_observation (Graph.source g e), point_observation (Graph.target g e)))
    (Cfg.edges (skeleton_cfg s)).

Definition old_observation s :=
  let g := Old.skeleton_graph (legacy_stmt s) in
  map (fun e => (legacy_point_observation (GraphCore.Graph.source g e),
    legacy_point_observation (GraphCore.Graph.target g e)))
    (flat_map (GraphCore.Graph.out g) (GraphCore.Graph.nodes g)).

Example fixture_endpoints_agree :
  map new_observation fixtures = map old_observation fixtures.
Proof.
  vm_compute; reflexivity.
Qed.

Example fixture_counts_agree :
  map (fun s => length (new_observation s)) fixtures =
    map (fun s => length (old_observation s)) fixtures.
Proof.
  vm_compute; reflexivity.
Qed.

Example fixture_label_checks_agree :
  map (labels_ok 0) fixtures = map (fun s => OldSyntax.labels_ok 0 (legacy_stmt s)) fixtures.
Proof.
  vm_compute; reflexivity.
Qed.
