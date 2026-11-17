(** * Generic joins on explicit index trees

    These fixtures supply small read-only trees to the operations-only join functor.
    For example, the triangle fixture has the sole assignment [2; 3; 5].
    Builds on: Join, IndexSig, ValueSig and Syntax. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig IndexSig Syntax Join.

Import List.ListNotations.

Module JoinFixtureValue <: VALUE_OPS.
  Definition t := positive.
  Definition eqb := Pos.eqb.
  Definition encode (p : positive) := p.
  Definition prim (_ : positive) (_ : list t) : option t := None.
  Definition merge (_ : positive) := Pos.max.
End JoinFixtureValue.

(** The fixture implements navigation only and claims no certified index laws. *)
Module JoinFixtureIndex <: INDEX_OPS JoinFixtureValue.
  Module C := CellKeyCode JoinFixtureValue.
  Definition t := list (positive * list (cell positive * positive)).
  Definition empty : t := [].
  Definition insert (_ : list (cell positive)) (ix : t) := ix.
  Definition remove (_ : list (cell positive)) (ix : t) := ix.
  Definition next (_ : t) := 16%positive.
  Definition root (_ : t) := 1%positive.

  Fixpoint edges (ix : t) (n : positive) : list (cell positive * positive) :=
    match ix with
    | [] => []
    | (m, es) :: rest => if Pos.eqb n m then es else edges rest n
    end.

  Fixpoint probe (c : cell positive) (es : list (cell positive * positive))
      : option positive :=
    match es with
    | [] => None
    | (d, m) :: rest => if C.eqb c d then Some m else probe c rest
    end.

  Definition child (ix : t) (n : positive) (c : cell positive) := probe c (edges ix n).
  Definition children (ix : t) (n : positive) := map fst (edges ix n).
  Definition degree (ix : t) (n : positive) := N.of_nat (length (edges ix n)).
End JoinFixtureIndex.

Module FixtureJoin := JoinCode JoinFixtureValue JoinFixtureIndex.

Definition first_relation : JoinFixtureIndex.t :=
  [(1, [(Val 3, 2); (Val 2, 3)]);
   (2, [(Val 3, 4)]);
   (3, [(Val 3, 5); (Val 4, 6)])]%positive.

Definition second_relation : JoinFixtureIndex.t :=
  [(1, [(Val 3, 2); (Val 4, 3)]);
   (2, [(Val 5, 4)]);
   (3, [(Val 6, 5)])]%positive.

Definition third_relation : JoinFixtureIndex.t :=
  [(1, [(Val 2, 2); (Val 7, 3)]);
   (2, [(Val 5, 4)]);
   (3, [(Val 6, 5)])]%positive.

Definition shared_plan := JPlan 3 [[0; 1]; [1; 2]].
Definition triangle_plan := JPlan 3 [[0; 1]; [1; 2]; [0; 2]].

(** The expected order is retained from the landed shared-two-atoms test. *)
Example shared_two_atoms :
  FixtureJoin.run shared_plan [first_relation; second_relation] =
    map (map Val) [[2; 4; 6]; [2; 3; 5]; [3; 3; 5]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** The expected tuple is retained from the landed triangle-three-atoms test. *)
Example triangle_three_atoms :
  FixtureJoin.run triangle_plan [first_relation; second_relation; third_relation] =
    map (map Val) [[2; 3; 5]]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** The empty-body observation is retained from the landed join tests. *)
Example empty_body : FixtureJoin.run (JPlan 0 []) [] = [[]].
Proof.
  vm_compute. reflexivity.
Qed.

(** The empty-relation observation is retained from the landed join tests. *)
Example empty_relation :
  FixtureJoin.run (JPlan 2 [[0; 1]]) [JoinFixtureIndex.empty] = [].
Proof.
  vm_compute. reflexivity.
Qed.

(** Equal degrees choose the earliest participating column. *)
Example pivot_ties_choose_first :
  FixtureJoin.choose_index triangle_plan
    [first_relation; second_relation; third_relation] 0 [1; 1; 1]%positive = Some 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** A smaller later degree wins over an earlier participant. *)
Example pivot_uses_smallest_degree :
  FixtureJoin.choose_index (JPlan 1 [[0]; [0]])
    [first_relation; second_relation] 0 [1; 2]%positive = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

(** Advancing a completed assignment fails instead of manufacturing an extra variable. *)
Example advance_stops_at_last_level :
  FixtureJoin.advance_nodes (JPlan 0 []) [] 0 [] (Val 2%positive) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** A nonparticipating relation retains its current node. *)
Example advance_keeps_other_nodes :
  FixtureJoin.advance_nodes shared_plan [first_relation; second_relation]
    0 [1; 1]%positive (Val 2%positive) = Some [3; 1]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** The first column rejects every child of the smaller second-column pivot. *)
Definition first_probe_miss_relation : JoinFixtureIndex.t :=
  [(1, [(Val 2, 2); (Val 3, 3); (Val 5, 4)])]%positive.

Definition later_probe_pivot_relation : JoinFixtureIndex.t :=
  [(1, [(Val 7, 2); (Val 11, 3)])]%positive.

Definition first_probe_miss_plan := JPlan 1 [[0]; [0]].

(** The pivot must come after the column that rejects its candidates. *)
Example first_probe_miss_uses_later_pivot :
  FixtureJoin.choose_index first_probe_miss_plan
    [first_probe_miss_relation; later_probe_pivot_relation] 0 [1; 1]%positive = Some 1.
Proof.
  vm_compute. reflexivity.
Qed.

(** Both pivot children fail the first probe, leaving the join empty. *)
Example run_first_probe_miss :
  FixtureJoin.run first_probe_miss_plan
    [first_probe_miss_relation; later_probe_pivot_relation] = [].
Proof.
  vm_compute. reflexivity.
Qed.
