(** * Pointer client seeding and saturation

    Both pointer clients preserve seed rows and propagate an address through a copy constraint.
    For example, copying pointer one to pointer three transfers address ten without address twenty.
    Builds on: the relational code tower and the Andersen and Steensgaard clients.

    Groups:
    - SeedTests: the seed database keeps the three input rows of each client.
    - SolveTests: saturation copies an address through a copy constraint. *)

From Stdlib Require Import List PArith NArith Bool.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Index Join Database Run.
From Galois.Clients Require Import AndersenSig Andersen Steensgaard.
Import List.ListNotations.

(** * Fixtures *)

Module SolveValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim (_ : positive) (_ : list positive) : option positive := None.
  Definition merge (_ : positive) := Pos.max.
End SolveValue.

Module SolveIndex := IndexCode SolveValue.
Module SolveJoin := JoinCode SolveValue SolveIndex.
Module SolveDatabase := DatabaseCode SolveValue SolveIndex.
Module SolveRun := RunCode SolveValue SolveIndex SolveJoin SolveDatabase.
Module SolveAndersen := AndersenCode SolveValue SolveIndex SolveJoin SolveDatabase SolveRun.
Module SolveSteensgaard := SteensgaardCode SolveValue SolveIndex SolveJoin SolveDatabase SolveRun.

(** Pointer one holds address ten, pointer two holds address twenty, and pointer three copies
    pointer one. *)
Definition solve_input : pointer_input :=
  PointerInput [Addr 1 10; Addr 2 20; Copy 3 1] [].

(** Saturation stops after at most 10 iterations and allocates at most 100 identifiers. *)
Definition solve_limits : limits := Limits 10 100.

Module SeedTests.

  Local Open Scope positive_scope.

  (** The queries that the seed rows of both clients must answer. *)
  Definition seed_queries : list (positive * list (cell positive)) :=
    [(1, [Val 1; Val 10]);
     (1, [Val 2; Val 20]);
     (2, [Val 3; Val 1]);
     (1, [Val 3; Val 10])].

  (** Andersen stores the three input constraints without adding a derived address constraint. *)
  Example andersen_seed_keeps_input_rows :
    map (fun query => fst (SolveDatabase.lookup (fst query) (snd query)
      (SolveAndersen.seed solve_input))) seed_queries =
    [Some None; Some None; Some None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Steensgaard stores the same three source constraints in its seed database. *)
  Example steensgaard_seed_keeps_input_rows :
    map (fun query => fst (SolveDatabase.lookup (fst query) (snd query)
      (SolveSteensgaard.seed solve_input))) seed_queries =
    [Some None; Some None; Some None; None].
  Proof.
    vm_compute; reflexivity.
  Qed.

End SeedTests.

Module SolveTests.

  Local Open Scope positive_scope.

  (** The address pairs that the solved databases must answer. *)
  Definition point_queries : list (positive * positive) :=
    [(1, 10); (2, 20); (3, 10); (3, 20)].

  (** The inclusion analysis solved for the input. *)
  Definition andersen_result := SolveAndersen.solve solve_input solve_limits.

  (** The unification analysis solved for the input. *)
  Definition steensgaard_result := SolveSteensgaard.solve solve_input solve_limits.

  (** Inclusion saturation reaches a fixpoint on this input. *)
  Example andersen_saturates : fst andersen_result = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Inclusion saturation copies address ten to pointer three and keeps address twenty apart. *)
  Example andersen_copies_address_ten :
    map (fun query => SolveAndersen.points (snd andersen_result) (fst query) (snd query))
      point_queries = [true; true; true; false].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unification saturation reaches a fixpoint on this input. *)
  Example steensgaard_saturates : fst steensgaard_result = Saturated.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Unification saturation finds the same targets without merging address twenty. *)
  Example steensgaard_copies_address_ten :
    map (fun query => SolveSteensgaard.points (snd steensgaard_result) (fst query) (snd query))
      point_queries = [true; true; true; false].
  Proof.
    vm_compute. reflexivity.
  Qed.

End SolveTests.
