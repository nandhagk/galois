(** * Constraint systems

    A system supplies costed targets and query trees independently of its laws.
    For example, a constant query can constrain an unknown without reading any unknown.
    Builds on: FixpointQuery, BaseMap and LatticeCore. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery.

Module System.

(** System callbacks compute targets and right-hand sides without proof inputs. *)
Record t (X C A : Type) := Make {
  constraints : list C;
  target_c : C -> Cost.t X;
  rhs_c : C -> Cost.t (Query.t X A)
}.

Arguments Make {X C A}.
Arguments constraints {X C A}.
Arguments target_c {X C A}.
Arguments rhs_c {X C A}.

Definition target {X C A} (S : t X C A) c := Cost.value (target_c S c).
Definition rhs {X C A} (S : t X C A) c := Cost.value (rhs_c S c).

(** Static summaries are computational data and may conservatively contain duplicates. *)
Record static {X C A} (S : t X C A) := Static {
  deps_c : C -> Cost.t (list X);
  side_targets_c : C -> Cost.t (list X)
}.

Arguments Static {X C A S}.
Arguments deps_c {X C A S}.
Arguments side_targets_c {X C A S}.

Definition deps {X C A S} (SS : @static X C A S) c := Cost.value (deps_c SS c).
Definition side_targets {X C A S} (SS : @static X C A S) c :=
  Cost.value (side_targets_c SS c).

(** Summary laws cover every read and side target on every assignment. *)
Record static_laws {X C A S} (SS : @static X C A S) : Prop := {
  reads_within : forall c s, incl (Query.reads (rhs S c) s) (deps SS c);
  sides_within : forall c s,
    incl (map fst (Query.sides (rhs S c) s)) (side_targets SS c)
}.

Arguments reads_within {X C A S SS}.
Arguments sides_within {X C A S SS}.

End System.

Abbreviation deps := System.deps.
Abbreviation side_targets := System.side_targets.

(** An assignment stores a finite map and interprets absent entries as bottom. *)
Definition assignment (X A : Type) := Map.t X A.

Definition lookup_c {X A} (EX : encoding X) (L : lattice A)
    (m : assignment X A) x := Map.find_or_c EX (bot L) x m.

Definition lookup {X A} (EX : encoding X) (L : lattice A) m x :=
  Cost.value (lookup_c EX L m x).

(** Lookup exposes presence and bottom through the public map equation. *)
Theorem lookup_equation {X A} (EX : encoding X) (L : lattice A) m x :
  lookup EX L m x = match Map.get EX x m with Some a => a | None => bot L end.
Proof.
  apply Map.find_or_equation.
Qed.

(** Assignment lookup retains the complete underlying map lookup charge. *)
Theorem lookup_cost {X A} (EX : encoding X) (L : lattice A) m x :
  Cost.ticks (lookup_c EX L m x) = Cost.ticks (Map.get_c EX x m).
Proof.
  unfold lookup_c. apply Map.find_or_cost.
Qed.

(** Empty assignments are pointwise bottom. *)
Theorem lookup_empty {X A} (EX : encoding X) (L : lattice A) x :
  lookup EX L Map.empty x = bot L.
Proof.
  rewrite lookup_equation, Map.get_empty; reflexivity.
Qed.

(** A post-solution bounds both returned and emitted values. *)
Definition post_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) :=
  forall c, In c (System.constraints S) ->
    leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true /\
    forall x a, In (x, a) (Query.sides (System.rhs S c) s) -> leb L a (s x) = true.

(** Monotonicity matches each side contribution with a larger contribution at the same key. *)
Definition monotone_query {X A} (L : lattice A) (q : Query.t X A) :=
  monotone_on_assignments L L (Query.eval q) /\
  forall s u, fun_leb L s u -> forall x a, In (x, a) (Query.sides q s) ->
    exists b, In (x, b) (Query.sides q u) /\ leb L a b = true.

(** Every listed constraint of a monotone system has a monotone query. *)
Definition monotone_system {X C A} (L : lattice A) (S : System.t X C A) :=
  forall c, In c (System.constraints S) -> monotone_query L (System.rhs S c).

Arguments lookup_c {X A} EX L m x : simpl never.
Arguments lookup {X A} EX L m x : simpl never.
