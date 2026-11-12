(** * Program semantics and traced behaviours

    Semantics describe initial states and transitions for each program value.
    For example, reachability includes an initial state before any transition.
    Builds on: Base.KeySig and Stdlib.List. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig.

Module Type SEMANTICS (P : TYPE).
  Parameter state : Type.
  Parameter initial : P.t -> state -> Prop.
  Parameter step : P.t -> state -> state -> Prop.
End SEMANTICS.

Inductive reachable {S : Type} (init : S -> Prop) (step : S -> S -> Prop) : S -> Prop :=
  | Reach_initial : forall s, init s -> reachable init step s
  | Reach_step : forall s t, reachable init step s -> step s t -> reachable init step t.

Inductive traced_run {S O : Type} (step : S -> list O -> S -> Prop)
    : S -> list O -> S -> Prop :=
  | Run_refl : forall s, traced_run step s nil s
  | Run_step : forall s l u tr t,
      step s l u -> traced_run step u tr t -> traced_run step s (l ++ tr) t.

CoInductive traced_diverges {S O : Type} (step : S -> list O -> S -> Prop) : S -> Prop :=
  | Diverges_step : forall s l t,
      step s l t -> traced_diverges step t -> traced_diverges step s.

Inductive ending :=
  | EndFinal
  | EndTrap
  | EndStop
  | EndStuck.

Module Type TRACES (P : TYPE) (M : SEMANTICS P).
  Parameter event : Type.
  Parameter lstep : P.t -> M.state -> list event -> M.state -> Prop.
  Parameter final trapped stopped : P.t -> M.state -> Prop.
  (** Forgetting event labels gives exactly the underlying transitions. *)
  Parameter lstep_spec : forall p s t, M.step p s t <-> exists l, lstep p s l t.
  Definition running p s := exists l t, lstep p s l t.
  Definition stuck p s :=
    ~ running p s /\ ~ final p s /\ ~ trapped p s /\ ~ stopped p s.
  Definition ends_as p k s :=
    match k with
    | EndFinal => final p s
    | EndTrap => trapped p s
    | EndStop => stopped p s
    | EndStuck => stuck p s
    end.
  Definition diverges_after p s tr :=
    exists t, traced_run (lstep p) s tr t /\ traced_diverges (lstep p) t.
  (** Behaviour equality retains endings, finite prefixes and diverging prefixes. *)
  Definition same_behaviour p s t : Prop :=
    (forall k tr,
      (exists u, traced_run (lstep p) s tr u /\ ends_as p k u) <->
      (exists u, traced_run (lstep p) t tr u /\ ends_as p k u)) /\
    (forall tr, (exists u, traced_run (lstep p) s tr u) <->
      (exists u, traced_run (lstep p) t tr u)) /\
    (forall tr, diverges_after p s tr <-> diverges_after p t tr).
  (** Final states have no successor. *)
  Parameter final_halts : forall p s, final p s -> ~ running p s.
  (** Trapped states have no successor. *)
  Parameter trapped_halts : forall p s, trapped p s -> ~ running p s.
  (** Resource-stopped states have no successor. *)
  Parameter stopped_halts : forall p s, stopped p s -> ~ running p s.
  (** Final and trapped classifications are disjoint. *)
  Parameter final_not_trapped : forall p s, final p s -> ~ trapped p s.
  (** Final and stopped classifications are disjoint. *)
  Parameter final_not_stopped : forall p s, final p s -> ~ stopped p s.
  (** Trapped and stopped classifications are disjoint. *)
  Parameter trapped_not_stopped : forall p s, trapped p s -> ~ stopped p s.
End TRACES.
