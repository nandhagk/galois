(** * One inhabited state

    A single live state has a separate unreachable bottom.
    For example, havoc preserves the live state for every unit replacement.
    Builds on: DomainsState and DomainsValueTest. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeSimple.
From Galois.Domains Require Import DomainsState.
From Galois.Tests.Domains Require Import DomainsValueTest.
Import List.ListNotations.

Definition one_state : StateAbs.t bool bool unit unit unit :=
  {| StateAbs.lat := bool_lattice;
     StateAbs.top := true;
     StateAbs.assign_c := fun _ _ s => Cost.ret s;
     StateAbs.havoc_c := fun _ s => Cost.ret s;
     StateAbs.assume_c := fun _ _ s => Cost.ret s;
     StateAbs.project_c := fun _ s => Cost.ret s |}.

Definition one_sem : StateSem.t unit unit :=
  {| StateSem.update := fun _ _ _ _ => tt |}.

(** The live unit-state fixture inhabits every state-law obligation. *)
Theorem one_state_laws :
  state_laws one_state unit_sem reach_values one_sem bool_gamma bool_gamma.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_gamma_laws.
  - intros st H. discriminate H.
  - intros. reflexivity.
  - constructor.
    + intros [] [] st. reflexivity.
    + intros [] [] [] st H. exfalso. apply H. reflexivity.
  - intros x t s st c Hs He. exact Hs.
  - intros x s st c Hs. exact Hs.
  - intros g ts s st cs Hs He Hg. exact Hs.
  - intros x s st Hs. exact Hs.
Qed.

Example live_havoc : StateAbs.havoc one_state tt true = true.
Proof. vm_compute. reflexivity. Qed.

Example unreachable_assignment :
  StateAbs.assign one_state tt (DomainsTerm.Leaf tt) false = false.
Proof. vm_compute. reflexivity. Qed.

Example empty_guard_support : StateAbs.assume one_state tt [] true = true.
Proof. vm_compute. reflexivity. Qed.
