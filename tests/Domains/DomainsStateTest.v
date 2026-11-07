(** * One inhabited state

    A single live state has a separate unreachable bottom.
    For example, havoc preserves the live state for every unit replacement.
    Builds on: DomainsState and DomainsValueTest. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeSimple.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState.
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
  state_laws one_state unit_sem one_sem bool_gamma bool_gamma.
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

(** Boolean variable names make the unchanged-other-variable obligation nonvacuous. *)
Definition two_sem : StateSem.t bool bool :=
  {| StateSem.update := fun x c st y => if Bool.eqb y x then c else st y |}.

Definition two_state : StateAbs.t bool bool bool unit unit :=
  {| StateAbs.lat := bool_lattice;
     StateAbs.top := true;
     StateAbs.assign_c := fun _ _ s => Cost.ret s;
     StateAbs.havoc_c := fun _ s => Cost.ret s;
     StateAbs.assume_c := fun _ _ s => Cost.ret s;
     StateAbs.project_c := fun _ s => Cost.ret s |}.

Definition two_value_sem : ValueSem.t bool unit unit :=
  {| ValueSem.eval := fun _ _ => Some false;
     ValueSem.holds := fun _ _ => True |}.

(** Updating either variable changes its value and leaves the distinct Boolean variable intact. *)
Theorem two_update_laws : StateSem.laws two_sem.
Proof.
  constructor.
  - intros [] c st; reflexivity.
  - intros [] [] c st H; try reflexivity; exfalso; apply H; reflexivity.
Qed.

(** Two-variable reachability inhabits the state contract with no value dictionary. *)
Theorem two_state_laws :
  state_laws two_state two_value_sem two_sem bool_gamma bool_gamma.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_gamma_laws.
  - intros st H. discriminate H.
  - intros. reflexivity.
  - exact two_update_laws.
  - intros x t s st c Hs He. exact Hs.
  - intros x s st c Hs. exact Hs.
  - intros g ts s st cs Hs He Hg. exact Hs.
  - intros x s st Hs. exact Hs.
Qed.

Example update_selected_variable :
  StateSem.update two_sem true false (fun x => x) true = false.
Proof. vm_compute. reflexivity. Qed.

Example update_keeps_other_variable :
  StateSem.update two_sem true false (fun x => x) false = false.
Proof. vm_compute. reflexivity. Qed.

Example update_other_direction :
  StateSem.update two_sem false true (fun x => x) true = true.
Proof. vm_compute. reflexivity. Qed.

Example two_variable_havoc_retains_both_replacements :
  (StateAbs.havoc two_state true true,
   StateSem.update two_sem true false (fun x => x) true,
   StateSem.update two_sem true true (fun x => x) true) = (true, false, true).
Proof. vm_compute. reflexivity. Qed.
