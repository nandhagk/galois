(** * Open value fixtures

    Reachability supplies a small inhabited open dictionary.
    For example, every successful unit operation yields a reachable value.
    Builds on: DomainsValue and LatticeSimple. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeSimple.
From Galois.Domains Require Import DomainsValue.
Import List.ListNotations.

Definition reach_values : ValueAbs.t bool unit unit :=
  {| ValueAbs.lat := bool_lattice;
     ValueAbs.top := true;
     ValueAbs.op_c := fun _ _ => Cost.ret true;
     ValueAbs.back_c := fun _ _ xs => Cost.ret xs;
     ValueAbs.guard_c := fun _ xs => Cost.ret xs |}.

Definition unit_sem : ValueSem.t unit unit unit :=
  {| ValueSem.eval := fun _ _ => Some tt;
     ValueSem.holds := fun _ _ => True |}.

(** Unit reachability inhabits every open value-law obligation. *)
Theorem reach_value_laws : value_laws reach_values unit_sem bool_gamma.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_gamma_laws.
  - intros c H. discriminate H.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros k a xs cs c Hxs He Ha. exact Hxs.
  - intros g xs cs Hxs Hg. exact Hxs.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

(** The reachability fixture's identity backward and guard transfers are reductive. *)
Theorem reach_value_refines : value_refines reach_values.
Proof.
  constructor; intros; induction fs as [|x fs IH]; constructor.
  - apply (leb_refl bool_laws).
  - exact IH.
  - apply (leb_refl bool_laws).
  - exact IH.
Qed.

Example reachable_operator : ValueAbs.op reach_values tt [true] = true.
Proof. vm_compute. reflexivity. Qed.

Example bottom_is_empty : gamma (@bool_gamma unit) false tt -> False.
Proof. vm_compute. discriminate. Qed.

Example empty_backward : ValueAbs.back reach_values tt false [] = [].
Proof. vm_compute. reflexivity. Qed.
