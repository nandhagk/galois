(** * Core dictionary observations

    Computed fixtures check pure wrapping, operator replacement and domain assembly.
    For example, replacing boolean widening keeps comparison and join unchanged.
    Builds on: LatticeCore, LatticeDomain and LatticeSimple. *)

From Stdlib Require Import Bool NArith List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeDomain LatticeSimple.
Import Cost.Notations List.ListNotations.

Definition pure_bool := of_pure implb false orb orb (fun a _ => a).

Example of_pure_values :
  (leb pure_bool false true, leb pure_bool true false, join pure_bool false true,
   widen pure_bool false true, narrow pure_bool false true) = (true, false, true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example of_pure_ticks :
  [Cost.ticks (leb_c pure_bool false false); Cost.ticks (join_c pure_bool false false);
   Cost.ticks (widen_c pure_bool false false); Cost.ticks (narrow_c pure_bool false false)] =
  [1%N; 1%N; 1%N; 1%N].
Proof.
  vm_compute; reflexivity.
Qed.

Definition threshold_widen (a b : bool) := if implb b a then a else true.
Definition threshold_bool := with_widen bool_lattice threshold_widen.

Example threshold_keeps_order_join :
  forall a b, (leb threshold_bool a b, join threshold_bool a b) =
    (leb bool_lattice a b, join bool_lattice a b).
Proof.
  vm_compute; reflexivity.
Qed.

Example threshold_boundaries :
  (widen threshold_bool false false, widen threshold_bool false true,
   widen threshold_bool true false, widen threshold_bool true true,
   Cost.ticks (widen_c threshold_bool false true)) = (false, true, true, true, 1%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example threshold_laws : lattice_laws threshold_bool.
Proof.
  apply with_widen_laws; [exact bool_laws | |]; intros [] []; reflexivity.
Qed.

Definition costed_bool := with_widen_c bool_lattice
  (fun _ _ => Cost.tick 7 ;; Cost.ret true).

Example costed_replacement_laws : lattice_laws costed_bool.
Proof.
  apply with_widen_c_laws; [exact bool_laws | |]; intros [] []; reflexivity.
Qed.

Example costed_replacement_ticks :
  (Cost.ticks (widen_c costed_bool false false), Cost.ticks (join_c costed_bool false false),
   widen costed_bool false false, join costed_bool false false) = (7%N, 1%N, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition bool_domain : domain bool nat :=
  domain_of_simple bool_lattice bool_top bool_gamma.

Example bool_domain_laws : domain_laws bool_domain.
Proof.
  apply domain_of_simple_laws.
  - exact bool_laws.
  - exact bool_lub.
  - exact bool_gamma_laws.
  - exact bool_bot_empty.
  - exact bool_top_full.
Qed.

Example bool_domain_computes :
  (join (lat bool_domain) false (top_v bool_domain),
   leb (lat bool_domain) (top_v bool_domain) false) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition weak_bool := simple implb false (fun _ _ => true).

Example weak_join_laws : lattice_laws weak_bool.
Proof.
  apply simple_laws; intros; repeat match goal with
  | b : bool |- _ => destruct b
  end; cbn in *; congruence.
Qed.

Example weak_join_is_not_least : ~ lub_laws weak_bool.
Proof.
  intro Hlub; pose proof (join_least Hlub false false false eq_refl eq_refl) as Hbad.
  vm_compute in Hbad; discriminate.
Qed.
