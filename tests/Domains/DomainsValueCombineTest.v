(** * Value composition fixtures

    Products reduce facts and disjunctions enumerate operand alternatives.
    For example, two binary operands with two alternatives produce four choices.
    Builds on: DomainsValueCombine and DomainsValueTest. *)

From Stdlib Require Import List Bool Arith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeSimple LatticeKitFamily.
From Galois.Domains Require Import DomainsValue DomainsValueCombine.
From Galois.Tests.Domains Require Import DomainsValueTest.
Import List.ListNotations.

Definition reach_product := ValueAbs.product reach_values reach_values Cost.ret.

Example product_transfer :
  ValueAbs.op reach_product tt [(false, true)] = (true, true).
Proof. vm_compute. reflexivity. Qed.

Example product_empty_guard : ValueAbs.guard reach_product tt [] = [].
Proof. vm_compute. reflexivity. Qed.

Example product_reducer :
  ValueAbs.op (ValueAbs.product reach_values reach_values
    (fun _ => Cost.ret (false, false))) tt [] = (false, false).
Proof. vm_compute. reflexivity. Qed.

Example identity_product_laws :
  value_laws reach_product unit_sem (product_gamma bool_gamma bool_gamma).
Proof.
  apply product_laws; try exact reach_value_laws. intros p c H. exact H.
Qed.

Example renamed_transfer :
  ValueAbs.op (ValueAbs.rename (fun _ : bool => tt) (fun _ : nat => tt) reach_values)
    false [] = true.
Proof. vm_compute. reflexivity. Qed.

Example renamed_laws :
  value_laws
    (ValueAbs.rename (fun _ : bool => tt) (fun _ : nat => tt) reach_values)
    {| ValueSem.eval := fun _ _ => Some tt; ValueSem.holds := fun _ _ => True |}
    bool_gamma.
Proof.
  apply rename_laws with (M := unit_sem).
  - exact reach_value_laws.
  - intros. reflexivity.
  - intros. exact I.
Qed.

Example choices_keep_order :
  Cost.value (ValueAbs.choices_c [[true; false]; [false; true]]) =
    [[true; false]; [true; true]; [false; false]; [false; true]].
Proof. vm_compute. reflexivity. Qed.

Example empty_choices :
  Cost.value (ValueAbs.choices_c [[true]; []]) = [].
Proof. vm_compute. reflexivity. Qed.

Example nullary_choices : Cost.value (@ValueAbs.choices_c bool []) = [[]].
Proof. vm_compute. reflexivity. Qed.

Definition list_fixture_lattice : lattice (list bool) :=
  {| leb_c := fun xs ys =>
       Cost.bind (existsb_c (fun x => Cost.ret x) xs) (fun x =>
       Cost.map (implb x) (existsb_c (fun y => Cost.ret y) ys));
     bot := [];
     join_c := @app_c bool;
     widen_c := @app_c bool;
     narrow_c := fun xs _ => Cost.ret xs |}.

Definition cover (xs : list bool) := existsb (fun x => x) xs.

Local Lemma cover_meaning xs c :
  gamma (disjunctive_gamma (@bool_gamma unit)) xs c <-> cover xs = true.
Proof.
  unfold cover, disjunctive_gamma. cbn. rewrite existsb_exists.
  split; intros [x [Hin Hx]]; exists x; split; assumption.
Qed.

Local Lemma list_family :
  family list_fixture_lattice bool_lattice (fun _ : unit => cover).
Proof.
  constructor.
  - intros xs ys.
    change (Cost.value (leb_c list_fixture_lattice xs ys) = true <->
      forall i : unit, leb bool_lattice (cover xs) (cover ys) = true).
    cbn [list_fixture_lattice leb_c]. autorewrite with galois_cost.
    change (implb (cover xs) (cover ys) = true <->
      forall i : unit, implb (cover xs) (cover ys) = true).
    split; [intros H []; exact H|intro H; exact (H tt)].
  - intros []. reflexivity.
  - intros [] xs ys.
    change (cover (Cost.value (app_c xs ys)) = orb (cover xs) (cover ys)).
    rewrite value_app_c. apply existsb_app.
  - intros [] xs ys.
    change (cover (Cost.value (app_c xs ys)) = orb (cover xs) (cover ys)).
    rewrite value_app_c. apply existsb_app.
  - intros [] xs ys. reflexivity.
Qed.

(** The disjunction fixture has inhabited weak laws and existential concrete meaning. *)
Theorem list_fixture_laws : lattice_laws list_fixture_lattice.
Proof.
  exact (family_laws list_family bool_laws).
Qed.

Local Lemma list_fixture_meaning :
  concretisation_laws list_fixture_lattice (disjunctive_gamma (@bool_gamma unit)).
Proof.
  constructor. intros xs ys c Hle Hx.
  apply cover_meaning in Hx. apply cover_meaning.
  pose proof (proj1 (family_leb list_family xs ys) Hle tt) as Hcovers.
  change (implb (cover xs) (cover ys) = true) in Hcovers.
  rewrite Hx in Hcovers. exact Hcovers.
Qed.

Definition compact_fixture k xs :=
  Cost.bind (length_c xs) (fun n =>
    if Nat.leb n k then Cost.ret xs else
    Cost.map (fun a => [a]) (ValueAbs.join_all_c bool_lattice xs)).

Local Lemma compact_fixture_sound k xs c :
  gamma (disjunctive_gamma (@bool_gamma unit)) xs c ->
  gamma (disjunctive_gamma (@bool_gamma unit)) (Cost.value (compact_fixture k xs)) c.
Proof.
  intro H. unfold compact_fixture. rewrite Cost.value_bind, value_length_c.
  destruct (Nat.leb (length xs) k); [exact H|].
  rewrite Cost.value_map. exists (Cost.value (ValueAbs.join_all_c bool_lattice xs)).
  split; [now left|].
  apply cover_meaning in H.
  unfold ValueAbs.join_all_c. rewrite value_fold_right_c.
  change (fold_right orb false xs = true).
  change (existsb (fun x => x) xs = true) in H.
  induction xs as [|x xs IH]; cbn in *; [discriminate|].
  destruct x; cbn in *; auto.
Qed.

Example inhabited_disjunction_laws :
  value_laws (ValueAbs.disjunctive 1 list_fixture_lattice compact_fixture reach_values)
    unit_sem (disjunctive_gamma bool_gamma).
Proof.
  apply disjunctive_laws.
  - exact reach_value_laws.
  - exact list_fixture_laws.
  - exact list_fixture_meaning.
  - reflexivity.
  - apply compact_fixture_sound.
Qed.

Example disjunctive_forward :
  ValueAbs.op (ValueAbs.disjunctive 1 list_fixture_lattice compact_fixture reach_values)
    tt [[true; false]; [false; true]] = [true].
Proof. vm_compute. reflexivity. Qed.

Example zero_cap_retains_legacy_singleton :
  Cost.value (compact_fixture 0 [true; false]) = [true].
Proof. vm_compute. reflexivity. Qed.

Example disjunction_backward_support :
  ValueAbs.back (ValueAbs.disjunctive 1 list_fixture_lattice compact_fixture reach_values)
    tt [] [[true; false]; []] = [[true]; [false]].
Proof. vm_compute. reflexivity. Qed.
