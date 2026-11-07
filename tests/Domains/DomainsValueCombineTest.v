(** * Value composition fixtures

    Products reduce facts and disjunctions enumerate operand alternatives.
    For example, two binary operands with two alternatives produce four choices.
    Builds on: DomainsValueCombine and DomainsValueTest. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeSimple LatticeKitFamily.
From Galois.Domains Require Import DomainsValue DomainsValueCombine.
From Galois.Tests.Domains Require Import DomainsValueTest.
Import List.ListNotations.

Local Open Scope nat_scope.

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
  ValueAbs.op (ValueAbs.rename (fun _ : bool => Cost.ret tt)
    (fun _ : nat => Cost.ret tt) reach_values)
    false [] = true.
Proof. vm_compute. reflexivity. Qed.

Example renamed_laws :
  value_laws
    (ValueAbs.rename (fun _ : bool => Cost.ret tt) (fun _ : nat => Cost.ret tt) reach_values)
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
  unfold ValueAbs.join_all_c. rewrite Cost.value_bind.
  destruct xs as [|x xs]; [discriminate H|].
  rewrite value_fold_left_c. change (fold_left orb xs x = true).
  change (orb x (existsb (fun x => x) xs) = true) in H.
  revert x H. induction xs as [|y xs IH]; intros x H; cbn in *.
  - now rewrite orb_false_r in H.
  - apply IH. destruct x, y; cbn in *; auto.
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

(** This chain permits a join that always loses every non-top distinction. *)
Inductive weak_fact : Type :=
  | WBot
  | WPoint
  | WTop.

Definition weak_le (a b : weak_fact) :=
  match a, b with
  | WBot, _ => true
  | _, WTop => true
  | WPoint, WPoint => true
  | _, _ => false
  end.

Definition weak_lattice := simple weak_le WBot (fun _ _ => WTop).

(** Always-top joins satisfy all weak laws on the three-element chain. *)
Theorem weak_lattice_laws : lattice_laws weak_lattice.
Proof.
  apply simple_laws.
  - intros []; reflexivity.
  - intros [] [] []; cbn [weak_le]; congruence.
  - intros []; reflexivity.
  - intros [] []; reflexivity.
  - intros [] []; reflexivity.
Qed.

Example weak_singleton_keeps_point :
  Cost.value (ValueAbs.join_all_c weak_lattice [WPoint]) = WPoint.
Proof. vm_compute. reflexivity. Qed.

Example weak_empty_uses_bottom :
  Cost.value (ValueAbs.join_all_c weak_lattice []) = WBot.
Proof. vm_compute. reflexivity. Qed.

Definition ordered_join_lattice :=
  simple Nat.leb 0 (fun a b => 2 * a + b + 1).

(** The order-sensitive arithmetic join satisfies weak upper bounds without leastness. *)
Theorem ordered_join_laws : lattice_laws ordered_join_lattice.
Proof.
  apply simple_laws.
  - apply Nat.leb_refl.
  - intros a b c Hab Hbc. apply Nat.leb_le in Hab, Hbc. apply Nat.leb_le. lia.
  - intro a. apply Nat.leb_le. lia.
  - intros a b. apply Nat.leb_le. lia.
  - intros a b. apply Nat.leb_le. lia.
Qed.

Example ordered_join_is_left_fold :
  Cost.value (ValueAbs.join_all_c ordered_join_lattice [1; 2; 3]) = 14.
Proof. vm_compute. reflexivity. Qed.

Example ordered_join_retains_input_order :
  Cost.value (ValueAbs.join_all_c ordered_join_lattice [3; 2; 1]) = 20.
Proof. vm_compute. reflexivity. Qed.

Definition expensive_rename :=
  ValueAbs.rename
    (fun _ : bool => Cost.bind (Cost.tick 5%N) (fun _ => Cost.ret tt))
    (fun _ : nat => Cost.bind (Cost.tick 7%N) (fun _ => Cost.ret tt)) reach_values.

Example rename_retains_operator_conversion_ticks :
  Cost.ticks (ValueAbs.op_c expensive_rename false []) = 7%N.
Proof. vm_compute. reflexivity. Qed.

Example rename_retains_backward_conversion_ticks :
  Cost.ticks (ValueAbs.back_c expensive_rename false true [true]) = 7%N.
Proof. vm_compute. reflexivity. Qed.

Example rename_retains_guard_conversion_ticks :
  Cost.ticks (ValueAbs.guard_c expensive_rename 0 [true]) = 9%N.
Proof. vm_compute. reflexivity. Qed.

Example expensive_rename_keeps_values : ValueAbs.op expensive_rename false [] = true.
Proof. vm_compute. reflexivity. Qed.
