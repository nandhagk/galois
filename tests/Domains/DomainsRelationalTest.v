(** * Relational environment fixtures

    Identity closure, repeated forgetting and finite renaming inhabit the relational contract.
    For example, shifting natural keys leaves coordinate zero at top.
    Builds on: DomainsRelational, DomainsEnv and DomainsEnvTest. *)

From Stdlib Require Import List Bool ZArith NArith Arith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeEnv.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState DomainsPoint
  DomainsRelational DomainsEnv.
From Galois.Tests.Domains Require Import DomainsEnvTest.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

(** The point environment supplies every relational law on an inhabited two-variable state. *)
Theorem relational_laws_fixture :
  relational_laws EnvFixture.RD EnvFixture.sem (StateEnv.semantics bool_encoding)
    EnvFixture.gam EnvFixture.gs.
Proof.
  apply env_relational_laws; [exact bool_encoding_laws|exact EnvFixture.value_laws_fixture|
    exact EnvFixture.greatest|exact EnvFixture.meet_sound].
Qed.

(** Forgetting both coordinates retains every sequential choice of replacement values. *)
Example forget_arbitrary_replacements :
  forall choose s st, gamma EnvFixture.gs s st ->
  gamma EnvFixture.gs (Relational.forget_all EnvFixture.RD [false; true] s)
    (fold_left (fun st x => StateSem.update (StateEnv.semantics bool_encoding)
      x (choose x) st) [false; true] st).
Proof.
  intros choose s st Henv.
  exact (forget_all_sound _ _ _ _ _ relational_laws_fixture [false; true] choose s st Henv).
Qed.

Example closure_identity :
  Relational.closure EnvFixture.RD (EnvFixture.stored [(false, PVal 2)]) =
    EnvFixture.stored [(false, PVal 2)].
Proof. vm_compute. reflexivity. Qed.

Example forget_selected_leaves_other_coordinate :
  let s := Relational.forget_all EnvFixture.RD [false; false]
    (EnvFixture.stored [(false, PVal 2); (true, PVal 3)]) in
  (EnvFixture.get false s, EnvFixture.get true s) = (PTop, PVal 3).
Proof. vm_compute. reflexivity. Qed.

Example forget_empty_list :
  Relational.forget_all EnvFixture.RD [] EnvFixture.empty = EnvFixture.empty.
Proof. vm_compute. reflexivity. Qed.

Definition swap (x : bool) := Cost.ret (negb x).

(** Swapping Boolean names is injective on the observed key conversion. *)
Example swap_injective : Relational.injective swap.
Proof.
  intros [] [] Hsame; discriminate || reflexivity.
Qed.

Example rename_swaps_coordinates :
  let s := Relational.rename EnvFixture.RD swap
    (EnvFixture.stored [(false, PVal 2); (true, PVal 3)]) in
  (EnvFixture.get false s, EnvFixture.get true s) = (PVal 3, PVal 2).
Proof. vm_compute. reflexivity. Qed.

Example project_real_term :
  Relational.project_term EnvFixture.RD (Node 7 [Leaf true])
    (EnvFixture.stored [(true, PVal 3)]) = PVal 7.
Proof. vm_compute. reflexivity. Qed.

Example project_variable_term :
  Relational.project_term EnvFixture.RD (Leaf true)
    (EnvFixture.stored [(true, PVal 3)]) = PVal 3.
Proof. vm_compute. reflexivity. Qed.

Example unreachable_relational_operations :
  (Relational.closure EnvFixture.RD None,
   Relational.forget_all EnvFixture.RD [false] None,
   Relational.rename EnvFixture.RD swap None,
   Relational.project_term EnvFixture.RD (Leaf false) None) = (None, None, None, PBot).
Proof. vm_compute. reflexivity. Qed.

Definition nat_state := StateEnv.state nat_encoding EnvFixture.values EnvFixture.meet.
Definition nat_relational := StateEnv.relational nat_encoding EnvFixture.values EnvFixture.meet.
Definition shift (x : nat) := Cost.ret (S x).
Definition natural_input : StateEnv.t nat_encoding point :=
  Some (env_of_list nat_encoding [(0%nat, PVal 2); (1%nat, PVal 3)]).
Definition natural_get x s := StateAbs.project nat_state x s.

(** Successor is injective and has no inverse at the fresh coordinate zero. *)
Example shift_injective : Relational.injective shift.
Proof.
  intros x y Hsame. now injection Hsame.
Qed.

Example fresh_coordinates_mean_top :
  let s := Relational.rename nat_relational shift natural_input in
  (natural_get 0 s, natural_get 1 s, natural_get 2 s, natural_get 9 s) =
    (PTop, PVal 2, PVal 3, PTop).
Proof. vm_compute. reflexivity. Qed.

Example fresh_coordinate_accepts_any_value :
  forall z, gamma (env_concretisation nat_encoding EnvFixture.values EnvFixture.gam)
    (Relational.rename nat_relational shift natural_input)
    (fun x => match x with 0%nat => z | 1%nat => 2%Z | _ => 3%Z end).
Proof.
  intro z.
  apply (proj2 (StateEnv.rename_meaning nat_encoding nat_encoding_laws
    EnvFixture.values EnvFixture.sem EnvFixture.gam EnvFixture.value_laws_fixture
    shift shift_injective natural_input _)).
  intro x.
  change (gamma EnvFixture.gam
    (Map.find_or nat_encoding PTop x (env_raw (env_of_list nat_encoding
      [(0%nat, PVal 2); (1%nat, PVal 3)])))
    (match S x with 0%nat => z | 1%nat => 2%Z | _ => 3%Z end)).
  rewrite Map.find_or_equation, env_of_list_raw, Map.of_list_get.
  cbn [fold_left fst snd].
  destruct (BaseEq.eqb_spec nat_encoding nat_encoding_laws x 1%nat) as [Heq|Hneq].
  - subst x. vm_compute. reflexivity.
  - destruct (BaseEq.eqb_spec nat_encoding nat_encoding_laws x 0%nat) as [Heq|Hzero].
    + subst x. vm_compute. reflexivity.
    + exact I.
Qed.

(** The full relational contract is inhabited over an infinite key carrier. *)
Theorem natural_relational_laws :
  relational_laws nat_relational EnvFixture.sem (StateEnv.semantics nat_encoding)
    EnvFixture.gam (env_concretisation nat_encoding EnvFixture.values EnvFixture.gam).
Proof.
  apply env_relational_laws; [exact nat_encoding_laws|exact EnvFixture.value_laws_fixture|
    exact EnvFixture.greatest|exact EnvFixture.meet_sound].
Qed.

Example charged_renaming_retains_client_cost :
  Cost.ticks (Relational.rename_c nat_relational (fun x => Cost.tick 13 ;; shift x)
    natural_input) =
  (Cost.ticks (Relational.rename_c nat_relational shift natural_input) + 26)%N.
Proof. vm_compute. reflexivity. Qed.

Example empty_renaming_calls_no_key_converter :
  Cost.ticks (Relational.rename_c nat_relational (fun x => Cost.tick 13 ;; shift x)
    (Some (env_empty nat_encoding))) = 1%N.
Proof. vm_compute. reflexivity. Qed.

Example rename_push_agreement :
  Relational.push_agrees shift (fun x => if Nat.eqb x 0 then 2%Z else 3%Z)
    (fun x => match x with 0%nat => 99%Z | 1%nat => 2%Z | _ => 3%Z end).
Proof.
  intros [|x]; reflexivity.
Qed.

Example colliding_renaming_is_not_lawful :
  ~ Relational.injective (fun _ : bool => Cost.ret false).
Proof.
  intro Hf. specialize (Hf false true eq_refl). discriminate Hf.
Qed.
