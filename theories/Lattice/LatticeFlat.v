(** * Flat lattices

    Flat values distinguish bottom, a known value and top.
    For example, joining distinct known values gives top.
    Builds on: LatticeCore, LatticeHeight and LatticeConcrete. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete.
Local Open Scope nat_scope.

(** A flat value adds a bottom and top to a carrier. *)
Inductive flat (A : Type) : Type :=
  | FBot
  | FVal (a : A)
  | FTop.

Arguments FBot {A}.
Arguments FVal {A}.
Arguments FTop {A}.

(** Flat comparison uses the supplied test for known values. *)
Definition flat_leb {A} (eqb : A -> A -> bool) (x y : flat A) : bool :=
  match x, y with
  | FBot, _ => true
  | _, FTop => true
  | FVal a, FVal b => eqb a b
  | _, _ => false
  end.

(** Flat join preserves equal known values and otherwise returns top. *)
Definition flat_join {A} (eqb : A -> A -> bool) (x y : flat A) : flat A :=
  match x, y with
  | FBot, _ => y
  | _, FBot => x
  | FVal a, FVal b => if eqb a b then FVal a else FTop
  | _, _ => FTop
  end.

(** Flat widening is join and narrowing keeps its left input. *)
Definition flat_lattice {A} (eqb : A -> A -> bool) : lattice (flat A) :=
  simple (flat_leb eqb) FBot (flat_join eqb).

(** Reflected equality is reflexive. *)
Lemma flat_eqb_refl {A} (eqb : A -> A -> bool) :
  eqb_spec eqb -> forall a, eqb a a = true.
Proof.
  intros H a; apply H; reflexivity.
Qed.

(** Flat operations satisfy weak laws when the equality test reflects equality. *)
Theorem flat_laws {A} (eqb : A -> A -> bool) :
  eqb_spec eqb -> lattice_laws (flat_lattice eqb).
Proof.
  intro Hspec; apply simple_laws.
  - intros [|a|]; cbn [flat_leb]; auto using flat_eqb_refl.
  - intros [|a|] [|b|] [|c|]; cbn [flat_leb]; intros Hab Hbc;
      try discriminate; try reflexivity.
    apply Hspec in Hab; subst b; exact Hbc.
  - intros [|a|]; reflexivity.
  - intros [|a|] [|b|]; cbn [flat_leb flat_join]; try reflexivity;
      try apply (flat_eqb_refl eqb Hspec).
    destruct (eqb a b) eqn:Hab; cbn [flat_leb];
      [apply (flat_eqb_refl eqb Hspec) | reflexivity].
  - intros [|a|] [|b|]; cbn [flat_leb flat_join]; try reflexivity;
      try apply (flat_eqb_refl eqb Hspec).
    destruct (eqb a b) eqn:Hab; cbn [flat_leb].
    + apply Hspec in Hab; subst b; apply (flat_eqb_refl eqb Hspec).
    + reflexivity.
Qed.

(** Flat joins are least when the equality test reflects equality. *)
Theorem flat_lub {A} (eqb : A -> A -> bool) :
  eqb_spec eqb -> lub_laws (flat_lattice eqb).
Proof.
  intro Hspec; constructor; intros x y z.
  change (flat_leb eqb x z = true -> flat_leb eqb y z = true ->
    flat_leb eqb (flat_join eqb x y) z = true).
  destruct x as [|a|], y as [|b|], z as [|c|]; cbn [flat_leb flat_join];
    intros Ha Hb; try discriminate; try reflexivity; try assumption.
  apply Hspec in Ha; apply Hspec in Hb; subst.
  rewrite (flat_eqb_refl eqb Hspec); apply (flat_eqb_refl eqb Hspec).
  all: destruct (eqb a b); reflexivity.
Qed.

(** Flat top bounds every flat value. *)
Definition flat_top {A} (eqb : A -> A -> bool) : top (flat_lattice eqb).
Proof.
  refine {| top_value := FTop |}; intros [|a|]; reflexivity.
Defined.

(** Flat meanings are empty at bottom and universal at top. *)
Definition flat_gamma {A C} (G : A -> C -> Prop) : concretisation (flat A) C :=
  {| gamma := fun x c =>
       match x with
       | FBot => False
       | FVal a => G a c
       | FTop => True
       end |}.

(** Flat meanings are monotone when the equality test reflects equality. *)
Theorem flat_gamma_laws {A C} (eqb : A -> A -> bool) (G : A -> C -> Prop) :
  eqb_spec eqb -> concretisation_laws (flat_lattice eqb) (flat_gamma G).
Proof.
  intro Hspec; constructor; intros [|a|] [|b|] c Hab Hc;
    cbn [flat_lattice simple of_pure leb flat_leb flat_gamma gamma] in *;
    try contradiction; try discriminate; try exact I.
  apply Hspec in Hab; subst b; exact Hc.
Qed.

(** Flat agreement is unrestricted at bottom and equality at top. *)
Definition flat_agree {A C} (R : A -> C -> C -> Prop) : agreement (flat A) C :=
  {| agree := fun a x y =>
       match a with
       | FBot => True
       | FVal v => R v x y
       | FTop => x = y
       end |}.

(** Reflexive component relations give reflexive and antitone flat agreement. *)
Theorem flat_agree_laws {A C} (eqb : A -> A -> bool) (R : A -> C -> C -> Prop) :
  eqb_spec eqb -> (forall a c, R a c c) ->
  agreement_laws (flat_lattice eqb) (flat_agree R).
Proof.
  intros Hspec HR; constructor.
  - intros [|a|] c; cbn [flat_agree agree]; auto.
  - intros [|a|] [|b|] x y Hab Hxy;
      cbn [flat_lattice simple of_pure leb flat_leb flat_agree agree] in *;
      try discriminate; try exact I; try exact Hxy.
    + apply Hspec in Hab; subst b; exact Hxy.
    + subst y; apply HR.
Qed.

(** Flat ranks are zero at bottom, one at known values and two at top. *)
Theorem flat_height {A} (eqb : A -> A -> bool) (Hspec : eqb_spec eqb) :
  height (flat_lattice eqb).
Proof.
  refine {| rank := fun x =>
              match x with
              | FBot => 0
              | FVal _ => 1
              | FTop => 2
              end;
            bound := 2 |}.
  - intros [|a|] _; cbn; lia.
  - intros [|a|] [|b|] _ _ Hle;
      cbn [flat_lattice simple of_pure leb flat_leb] in *; try discriminate; lia.
  - intros x y _ _ Hstrict.
    change (flat_leb eqb (flat_join eqb x y) x = false) in Hstrict.
    change ((match x with FBot => 0 | FVal _ => 1 | FTop => 2 end) <
      (match flat_join eqb x y with FBot => 0 | FVal _ => 1 | FTop => 2 end)).
    destruct x as [|a|], y as [|b|];
      cbn [flat_leb flat_join] in *;
      try discriminate; try lia.
    + rewrite (flat_eqb_refl eqb Hspec) in Hstrict; discriminate.
    + destruct (eqb a b) eqn:Hab; cbn [flat_leb] in *.
      * rewrite (flat_eqb_refl eqb Hspec) in Hstrict; discriminate.
      * lia.
Defined.

(** Flat bottom denotes no concrete values. *)
Theorem flat_bot_empty {A C} (eqb : A -> A -> bool) (G : A -> C -> Prop) :
  bottom_empty (flat_lattice eqb) (flat_gamma G).
Proof.
  constructor; intros c Hfalse; exact Hfalse.
Qed.

(** Flat top denotes every concrete value. *)
Theorem flat_top_full {A C} (eqb : A -> A -> bool) (G : A -> C -> Prop) :
  top_full (flat_top eqb) (flat_gamma G).
Proof.
  constructor; intro c; exact I.
Qed.

(** Flat bottom imposes no agreement requirement. *)
Theorem flat_agree_bot {A C} (eqb : A -> A -> bool) (R : A -> C -> C -> Prop) :
  agreement_bot (flat_lattice eqb) (flat_agree R).
Proof.
  constructor; intros x y; exact I.
Qed.

(** Pure flat operations charge one tick per dictionary operation. *)
Theorem flat_cost {A} (eqb : A -> A -> bool) :
  cost_bounded_on (flat_lattice eqb) (fun _ => True) 1%N.
Proof.
  intros a b _ _; repeat split; reflexivity.
Qed.

(** Every flat operation stays in the unrestricted carrier. *)
Theorem flat_closed {A} (eqb : A -> A -> bool) :
  closed_on (flat_lattice eqb) (fun _ => True).
Proof.
  constructor; intros; exact I.
Qed.

(** Flat widening credits complement the three-level height. *)
Theorem flat_wrank {A} (eqb : A -> A -> bool) (Hspec : eqb_spec eqb) :
  widening_rank (flat_lattice eqb).
Proof.
  exact (height_wrank _ (flat_laws eqb Hspec) (flat_lub eqb Hspec)
    (flat_closed eqb) (fun _ _ => eq_refl) (flat_height eqb Hspec)).
Defined.

Arguments flat_lattice {A} eqb : simpl never.
