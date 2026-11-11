(** * Lawful infinite-carrier affine completion clients

    Strict affine maps over flat integers satisfy the complete tabulator law domain.
    For example, translation followed by scaling and translation maps 4 to 13 across a matched call.
    Builds on: LatticeFlat and the actual jump and value completion theorems. *)

From Stdlib Require Import List Bool ZArith Ring Lia PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeFlat LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkStack FrameworkTabulate FrameworkTabValues FrameworkTabWeight FrameworkTabPaths
  FrameworkTabCost FrameworkTabJumpProgress FrameworkTabJumpClosure FrameworkTabValueProgress
  FrameworkTabValueClosure FrameworkTabSound.
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabulateTest
  FrameworkTabSoundTest FrameworkTabJumpClosureTest.
Import List.ListNotations.
Local Open Scope Z_scope.

Module LawfulAffine.

Definition value := flat Z.
Definition function := flat (Z * Z).

Definition pair_eqb (f g : Z * Z) :=
  Z.eqb (fst f) (fst g) && Z.eqb (snd f) (snd g).

Local Lemma integer_eqb_spec : eqb_spec Z.eqb.
Proof.
  intros x y; apply Z.eqb_eq.
Qed.

Local Lemma pair_eqb_spec : eqb_spec pair_eqb.
Proof.
  intros [a b] [c d]; unfold pair_eqb; cbn [fst snd].
  rewrite andb_true_iff, !Z.eqb_eq; split.
  - intros [-> ->]; reflexivity.
  - intro Heq; injection Heq as -> ->; split; reflexivity.
Qed.

Definition values := flat_lattice Z.eqb.
Definition functions := flat_lattice pair_eqb.

Definition compose (f g : function) : function :=
  match f, g with
  | FBot, _ | _, FBot => FBot
  | FVal (a, b), FVal (c, d) => FVal (a * c, a * d + b)
  | _, _ => FTop
  end.

(** The flat extension preserves both bottom and top, including for zero slopes. *)
Definition apply (f : function) (x : value) : value :=
  match f, x with
  | FBot, _ | _, FBot => FBot
  | FVal (a, b), FVal z => FVal (a * z + b)
  | _, _ => FTop
  end.

Definition micro : Micro.t value function :=
  Micro.of_pure (FVal (1, 0)) compose apply functions.

Local Lemma values_laws : lattice_laws values.
Proof.
  apply flat_laws; exact integer_eqb_spec.
Qed.

Local Lemma functions_laws : lattice_laws functions.
Proof.
  apply flat_laws; exact pair_eqb_spec.
Qed.

Local Lemma flat_cases {X} (eq : X -> X -> bool) (HE : eqb_spec eq) x y :
  leb (flat_lattice eq) x y = true -> x = FBot \/ y = FTop \/ x = y.
Proof.
  destruct x as [|x|], y as [|y|]; intro Hle;
    try (left; reflexivity); try (right; left; reflexivity);
    try (right; right; reflexivity); try discriminate.
  right; right; f_equal; apply HE; exact Hle.
Qed.

Local Lemma apply_value_mono f x y :
  leb values x y = true -> leb values (apply f x) (apply f y) = true.
Proof.
  intro Hle; destruct (flat_cases Z.eqb integer_eqb_spec x y Hle) as [Hx|[Hy|Heq]].
  - subst x; destruct f as [|[a b]|]; cbn [apply]; apply (bot_least values_laws).
  - subst y; destruct f as [|[a b]|], x as [|x|]; try reflexivity.
  - subst y; apply leb_refl; exact values_laws.
Qed.

Local Lemma apply_function_mono f g x :
  leb functions f g = true -> leb values (apply f x) (apply g x) = true.
Proof.
  intro Hle; destruct (flat_cases pair_eqb pair_eqb_spec f g Hle) as [Hf|[Hg|Heq]].
  - subst f; cbn [apply]; apply (bot_least values_laws).
  - subst g; destruct x as [|x|], f as [|[a b]|]; try reflexivity.
  - subst g; apply leb_refl; exact values_laws.
Qed.

Local Lemma compose_left_mono f f' g :
  leb functions f f' = true -> leb functions (compose f g) (compose f' g) = true.
Proof.
  intro Hle; destruct (flat_cases pair_eqb pair_eqb_spec f f' Hle) as [Hf|[Hf'|Heq]].
  - subst f; cbn [compose]; apply (bot_least functions_laws).
  - subst f'; destruct g as [|[c d]|], f as [|[a b]|]; try reflexivity.
  - subst f'; apply leb_refl; exact functions_laws.
Qed.

Local Lemma compose_right_mono f g g' :
  leb functions g g' = true -> leb functions (compose f g) (compose f g') = true.
Proof.
  intro Hle; destruct (flat_cases pair_eqb pair_eqb_spec g g' Hle) as [Hg|[Hg'|Heq]].
  - subst g; destruct f as [|[a b]|]; cbn [compose]; apply (bot_least functions_laws).
  - subst g'; destruct f as [|[a b]|], g as [|[c d]|]; try reflexivity.
  - subst g'; apply leb_refl; exact functions_laws.
Qed.

Local Lemma compose_apply f g x : apply (compose f g) x = apply f (apply g x).
Proof.
  destruct f as [|[a b]|], g as [|[c d]|], x as [|z|];
    cbn [compose apply]; try reflexivity; f_equal; ring.
Qed.

Local Lemma apply_identity x : apply (FVal (1, 0)) x = x.
Proof.
  destruct x as [|z|]; cbn [apply]; try reflexivity; f_equal; ring.
Qed.

(** All affine functions and values satisfy the unchanged Micro laws, including top and bottom. *)
Theorem micro_laws : micro_laws values micro.
Proof.
  constructor.
  - exact functions_laws.
  - apply flat_lub; exact pair_eqb_spec.
  - intro x; change (equivalent values (apply (FVal (1, 0)) x) x).
    rewrite apply_identity; split; apply leb_refl; exact values_laws.
  - intros f g x; change (equivalent values (apply (compose f g) x) (apply f (apply g x))).
    rewrite compose_apply; split; apply leb_refl; exact values_laws.
  - exact apply_value_mono.
  - exact apply_function_mono.
  - intros f f' g g' Hf Hg.
    eapply leb_trans; [exact functions_laws|apply compose_left_mono; exact Hf|].
    apply compose_right_mono; exact Hg.
  - intros f g x; split; apply apply_function_mono;
      [apply join_upper_l|apply join_upper_r]; exact functions_laws.
Qed.

Local Lemma compose_identity_left f : compose (FVal (1, 0)) f = f.
Proof.
  destruct f as [|[a b]|]; cbn [compose]; try reflexivity; f_equal; f_equal; ring.
Qed.

Local Lemma compose_identity_right f : compose f (FVal (1, 0)) = f.
Proof.
  destruct f as [|[a b]|]; cbn [compose]; try reflexivity; f_equal; f_equal; ring.
Qed.

Local Lemma compose_associative f g h : compose (compose f g) h = compose f (compose g h).
Proof.
  destruct f as [|[a b]|], g as [|[c d]|], h as [|[e f]|];
    cbn [compose]; try reflexivity; f_equal; f_equal; ring.
Qed.

(** The same affine dictionary satisfies symbolic F-order units and associativity. *)
Theorem weight_laws : TabWeight.laws micro.
Proof.
  constructor.
  - intro f; change (equivalent functions (compose (FVal (1, 0)) f) f).
    rewrite compose_identity_left; split; apply leb_refl; exact functions_laws.
  - intro f; change (equivalent functions (compose f (FVal (1, 0))) f).
    rewrite compose_identity_right; split; apply leb_refl; exact functions_laws.
  - intros f g h; change (equivalent functions (compose (compose f g) h) (compose f (compose g h))).
    rewrite compose_associative; split; apply leb_refl; exact functions_laws.
Qed.

Definition value_height := flat_height Z.eqb integer_eqb_spec.
Definition function_height := flat_height pair_eqb pair_eqb_spec.

(** The two affine carriers retain an injective embedding of every integer. *)
Theorem infinite_carriers x y :
  (@FVal Z x = FVal y -> x = y) /\
  (@FVal (Z * Z) (1, x) = FVal (1, y) -> x = y).
Proof.
  split; congruence.
Qed.

Definition problem : Ide.t nat nat nat unit value function :=
  Ide.Make affine_ifds values micro (fun e _ _ => Cost.ret
    (match e with
    | 0%nat => FVal (1, 1)
    | 1%nat => FVal (2, 0)
    | _ => FVal (1, 3)
    end)).

(** A lawful infinite-carrier affine client constructs and certifies both actual phases. *)
Theorem complete z :
  exists jumps result,
    TabJumpProgress.complete problem 0%nat function_height = Tab.Certified jumps /\
    TabValueProgress.complete problem (proj1_sig jumps) (0%nat, None) (FVal z) value_height =
      TabValues.Certified result.
Proof.
  destruct (arbitrary_jump_completion problem 0%nat function_height
    nat_encoding_laws nat_encoding_laws unit_encoding_laws functions_laws) as [jumps Hjump].
  destruct (TabValueClosure.complete_certified problem (proj1_sig jumps)
    (0%nat, None) (FVal z) value_height
    nat_encoding_laws nat_encoding_laws unit_encoding_laws values_laws) as [result Hvalue].
  exists jumps, result; split; assumption.
Qed.

Local Lemma flow_closed : Ifds.flow_closed affine_ifds.
Proof.
  intros e x y He Hx Hflow; change (In y [x]) in Hflow.
  destruct Hflow as [Heq|Hbad]; [subst y; exact Hx|inversion Hbad].
Qed.

(** Total affine completion bounds every original execution, including pending-call prefixes. *)
Theorem completed_paths_sound z :
  exists jumps result,
    TabJumpProgress.complete problem 0%nat function_height = Tab.Certified jumps /\
    TabValueProgress.complete problem (proj1_sig jumps) (0%nat, None) (FVal z) value_height =
      TabValues.Certified result /\
    forall n d stack, Stack.path affine_ifds (0%nat, None, []) (n, d, stack) ->
      exists as_, TabPaths.trace problem (0%nat, None, []) as_ (n, d, stack) /\
        Forall (fun a => In a (Jump.arcs problem)) as_ /\
        leb values (apply (TabWeight.weight problem as_) (FVal z))
          (TabValues.lookup problem (proj1_sig result) (n, d)) = true.
Proof.
  destruct (complete z) as [jumps [result [Hjump Hvalue]]].
  exists jumps, result; split; [exact Hjump|]; split; [exact Hvalue|].
  rewrite TabJumpProgress.complete_agrees in Hjump.
  rewrite TabValueProgress.complete_agrees in Hvalue.
  intros n d stack Hpath.
  apply (TabSound.tabulate_values_sound problem (0%nat, None) (FVal z)
    (TabCost.rank_fuel (Tab.prepare problem 0%nat) (bound function_height))
    (TabCost.inventory_fuel
      (TabValues.inventory (TabValues.prepare problem (proj1_sig jumps) (0%nat, None)))
      (bound value_height)) jumps result n d stack).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact values_laws.
  - exact micro_laws.
  - exact weight_laws.
  - exact taint_graph_wf.
  - exact flow_closed.
  - exact Logic.I.
  - exact Hjump.
  - exact Hvalue.
  - exact Hpath.
Qed.

(** Lawful affine value leastness uses the actual public value analysis and its own lub duty. *)
Theorem completed_values_least J z sigma :
  post_solution values
    (Analysis.system (value_analysis problem (Jump.lookup_c problem J) (0%nat, None) (FVal z)))
    sigma ->
  exists c,
    TabValueProgress.complete problem J (0%nat, None) (FVal z) value_height =
      TabValues.Certified c /\
    forall v, leb values (TabValues.lookup problem (proj1_sig c) v) (sigma v) = true.
Proof.
  intro Hpost; apply TabValueClosure.complete_least.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact unit_encoding_laws.
  - exact values_laws.
  - apply flat_lub; exact integer_eqb_spec.
  - exact micro_laws.
  - exact Hpost.
Qed.

Example noncommuting_completed_value :
  match TabJumpProgress.complete problem 0%nat function_height with
  | Tab.Certified jumps =>
    match TabValueProgress.complete problem (proj1_sig jumps)
      (0%nat, None) (FVal 4) value_height with
    | TabValues.Certified result => Some (TabValues.lookup problem (proj1_sig result) (3%nat, None))
    | _ => None
    end
  | _ => None
  end = Some (FVal 13).
Proof.
  vm_compute; reflexivity.
Qed.

Example reversing_noncommuting_weights_changes_the_result :
  (apply (compose (FVal (1, 3)) (compose (FVal (2, 0)) (FVal (1, 1)))) (FVal 4),
   apply (compose (FVal (1, 1)) (compose (FVal (2, 0)) (FVal (1, 3)))) (FVal 4)) =
    (FVal 13, FVal 15).
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_boundary_observations :
  (apply (FVal (0, 7)) FBot, apply (FVal (0, 7)) FTop,
   compose (FVal (0, 7)) FTop, apply (FVal (1, 0)) (FVal 0)) =
    (FBot, FTop, FTop, FVal 0).
Proof.
  vm_compute; reflexivity.
Qed.

Definition diamond : Ide.t nat nat nat unit value function :=
  Ide.Make diamond_ifds values micro (fun e _ _ => Cost.ret
    (match e with
    | 1%nat => FVal (0, 0)
    | 4%nat => FVal (0, 7)
    | _ => FVal (1, 0)
    end)).

(** The lawful nondistributive diamond has a least ground solution despite path-join imprecision. *)
Theorem completed_diamond_least J :
  jump_post diamond 0%nat J ->
  exists c, TabJumpProgress.complete diamond 0%nat function_height = Tab.Certified c /\
    forall key, leb functions (Jump.lookup diamond (proj1_sig c) key) (J key) = true.
Proof.
  intro Hpost; apply TabJumpClosure.complete_least.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - apply Tab.arc_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - apply Tab.incoming_enc_laws.
    + apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
      apply FrameworkKey.option_laws; exact unit_encoding_laws.
    + apply Tab.arc_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact micro_laws.
  - exact Hpost.
Qed.

Example lawful_nondistributive_diamond :
  match TabJumpProgress.complete diamond 0%nat function_height with
  | Tab.Certified jumps =>
    (Jump.lookup diamond (proj1_sig jumps) ((0%nat, None), (4%nat, None)),
     join functions
       (compose (FVal (0, 7)) (compose (FVal (1, 0)) (FVal (1, 0))))
       (compose (FVal (0, 7)) (compose (FVal (1, 0)) (FVal (0, 0)))))
  | _ => (FBot, FBot)
  end = (FTop, FVal (0, 7)).
Proof.
  vm_compute; reflexivity.
Qed.

End LawfulAffine.
