(** * Environment contract boundaries

    Environment comparisons require the map invariant at their semantic boundary.
    For example, duplicate raw bindings can make a map reject comparison with itself.
    Builds on: BaseMap, BaseEncoding, LatticeConcrete and LatticeKitFamily. *)

From Stdlib Require Import Bool List PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeKitFamily
  LatticeSimple LatticeAdjoin LatticeEnv.
Import List.ListNotations.

(** Missing boolean bindings read as the supplied default. *)
Definition fixture_default (d : bool) (o : option bool) :=
  match o with
  | Some b => b
  | None => d
  end.

(** This local mathematical model retains the reference list's first-code lookup rule. *)
Local Fixpoint reference_list_lookup (p : positive)
    (xs : list (positive * (positive * bool))) : option bool :=
  match xs with
  | [] => None
  | (q, (_, v)) :: rest =>
    if Pos.eqb p q then Some v else reference_list_lookup p rest
  end.

(** This local model compares stored left values with first-code right lookups. *)
Local Definition reference_list_forall2 r
    (xs ys : list (positive * (positive * bool))) :=
  forallb (fun e => r (snd (snd e)) (reference_list_lookup (fst e) ys)) xs.

(** This deliberately malformed local list repeats a code with conflicting values. *)
Local Definition reference_duplicate_raw_map : list (positive * (positive * bool)) :=
  [(1%positive, (1%positive, false)); (1%positive, (1%positive, true))].

Example duplicate_raw_lookup :
  reference_list_lookup 1%positive reference_duplicate_raw_map = Some false.
Proof.
  vm_compute. reflexivity.
Qed.

Example raw_bottom_default_comparison_not_reflexive :
  reference_list_forall2 (fun a b => implb a (fixture_default false b))
    reference_duplicate_raw_map reference_duplicate_raw_map = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Reversing the conflicting values exposes the corresponding top-default failure. *)
Local Definition reference_duplicate_top_raw_map : list (positive * (positive * bool)) :=
  [(1%positive, (1%positive, true)); (1%positive, (1%positive, false))].

Example raw_top_default_comparison_not_reflexive :
  reference_list_forall2 (fun b a => implb (fixture_default true a) b)
    reference_duplicate_top_raw_map reference_duplicate_top_raw_map = false.
Proof.
  vm_compute. reflexivity.
Qed.

(** Public list construction resolves duplicate input keys by replacement. *)
Definition duplicate_input_map :=
  Map.of_list positive_encoding [(1%positive, false); (1%positive, true)].

Example constructed_bottom_default_comparison_reflexive :
  Map.forall2 (fun a b => implb a (fixture_default false b))
    duplicate_input_map duplicate_input_map = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example constructed_top_default_comparison_reflexive :
  Map.forall2 (fun b a => implb (fixture_default true a) b)
    duplicate_input_map duplicate_input_map = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty observation family denotes every concrete value, even with false slots. *)
Definition empty_index_gamma : concretisation unit nat :=
  family_gamma (fun _ : Empty_set => @bool_gamma nat) (fun _ _ => false).

Example empty_index_intersection_is_universal :
  forall c, gamma empty_index_gamma tt c.
Proof.
  intros c i. destruct i.
Qed.

Example top_default_left_narrow_is_not_an_exact_family :
  (env_default true (env_optional Top_default true bool_lattice Env_narrow None (Some false)),
    narrow bool_lattice true false) = (false, true).
Proof.
  vm_compute. reflexivity.
Qed.

Definition bool_meet_narrow := with_narrow bool_lattice andb.

Definition bool_meet_top : top bool_meet_narrow.
Proof.
  refine {| top_value := true |}; intros []; reflexivity.
Defined.

Definition bool_bottom_contract :
  env_default_laws Bottom_default false bool_lattice.
Proof.
  constructor; intros op [a|] [b|]; destruct op; try destruct a; try destruct b; reflexivity.
Defined.

Definition bool_top_contract :
  env_default_laws Top_default true bool_meet_narrow.
Proof.
  constructor; intros op [a|] [b|]; destruct op; try destruct a; try destruct b; reflexivity.
Defined.

Definition env_bool_bottom := env Bottom_default positive_encoding bool_lattice bool_top.
Definition env_bool_top := env Top_default positive_encoding bool_meet_narrow bool_meet_top.
Definition env_universe := [1%positive; 2%positive; 3%positive].
Definition e0 : env_map positive_encoding bool := env_empty positive_encoding.
Definition e1 := env_of_list positive_encoding [(1%positive, true)].
Definition e2 := env_of_list positive_encoding [(2%positive, true)].
Definition et1 := env_of_list positive_encoding [(1%positive, false)].
Definition et2 := env_of_list positive_encoding [(2%positive, false)].

Example bottom_default_operations :
  (leb env_bool_bottom e0 e1, leb env_bool_bottom e1 e2,
    Map.elements (env_raw (join env_bool_bottom e1 e2)),
    Map.elements (env_raw (widen env_bool_bottom e1 e2)),
    Map.elements (env_raw (narrow env_bool_bottom e1 e2))) =
  (true, false, [(2%positive, true); (1%positive, true)],
    [(2%positive, true); (1%positive, true)], [(1%positive, true)]).
Proof.
  vm_compute. reflexivity.
Qed.

Example top_default_absorbing_join :
  (leb env_bool_top (Some et1) (Some et2),
    option_map (fun m => Map.elements (env_raw m))
      (join env_bool_top (Some et1) (Some et2)),
    option_map (fun m => Map.elements (env_raw m))
      (widen env_bool_top (Some et1) (Some et2)),
    option_map (fun m => Map.elements (env_raw m))
      (narrow env_bool_top (Some et1) (Some et2))) =
  (false, Some [], Some [], Some [(2%positive, false); (1%positive, false)]).
Proof.
  vm_compute. reflexivity.
Qed.

Example top_default_fresh_bottom_boundary :
  (leb env_bool_top None (Some e0), leb env_bool_top (Some e0) None,
    env_get Top_default positive_encoding bool_meet_narrow bool_meet_top 1%positive None,
    env_get Top_default positive_encoding bool_meet_narrow bool_meet_top 1%positive (Some e0)) =
  (true, false, None, Some true).
Proof.
  vm_compute. reflexivity.
Qed.

Example ordinary_boolean_weak_laws_in_both_policies :
  lattice_laws (env Bottom_default positive_encoding bool_lattice bool_top) /\
  lattice_laws (env Top_default positive_encoding bool_lattice bool_top).
Proof.
  split; apply env_laws; [exact positive_encoding_laws | exact bool_laws |
    exact positive_encoding_laws | exact bool_laws].
Qed.

Example ordinary_boolean_least_joins_in_both_policies :
  lub_laws (env Bottom_default positive_encoding bool_lattice bool_top) /\
  lub_laws (env Top_default positive_encoding bool_lattice bool_top).
Proof.
  split; apply env_lub; [exact positive_encoding_laws | exact bool_laws | exact bool_lub |
    exact positive_encoding_laws | exact bool_laws | exact bool_lub].
Qed.

Example bottom_policy_exact_family :
  family env_bool_bottom bool_lattice
    (fun k m => env_read positive_encoding false k m).
Proof.
  exact (env_core_family positive_encoding positive_encoding_laws bool_lattice
    bool_laws bool_bottom_contract).
Qed.

Example top_policy_exact_family :
  family env_bool_top (lift_bot bool_meet_narrow)
    (env_get Top_default positive_encoding bool_meet_narrow bool_meet_top).
Proof.
  exact (env_top_family positive_encoding positive_encoding_laws 1%positive
    bool_meet_narrow bool_meet_top bool_top_contract).
Qed.

Definition bool_meet_laws : lattice_laws bool_meet_narrow.
Proof.
  apply with_narrow_laws; [exact bool_laws | |];
    intros [] [] Hle; cbn in *; congruence.
Defined.

Definition bool_meet_lub : lub_laws bool_meet_narrow :=
  with_narrow_lub bool_lattice andb bool_lub.

Definition bool_meet_closed : closed_on bool_meet_narrow (fun _ => True).
Proof.
  constructor; intros; exact I.
Defined.

Definition bool_meet_height := with_narrow_height bool_lattice andb bool_height.
Definition bool_meet_wrank :=
  height_wrank bool_meet_narrow bool_meet_laws bool_meet_lub bool_meet_closed
    (fun _ _ => eq_refl) bool_meet_height.

Definition bottom_environment_closed U :
  closed_on env_bool_bottom
    (within_env Bottom_default positive_encoding bool_lattice bool_top U (fun _ => True)).
Proof.
  apply (env_closed Bottom_default positive_encoding positive_encoding_laws
    bool_lattice bool_top U (fun _ => True) bool_laws bool_lub bool_closed
    bool_bottom_contract I).
  intros [] [] _ _ [Ha Ha'] [Hb Hb']; vm_compute in *; split; congruence.
Defined.

Definition top_environment_closed U :
  closed_on env_bool_top
    (within_env Top_default positive_encoding bool_meet_narrow bool_meet_top U
      (fun _ => True)).
Proof.
  apply (env_closed Top_default positive_encoding positive_encoding_laws
    bool_meet_narrow bool_meet_top U (fun _ => True) bool_meet_laws bool_meet_lub
    bool_meet_closed bool_top_contract I).
  intros [] [] _ _ [Ha Ha'] [Hb Hb']; vm_compute in *; split; congruence.
Defined.

Definition bottom_environment_height U :=
  env_height Bottom_default positive_encoding positive_encoding_laws bool_lattice bool_top
    U (fun _ => True) bool_laws bool_lub bool_closed bool_bottom_contract bool_height.

Definition bottom_environment_wrank U :=
  env_wrank Bottom_default positive_encoding positive_encoding_laws bool_lattice bool_top
    U (fun _ => True) bool_laws bool_bottom_contract bool_wrank.

Definition top_environment_height U :=
  env_height Top_default positive_encoding positive_encoding_laws
    bool_meet_narrow bool_meet_top U (fun _ => True)
    bool_meet_laws bool_meet_lub bool_meet_closed bool_top_contract bool_meet_height.

Definition top_environment_wrank U :=
  env_wrank Top_default positive_encoding positive_encoding_laws
    bool_meet_narrow bool_meet_top U (fun _ => True)
    bool_meet_laws bool_top_contract bool_meet_wrank.

Definition top_environment_top : top env_bool_top.
Proof.
  refine (env_top Top_default positive_encoding positive_encoding_laws
    bool_meet_narrow bool_meet_top bool_meet_laws e0 _).
  intro k; change (Map.find_or positive_encoding true k (@Map.empty positive bool) = true).
  rewrite Map.find_or_equation, Map.get_empty; reflexivity.
Defined.

Definition lifted_environment_closed U :=
  lift_bot_closed env_bool_bottom (bottom_environment_closed U).
Definition lifted_environment_height U :=
  lift_bot_height env_bool_bottom
    (env_laws Bottom_default positive_encoding positive_encoding_laws _ _ bool_laws)
    (bottom_environment_height U).
Definition lifted_environment_wrank U :=
  lift_bot_wrank env_bool_bottom (bottom_environment_wrank U).

Example lifted_environment_empty_universe_measures :
  (rank (lifted_environment_height []) None,
    rank (lifted_environment_height []) (Some e0),
    bound (lifted_environment_height []),
    wrank (lifted_environment_wrank []) None,
    wrank (lifted_environment_wrank []) (Some e0),
    wbound (lifted_environment_wrank [])) = (0, 1, 1, 1, 0, 1)%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example lifted_environment_reached_empty_is_supported :
  lift_bot_inv (within_env Bottom_default positive_encoding bool_lattice bool_top []
    (fun _ => True)) (Some e0).
Proof.
  split; [intro k; exact I | intros k _].
  change (equivalent bool_lattice
    (Map.find_or positive_encoding false k (@Map.empty positive bool)) false).
  rewrite Map.find_or_equation, Map.get_empty; split; reflexivity.
Qed.

Example lifted_environment_reached_empty_is_above_fresh_bottom :
  leb (lift_bot env_bool_bottom) (Some e0) None = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example top_default_core_has_no_least_empty_map :
  (leb (env_valid_core positive_encoding Top_default true bool_meet_narrow) e0 et1,
    leb bool_meet_narrow true false) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example both_policy_measure_boundaries :
  (rank (bottom_environment_height env_universe) e1,
    bound (bottom_environment_height env_universe),
    rank (top_environment_height env_universe) None,
    rank (top_environment_height env_universe) (Some e0),
    bound (top_environment_height env_universe),
    bound (top_environment_height []), wbound (top_environment_wrank [])) =
  (1, 3, 0, 4, 4, 1, 1)%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Definition et12 := env_of_list positive_encoding [(1%positive, false); (2%positive, false)].
Definition et123 := env_fill positive_encoding env_universe false.

Example top_policy_chain_reaches_the_lifted_bound :
  (List.map (rank (top_environment_height env_universe))
      [None; Some et123; Some et12; Some et1; Some e0],
    List.map (fun p => (leb env_bool_top (fst p) (snd p),
      leb env_bool_top (snd p) (fst p)))
      [(None, Some et123); (Some et123, Some et12); (Some et12, Some et1);
        (Some et1, Some e0)]) =
  ([0; 1; 2; 3; 4]%nat,
    [(true, false); (true, false); (true, false); (true, false)]).
Proof.
  vm_compute. reflexivity.
Qed.

Example duplicate_universe_counts_repeated_environment_slots :
  (rank (bottom_environment_height [1%positive; 1%positive; 2%positive]) e1,
    bound (bottom_environment_height [1%positive; 1%positive; 2%positive])) = (2, 3)%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example environment_cost_boundaries :
  (Cost.ticks (leb_c env_bool_bottom e0 e1),
    Cost.ticks (join_c env_bool_bottom e0 e0),
    Cost.ticks (leb_c env_bool_top None (Some e0)),
    Cost.ticks (join_c env_bool_top None (Some e0))) = (0, 1, 1, 1)%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition charged_boolean : lattice bool :=
  {| leb_c := fun a b => Cost.lift (fun _ => 37%N) (implb a) b;
     join_c := fun a b => Cost.lift (fun _ => 41%N) (orb a) b;
     widen_c := fun a b => Cost.lift (fun _ => 43%N) (orb a) b;
     narrow_c := fun a b => Cost.lift (fun _ => 47%N) (fun _ => a) b;
     bot := false |}.

Definition charged_boolean_top : top charged_boolean.
Proof.
  refine {| top_value := true |}; intros []; reflexivity.
Defined.

Example environment_retains_component_callback_charges :
  let L := env Bottom_default positive_encoding charged_boolean charged_boolean_top in
  (Cost.ticks (leb_c L e1 e1), Cost.ticks (join_c L e1 e1),
    Map.elements (env_raw (join L e1 e1))) = (40%N, 44%N, [(1%positive, true)]).
Proof.
  vm_compute. reflexivity.
Qed.

Definition empty_key_encoding : encoding Empty_set :=
  BaseEncoding.of_pure (fun k : Empty_set => match k with end).
Definition empty_key_encoding_laws : encoding_laws empty_key_encoding.
Proof.
  constructor; intros [].
Defined.

Example empty_index_top_policy_has_total_weak_laws :
  lattice_laws (env Top_default empty_key_encoding bool_lattice bool_top).
Proof.
  apply env_laws; [exact empty_key_encoding_laws | exact bool_laws].
Qed.

Example empty_index_top_policy_still_distinguishes_fresh_bottom :
  let L := env Top_default empty_key_encoding bool_lattice bool_top in
  let m : env_map empty_key_encoding bool := env_empty empty_key_encoding in
  (leb L (Some m) None, leb L None (Some m)) = (false, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_index_reached_meaning_is_universal :
  forall s : Empty_set -> nat,
  gamma (env_gamma Top_default empty_key_encoding bool_lattice bool_top
    (fun _ => @bool_gamma nat)) (Some (env_empty empty_key_encoding)) s.
Proof.
  intros s k; destruct k.
Qed.

Example empty_index_fresh_meaning_is_empty :
  forall s : Empty_set -> nat,
  ~ gamma (env_gamma Top_default empty_key_encoding bool_lattice bool_top
    (fun _ => @bool_gamma nat)) None s.
Proof.
  intros s Hs; exact Hs.
Qed.

Definition singleton_supported d v :
  env_support positive_encoding bool_lattice d env_universe (fun _ => True)
    (env_of_list positive_encoding [(1%positive, v)]).
Proof.
  split; [intros; exact I |].
  intros k Hout.
  assert (Hneq : k <> 1%positive).
  { intro Heq; subst k; apply Hout; left; reflexivity. }
  assert (Hkey : eqb positive_encoding k 1%positive = false).
  { apply (eqb_false_iff positive_encoding positive_encoding_laws), Hneq. }
  unfold env_read; rewrite Map.find_or_equation, env_of_list_raw, Map.of_list_get.
  cbn [fold_left fst snd]; rewrite Hkey; split; destruct d; reflexivity.
Defined.

Example supported_nondefault_values_in_both_policies :
  within_env Bottom_default positive_encoding bool_lattice bool_top env_universe
    (fun _ => True) e1 /\
  within_env Top_default positive_encoding bool_meet_narrow bool_meet_top env_universe
    (fun _ => True) (Some et1).
Proof.
  split; apply singleton_supported.
Qed.

Example empty_universe_rejects_nondefault_bottom_map :
  ~ within_env Bottom_default positive_encoding bool_lattice bool_top []
    (fun _ => True) e1.
Proof.
  intros [_ Hout]; specialize (Hout 1%positive (fun H => H)).
  vm_compute in Hout; destruct Hout as [Hfalse _]; discriminate.
Qed.

Example empty_universe_rejects_nondefault_top_map :
  ~ within_env Top_default positive_encoding bool_meet_narrow bool_meet_top []
    (fun _ => True) (Some et1).
Proof.
  intros [_ Hout]; specialize (Hout 1%positive (fun H => H)).
  vm_compute in Hout; destruct Hout as [_ Hfalse]; discriminate.
Qed.

Definition indexed_gamma (k : bool) : concretisation bool bool :=
  {| gamma := fun a c => c = k -> a = true |}.

Example indexed_component_gamma_laws :
  forall k, concretisation_laws bool_lattice (indexed_gamma k).
Proof.
  intro k; constructor; intros [] [] c Hab Hc Hk; vm_compute in Hab;
    try discriminate; try reflexivity; exact (Hc Hk).
Qed.

Definition indexed_store := fun _ : bool => false.
Definition only_false_key := env_of_list bool_encoding [(false, true)].
Definition only_true_key := env_of_list bool_encoding [(true, true)].

Example indexed_environment_meaning_distinguishes_coordinates :
  gamma (env_gamma Bottom_default bool_encoding bool_lattice bool_top indexed_gamma)
    only_false_key indexed_store /\
  ~ gamma (env_gamma Bottom_default bool_encoding bool_lattice bool_top indexed_gamma)
    only_true_key indexed_store.
Proof.
  split.
  - intros []; vm_compute; congruence.
  - intro H; specialize (H false); vm_compute in H; discriminate (H eq_refl).
Qed.

Example indexed_environment_agreement_distinguishes_coordinates :
  agree (env_agree Bottom_default bool_encoding bool_lattice bool_top
    (fun _ => @bool_agree bool)) only_false_key (fun _ => false) (fun k => k) /\
  ~ agree (env_agree Bottom_default bool_encoding bool_lattice bool_top
    (fun _ => @bool_agree bool)) only_true_key (fun _ => false) (fun k => k).
Proof.
  split.
  - intros []; vm_compute; congruence.
  - intro H; specialize (H true); vm_compute in H; discriminate (H eq_refl).
Qed.

Example indexed_meaning_transport_client :
  concretisation_laws (env Bottom_default bool_encoding bool_lattice bool_top)
    (env_gamma Bottom_default bool_encoding bool_lattice bool_top indexed_gamma).
Proof.
  apply env_gamma_laws; [exact bool_encoding_laws | exact bool_laws |
    exact indexed_component_gamma_laws].
Qed.

Example setter_value_and_fresh_bottom_observations :
  (env_get Bottom_default positive_encoding bool_lattice bool_top 1%positive
      (env_set Bottom_default positive_encoding 1%positive true e0),
    env_get Bottom_default positive_encoding bool_lattice bool_top 2%positive
      (env_set Bottom_default positive_encoding 1%positive true e0),
    env_get Top_default positive_encoding bool_meet_narrow bool_meet_top 1%positive
      (env_set Top_default positive_encoding 1%positive false (Some e0)),
    env_get Top_default positive_encoding bool_meet_narrow bool_meet_top 1%positive
      (env_set Top_default positive_encoding 1%positive false None)) =
  (true, false, Some false, None).
Proof.
  vm_compute. reflexivity.
Qed.
