(** * Bounded collection fixtures

    Finite support supplies total heights and rejects values outside its universe.
    For example, the three-key may chain reaches the advertised bound.
    Builds on: LatticeBounded and the collection constructors. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSub LatticeSet
  LatticeEnv LatticeSimple LatticeBounded.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition universe := [1%positive; 2%positive; 3%positive].
Definition BS := bounded_set positive_encoding universe.
Definition b0 : {s | within_set positive_encoding universe s}.
Proof.
  refine (exist _ (set_empty positive_encoding) _).
  exact (bot_inv (within_set_closed positive_encoding universe)).
Defined.

Definition b1 : {s | within_set positive_encoding universe s}.
Proof.
  refine (exist _ (set_of_list positive_encoding [1%positive]) _).
  intros k Hk.
  pose proof (set_of_list_within positive_encoding positive_encoding_laws
    [1%positive] k Hk) as Hin.
  destruct Hin as [Hin|Hin]; [left; exact Hin | contradiction].
Defined.

Definition b12 : {s | within_set positive_encoding universe s}.
Proof.
  refine (exist _ (set_of_list positive_encoding [1%positive; 2%positive]) _).
  intros k Hk.
  pose proof (set_of_list_within positive_encoding positive_encoding_laws
    [1%positive; 2%positive] k Hk) as Hin.
  destruct Hin as [Hin|[Hin|Hin]]; [left | right; left | contradiction]; exact Hin.
Defined.

Definition b123 : {s | within_set positive_encoding universe s} :=
  exist _ (set_of_list positive_encoding universe)
    (set_of_list_within positive_encoding positive_encoding_laws universe).

Example bounded_chain_reaches_bound :
  (List.map (rank (bounded_set_height positive_encoding positive_encoding_laws universe))
    [b0; b1; b12; b123],
    bound (bounded_set_height positive_encoding positive_encoding_laws universe)) =
  ([0; 1; 2; 3], 3).
Proof.
  vm_compute. reflexivity.
Qed.

Example bounded_projection_and_join :
  (leb BS b1 b12,
    FinSet.elements (set_raw (proj1_sig (join BS b1 b12)))) =
  (true, [2%positive; 1%positive]).
Proof.
  vm_compute. reflexivity.
Qed.

Example bounded_outside_rejected :
  FinSet.mem positive_encoding 4%positive
    (set_raw (set_of_list positive_encoding [4%positive])) = true /\
  List.existsb (BaseEq.eqb positive_encoding 4%positive) universe = false.
Proof.
  vm_compute. auto.
Qed.

Example bounded_empty_universe_height :
  bound (bounded_set_height positive_encoding positive_encoding_laws []) = 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example outside_value_has_no_bounded_representative :
  forall b : {s | within_set positive_encoding universe s},
  proj1_sig b <> set_of_list positive_encoding [4%positive].
Proof.
  apply (bounded_set_rejects positive_encoding universe _ 4%positive).
  - vm_compute. reflexivity.
  - vm_compute; intuition discriminate.
Qed.

Definition bool_defaults : env_default_laws Bottom_default false bool_lattice.
Proof.
  constructor; intros op [a|] [b|]; destruct op; try destruct a; try destruct b; reflexivity.
Defined.

Definition widen_default :
  forall a b, True -> True -> equivalent bool_lattice a false ->
  equivalent bool_lattice b false -> equivalent bool_lattice (widen bool_lattice a b) false.
Proof.
  intros [] [] _ _ [Ha Ha'] [Hb Hb']; vm_compute in *; split; congruence.
Defined.

Definition bool_universe := [false; true].
Definition BE := bounded_env Bottom_default bool_encoding bool_encoding_laws
  bool_lattice bool_top bool_universe (fun _ => True) bool_laws bool_lub bool_closed
  bool_defaults I widen_default.

Definition BE_height : height BE.
Proof.
  apply bounded_height.
  exact (env_height Bottom_default bool_encoding bool_encoding_laws
    bool_lattice bool_top bool_universe (fun _ => True)
    bool_laws bool_lub bool_closed bool_defaults bool_height).
Defined.

Definition all_bool_maps_supported (m : env_map bool_encoding bool) :
  within_env Bottom_default bool_encoding bool_lattice bool_top bool_universe
    (fun _ => True) m.
Proof.
  split; [intros; exact I | intros [] Hout; exfalso; apply Hout; vm_compute; auto].
Defined.

Definition be0 := exist _ (env_empty bool_encoding)
  (all_bool_maps_supported (env_empty bool_encoding)).
Definition be1 := exist _ (env_of_list bool_encoding [(false, true)])
  (all_bool_maps_supported (env_of_list bool_encoding [(false, true)])).

Example bounded_environment_height_and_cost :
  (rank BE_height be0, rank BE_height be1, bound BE_height,
    Cost.ticks (join_c BE be0 be0), Cost.ticks (narrow_c BE be0 be0)) =
  (0, 1, 2, 1%N, 2%N).
Proof.
  vm_compute. reflexivity.
Qed.

Definition positive_environment_closed :=
  env_closed Bottom_default positive_encoding positive_encoding_laws
    bool_lattice bool_top universe (fun _ => True) bool_laws bool_lub bool_closed
    bool_defaults I widen_default.

Definition positive_bounded_top :
  top (sub_lattice (env Bottom_default positive_encoding bool_lattice bool_top)
    (within_env Bottom_default positive_encoding bool_lattice bool_top universe
      (fun _ => True)) positive_environment_closed).
Proof.
  refine (bounded_env_top positive_encoding positive_encoding_laws bool_lattice bool_top
    bool_laws universe (fun _ => True) positive_environment_closed
    (env_fill positive_encoding universe true) _ _).
  - apply env_fill_supported; [exact positive_encoding_laws | exact bool_laws |
      exact I | exact I].
  - intros k Hin; apply env_fill_inside; [exact positive_encoding_laws | exact Hin].
Defined.

Example bounded_top_does_not_claim_an_unbounded_top :
  let m := proj1_sig (top_value positive_bounded_top) in
  (env_read positive_encoding false 1%positive m,
    env_read positive_encoding false 4%positive m) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.
