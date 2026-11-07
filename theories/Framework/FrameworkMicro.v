(** * Symbolic edge functions

    Micro-functions compose without enumerating their value or function carriers.
    For example, IFDS uses Boolean reachability as its symbolic function.
    Builds on: LatticeCore and LatticeSimple. *)

From Stdlib Require Import Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
Import Cost.Notations.

Module Micro.

(** Composition applies its right argument first and retains both callback charges. *)
Record t (A F : Type) := Make {
  id : F;
  compose_c : F -> F -> Cost.t F;
  apply_c : F -> A -> Cost.t A;
  lat : lattice F
}.
Arguments Make {A F}.
Arguments id {A F}.
Arguments compose_c {A F}.
Arguments apply_c {A F}.
Arguments lat {A F}.

Definition compose {A F} (M : t A F) f g := Cost.value (compose_c M f g).
Definition apply {A F} (M : t A F) f a := Cost.value (apply_c M f a).

(** Primitive symbolic operations can use the one-tick pure adapter. *)
Definition of_pure {A F} id compose apply lat : t A F :=
  Make id (fun f g => Cost.step ;; Cost.ret (compose f g))
    (fun f a => Cost.step ;; Cost.ret (apply f a)) lat.

(** IFDS stores reachability and composes it by conjunction. *)
Definition boolean : t unit bool :=
  of_pure true andb (fun _ _ => tt) bool_lattice.

End Micro.

(** Algebra laws concern application and order, independently of runtime construction. *)
Record micro_laws {A F} (LA : lattice A) (M : Micro.t A F) : Prop := {
  lat_ok : lattice_laws (Micro.lat M);
  lub_ok : lub_laws (Micro.lat M);
  id_apply : forall a, equivalent LA (Micro.apply M (Micro.id M) a) a;
  compose_apply : forall f g a,
    equivalent LA (Micro.apply M (Micro.compose M f g) a)
      (Micro.apply M f (Micro.apply M g a));
  apply_mono : forall f a b, leb LA a b = true ->
    leb LA (Micro.apply M f a) (Micro.apply M f b) = true;
  apply_order : forall f g a, leb (Micro.lat M) f g = true ->
    leb LA (Micro.apply M f a) (Micro.apply M g a) = true;
  compose_mono : forall f f' g g',
    leb (Micro.lat M) f f' = true -> leb (Micro.lat M) g g' = true ->
    leb (Micro.lat M) (Micro.compose M f g) (Micro.compose M f' g') = true;
  join_upper : forall f g a,
    leb LA (Micro.apply M f a) (Micro.apply M (join (Micro.lat M) f g) a) = true /\
    leb LA (Micro.apply M g a) (Micro.apply M (join (Micro.lat M) f g) a) = true
}.
Arguments apply_order {A F LA M}.

(** Boolean micro-functions satisfy the algebra over the unit value lattice. *)
Theorem micro_boolean_laws : micro_laws unit_lattice Micro.boolean.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_lub.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
  - intros [] [] [] _; reflexivity.
  - intros [] [] [] _; reflexivity.
  - intros [] [] [] []; cbn; congruence.
  - intros [] [] []; split; reflexivity.
Qed.
