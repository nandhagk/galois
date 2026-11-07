(** * Domain bundles

    A domain groups abstract operations, a top value and a concrete interpretation.
    For example, boolean reachability interprets true as all concrete values.
    Builds on: LatticeCore, LatticeHeight and LatticeConcrete. *)

From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete.

(** The domain bundle holds data without requiring soundness or termination evidence. *)
Record domain (A C : Type) : Type := Domain {
  lat : lattice A;
  top_v : A;
  gam : concretisation A C
}.

Arguments lat {A C}.
Arguments top_v {A C}.
Arguments gam {A C}.

(** Domain laws require least joins, monotone meaning, empty bottom and full top. *)
Record domain_laws {A C} (D : domain A C) : Prop := {
  dom_lattice : lattice_laws (lat D);
  dom_lub : lub_laws (lat D);
  dom_top : forall a, leb (lat D) a (top_v D) = true;
  dom_mono : concretisation_laws (lat D) (gam D);
  dom_bot_empty : forall c, ~ gamma (gam D) (bot (lat D)) c;
  dom_top_full : forall c, gamma (gam D) (top_v D) c
}.

(** Finiteness supplies closure and termination measures relative to an invariant. *)
Record domain_finite {A C} (D : domain A C) (inv : A -> Prop) : Type := {
  fin_closed : closed_on (lat D) inv;
  fin_height : height_on (lat D) inv;
  fin_wrank : widening_rank_on (lat D) inv
}.

Arguments dom_lattice {A C D}.
Arguments dom_lub {A C D}.
Arguments dom_top {A C D}.
Arguments dom_mono {A C D}.
Arguments dom_bot_empty {A C D}.
Arguments dom_top_full {A C D}.
Arguments fin_closed {A C D inv}.
Arguments fin_height {A C D inv}.
Arguments fin_wrank {A C D inv}.

(** A lattice, a supplied top and a meaning build a domain without semantic proof arguments. *)
Definition domain_of_simple {A C} (L : lattice A) (T : top L)
    (G : concretisation A C) : domain A C :=
  {| lat := L;
     top_v := top_value T;
     gam := G |}.

(** Separate component laws establish the laws of the assembled domain. *)
Theorem domain_of_simple_laws {A C} (L : lattice A) (T : top L)
    (G : concretisation A C) :
  lattice_laws L -> lub_laws L -> concretisation_laws L G ->
  bottom_empty L G -> top_full T G -> domain_laws (domain_of_simple L T G).
Proof.
  intros HL Hlub HG Hbot Htop; constructor; cbn.
  - exact HL.
  - exact Hlub.
  - apply (top_greatest T).
  - exact HG.
  - apply (gamma_bot_empty Hbot).
  - apply (gamma_top_full Htop).
Qed.
