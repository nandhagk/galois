(** * Analyses and termination evidence

    Analyses compute from dictionaries and summaries without carrying law proofs.
    For example, a flat policy requests joining without widening points.
    Builds on: FixpointSystem, FixpointEval and LatticeHeight. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval.
Import Cost.Notations.

Module Policy.

(** Policies supply charged scheduling callbacks independently of their laws. *)
Record t (X : Type) := Make {
  order_c : X -> Cost.t positive;
  widen_at_c : X -> Cost.t bool;
  delay : nat;
  narrowing : nat
}.

Arguments Make {X}.
Arguments order_c {X}.
Arguments widen_at_c {X}.
Arguments delay {X}.
Arguments narrowing {X}.

Definition order {X} (p : t X) x := Cost.value (order_c p x).
Definition widen_at {X} (p : t X) x := Cost.value (widen_at_c p x).

(** Flat scheduling requests no widening and no narrowing. *)
Definition flat X : t X :=
  Make (fun _ => Cost.ret 1%positive) (fun _ => Cost.ret false) 0 0.

(** Code scheduling orders keys by their encoded positive values. *)
Definition by_code {X} (EX : encoding X) : t X :=
  Make (encode_c EX) (fun _ => Cost.ret false) 0 0.

End Policy.
Import Policy.

Module Analysis.

(** An analysis bundles computational inputs alone. *)
Record t (X C A : Type) := Make {
  key_enc : encoding X;
  row_enc : encoding C;
  lat : lattice A;
  system : System.t X C A;
  static : System.static system;
  policy : Policy.t X
}.

Arguments Make {X C A}.
Arguments key_enc {X C A}.
Arguments row_enc {X C A}.
Arguments lat {X C A}.
Arguments system {X C A}.
Arguments static {X C A}.
Arguments policy {X C A}.

(** Sound engine reasoning requires lawful keys, weak lattice laws and covering summaries. *)
Record laws {X C A} (a : t X C A) : Prop := {
  key_laws : encoding_laws (key_enc a);
  row_laws : encoding_laws (row_enc a);
  lattice_law : lattice_laws (lat a);
  static_law : System.static_laws (static a)
}.

Arguments key_laws {X C A a}.
Arguments row_laws {X C A a}.
Arguments lattice_law {X C A a}.
Arguments static_law {X C A a}.

(** Joining policies select no widening points. *)
Definition joining {X C A} (a : t X C A) :=
  forall x, Policy.widen_at (policy a) x = false.

End Analysis.
Import Analysis.

Module Terminates.

(** Finite-height evidence supplies closure and query preservation on an explicit invariant. *)
Record t {X C A} (a : Analysis.t X C A) := Finite {
  inv : A -> Prop;
  hgt : height_on (Analysis.lat a) inv;
  inv_bot : inv (bot (Analysis.lat a));
  inv_join : forall x y, inv x -> inv y -> inv (join (Analysis.lat a) x y);
  inv_closed : forall s, (forall x, inv (s x)) ->
    forall c, In c (System.constraints (Analysis.system a)) ->
    forall xa, In xa (fst (Eval.outputs (Analysis.system a) c s)) -> inv (snd xa)
}.

Arguments inv {X C A a}.
Arguments hgt {X C A a}.
Arguments inv_bot {X C A a}.
Arguments inv_join {X C A a}.
Arguments inv_closed {X C A a}.

End Terminates.
Import Terminates.
