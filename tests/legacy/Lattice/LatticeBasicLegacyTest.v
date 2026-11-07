(** * Basic combinator differential fixtures

    Every pair from each sample compares all four new and legacy operations.
    For example, the disjunction sample includes an oversized list at every tested cap.
    Builds on: the new basic combinators and the legacy Order combinators. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeAdjoin
  LatticeFlat LatticeLift LatticeProduct LatticeDual LatticeDisjunction.
From GaloisLegacy.Order Require OrderLattice OrderBasic OrderFlat OrderLift
  OrderProduct OrderDual OrderDisjunction.
Import List.ListNotations Cost.Notations.

Definition new_observation {A B} (encode : A -> B) (L : lattice A) (a b : A) :=
  (leb L a b, encode (join L a b), encode (widen L a b), encode (narrow L a b)).

Definition old_observation {A} (L : OrderLattice.lattice A) (a b : A) :=
  (OrderLattice.leb L a b, OrderLattice.join L a b,
   OrderLattice.widen L a b, OrderLattice.narrow L a b).

Definition observations {A B} (sample : list A) (encode : A -> B)
    (L : lattice A) (old : OrderLattice.lattice B) :=
  (map (fun a => map (new_observation encode L a) sample) sample,
   map (fun a => map (fun b => old_observation old (encode a) (encode b)) sample) sample).

Definition legacy_flat (x : flat bool) : OrderFlat.flat bool :=
  match x with
  | FBot => OrderFlat.FBot
  | FVal a => OrderFlat.FVal a
  | FTop => OrderFlat.FTop
  end.

Definition legacy_lift (x : lift_top bool) : OrderLift.lift_top bool :=
  match x with
  | Elem a => OrderLift.Elem a
  | Unknown => OrderLift.Unknown
  end.

Example flat_legacy_all_pairs :
  let result := observations [FBot; FVal false; FTop] legacy_flat
    (flat_lattice Bool.eqb) (OrderFlat.flat_lattice Bool.eqb) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.

Example bottom_lift_legacy_all_pairs :
  let result := observations [None; Some false; Some true] (fun x => x)
    (lift_bot bool_lattice) (OrderLift.option_lattice OrderBasic.bool_lattice) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.

Example top_lift_legacy_all_pairs :
  let result := observations [Elem false; Elem true; Unknown] legacy_lift
    (lift_top_lattice bool_lattice) (OrderLift.lift_top_lattice OrderBasic.bool_lattice) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_legacy_all_pairs :
  let result := observations [(FBot, false); (FVal false, false); (FTop, true)]
    (fun x => (legacy_flat (fst x), snd x))
    (product (flat_lattice Bool.eqb) bool_lattice)
    (OrderProduct.product_lattice (OrderFlat.flat_lattice Bool.eqb) OrderBasic.bool_lattice) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_legacy_all_pairs :
  let sample := [[]; [FBot; FVal false; FVal true]] in
  let results := map (fun k => observations sample (map legacy_flat)
    (disjunction k (flat_lattice Bool.eqb))
    (OrderDisjunction.disjunction_lattice k (OrderFlat.flat_lattice Bool.eqb))) [0; 1; 2] in
  map fst results = map snd results.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_legacy_all_pairs :
  let result := observations [false; true] (fun x => x)
    (dual bool_lattice bool_top (fun a b => Cost.step ;; Cost.ret (andb a b)))
    (OrderDual.dual_lattice OrderBasic.bool_lattice OrderBasic.bool_top andb) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.

Definition custom_bool : lattice bool :=
  of_pure implb false orb (fun _ _ => true) andb.

Definition custom_legacy_bool : OrderLattice.lattice bool :=
  {| OrderLattice.leb := implb;
     OrderLattice.bot := false;
     OrderLattice.join := orb;
     OrderLattice.widen := fun _ _ => true;
     OrderLattice.narrow := andb |}.

Example custom_lift_legacy_all_pairs :
  let result := observations [Elem false; Elem true; Unknown] legacy_lift
    (lift_top_lattice custom_bool) (OrderLift.lift_top_lattice custom_legacy_bool) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.

Example custom_product_legacy_all_pairs :
  let result := observations [(false, false); (true, false); (true, true)] (fun x => x)
    (product custom_bool custom_bool)
    (OrderProduct.product_lattice custom_legacy_bool custom_legacy_bool) in
  fst result = snd result.
Proof.
  vm_compute; reflexivity.
Qed.
