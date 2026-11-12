(** * Value products

    Products apply value transfers to each component independently.
    For example, a forward transfer pairs the two component results.
    Builds on: ProductSig and lattice products. *)

From Stdlib Require Import List.
From Galois.Lattice Require Import Product.
From Galois.Domains Require Import LangSig ValueSig ProductSig.

Module ProductCode (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L) <: PRODUCT_OPS L A B.
  Include Product.ProductCode A B.
  Definition top : t := (A.top, B.top).
  Definition meet (x y : t) : t := (A.meet (fst x) (fst y), B.meet (snd x) (snd y)).
  Definition wparam := (A.wparam * B.wparam)%type.
  Definition widen (p : wparam) (x y : t) : t :=
    (A.widen (fst p) (fst x) (fst y), B.widen (snd p) (snd x) (snd y)).
  Definition narrow (x y : t) : t :=
    (A.narrow (fst x) (fst y), B.narrow (snd x) (snd y)).
  Definition forward (o : L.op) (xs : list t) : t :=
    (A.forward o (map fst xs), B.forward o (map snd xs)).
  Definition backward (o : L.op) (r : t) (xs : list t) : list t :=
    combine (A.backward o (fst r) (map fst xs)) (B.backward o (snd r) (map snd xs)).
  Definition guard (g : L.guard) (xs : list t) : list t :=
    combine (A.guard g (map fst xs)) (B.guard g (map snd xs)).
End ProductCode.
