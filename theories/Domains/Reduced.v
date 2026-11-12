(** * Reduced value products

    Reduced products apply a fixed number of reduction rounds after transfers.
    For example, backward transfer reduces each paired result.
    Builds on: ProductSig and value products. *)

From Stdlib Require Import List Arith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig ProductSig Product.

Module ReducedCode (L : LANG_OPS) (A B : VALUE_DOMAIN_OPS L)
    (R : REDUCER_OPS A B) (K : ROUNDS) <: REDUCED_OPS L A B R K.
  Module P := ProductCode L A B.
  Definition t := P.t.
  Definition leb := P.leb.
  Definition bot := P.bot.
  Definition is_bot := P.is_bot.
  Definition join := P.join.
  Definition top := P.top.
  Definition meet := P.meet.
  Definition wparam := P.wparam.
  Definition widen := P.widen.
  Definition narrow := P.narrow.
  Definition red (x : t) : t := Nat.iter K.rounds R.reduce x.
  Definition forward (o : L.op) (xs : list t) : t := red (P.forward o xs).
  Definition backward (o : L.op) (r : t) (xs : list t) : list t :=
    map red (P.backward o r xs).
  Definition guard (g : L.guard) (xs : list t) : list t := map red (P.guard g xs).
End ReducedCode.
