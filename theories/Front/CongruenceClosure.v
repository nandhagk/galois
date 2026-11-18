(** * A model of the closure of finitely many equations

    The congruence closure of a list of equations, computed on the finite set of their
    subterms, gives each term a canonical form. Terms with their canonical forms as meanings
    form a model whose equality is exactly the closure, so no quotient is needed.
    For example, the closure of the one equation [Deref (Cell x) = Cell a] gives both sides one
    canonical form, and leaves every other term its own.

    Builds on: the signature of the reference closure and the engine models. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import Spec RunnerSig CongruenceRefSig.

Import List.ListNotations.

Module ClosureModel (V : VALUE).
  Lemma closure_model : forall (eqs : list (@expr V.t * @expr V.t))
      (P : positive -> list V.t -> Prop),
    exists M : @model V.t, (forall t u, denote M t = denote M u <-> closure eqs t u) /\
      (forall r vs, rel M r (map inr vs) <-> P r vs).
  Proof.
  Admitted. (* STUB *)
End ClosureModel.
