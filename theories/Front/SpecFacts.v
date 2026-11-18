(** * Facts about specifications

    The relational meaning of a specification is the least relation that contains the input
    rows and is closed under the clauses. [derived_least] states this as an induction principle
    over any relation [P]: when [P] contains the inputs and every clause whose body holds in
    [P] has its head in [P], every derived row is in [P].
    For example, the derived [Egglog] programs prove their glue lemmas from it.

    Builds on: the specifications. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec.

Import List.ListNotations.

Section Least.
Context {V : Type} (prim : positive -> list V -> option V).

(** A premise holds in a relation [P] under an environment. *)
Definition premise_in (P : positive -> list V -> Prop) (e : positive -> option V)
    (p : premise V) : Prop :=
  match p with
  | Holds r args => exists vs, pat_values prim e args = Some vs /\ P r vs
  | Equals _ _ _ => False
  | Computes q args v => exists vs w, pat_values prim e args = Some vs /\ prim q vs = Some w /\
      pat_value prim e v = Some w
  end.

(** The rows of a relational specification form the least relation that contains the inputs
    and is closed under the clauses. *)
Lemma derived_least (s : spec V) (I P : positive -> list V -> Prop) :
  (forall r vs, In r (inputs s) -> I r vs -> P r vs) ->
  (forall c e r args vs, In c (clauses s) -> head c = Derive r args ->
    Forall (premise_in P e) (body c) -> pat_values prim e args = Some vs -> P r vs) ->
  forall r vs, derived prim s I r vs -> P r vs.
Proof.
  intros Hinputs Hclauses.
  fix IH 3.
  intros r vs Hderived.
  destruct Hderived as [r vs Hin HI | c e r args vs Hin Hhead Hbody Hvalues].
  - exact (Hinputs r vs Hin HI).
  - apply (Hclauses c e r args vs Hin Hhead); [| exact Hvalues].
    clear Hin Hhead Hvalues.
    induction Hbody as [e | e r' args' vs' rest Hvalues' Hrow Hrest IHrest
      | e q args' v vs' w rest Hvalues' Hprim Hvalue Hrest IHrest].
    + constructor.
    + constructor; [exists vs'; split; [exact Hvalues' | exact (IH r' vs' Hrow)] | exact IHrest].
    + constructor; [exists vs', w; repeat split; assumption | exact IHrest].
Qed.

End Least.

(** An environment that binds the variables 1 to n to a list of n values. *)
Definition env_of {V : Type} (vs : list V) (x : positive) : option V :=
  nth_error vs (Pos.to_nat x - 1).
