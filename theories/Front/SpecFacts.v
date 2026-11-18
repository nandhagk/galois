(** * Facts about specifications

    The relational meaning of a specification is the least relation that contains the input
    rows and is closed under the clauses. [derived_least] states this as an induction principle
    over any relation [P]: when [P] contains the inputs and every clause whose body holds in
    [P] has its head in [P], every derived row is in [P].
    For example, the derived [Egglog] programs prove their glue lemmas from it.

    Main results
    - [derived_least] Every relation that contains the inputs and is closed under the clauses
      contains the derived rows.
    - [derived_mono] Derived rows grow with the input rows.
    - [represents_denote] A term that a cell represents means, in a model of the view, what
      the cell means.

    Builds on: the specifications and the models of the engine. *)

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

(** Derived rows grow with the input rows. *)
Lemma derived_mono {V : Type} (prim : positive -> list V -> option V) (s : spec V)
    (I1 I2 : positive -> list V -> Prop) :
  (forall r vs, I1 r vs -> I2 r vs) ->
  forall r vs, derived prim s I1 r vs -> derived prim s I2 r vs.
Proof.
  intros Hsub.
  apply derived_least.
  - intros r vs Hin HI.
    apply derived_input; [exact Hin | exact (Hsub r vs HI)].
  - intros c e r args vs Hin Hhead Hbody Hvalues.
    apply (derived_clause prim s I2 c e r args vs Hin Hhead); [| exact Hvalues].
    clear Hin Hhead Hvalues.
    induction Hbody as [| p ps Hp Hps IHps]; [constructor |].
    destruct p as [r' args' | f args' v | q args' v]; cbn in Hp.
    + destruct Hp as [vs' [Hvalues' Hrow]].
      exact (derived_row prim s I2 e r' args' vs' ps Hvalues' Hrow IHps).
    + contradiction.
    + destruct Hp as [vs' [w [Hvalues' [Hprim Hvalue]]]].
      exact (derived_computes prim s I2 e q args' v vs' w ps Hvalues' Hprim Hvalue IHps).
Qed.

(** * Represented terms *)

(** A term that a cell represents in a view means, in a model of the view, what the cell
    means. *)
Lemma represents_denote {V : Type} (merge : positive -> V -> V -> V) (M : @model V)
    (nu : positive -> carrier M) (w : @view V) :
  sat merge M nu w -> forall c t, represents w c t -> den nu c = denote M t.
Proof.
  intros [Hrows [Hsame _]].
  fix IH 3.
  intros c t Hrep.
  destruct Hrep as [v | f k i j args Hrow Hij Hargs].
  - reflexivity.
  - cbn [den denote].
    pose proof (Hrows f k (Some (Id j)) Hrow) as Hholds.
    unfold holds in Hholds.
    destruct (kind w f) as [[| |m] |]; try contradiction.
    rewrite (Hsame i j Hij), <- Hholds.
    f_equal. f_equal.
    clear Hrow Hij Hholds.
    induction Hargs as [| c t k' args' Hc Hrest IHrest]; [reflexivity |].
    cbn [map]. rewrite (IH c t Hc), IHrest. reflexivity.
Qed.

(** An environment that binds the variables 1 to n to a list of n values. *)
Definition env_of {V : Type} (vs : list V) (x : positive) : option V :=
  nth_error vs (Pos.to_nat x - 1).
