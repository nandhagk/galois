(** * Relational state dictionaries

    Relational operations close states, forget variables and rename finite information.
    For example, an injective shift leaves new coordinates unconstrained.
    Builds on: DomainsState and DomainsTerm. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState.
Import Cost.Notations.

Module Relational.

(** Relational callbacks retain their own charges and need no semantic evidence to run. *)
Record t (S A X K G : Type) := Make {
  state : StateAbs.t S A X K G;
  closure_c : S -> Cost.t S;
  forget_all_c : list X -> S -> Cost.t S;
  rename_c : (X -> Cost.t X) -> S -> Cost.t S;
  project_term_c : term K X -> S -> Cost.t A
}.

Arguments state {S A X K G}.
Arguments closure_c {S A X K G}.
Arguments forget_all_c {S A X K G}.
Arguments rename_c {S A X K G}.
Arguments project_term_c {S A X K G}.

Definition closure {S A X K G} (D : t S A X K G) s :=
  Cost.value (closure_c D s).

Definition forget_all {S A X K G} (D : t S A X K G) xs s :=
  Cost.value (forget_all_c D xs s).

Definition rename {S A X K G} (D : t S A X K G) f s :=
  Cost.value (rename_c D f s).

Definition project_term {S A X K G} (D : t S A X K G) e s :=
  Cost.value (project_term_c D e s).

(** Forgetting visits the supplied occurrences in order, including duplicates. *)
Definition forget_c {S A X K G} (D : StateAbs.t S A X K G) xs s :=
  fold_left_c (fun s x => Cost.step ;; StateAbs.havoc_c D x s) xs s.

(** The charged forgetting operation is repeated state havoc. *)
Theorem forget_equation {S A X K G} (D : StateAbs.t S A X K G) xs s :
  Cost.value (forget_c D xs s) = fold_left (fun s x => StateAbs.havoc D x s) xs s.
Proof.
  unfold forget_c. rewrite value_fold_left_c. reflexivity.
Qed.

(** A renaming is injective on its observed values independently of callback costs. *)
Definition injective {X} (f : X -> Cost.t X) :=
  forall x y, Cost.value (f x) = Cost.value (f y) -> x = y.

(** Push agreement fixes image coordinates and imposes no condition on fresh coordinates. *)
Definition push_agrees {X C} (f : X -> Cost.t X) (old new : X -> C) :=
  forall x, new (Cost.value (f x)) = old x.

End Relational.

(** Relational laws give closure equivalence, ordered forgetting and injective push/pull meaning. *)
Record relational_laws {S A X K G C} (D : Relational.t S A X K G)
    (M : ValueSem.t C K G) (SM : StateSem.t X C)
    (gam : concretisation A C) (gs : concretisation S (X -> C)) : Prop := {
  relational_state_laws : state_laws (Relational.state D) M SM gam gs;
  closure_meaning : forall s st,
    gamma gs (Relational.closure D s) st <-> gamma gs s st;
  closure_below : forall s,
    leb (StateAbs.lat (Relational.state D)) (Relational.closure D s) s = true;
  forget_all_equation : forall xs s, Relational.forget_all D xs s =
    fold_left (fun s x => StateAbs.havoc (Relational.state D) x s) xs s;
  rename_push : forall f s old new, Relational.injective f ->
    Relational.push_agrees f old new -> gamma gs s old ->
    gamma gs (Relational.rename D f s) new;
  rename_pull : forall f s new, Relational.injective f ->
    (gamma gs (Relational.rename D f s) new <->
      gamma gs s (fun x => new (Cost.value (f x))));
  project_term_sound : forall e s st c, gamma gs s st ->
    eval_term (ValueSem.eval M) st e = Some c ->
    gamma gam (Relational.project_term D e s) c
}.

Arguments relational_state_laws {S A X K G C D M SM gam gs}.
Arguments closure_meaning {S A X K G C D M SM gam gs}.
Arguments closure_below {S A X K G C D M SM gam gs}.
Arguments forget_all_equation {S A X K G C D M SM gam gs}.
Arguments rename_push {S A X K G C D M SM gam gs}.
Arguments rename_pull {S A X K G C D M SM gam gs}.
Arguments project_term_sound {S A X K G C D M SM gam gs}.

(** Repeated forgetting describes every ordered sequence of concrete replacements. *)
Theorem forget_all_sound {S A X K G C} (D : Relational.t S A X K G)
    (M : ValueSem.t C K G) (SM : StateSem.t X C) gam gs
    (H : relational_laws D M SM gam gs) xs (choose : X -> C) s st :
  gamma gs s st ->
  gamma gs (Relational.forget_all D xs s)
    (fold_left (fun st x => StateSem.update SM x (choose x) st) xs st).
Proof.
  rewrite (forget_all_equation H). revert s st.
  induction xs as [|x xs IH]; intros s st Henv; [exact Henv|].
  cbn [fold_left]. apply IH.
  exact (havoc_sound _ _ _ _ _ (relational_state_laws H) x s st (choose x) Henv).
Qed.
