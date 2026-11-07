(** * State-domain contracts

    State transfers describe variable maps through assignments, havoc and guards.
    For example, havoc retains every concrete replacement of one variable.
    Builds on: DomainsValue and DomainsTerm. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Domains Require Import DomainsValue DomainsTerm.

Module StateAbs.

(** A state dictionary runs independently of concrete semantics and semantic laws. *)
Record t (S A X K G : Type) : Type := Make {
  lat : lattice S;
  top : S;
  assign_c : X -> term K X -> S -> Cost.t S;
  havoc_c : X -> S -> Cost.t S;
  assume_c : G -> list (term K X) -> S -> Cost.t S;
  project_c : X -> S -> Cost.t A
}.

Arguments lat {S A X K G}.
Arguments top {S A X K G}.
Arguments assign_c {S A X K G}.
Arguments havoc_c {S A X K G}.
Arguments assume_c {S A X K G}.
Arguments project_c {S A X K G}.

Definition assign {S A X K G} (D : t S A X K G) x e s := Cost.value (assign_c D x e s).
Definition havoc {S A X K G} (D : t S A X K G) x s := Cost.value (havoc_c D x s).
Definition assume {S A X K G} (D : t S A X K G) g ts s := Cost.value (assume_c D g ts s).
Definition project {S A X K G} (D : t S A X K G) x s := Cost.value (project_c D x s).

End StateAbs.

Module StateSem.

(** Concrete state updates are supplied independently of the abstract dictionary. *)
Record t (X C : Type) : Type := Make {
  update : X -> C -> (X -> C) -> X -> C
}.

Arguments update {X C}.

(** Updates change the selected variable and leave every other variable unchanged. *)
Record laws {X C} (D : t X C) : Prop := {
  update_same : forall x c st, update D x c st x = c;
  update_other : forall x y c st, x <> y -> update D x c st y = st y
}.

End StateSem.

(** State laws describe defined assignments, arbitrary havoc values and satisfying guards. *)
Record state_laws {S A X K G C} (SD : StateAbs.t S A X K G)
    (M : ValueSem.t C K G) (SM : StateSem.t X C)
    (gam : concretisation A C) (gs : concretisation S (X -> C)) : Prop := {
  state_lat_ok : lattice_laws (StateAbs.lat SD);
  state_gamma_ok : concretisation_laws (StateAbs.lat SD) gs;
  state_bot_empty : forall st, ~ gamma gs (bot (StateAbs.lat SD)) st;
  state_top_full : forall st, gamma gs (StateAbs.top SD) st;
  state_update_ok : StateSem.laws SM;
  assign_sound : forall x t s st c, gamma gs s st ->
    eval_term (ValueSem.eval M) st t = Some c ->
    gamma gs (StateAbs.assign SD x t s) (StateSem.update SM x c st);
  havoc_sound : forall x s st c, gamma gs s st ->
    gamma gs (StateAbs.havoc SD x s) (StateSem.update SM x c st);
  state_assume_sound : forall g ts s st cs, gamma gs s st ->
    sequence (map (eval_term (ValueSem.eval M) st) ts) = Some cs ->
    ValueSem.holds M g cs -> gamma gs (StateAbs.assume SD g ts s) st;
  project_sound : forall x s st, gamma gs s st -> gamma gam (StateAbs.project SD x s) (st x)
}.
