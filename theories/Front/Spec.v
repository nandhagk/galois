(** * Specifications as programs

    A specification is the deep embedding of the inductives that an engine program is read
    from. It lists the tables, the input tables, and one clause per constructor, each with a
    body of premises and one head. Relational clauses mean the least relation that contains the
    input rows and is closed under them ([derived]). Equational clauses mean the least congruence
    that contains their instances whose bodies hold in the inputs ([congruent]). Every clause also
    has a meaning in the models of the engine ([satisfies]), which the theorems about rewrites
    and lattice tables use.

    For example, the constructor [path_step x y z : path x y -> edge y z -> path x z] is the
    clause with body [Holds path [PVar x; PVar y]; Holds edge [PVar y; PVar z]] and head
    [Derive path [PVar x; PVar z]].

    Builds on: Egglog Syntax and Model. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.

Import List.ListNotations.

(** * Embedding *)

(** A pattern over the variables of a clause: a variable, a value, a constructor of a
    datatype, or a primitive operation on values. *)
Inductive pat (V : Type) : Type :=
  | PVar (x : positive)
  | PVal (v : V)
  | PNode (f : positive) (args : list (pat V))
  | POp (p : positive) (args : list (pat V)).

Arguments PVar {V}.
Arguments PVal {V}.
Arguments PNode {V}.
Arguments POp {V}.

(** A premise reads a row of a relation, the value of a lattice table, or the result of a
    primitive. *)
Inductive premise (V : Type) : Type :=
  | Holds (r : positive) (args : list (pat V))
  | Equals (f : positive) (args : list (pat V)) (v : pat V)
  | Computes (p : positive) (args : list (pat V)) (v : pat V).

Arguments Holds {V}.
Arguments Equals {V}.
Arguments Computes {V}.

(** A consequence adds a row, joins a value into a lattice table, merges two built terms, or
    merges a matched term with a built one. *)
Inductive consequence (V : Type) : Type :=
  | Derive (r : positive) (args : list (pat V))
  | Assign (f : positive) (args : list (pat V)) (v : pat V)
  | Unify (l r : pat V)
  | Rewrites (l r : pat V).

Arguments Derive {V}.
Arguments Assign {V}.
Arguments Unify {V}.
Arguments Rewrites {V}.

(** One constructor of an inductive: its premises and its conclusion. *)
Record clause (V : Type) : Type := Clause {
  body : list (premise V);
  head : consequence V
}.

Arguments Clause {V}.
Arguments body {V}.
Arguments head {V}.

(** The tables with their sorts and outputs, the tables whose rows come from the input, and
    the clauses. *)
Record spec (V : Type) : Type := Spec {
  tables : list decl;
  inputs : list positive;
  clauses : list (clause V)
}.

Arguments Spec {V}.
Arguments tables {V}.
Arguments inputs {V}.
Arguments clauses {V}.

(** * Meaning *)

Section Meaning.
Context {V : Type} (prim : positive -> list V -> option V).

(** ** Values *)

(** The value of a pattern without constructors, with primitives applied. *)
Fixpoint pat_value (e : positive -> option V) (p : pat V) : option V :=
  match p with
  | PVar x => e x
  | PVal v => Some v
  | PNode _ _ => None
  | POp q args =>
      match (fix values (ps : list (pat V)) : option (list V) :=
               match ps with
               | [] => Some []
               | p :: rest =>
                   match pat_value e p, values rest with
                   | Some v, Some vs => Some (v :: vs)
                   | _, _ => None
                   end
               end) args with
      | Some vs => prim q vs
      | None => None
      end
  end.

(** The values of a list of patterns, when each has one. *)
Fixpoint pat_values (e : positive -> option V) (ps : list (pat V)) : option (list V) :=
  match ps with
  | [] => Some []
  | p :: rest =>
      match pat_value e p, pat_values e rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** ** Relations *)

(** The least relation that contains the input rows [I] of the input tables and is closed
    under the clauses whose heads derive rows. *)
Inductive derived (s : spec V) (I : positive -> list V -> Prop) : positive -> list V -> Prop :=
  | derived_input r vs : In r (inputs s) -> I r vs -> derived s I r vs
  | derived_clause c e r args vs : In c (clauses s) -> head c = Derive r args ->
      derived_body s I e (body c) -> pat_values e args = Some vs -> derived s I r vs
with derived_body (s : spec V) (I : positive -> list V -> Prop) :
    (positive -> option V) -> list (premise V) -> Prop :=
  | derived_nil e : derived_body s I e []
  | derived_row e r args vs rest : pat_values e args = Some vs -> derived s I r vs ->
      derived_body s I e rest -> derived_body s I e (Holds r args :: rest)
  | derived_computes e q args v vs w rest : pat_values e args = Some vs ->
      prim q vs = Some w ->
      pat_value e v = Some w -> derived_body s I e rest ->
      derived_body s I e (Computes q args v :: rest).

(** The values that the clauses join into a lattice table at a key, from bodies that read
    relations and primitives. *)
Inductive assigned (s : spec V) (I : positive -> list V -> Prop) :
    positive -> list V -> V -> Prop :=
  | assigned_clause c e f args v ks w : In c (clauses s) -> head c = Assign f args v ->
      derived_body s I e (body c) -> pat_values e args = Some ks -> pat_value e v = Some w ->
      assigned s I f ks w.

(** ** Terms *)

(** The term of a pattern. A primitive applies to arguments that are all literals. *)
Fixpoint pat_term (e : positive -> option (@expr V)) (p : pat V) : option (@expr V) :=
  match p with
  | PVar x => e x
  | PVal v => Some (ELit v)
  | PNode f args =>
      match (fix terms (ps : list (pat V)) : option (list (@expr V)) :=
               match ps with
               | [] => Some []
               | p :: rest =>
                   match pat_term e p, terms rest with
                   | Some t, Some ts => Some (t :: ts)
                   | _, _ => None
                   end
               end) args with
      | Some ts => Some (EApp f ts)
      | None => None
      end
  | POp q args =>
      match (fix literals (ps : list (pat V)) : option (list V) :=
               match ps with
               | [] => Some []
               | p :: rest =>
                   match pat_term e p, literals rest with
                   | Some (ELit v), Some vs => Some (v :: vs)
                   | _, _ => None
                   end
               end) args with
      | Some vs =>
          match prim q vs with
          | Some v => Some (ELit v)
          | None => None
          end
      | None => None
      end
  end.

(** The literal values of a list of patterns, when each is a literal term. *)
Fixpoint pat_literals (e : positive -> option (@expr V)) (ps : list (pat V)) :
    option (list V) :=
  match ps with
  | [] => Some []
  | p :: rest =>
      match pat_term e p, pat_literals e rest with
      | Some (ELit v), Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

(** A body that reads only input rows and primitives holds in the input rows [I]. *)
Definition input_premise (I : positive -> list V -> Prop) (e : positive -> option (@expr V))
    (p : premise V) : Prop :=
  match p with
  | Holds r args => exists vs, pat_literals e args = Some vs /\ I r vs
  | Equals _ _ _ => False
  | Computes q args v => exists vs w, pat_literals e args = Some vs /\ prim q vs = Some w /\
      pat_term e v = Some (ELit w)
  end.

(** The least congruence that contains each instance of an equational clause whose body
    holds in the input rows [I]. *)
Inductive congruent (s : spec V) (I : positive -> list V -> Prop) :
    @expr V -> @expr V -> Prop :=
  | congruent_refl t : congruent s I t t
  | congruent_sym t u : congruent s I t u -> congruent s I u t
  | congruent_trans t u w : congruent s I t u -> congruent s I u w -> congruent s I t w
  | congruent_cong f ts us : Forall2 (congruent s I) ts us ->
      congruent s I (EApp f ts) (EApp f us)
  | congruent_clause c e l r tl tr : In c (clauses s) ->
      (head c = Unify l r \/ head c = Rewrites l r) ->
      Forall (input_premise I e) (body c) -> pat_term e l = Some tl -> pat_term e r = Some tr ->
      congruent s I tl tr.

(** One step of rewriting: an instance of a rewrite clause whose body holds in [I]. *)
Inductive rewrite_step (s : spec V) (I : positive -> list V -> Prop) :
    @expr V -> @expr V -> Prop :=
  | rewrite_step_clause c e l r tl tr : In c (clauses s) -> head c = Rewrites l r ->
      Forall (input_premise I e) (body c) -> pat_term e l = Some tl -> pat_term e r = Some tr ->
      rewrite_step s I tl tr.

(** ** Models *)

Section Models.
Variable (merge : positive -> V -> V -> V) (M : @model V).

(** The meaning of a pattern in [M]. *)
Fixpoint pat_meaning (e : positive -> option (carrier M + V)) (p : pat V) :
    option (carrier M + V) :=
  match p with
  | PVar x => e x
  | PVal v => Some (inr v)
  | PNode f args =>
      match (fix meanings (ps : list (pat V)) : option (list (carrier M + V)) :=
               match ps with
               | [] => Some []
               | p :: rest =>
                   match pat_meaning e p, meanings rest with
                   | Some x, Some xs => Some (x :: xs)
                   | _, _ => None
                   end
               end) args with
      | Some xs => Some (inl (con M f xs))
      | None => None
      end
  | POp q args =>
      match (fix plain (ps : list (pat V)) : option (list V) :=
               match ps with
               | [] => Some []
               | p :: rest =>
                   match pat_meaning e p, plain rest with
                   | Some (inr v), Some vs => Some (v :: vs)
                   | _, _ => None
                   end
               end) args with
      | Some vs =>
          match prim q vs with
          | Some v => Some (inr v)
          | None => None
          end
      | None => None
      end
  end.

(** The meanings of a list of patterns, when each has one. *)
Fixpoint pat_meanings (e : positive -> option (carrier M + V)) (ps : list (pat V)) :
    option (list (carrier M + V)) :=
  match ps with
  | [] => Some []
  | p :: rest =>
      match pat_meaning e p, pat_meanings e rest with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
  end.

(** A premise is true in [M] under [e]. *)
Definition premise_true (e : positive -> option (carrier M + V)) (p : premise V) : Prop :=
  match p with
  | Holds r args => exists xs, pat_meanings e args = Some xs /\ rel M r xs
  | Equals f args v => exists xs w, pat_meanings e args = Some xs /\
      pat_meaning e v = Some (inr w) /\ lat M f xs w
  | Computes q args v => exists vs w, pat_meanings e args = Some (map inr vs) /\
      prim q vs = Some w /\ pat_meaning e v = Some (inr w)
  end.

(** A head is true in [M] under [e]. *)
Definition head_true (e : positive -> option (carrier M + V)) (h : consequence V) : Prop :=
  match h with
  | Derive r args => exists xs, pat_meanings e args = Some xs /\ rel M r xs
  | Assign f args v => exists xs w, pat_meanings e args = Some xs /\
      pat_meaning e v = Some (inr w) /\ lat M f xs w
  | Unify l r => exists x, pat_meaning e l = Some x /\ pat_meaning e r = Some x
  | Rewrites l r => exists x, pat_meaning e l = Some x /\ pat_meaning e r = Some x
  end.

(** [M] is a model of [s] over the input rows [I]: the input rows hold, every clause holds
    under every environment, and each lattice table is closed under its merge. *)
Definition satisfies (s : spec V) (I : positive -> list V -> Prop) : Prop :=
  (forall r vs, In r (inputs s) -> I r vs -> rel M r (map inr vs)) /\
  (forall c e, In c (clauses s) -> Forall (premise_true e) (body c) -> head_true e (head c)) /\
  (forall f m k a b, lookup_kind (tables s) f = Some (OLat m) ->
    lat M f k a -> lat M f k b -> lat M f k (merge m a b)).

End Models.

End Meaning.
