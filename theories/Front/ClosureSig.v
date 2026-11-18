(** * The reference congruence closure

    The congruence closure of finitely many equations between expressions, computed on the
    finite set of their terms and subterms, called the universe. A class is a set of positions
    of the universe with one representative position. The classes start from the equations and
    grow by passes that merge two applications of one constructor whose arguments are in one
    class each, until a pass merges nothing. The normal form of an expression is then the
    representative of its class when it is congruent to a term of the universe, and the
    application of its constructor to the normal forms of its arguments otherwise. Two
    expressions have one normal form exactly when the closure equates them, which gives a model
    of the closure without a quotient. The proofs use the code, and the tests in
    [tests/Front/ClosureTest.v] run it.
    For example, with the one equation [f(a) = b], the normal forms of [g(f(a))] and [g(b)] are
    one expression, and [g(a)] keeps its own.

    Main results
    - [rep_of_sound], [rep_of_eqs], [rep_of_cong] The classes are inside the closure, and they
      contain the equations and are closed under congruence on the universe.
    - [nf_universe], [nf_app], [nf_sound] Normal forms extend the classes to all expressions,
      and one normal form means one class of the closure.
    - [closure_model] The closure of equations between applications is the equality of a
      model.

    Builds on: the expressions and models of the engine. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model.

Import List.ListNotations.

(** * Closure *)

(** The least congruence that contains listed equations. *)
Inductive closure {V} (eqs : list (@expr V * @expr V)) : @expr V -> @expr V -> Prop :=
  | closure_eq t u : In (t, u) eqs -> closure eqs t u
  | closure_refl t : closure eqs t t
  | closure_sym t u : closure eqs t u -> closure eqs u t
  | closure_trans t u w : closure eqs t u -> closure eqs u w -> closure eqs t w
  | closure_cong f ts us : Forall2 (closure eqs) ts us -> closure eqs (EApp f ts) (EApp f us).

(** Every equation is between two applications. *)
Definition apps_only {V} (eqs : list (@expr V * @expr V)) : Prop :=
  Forall (fun tu => (exists f ts, fst tu = EApp f ts) /\ (exists g us, snd tu = EApp g us)) eqs.

(** * Code *)

Section Code.
Context {V : Type} (eqb : V -> V -> bool).

(** Equality of expressions, with [eqb] at literals. *)
Fixpoint expr_eqb (t u : @expr V) : bool :=
  match t, u with
  | ELit v, ELit w => eqb v w
  | EApp f ts, EApp g us =>
      Pos.eqb f g &&
      (fix go (ts us : list (@expr V)) : bool :=
         match ts, us with
         | [], [] => true
         | t :: ts', u :: us' => expr_eqb t u && go ts' us'
         | _, _ => false
         end) ts us
  | _, _ => false
  end.

(** Equality of lists of expressions. *)
Fixpoint exprs_eqb (ts us : list (@expr V)) : bool :=
  match ts, us with
  | [], [] => true
  | t :: ts', u :: us' => expr_eqb t u && exprs_eqb ts' us'
  | _, _ => false
  end.

(** The subterms of an expression, with those of each argument before the expression. *)
Fixpoint subterms (t : @expr V) : list (@expr V) :=
  match t with
  | ELit _ => [t]
  | EApp _ ts =>
      (fix go (ts : list (@expr V)) : list (@expr V) :=
         match ts with
         | [] => []
         | u :: rest => subterms u ++ go rest
         end) ts ++ [t]
  end.

(** The first position of an expression in a list. *)
Fixpoint position (t : @expr V) (ts : list (@expr V)) : option nat :=
  match ts with
  | [] => None
  | u :: rest => if expr_eqb t u then Some 0 else option_map S (position t rest)
  end.

(** The list with each expression once, at its last occurrence. *)
Fixpoint dedup (ts : list (@expr V)) : list (@expr V) :=
  match ts with
  | [] => []
  | t :: rest => if existsb (expr_eqb t) rest then dedup rest else t :: dedup rest
  end.

(** The universe of equations, with their two sides and all their subterms, each once. *)
Definition universe (eqs : list (@expr V * @expr V)) : list (@expr V) :=
  dedup (flat_map (fun tu => subterms (fst tu) ++ subterms (snd tu)) eqs).

(** The representative position of a position. *)
Definition rep_at (reps : list nat) (i : nat) : nat := nth i reps i.

(** Merge the class of position [j] into the class of position [i]. *)
Definition merge_at (reps : list nat) (i j : nat) : list nat :=
  let ri := rep_at reps i in
  let rj := rep_at reps j in
  map (fun r => if Nat.eqb r rj then ri else r) reps.

(** The arguments of two applications are in one class each. *)
Fixpoint args_agree (U : list (@expr V)) (reps : list nat) (ts us : list (@expr V)) : bool :=
  match ts, us with
  | [], [] => true
  | t :: ts', u :: us' =>
      match position t U, position u U with
      | Some a, Some b => Nat.eqb (rep_at reps a) (rep_at reps b) && args_agree U reps ts' us'
      | _, _ => false
      end
  | _, _ => false
  end.

(** Two positions hold applications of one constructor whose arguments are in one class
    each. *)
Definition congruent_at (U : list (@expr V)) (reps : list nat) (i j : nat) : bool :=
  match nth_error U i, nth_error U j with
  | Some (EApp f ts), Some (EApp g us) => Pos.eqb f g && args_agree U reps ts us
  | _, _ => false
  end.

(** All pairs of positions below [n]. *)
Definition pairs (n : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq 0 n)) (seq 0 n).

(** One pass merges each pair of positions in two classes that are congruent in the classes so
    far. *)
Definition pass (U : list (@expr V)) (reps : list nat) : list nat :=
  fold_left (fun reps ij =>
    if negb (Nat.eqb (rep_at reps (fst ij)) (rep_at reps (snd ij))) &&
       congruent_at U reps (fst ij) (snd ij)
    then merge_at reps (fst ij) (snd ij)
    else reps) (pairs (length U)) reps.

(** Equality of lists of positions. *)
Fixpoint nats_eqb (ns ms : list nat) : bool :=
  match ns, ms with
  | [], [] => true
  | n :: ns', m :: ms' => Nat.eqb n m && nats_eqb ns' ms'
  | _, _ => false
  end.

(** The classes of the equations alone. Each position is its own class, and then the two sides
    of each equation are merged. *)
Definition seed_classes (U : list (@expr V)) (eqs : list (@expr V * @expr V)) : list nat :=
  fold_left (fun reps tu =>
    match position (fst tu) U, position (snd tu) U with
    | Some a, Some b => merge_at reps a b
    | _, _ => reps
    end) eqs (seq 0 (length U)).

(** Passes until one merges nothing. Each other pass merges two classes, so the fuel of one
    pass for each position suffices. *)
Fixpoint close_classes (U : list (@expr V)) (fuel : nat) (reps : list nat) : list nat :=
  match fuel with
  | O => reps
  | S fuel' =>
      let next := pass U reps in
      if nats_eqb next reps then reps else close_classes U fuel' next
  end.

(** The classes of the closure, as the representative position of each position of the
    universe. *)
Definition classes (eqs : list (@expr V * @expr V)) : list nat :=
  let U := universe eqs in
  close_classes U (length U) (seed_classes U eqs).

(** The representative of an expression in the classes [reps] of [U], and the expression
    itself outside [U]. *)
Definition rep_in (U : list (@expr V)) (reps : list nat) (t : @expr V) : @expr V :=
  match position t U with
  | Some i => nth (rep_at reps i) U t
  | None => t
  end.

(** The representative of an expression in the closure of the equations. *)
Definition rep_of (eqs : list (@expr V * @expr V)) (t : @expr V) : @expr V :=
  rep_in (universe eqs) (classes eqs) t.

(** The normal form of an expression in the classes [reps] of [U]. An application whose
    arguments have the representatives of the arguments of a term of [U] has the representative
    of that term, and any other application is itself over the normal forms of its
    arguments. *)
Fixpoint nf_in (U : list (@expr V)) (reps : list nat) (t : @expr V) : @expr V :=
  match t with
  | ELit _ => rep_in U reps t
  | EApp f ts =>
      let ns :=
        (fix go (ts : list (@expr V)) : list (@expr V) :=
           match ts with
           | [] => []
           | u :: rest => nf_in U reps u :: go rest
           end) ts in
      match find (fun u =>
               match u with
               | EApp g us => Pos.eqb f g && exprs_eqb (map (rep_in U reps) us) ns
               | ELit _ => false
               end) U with
      | Some u => rep_in U reps u
      | None => EApp f ns
      end
  end.

(** The normal form of an expression in the closure of the equations. *)
Definition nf (eqs : list (@expr V * @expr V)) (t : @expr V) : @expr V :=
  nf_in (universe eqs) (classes eqs) t.

End Code.

(** * Proof plan *)

(** The classes of the closure. *)
Module Type CLOSURE_CLASSES (V : VALUE).
  (** The universe holds both sides of each equation. *)
  Parameter universe_eqs : forall eqs t u, In (t, u) eqs ->
    In t (universe V.eqb eqs) /\ In u (universe V.eqb eqs).
  (** The universe holds the arguments of each of its applications. *)
  Parameter universe_args : forall eqs f ts t, In (EApp f ts) (universe V.eqb eqs) -> In t ts ->
    In t (universe V.eqb eqs).
  (** The representative of a term of the universe is a term of the universe and its own
      representative. *)
  Parameter rep_of_universe : forall eqs t, In t (universe V.eqb eqs) ->
    In (rep_of V.eqb eqs t) (universe V.eqb eqs) /\
    rep_of V.eqb eqs (rep_of V.eqb eqs t) = rep_of V.eqb eqs t.
  (** Two expressions with one representative are equal in the closure. *)
  Parameter rep_of_sound : forall eqs t u, rep_of V.eqb eqs t = rep_of V.eqb eqs u ->
    closure eqs t u.
  (** The two sides of each equation have one representative. *)
  Parameter rep_of_eqs : forall eqs t u, In (t, u) eqs -> rep_of V.eqb eqs t = rep_of V.eqb eqs u.
  (** Two applications of one constructor in the universe whose arguments have one
      representative each have one representative. *)
  Parameter rep_of_cong : forall eqs f ts us,
    In (EApp f ts) (universe V.eqb eqs) -> In (EApp f us) (universe V.eqb eqs) ->
    Forall2 (fun t u => rep_of V.eqb eqs t = rep_of V.eqb eqs u) ts us ->
    rep_of V.eqb eqs (EApp f ts) = rep_of V.eqb eqs (EApp f us).
End CLOSURE_CLASSES.

(** The normal forms of the closure. *)
Module Type CLOSURE_FORMS (V : VALUE).
  (** A term of the universe has its representative as normal form. *)
  Parameter nf_universe : forall eqs t, In t (universe V.eqb eqs) ->
    nf V.eqb eqs t = rep_of V.eqb eqs t.
  (** The normal form of an application depends only on the normal forms of its arguments. *)
  Parameter nf_app : forall eqs f ts,
    nf V.eqb eqs (EApp f ts) = nf V.eqb eqs (EApp f (map (nf V.eqb eqs) ts)).
  (** A literal outside the universe is its own normal form. *)
  Parameter nf_lit : forall eqs v, ~ In (ELit v) (universe V.eqb eqs) ->
    nf V.eqb eqs (ELit v) = ELit v.
  (** Two expressions with one normal form are equal in the closure. *)
  Parameter nf_sound : forall eqs t u, nf V.eqb eqs t = nf V.eqb eqs u -> closure eqs t u.
End CLOSURE_FORMS.

(** The model of the closure. *)
Module Type CLOSURE_MODEL (V : VALUE).
  (** The closure of finitely many equations between applications is the equality of a model
      whose relations hold exactly of the rows of a given relation on values, and whose
      lattice tables are empty. *)
  Parameter closure_model : forall (eqs : list (@expr V.t * @expr V.t))
      (P : positive -> list V.t -> Prop),
    apps_only eqs ->
    exists M : @model V.t, (forall t u, denote M t = denote M u <-> closure eqs t u) /\
      (forall r xs, rel M r xs <-> exists vs, xs = map inr vs /\ P r vs) /\
      (forall f xs v, ~ lat M f xs v).
End CLOSURE_MODEL.
