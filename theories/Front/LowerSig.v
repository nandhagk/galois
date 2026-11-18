(** * Lowering specifications to engine programs

    Each clause becomes one engine rule. Its premises become query atoms, and its head becomes
    actions that build each constructor term ([Make]) and each primitive value ([Let]) before
    the last action, which puts a row, puts a lattice value or joins two classes. A rewrite
    matches its left side in the query and joins it with its built right side. An equation
    premise [f x1 .. xn = y] defines [y] by a [Let] when no table atom binds [y], and every
    other primitive premise is a [Prim] check after the table atoms. Fresh variables follow the
    largest variable of the clause.

    For example, the clause [Holds copy [x; y], Holds points_to [y; a] => Derive points_to
    [x; a]] lowers to the rule with query [copy(x, y), points_to(y, a)] and the one action
    [Put points_to [x; a]].

    Builds on: the specifications and the Egglog syntax. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax Model.
From Galois.Front Require Import Spec.

Import List.ListNotations.

Local Open Scope positive_scope.

Section Lower.
Context {V : Type}.

(** * Variables *)

(** The largest variable of a pattern, at least 1. *)
Fixpoint pat_top (p : pat V) : positive :=
  match p with
  | PVar x => x
  | PVal _ => 1
  | PNode _ args | POp _ args =>
      (fix tops (ps : list (pat V)) : positive :=
         match ps with
         | [] => 1
         | p :: rest => Pos.max (pat_top p) (tops rest)
         end) args
  end.

(** The largest variable of a list of patterns, at least 1. *)
Definition pats_top (ps : list (pat V)) : positive :=
  fold_right (fun p m => Pos.max (pat_top p) m) 1 ps.

(** The largest variable of a premise. *)
Definition premise_top (p : premise V) : positive :=
  match p with
  | Holds _ args => pats_top args
  | Equals _ args v | Computes _ args v => Pos.max (pats_top args) (pat_top v)
  end.

(** The largest variable of a head. *)
Definition head_top (h : consequence V) : positive :=
  match h with
  | Derive _ args => pats_top args
  | Assign _ args v => Pos.max (pats_top args) (pat_top v)
  | Unify l r | Rewrites l r => Pos.max (pat_top l) (pat_top r)
  end.

(** The first fresh variable of a clause. *)
Definition clause_fresh (c : clause V) : positive :=
  Pos.succ (fold_right (fun p m => Pos.max (premise_top p) m) (head_top (head c)) (body c)).

(** * Actions *)

(** The actions that build the subterms of a pattern, its engine term and the next fresh
    variable. *)
Fixpoint build_pat (next : positive) (p : pat V) : list (action V) * term V * positive :=
  match p with
  | PVar x => ([], Var x, next)
  | PVal v => ([], Lit v, next)
  | PNode f args =>
      let '(acts, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (action V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := build_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (acts ++ [Make n f ts], Var n, Pos.succ n)
  | POp q args =>
      let '(acts, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (action V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := build_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (acts ++ [Let n q ts], Var n, Pos.succ n)
  end.

(** [build_pat] over a list of patterns. *)
Fixpoint build_pats (next : positive) (ps : list (pat V)) :
    list (action V) * list (term V) * positive :=
  match ps with
  | [] => ([], [], next)
  | p :: rest =>
      let '(a1, t, n1) := build_pat next p in
      let '(a2, ts, n2) := build_pats n1 rest in
      (a1 ++ a2, t :: ts, n2)
  end.

(** * Queries *)

(** The atoms that bind the subterms of a pattern in a query, the engine term of the pattern
    and the next fresh variable. *)
Fixpoint query_pat (next : positive) (p : pat V) : list (atom V) * term V * positive :=
  match p with
  | PVar x => ([], Var x, next)
  | PVal v => ([], Lit v, next)
  | PNode f args =>
      let '(atoms, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (atom V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := query_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (atoms ++ [Fun V f ts (Some (Var n))], Var n, Pos.succ n)
  | POp q args =>
      let '(atoms, ts, n) :=
        (fix go (next : positive) (ps : list (pat V)) :
            list (atom V) * list (term V) * positive :=
           match ps with
           | [] => ([], [], next)
           | p :: rest =>
               let '(a1, t, n1) := query_pat next p in
               let '(a2, ts, n2) := go n1 rest in
               (a1 ++ a2, t :: ts, n2)
           end) next args in
      (atoms ++ [Prim V q ts (Var n)], Var n, Pos.succ n)
  end.

(** [query_pat] over a list of patterns. *)
Fixpoint query_pats (next : positive) (ps : list (pat V)) :
    list (atom V) * list (term V) * positive :=
  match ps with
  | [] => ([], [], next)
  | p :: rest =>
      let '(a1, t, n1) := query_pat next p in
      let '(a2, ts, n2) := query_pats n1 rest in
      (a1 ++ a2, t :: ts, n2)
  end.

(** The atoms of a premise and the next fresh variable. *)
Definition query_premise (next : positive) (p : premise V) : list (atom V) * positive :=
  match p with
  | Holds r args =>
      let '(a, ts, n) := query_pats next args in (a ++ [Fun V r ts None], n)
  | Equals f args v =>
      let '(a1, ts, n1) := query_pats next args in
      let '(a2, t, n2) := query_pat n1 v in
      (a1 ++ a2 ++ [Fun V f ts (Some t)], n2)
  | Computes q args v =>
      let '(a1, ts, n1) := query_pats next args in
      let '(a2, t, n2) := query_pat n1 v in
      (a1 ++ a2 ++ [Prim V q ts t], n2)
  end.


(** The variables that the table atoms of a pattern bind, outside primitive applications. *)
Fixpoint pat_bound (p : pat V) : list positive :=
  match p with
  | PVar x => [x]
  | PVal _ | POp _ _ => []
  | PNode _ args =>
      (fix go (ps : list (pat V)) : list positive :=
         match ps with
         | [] => []
         | p :: rest => pat_bound p ++ go rest
         end) args
  end.

(** The variables that the table atoms of a body bind. *)
Definition body_bound (ps : list (premise V)) : list positive :=
  flat_map (fun p =>
    match p with
    | Holds _ args => flat_map pat_bound args
    | Equals _ args v => flat_map pat_bound args ++ pat_bound v
    | Computes _ _ _ => []
    end) ps.

(** The query of a body, the actions that define the variables of its equations, and the next
    fresh variable. An equation [f x1 .. xn = y] defines [y] by a [Let] when [y] is not in
    [bound], and [y] is bound for the premises after it. Every other premise gives query
    atoms. *)
Fixpoint query_body (bound : list positive) (next : positive) (ps : list (premise V)) :
    list (atom V) * list (action V) * positive :=
  match ps with
  | [] => ([], [], next)
  | Computes q args (PVar y) :: rest =>
      if existsb (Pos.eqb y) bound then
        let '(a1, n1) := query_premise next (Computes q args (PVar y)) in
        let '(a2, acts, n2) := query_body bound n1 rest in
        (a1 ++ a2, acts, n2)
      else
        let '(a1, ts, n1) := build_pats next args in
        let '(a2, acts, n2) := query_body (y :: bound) n1 rest in
        (a2, a1 ++ Let y q ts :: acts, n2)
  | p :: rest =>
      let '(a1, n1) := query_premise next p in
      let '(a2, acts, n2) := query_body bound n1 rest in
      (a1 ++ a2, acts, n2)
  end.

(** * Rules *)

(** The table atoms of a query, then its [Prim] checks, which need the variables that the table
    atoms bind. *)
Definition checks_last (q : list (atom V)) : list (atom V) :=
  filter (fun a => match a with Fun _ _ _ _ => true | Prim _ _ _ _ => false end) q ++
  filter (fun a => match a with Fun _ _ _ _ => false | Prim _ _ _ _ => true end) q.

(** The engine rule of a clause. The query matches the premises and the left side of a
    rewrite. The actions define the values of the equations, build the terms of the head, and
    then put its row or lattice value or join its two sides. *)
Definition clause_rule (c : clause V) : rule V :=
  let left := match head c with Rewrites l _ => pat_bound l | _ => [] end in
  let '(q, lets, n1) := query_body (body_bound (body c) ++ left) (clause_fresh c) (body c) in
  match head c with
  | Derive r args =>
      let '(acts, ts, _) := build_pats n1 args in
      Rule V (checks_last q) (lets ++ acts ++ [Put r ts None])
  | Assign f args v =>
      let '(a1, ts, n2) := build_pats n1 args in
      let '(a2, t, _) := build_pat n2 v in
      Rule V (checks_last q) (lets ++ a1 ++ a2 ++ [Put f ts (Some t)])
  | Unify l r =>
      let '(a1, tl, n2) := build_pat n1 l in
      let '(a2, tr, _) := build_pat n2 r in
      Rule V (checks_last q) (lets ++ a1 ++ a2 ++ [Union tl tr])
  | Rewrites l r =>
      let '(lq, tl, n2) := query_pat n1 l in
      let '(acts, tr, _) := build_pat n2 r in
      Rule V (checks_last (q ++ lq)) (lets ++ acts ++ [Union tl tr])
  end.

(** * Programs *)

(** The engine rules of a specification, one for each clause in clause order. *)
Definition spec_rules (s : spec V) : list (rule V) := map clause_rule (clauses s).

(** The engine program of a specification. *)
Definition spec_program (s : spec V) : program V := Program V (tables s) (spec_rules s).

End Lower.

(** * Laws *)

(** The rows of values without output of a view, as a relation. *)
Definition view_rows {V} (w : @view V) (r : positive) (vs : list V) : Prop :=
  row w r (map Val vs) None.

Module Type LOWER_LAWS.
  (** A row that the lowered relational program derives from value rows of input tables is a
      derived row of the specification. *)
  Parameter lower_sound : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r k,
    relational_fragment (spec_program s) = true ->
    (forall r' k' o', row w0 r' k' o' ->
      In r' (inputs s) /\ o' = None /\ exists vs, k' = map Val vs) ->
    derives prim (spec_program s) w0 r k ->
    exists vs, k = map Val vs /\ derived prim s (view_rows w0) r vs.
  (** A derived row of a relational specification is derived by its lowered program. *)
  Parameter lower_complete : forall {V} (prim : positive -> list V -> option V) (s : spec V)
      (w0 : @view V) r vs,
    relational_fragment (spec_program s) = true ->
    derived prim s (view_rows w0) r vs -> derives prim (spec_program s) w0 r (map Val vs).
End LOWER_LAWS.
