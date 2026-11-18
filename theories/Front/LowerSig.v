(** * Lowering specifications to engine programs

    A clause whose head derives a row, assigns a lattice value or unifies two built terms
    becomes an engine rule: its premises become query atoms, and its head becomes actions that
    build each constructor term ([Make]) and each primitive value ([Let]) before the last
    action. A clause whose head rewrites a matched term becomes an Egraph rewrite: the left
    side is the matched pattern, the right side the built pattern, and the premises the
    condition. Fresh variables follow the largest variable of the clause.

    For example, the clause [Holds copy [x; y], Holds points_to [y; a] => Derive points_to
    [x; a]] lowers to the rule with query [copy(x, y), points_to(y, a)] and the one action
    [Put points_to [x; a]].

    Builds on: the specifications, the Egglog syntax and the Egraph syntax. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import Syntax.
From Galois.Egraph Require Import Syntax.
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

(** The query of a body and the next fresh variable. *)
Fixpoint query_body (next : positive) (ps : list (premise V)) : list (atom V) * positive :=
  match ps with
  | [] => ([], next)
  | p :: rest =>
      let '(a1, n1) := query_premise next p in
      let '(a2, n2) := query_body n1 rest in
      (a1 ++ a2, n2)
  end.

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

(** The actions of a head that the engine runs, or none for a rewrite. *)
Definition head_actions (next : positive) (h : consequence V) : option (list (action V)) :=
  match h with
  | Derive r args =>
      let '(acts, ts, _) := build_pats next args in Some (acts ++ [Put r ts None])
  | Assign f args v =>
      let '(a1, ts, n1) := build_pats next args in
      let '(a2, t, _) := build_pat n1 v in
      Some (a1 ++ a2 ++ [Put f ts (Some t)])
  | Unify l r =>
      let '(a1, tl, n1) := build_pat next l in
      let '(a2, tr, _) := build_pat n1 r in
      Some (a1 ++ a2 ++ [Union tl tr])
  | Rewrites _ _ => None
  end.

(** The engine rule of a clause that is not a rewrite. *)
Definition clause_rule (c : clause V) : option (rule V) :=
  let '(q, n) := query_body (clause_fresh c) (body c) in
  match head_actions n (head c) with
  | Some acts => Some (Rule V q acts)
  | None => None
  end.

(** * Rewrites *)

(** The flat nodes of a pattern appended after [ns], with the index of its root. A primitive
    on the right side becomes a hole that the condition binds, so [lift] records the atoms
    that compute it. *)
Fixpoint flat_pat (ns : list (pnode V)) (next : positive) (p : pat V) :
    list (pnode V) * nat * list (atom V) * positive :=
  match p with
  | PVar x => (ns ++ [PHole x], length ns, [], next)
  | PVal v => (ns ++ [PLit v], length ns, [], next)
  | PNode f args =>
      let '(ns1, ixs, lift, n1) :=
        (fix go (ns : list (pnode V)) (next : positive) (ps : list (pat V)) :
            list (pnode V) * list nat * list (atom V) * positive :=
           match ps with
           | [] => (ns, [], [], next)
           | p :: rest =>
               let '(ns1, i, l1, n1) := flat_pat ns next p in
               let '(ns2, rest_ixs, l2, n2) := go ns1 n1 rest in
               (ns2, i :: rest_ixs, l1 ++ l2, n2)
           end) ns next args in
      (ns1 ++ [PApp f ixs], length ns1, lift, n1)
  | POp q args =>
      let '(atoms, ts, n1) := query_pats next args in
      (ns ++ [PHole n1], length ns, atoms ++ [Prim V q ts (Var n1)], Pos.succ n1)
  end.

(** The Egraph rewrite of a rewrite clause. *)
Definition clause_rewrite (c : clause V) : option (rewrite V) :=
  match head c with
  | Rewrites l r =>
      let '(q, n1) := query_body (clause_fresh c) (body c) in
      let '(lns, li, _, n2) := flat_pat [] n1 l in
      let '(rns, ri, lift, _) := flat_pat [] n2 r in
      Some (Rewrite V (FPat V lns li) (FPat V rns ri) (q ++ lift))
  | _ => None
  end.

(** * Programs *)

(** The engine rules of a specification, in clause order. *)
Definition spec_rules (s : spec V) : list (rule V) :=
  fold_right (fun c rs => match clause_rule c with Some r => r :: rs | None => rs end) []
    (clauses s).

(** The Egraph rewrites of a specification, in clause order. *)
Definition spec_rewrites (s : spec V) : list (rewrite V) :=
  fold_right (fun c rs => match clause_rewrite c with Some r => r :: rs | None => rs end) []
    (clauses s).

(** The engine program of a specification without rewrites. *)
Definition spec_program (s : spec V) : program V := Program V (tables s) (spec_rules s).

End Lower.
