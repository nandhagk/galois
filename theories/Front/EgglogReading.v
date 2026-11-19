(** * Reading inductives in the derive command

    This file declares the Elpi file [egglog.reading] of the command [Egglog] of [Derive.v].
    It reads the type of an index as a sort, walks the binders of a constructor into numbered
    variables and premises, reads an input premise [In e (f q)] as the key of an input table,
    and reads a relation as a table over values or as an equation over a datatype. The tables
    of a program are keys with codes, and the code of a table is a constant once the command
    has defined it.

    For example, [rel-info] reads the relation [path edges : positive -> positive -> Prop] as
    a relation over values with the sorts [[SVal; SVal]], and [walk] numbers the binders
    [x y z] of [path_step] 1, 2 and 3.

    Builds on: the Egglog syntax of sorts, the values of [egglog.primitives], and Elpi. *)

From elpi Require Import elpi.
From Galois.Egglog Require Import Syntax.

(** * Reading inductives *)

Elpi File egglog.reading lp:{{

% ---------------------------------------------------------------------------------------------
% Datatypes and sorts

pred datatype i:term, o:inductive.
datatype (global (indt I)) I :-
  not (value-type (global (indt I))),
  coq.env.indt I tt 0 _ Arity _ _, not (Arity = sort prop).

pred sort-term i:term, o:term.
sort-term T {{ SVal }} :- value-type T, !.
sort-term T {{ SId }} :- datatype T _, !.
sort-term T _ :- coq.error "Egglog: a table argument has type" {coq.term->string T}
  "which is neither a registered value type nor a datatype".

% The datatypes that a term or type mentions, by its constructors.
pred datatypes-of-type i:term, o:list inductive.
datatypes-of-type T [I] :- datatype T I, !.
datatypes-of-type _ [].

% ---------------------------------------------------------------------------------------------
% Tables

kind tkey type.
type tk-rel inductive -> tkey.     % a relation over values
type tk-con constructor -> tkey.   % an input constructor or a datatype constructor
type tk-src term -> tkey.          % an input list of tuples, by its projection
type tk-param int -> tkey.         % an input list of tuples that is a parameter, by position
type tk-nil term -> tkey.          % the empty list of an element type
type tk-cons term -> tkey.         % an element in front of a list, by the element type

kind table type.
type table tkey -> int -> list term -> term -> table.   % key, code, sorts, output

pred find-table i:list table, i:tkey, o:int, o:list term, o:term.
find-table [table K N S O | _] K N S O :- !.
find-table [_ | Ts] K N S O :- find-table Ts K N S O.

% The code constant of a table, once the command has defined it.
pred code-const o:tkey, o:term.

pred code-of i:list table, i:tkey, o:term.
code-of _ K P :- code-const K P, !.
code-of Ts K P :- find-table Ts K N _ _, !, int->pos N P.
code-of _ K _ :- coq.error "Egglog: no table for" K.

% ---------------------------------------------------------------------------------------------
% Parameters and binders

pred with-params i:int, i:term, i:list term, i:(list term -> prop).
with-params 0 _ Acc K :- !, std.rev Acc Ps, K Ps.
with-params N (prod Name Ty F) Acc K :- M is N - 1,
  pi p\ decl p Name Ty => with-params M (F p) [p | Acc] K.

pred is-prop i:term.
is-prop Ty :- coq.typecheck Ty S ok, coq.reduction.lazy.whd S (sort prop).

% walk Ty Vars Hyps K: binders of data become numbered variables, binders of propositions
% become hypotheses, and K receives them with the conclusion.
pred walk i:term, i:list (pair term int), i:list term,
  i:(list (pair term int) -> list term -> term -> prop).
walk (prod Name Ty F) Vars Hyps K :- is-prop Ty, !,
  pi h\ decl h Name Ty => walk (F h) Vars [Ty | Hyps] K.
walk (prod Name Ty F) Vars Hyps K :- !, std.length Vars N, I is N + 1,
  pi x\ decl x Name Ty => walk (F x) [pr x I | Vars] Hyps K.
walk C Vars Hyps K :- std.rev Vars Vs, std.rev Hyps Hs, K Vs Hs C.

pred drop i:int, i:list term, o:list term.
drop 0 L L :- !.
drop N [_ | L] R :- M is N - 1, drop M L R.

% ---------------------------------------------------------------------------------------------
% Input premises

pred in-premise i:term, o:term, o:term.
in-premise (app [global GR, _, Elem, Coll]) Elem Coll :- coq.locate "List.In" GR.

% input-key Elem Coll Key Args Sorts
pred input-key i:list term, i:term, i:term, o:tkey, o:list term, o:list term.
input-key Ps (app [global (indc P), T1, T2, A, B]) Coll Key [A, B] [S1, S2] :-
  coq.locate "pair" (indc P), !, sort-term T1 S1, sort-term T2 S2, source-key Ps Coll Key.
input-key _ (app [global (indc C) | Args]) _ (tk-con C) Args Sorts :- !,
  coq.env.typeof (indc C) Ty, arg-types Ty Tys, std.map Tys sort-term Sorts.
input-key _ (global (indc C)) _ (tk-con C) [] [] :- !.

pred source-key i:list term, i:term, o:tkey.
source-key Ps P (tk-param I) :- param-index Ps P 1 I, !.
source-key _ (app [Head | _]) (tk-src Head) :- !.
source-key _ C _ :- coq.error "Egglog: an input list must be a parameter or a projection of one:"
  {coq.term->string C}.

pred param-index i:list term, i:term, i:int, o:int.
param-index [P | _] P I I :- !.
param-index [_ | Ps] P I J :- K is I + 1, param-index Ps P K J.
input-key _ E _ _ _ _ :- coq.error "Egglog: an input element must be a constructor or a pair:"
  {coq.term->string E}.

% ---------------------------------------------------------------------------------------------
% Relations

% A lattice relation, with the code of its merge in the primitive set and the merge function.
% The command assumes one clause for each declaration 'merge R g' after 'with <primitives>'.
% The file egglog.lattice assumes these clauses with with-lattices.
pred lattice-of o:inductive, o:term, o:term.

% The keys and the value of the indices of a lattice relation: all of them but the last, and
% the last.
pred split-last i:list A, o:list A, o:A.
split-last [X] [] X :- !.
split-last [X | Xs] [X | Ys] L :- split-last Xs Ys L.

kind rel type.
type rel inductive -> int -> bool -> list term -> rel.   % relation, parameters, equational?, sorts

% A lattice relation has the sorts of its keys, which are all its indices but the last.
pred rel-info i:inductive, o:rel.
rel-info I (rel I NP Eq Sorts) :-
  coq.env.indt I tt NP _ Arity _ _,
  index-types NP Arity Tys,
  if (lattice-of I _ _)
     (Eq = ff, std.forall Tys check-value, split-last Tys Keys _, std.map Keys sort-term Sorts)
     (if (Tys = [T, T], datatype T _) (Eq = tt, Sorts = [])
        (Eq = ff, std.forall Tys check-value, std.map Tys sort-term Sorts)).

pred index-types i:int, i:term, o:list term.
index-types 0 (prod _ Ty F) [Ty | Tys] :- !, pi x\ index-types 0 (F x) Tys.
index-types 0 _ [] :- !.
index-types N (prod _ _ F) Tys :- M is N - 1, pi x\ index-types M (F x) Tys.

}}.
