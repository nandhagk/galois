(** * Reading inductives in the derive command

    This file declares the Elpi file [egglog.reading] of the command [Egglog] of [Derive.v].
    It reads the type of an index as a sort, walks the binders of a constructor into numbered
    variables and premises, reads an input premise [In e (f q)] as the key of an input table,
    and reads a relation as a table over values or as an equation over a datatype. The tables
    of a program are keys with codes, and the code of a table is a constant once the command
    has defined it. The relations over values that read each other through their premises
    form a group, and the groups come in an order where each group comes after the groups
    that it reads.

    For example, [rel-info] reads the relation [path edges : positive -> positive -> Prop] as
    a relation over values with the sorts [[SVal; SVal]], and [walk] numbers the binders
    [x y z] of [path_step] 1, 2 and 3. The relations [even] and [odd] of a mutual inductive,
    whose premises read each other, form one group.

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

% The number of indices of a relation, which is the number of products of its arity after its
% N parameters.
pred index-count i:int, i:term, o:int.
index-count 0 (prod _ _ F) N :- !, (pi x\ index-count 0 (F x) M), N is M + 1.
index-count 0 _ 0 :- !.
index-count N (prod _ _ F) C :- M is N - 1, pi x\ index-count M (F x) C.

% ---------------------------------------------------------------------------------------------
% Groups of relations that read each other

% The relations of Rels that the premises of the constructors of a relation read.
pred reads-of i:list rel, i:rel, o:list inductive.
reads-of Rels (rel R NP _ _) Qs :-
  coq.env.indt R _ _ _ _ _ KTys,
  std.map KTys (con-reads Rels NP) Qss, std.flatten Qss Qs.

pred con-reads i:list rel, i:int, i:term, o:list inductive.
con-reads Rels NP KTy Qs :-
  with-params NP KTy [] (ps\ sigma Inst\ coq.subst-prod ps KTy Inst,
    walk Inst [] [] (_\ hyps\ _\ std.map-filter hyps (premise-rel Rels) Qs)).

pred premise-rel i:list rel, i:term, o:inductive.
premise-rel Rels (app [global (indt Q) | _]) Q :- std.exists Rels (r\ r = rel Q _ _ _).

% The relations that the relations of Frontier reach through premises, in the graph G from each
% relation to the relations that its premises read, together with those of Seen.
pred reached i:list (pair inductive (list inductive)), i:list inductive, i:list inductive,
  o:list inductive.
reached _ [] Seen Seen.
reached G [I | Is] Seen Out :- std.mem! Seen I, !, reached G Is Seen Out.
reached G [I | Is] Seen Out :-
  std.lookup! G I Next, std.append Next Is Frontier, reached G Frontier [I | Seen] Out.

% The group of R holds the relations of Rels that R reaches and that reach R, in the order of
% Rels.
pred group-of i:list rel, i:list (pair inductive (list inductive)), i:inductive, o:list rel.
group-of Rels G R Group :-
  reached G [R] [] FromR,
  std.filter Rels (r\ sigma Q ToQ\ r = rel Q _ _ _, std.mem! FromR Q,
    reached G [Q] [] ToQ, std.mem! ToQ R) Group.

% The relations over values Rels in groups. The relations of a group read each other through
% their premises, as the relations of a mutual inductive can, and keep the order of Rels. Each
% group comes after the groups that its premises read. Of the groups that can come next, the
% group of the first relation in Rels comes next, so relations that come after the relations
% that they read keep their order.
pred read-groups i:list rel, o:list (list rel).
read-groups Rels Groups :-
  std.map Rels (r\ e\ sigma I Qs\ r = rel I _ _ _, reads-of Rels r Qs, e = pr I Qs) G,
  order-groups Rels G [] Groups.

pred order-groups i:list rel, i:list (pair inductive (list inductive)), i:list inductive,
  o:list (list rel).
order-groups Rels G Done [Group | Groups] :- next-group Rels Rels G Done Group, !,
  std.map Group (r\ i\ r = rel i _ _ _) Is, std.append Done Is Done1,
  order-groups Rels G Done1 Groups.
order-groups Rels _ Done [] :-
  if (std.forall Rels (r\ sigma I\ r = rel I _ _ _, std.mem! Done I)) true
     (coq.error "Egglog: no order of the relations puts each group after the groups it reads.").

% The group of the first relation of Cands that has no group yet and whose group reads only its
% own relations and the relations in Done.
pred next-group i:list rel, i:list rel, i:list (pair inductive (list inductive)),
  i:list inductive, o:list rel.
next-group Rels [rel R _ _ _ | _] G Done Group :- not (std.mem! Done R),
  group-of Rels G R Group,
  std.forall Group (m\ sigma M Qs\ m = rel M _ _ _, std.lookup! G M Qs,
    std.forall Qs (q\ std.mem! Done q ; std.exists Group (g\ g = rel q _ _ _))), !.
next-group Rels [_ | Cands] G Done Group :- next-group Rels Cands G Done Group.

}}.
