(** * Reading inductives in the derive command

    This file declares the Elpi file [egglog.reading] of the command [Egglog] of [Derive.v].
    It reads the type of an index as a sort, walks the binders of a constructor into numbered
    variables and premises, reads an input premise [In e (f q)] as the key of an input table,
    and reads a relation as a table over values or as an equation over a datatype. The
    datatypes of a program are the datatype of the indices of each equation and every datatype
    that its constructors reach, directly or through the elements of lists. A pair that a list
    of a clause holds as one variable [p] is two variables of the clause, one for each side.
    The tables of a program are keys with codes, and the code of a table is a constant once the
    command has defined it. The relations over values that read each other through their
    premises form a group, and the groups come in an order where each group comes after the
    groups that it reads.

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

% The element type of a list type.
pred list-of i:term, o:term.
list-of {{ list lp:E }} E.

% The components of a list element: the two sides of a pair, or the element itself.
pred elem-parts i:term, o:list term.
elem-parts {{ prod lp:A lp:B }} [A, B] :- !.
elem-parts E [E].

% The datatypes of a relation index of type T: the datatype T, and every datatype that it
% reaches through the arguments of its constructors and the elements of their lists, in the
% order of a walk from T.
pred datatypes-of-type i:term, o:list inductive.
datatypes-of-type T Ds :- datatype T I, !, reachable-datatypes [I] [] Ds.
datatypes-of-type _ [].

pred reachable-datatypes i:list inductive, i:list inductive, o:list inductive.
reachable-datatypes [] Acc Out :- std.rev Acc Out.
reachable-datatypes [I | Is] Acc Out :- std.mem! Acc I, !, reachable-datatypes Is Acc Out.
reachable-datatypes [I | Is] Acc Out :-
  coq.env.indt I _ _ _ _ _ KTys,
  std.map KTys (kty\ ds\ sigma Tys\ arg-types kty Tys,
    std.flatten {std.map Tys type-datatypes} ds) Dss,
  std.flatten Dss Ds, std.append Ds Is Next,
  reachable-datatypes Next [I | Acc] Out.

% The datatypes of a constructor argument of type T: T itself, or those of the elements of a
% list.
pred type-datatypes i:term, o:list inductive.
type-datatypes T [I] :- datatype T I, !.
type-datatypes T Ds :- list-of T E, !, std.flatten {std.map {elem-parts E} type-datatypes} Ds.
type-datatypes _ [].

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
% become hypotheses, and K receives them with the conclusion. A pair that a list holds as an
% element becomes two variables, as split-walk says.
pred walk i:term, i:list (pair term int), i:list term,
  i:(list (pair term int) -> list term -> term -> prop).
walk (prod Name Ty F) Vars Hyps K :- split-walk Name Ty F Vars Hyps K, !.
walk (prod Name Ty F) Vars Hyps K :- is-prop Ty, !,
  pi h\ decl h Name Ty => walk (F h) Vars [Ty | Hyps] K.
walk (prod Name Ty F) Vars Hyps K :- !, std.length Vars N, I is N + 1,
  pi x\ decl x Name Ty => walk (F x) [pr x I | Vars] Hyps K.
walk C Vars Hyps K :- std.rev Vars Vs, std.rev Hyps Hs, K Vs Hs C.

pred drop i:int, i:list term, o:list term.
drop 0 L L :- !.
drop N [_ | L] R :- M is N - 1, drop M L R.

% ---------------------------------------------------------------------------------------------
% Pairs written as variables in lists

% A binder of type [A * B] that a list holds as an element, as in [p :: rest]. The command reads
% such a pair as its two sides, which are two variables of the clause.
pred split-pair i:term, i:(term -> term), o:term, o:term.
split-pair {{ prod lp:A lp:B }} F A B :- pi x\ list-elem x (F x).

% The term T holds X as an element of a list.
pred list-elem i:term, i:term.
list-elem X {{ @cons _ lp:X _ }} :- !.
list-elem X (app Ts) :- !, std.exists Ts (list-elem X).
list-elem X (prod _ T F) :- !, (list-elem X T ; pi y\ list-elem X (F y)).
list-elem X (fun _ T F) :- !, (list-elem X T ; pi y\ list-elem X (F y)).

% Walk the binders of a clause, where the pair [p] becomes two variables [a] and [b]. The clause
% reads [(a, b)] wherever it has [p], and [a] and [b] where it has [fst p] and [snd p].
pred split-walk i:name, i:term, i:(term -> term), i:list (pair term int), i:list term,
  i:(list (pair term int) -> list term -> term -> prop).
split-walk N T F Vars Hyps K :- split-pair T F A B, !,
  std.length Vars L, I is L + 1, J is L + 2,
  coq.name->id N S, coq.id->name {calc (S ^ "_1")} NA, coq.id->name {calc (S ^ "_2")} NB,
  pi a b\ sigma P Body\ decl a NA A => decl b NB B =>
    (P = {{ @pair lp:A lp:B lp:a lp:b }}, unproject (F P) Body,
     if (pair-outside-list P Body)
        (coq.error "Egglog: the pair" S "is an element of a list in a pattern, so it stands for"
          "its two sides, and the clause uses it in another place as well. Write its sides as"
          "two variables, or use only fst" S "and snd" S "there.")
        true,
     walk Body [pr b J, pr a I | Vars] Hyps K).

% The pair P occurs in the term T outside the elements of lists.
pred pair-outside-list i:term, i:term.
pair-outside-list P {{ @cons _ lp:X lp:Rest }} :- !,
  (not (X = P), pair-outside-list P X ; pair-outside-list P Rest).
pair-outside-list P P :- !.
pair-outside-list P (app Ts) :- !, std.exists Ts (pair-outside-list P).
pair-outside-list P (prod _ T F) :- !, (pair-outside-list P T ; pi y\ pair-outside-list P (F y)).
pair-outside-list P (fun _ T F) :- !, (pair-outside-list P T ; pi y\ pair-outside-list P (F y)).

% The term T with each projection of an explicit pair replaced by its side.
pred unproject i:term, o:term.
unproject T U :-
  (pi A B A2 B2 X Y X1\
    copy {{ @fst lp:A lp:B (@pair lp:A2 lp:B2 lp:X lp:Y) }} X1 :- !, copy X X1) =>
  (pi A B A2 B2 X Y Y1\
    copy {{ @snd lp:A lp:B (@pair lp:A2 lp:B2 lp:X lp:Y) }} Y1 :- !, copy Y Y1) =>
  copy T U.

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
