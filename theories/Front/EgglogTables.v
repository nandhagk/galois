(** * Tables of a program in the derive command

    This file declares the Elpi file [egglog.tables] of the command [Egglog] of [Derive.v].
    It collects the tables of a program from the relations that the command reads. A relation
    over values is a table, and so are the input tables that its premises read, the
    constructors of its datatypes and their list tables. The command numbers the tables from 1
    in this order, declares each with its sorts and its output, and defines a code constant
    for each.

    For example, the program [Path] of the relation [path] has the tables [path] and [edges],
    with the code constants [Path.path_code] and [Path.edges_code].

    Builds on: the Egglog syntax of declarations, the reading of [egglog.reading], the lists
    of [egglog.lists], and Elpi. *)

From Stdlib Require Import PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Syntax.

(** * Tables of a program *)

Elpi File egglog.tables lp:{{

% ---------------------------------------------------------------------------------------------
% Collecting the tables of the relations

pred input-keys i:list rel, i:rel, i:term, i:list (pair tkey (list term)),
  o:list (pair tkey (list term)).
input-keys _ (rel _ NP _ _) KTy Acc Out :-
  with-params NP KTy [] (ps\ sigma Inst\
    coq.subst-prod ps KTy Inst,
    walk Inst [] [] (_\ hyps\ _\ std.fold hyps Acc (add-input-key ps) Out)).

pred add-input-key i:list term, i:term, i:list (pair tkey (list term)),
  o:list (pair tkey (list term)).
add-input-key Ps H Acc Out :- in-premise H Elem Coll, !, input-key Ps Elem Coll Key _ Sorts,
  if (std.exists Acc (p\ sigma S\ p = pr Key S)) (Out = Acc) (std.append Acc [pr Key Sorts] Out).
add-input-key _ _ Acc Acc.

pred datatype-tables i:list inductive, i:list (pair tkey (list term)),
  o:list (pair tkey (list term)).
datatype-tables [] Acc Acc.
datatype-tables [I | Is] Acc Out :-
  coq.env.indt I _ _ _ _ Ks KTys,
  std.map2 Ks KTys (k\ ty\ e\ sigma Tys Ss\ arg-types ty Tys, std.map Tys (con-arg-sort I) Ss,
    e = pr (tk-con k) Ss) Es,
  std.append Acc Es Acc1,
  std.fold KTys Acc1 list-tables Acc2,
  datatype-tables Is Acc2 Out.

pred number i:list (pair tkey (list term)), i:int, i:list inductive, o:list table.
number [] _ _ [].
number [pr K Ss | Rest] N Dts [table K N Ss Out | Ts] :-
  table-output K Dts Out, M is N + 1, number Rest M Dts Ts.

% The output of a table: a lattice relation has a value, a constructor of a datatype and a list
% table have a class, and every other table is a relation.
pred table-output i:tkey, i:list inductive, o:term.
table-output (tk-rel R) _ {{ OLat lp:Code }} :- lattice-of R Code _, !.
table-output (tk-con C) Dts {{ OId }} :-
  std.exists Dts (d\ sigma Ty\ coq.env.indc C _ _ _ Ty, con-of d Ty), !.
table-output (tk-nil _) _ {{ OId }} :- !.
table-output (tk-cons _) _ {{ OId }} :- !.
table-output _ _ {{ ORel }}.

pred undup i:list inductive, i:list inductive, o:list inductive.
undup [] Acc Out :- std.rev Acc Out.
undup [X | Xs] Acc Out :- std.mem! Acc X, !, undup Xs Acc Out.
undup [X | Xs] Acc Out :- undup Xs [X | Acc] Out.

pred con-of i:inductive, i:term.
con-of D (prod _ _ F) :- !, pi x\ con-of D (F x).
con-of D (global (indt D)).

pred decl-of i:list table, i:table, o:term.
decl-of Ts (table K _ Ss Out) {{ Decl lp:P lp:SL lp:Out }} :-
  code-of Ts K P, list->term {{ sort }} Ss SL.

% ---------------------------------------------------------------------------------------------
% Code constants

% The name of the code constant of a table. A parameter that is an input list names its table.
pred code-name i:list string, i:table, o:string.
code-name _ (table (tk-rel R) _ _ _) N :- !, N is {coq.gref->id (indt R)} ^ "_code".
code-name _ (table (tk-con K) _ _ _) N :- !, N is {coq.gref->id (indc K)} ^ "_code".
code-name _ (table (tk-src (global GR)) _ _ _) N :- !, N is {coq.gref->id GR} ^ "_code".
code-name _ (table (tk-nil E) _ _ _) N :- !, N is "nil_" ^ {type-name E} ^ "_code".
code-name _ (table (tk-cons E) _ _ _) N :- !, N is "cons_" ^ {type-name E} ^ "_code".
code-name PNames (table (tk-param I) _ _ _) N :- std.nth {calc (I - 1)} PNames P,
  N is P ^ "_code".

% The names of the first N binders of a type: the parameters of a relation.
pred param-names i:int, i:term, o:list string.
param-names 0 _ [] :- !.
param-names N (prod Name _ F) [S | Ss] :- coq.name->id Name S, M is N - 1,
  pi x\ param-names M (F x) Ss.

% Define the code constant of a table.
pred define-code i:list string, i:table, o:pair tkey term.
define-code PNames T (pr K (global (const C))) :- T = table K N _ _,
  code-name PNames T Name, int->pos N P,
  coq.env.add-const Name P {{ positive }} @transparent! C.

}}.
