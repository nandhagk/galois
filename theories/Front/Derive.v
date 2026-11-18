(** * Deriving engine programs from inductives

    The command [Egglog P from R1 .. Rn.] reads the inductive relations [R1] to [Rn] and
    defines a module [P] with the specification of their constructors ([P.spec]), its engine
    program ([P.program]), the input rows of their parameters ([P.inputs], [P.facts]) and the
    meaning of each table ([P.relation]). A relation over values is a table. A relation [R t u]
    over a datatype is an equation, and the constructors of the datatype are tables. A premise
    [In e (f q)] reads an input table, and a premise [Ri ..] reads a relation. Variables are
    numbered in binder order, and every table code and variable number is generated.

    For example, [Egglog Andersen from may_points.] defines [Andersen.spec] with one clause per
    constructor of [may_points], and [Andersen.facts q] lists the input rows of [q].

    Builds on: the specifications, their lowering, and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Syntax.
From Galois.Egraph Require Import Syntax.
From Galois.Front Require Import Spec LowerSig.

Import List.ListNotations.

Elpi Command Egglog.
Elpi Accumulate lp:{{

% ---------------------------------------------------------------------------------------------
% Types

pred value-type i:term.
value-type T :- coq.locate "positive" GR, T = global GR.

pred datatype i:term, o:inductive.
datatype (global (indt I)) I :-
  not (value-type (global (indt I))),
  coq.env.indt I tt 0 _ Arity _ _, not (Arity = sort prop).

pred sort-term i:term, o:term.
sort-term T {{ SVal }} :- value-type T, !.
sort-term T {{ SId }} :- datatype T _, !.
sort-term T _ :- coq.error "Egglog: a table argument has type" {coq.term->string T}
  "which is neither positive nor a datatype".

% ---------------------------------------------------------------------------------------------
% Numerals and lists

pred int->pos i:int, o:term.
int->pos 1 {{ xH }} :- !.
int->pos N {{ xO lp:P }} :- 0 is N mod 2, !, M is N div 2, int->pos M P.
int->pos N {{ xI lp:P }} :- M is N div 2, int->pos M P.

pred list->term i:term, i:list term, o:term.
list->term Ty [] {{ @nil lp:Ty }}.
list->term Ty [X | Xs] {{ @cons lp:Ty lp:X lp:T }} :- list->term Ty Xs T.

% ---------------------------------------------------------------------------------------------
% Tables

kind tkey type.
type tk-rel inductive -> tkey.     % a relation over values
type tk-con constructor -> tkey.   % an input constructor or a datatype constructor
type tk-src term -> tkey.          % an input list of tuples, by its projection
type tk-param int -> tkey.         % an input list of tuples that is a parameter, by position

kind table type.
type table tkey -> int -> list term -> term -> table.   % key, code, sorts, output

pred find-table i:list table, i:tkey, o:int, o:list term, o:term.
find-table [table K N S O | _] K N S O :- !.
find-table [_ | Ts] K N S O :- find-table Ts K N S O.

pred code-of i:list table, i:tkey, o:term.
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
% Collecting tables

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

pred arg-types i:term, o:list term.
arg-types (prod _ Ty F) [Ty | Tys] :- !, pi x\ arg-types (F x) Tys.
arg-types _ [].

% The datatypes that a term or type mentions, by its constructors.
pred datatypes-of-type i:term, o:list inductive.
datatypes-of-type T [I] :- datatype T I, !.
datatypes-of-type _ [].

% ---------------------------------------------------------------------------------------------
% Relations

kind rel type.
type rel inductive -> int -> bool -> list term -> rel.   % relation, parameters, equational?, sorts

pred rel-info i:inductive, o:rel.
rel-info I (rel I NP Eq Sorts) :-
  coq.env.indt I tt NP _ Arity _ _,
  index-types NP Arity Tys,
  if (Tys = [T, T], datatype T _) (Eq = tt, Sorts = []) (Eq = ff, std.map Tys sort-term Sorts).

pred index-types i:int, i:term, o:list term.
index-types 0 (prod _ Ty F) [Ty | Tys] :- !, pi x\ index-types 0 (F x) Tys.
index-types 0 _ [] :- !.
index-types N (prod _ _ F) Tys :- M is N - 1, pi x\ index-types M (F x) Tys.

% ---------------------------------------------------------------------------------------------
% Patterns

pred var-index i:list (pair term int), i:term, o:int.
var-index [pr X I | _] X I :- !.
var-index [_ | Vs] X I :- var-index Vs X I.

pred pat-of i:list table, i:list (pair term int), i:term, o:term.
pat-of _ Vars X {{ @PVar positive lp:P }} :- var-index Vars X I, !, int->pos I P.
pat-of Ts Vars (app [global (indc K) | Args]) {{ @PNode positive lp:Code lp:PArgs }} :-
  find-table Ts (tk-con K) _ _ O, O = {{ OId }}, !, code-of Ts (tk-con K) Code,
  std.map Args (pat-of Ts Vars) Ps, list->term {{ pat positive }} Ps PArgs.
pat-of Ts _ (global (indc K)) {{ @PNode positive lp:Code nil }} :-
  find-table Ts (tk-con K) _ _ O, O = {{ OId }}, !, code-of Ts (tk-con K) Code.
pat-of _ Vars T {{ @PVal positive lp:T }} :-
  not (std.exists Vars (v\ sigma X\ v = pr X _, occurs X T)),
  coq.typecheck T Ty ok, value-type Ty, !.
pat-of _ _ T _ :- coq.error "Egglog: cannot read the term" {coq.term->string T}.

pred pats-of i:list table, i:list (pair term int), i:list term, o:term.
pats-of Ts Vars Args L :- std.map Args (pat-of Ts Vars) Ps, list->term {{ pat positive }} Ps L.

% ---------------------------------------------------------------------------------------------
% Premises and conclusions

pred find-rel i:list rel, i:inductive, o:int, o:bool.
find-rel [rel R NP Eq _ | _] R NP Eq :- !.
find-rel [_ | Rs] R NP Eq :- find-rel Rs R NP Eq.

pred premise-of i:list table, i:list rel, i:list term, i:list (pair term int), i:term,
  o:term.
premise-of Ts _ Ps Vars H {{ @Holds positive lp:Code lp:PArgs }} :-
  in-premise H Elem Coll, !, input-key Ps Elem Coll Key Args _, code-of Ts Key Code,
  pats-of Ts Vars Args PArgs.
premise-of Ts Rels _ Vars (app [global (indt R) | All]) {{ @Holds positive lp:Code lp:PArgs }} :-
  find-rel Rels R NP ff, !, drop NP All Args, code-of Ts (tk-rel R) Code,
  pats-of Ts Vars Args PArgs.
premise-of _ _ _ _ H _ :- coq.error "Egglog: cannot read the premise" {coq.term->string H}.

% A closure law of an equational relation R: reflexivity, symmetry, transitivity or the
% congruence of one constructor.
pred closure-law i:inductive, i:int, i:list term, i:term.
closure-law R NP Hyps (app [global (indt R) | All]) :-
  drop NP All [L, Rt],
  std.map Hyps (h\ p\ sigma HA\ h = app [global (indt R) | HA], drop NP HA p) Pairs,
  closure-shape Pairs L Rt.

pred closure-shape i:list (list term), i:term, i:term.
closure-shape [] X X :- !.
closure-shape [[A, B]] B A :- !.
closure-shape [[A, B], [B, C]] A C :- !.
closure-shape Pairs (app [K | As]) (app [K | Bs]) :- cong-args Pairs As Bs.

pred cong-args i:list (list term), i:list term, i:list term.
cong-args [] [] [] :- !.
cong-args Ps [A | As] [A | Bs] :- !, cong-args Ps As Bs.
cong-args [[A, B] | Ps] [A | As] [B | Bs] :- cong-args Ps As Bs.

pred mentions i:term, i:list (pair term int), o:list int.
mentions T Vars Is :- std.filter Vars (v\ sigma X\ v = pr X _, occurs X T) Ws,
  std.map Ws (w\ i\ w = pr _ i) Is.

pred clause-of i:list table, i:list rel, i:rel, i:term, o:list term.
clause-of Ts Rels (rel R NP Eq _) KTy Out :-
  with-params NP KTy [] (ps\ sigma Inst\
    coq.subst-prod ps KTy Inst,
    walk Inst [] [] (vars\ hyps\ concl\ clause-body Ts Rels R NP Eq ps vars hyps concl Out)).

pred clause-body i:list table, i:list rel, i:inductive, i:int, i:bool, i:list term,
  i:list (pair term int), i:list term, i:term, o:list term.
clause-body _ _ R NP tt _ _ Hyps Concl [] :- closure-law R NP Hyps Concl, !.
clause-body Ts Rels R NP Eq Params Vars Hyps (app [global (indt R) | All]) [C] :-
  std.map Hyps (premise-of Ts Rels Params Vars) Ps, list->term {{ premise positive }} Ps Body,
  drop NP All Args,
  if (Eq = tt)
     (Args = [L, Rt], pat-of Ts Vars L PL, pat-of Ts Vars Rt PR,
      std.fold Hyps [] (h\ a\ b\ sigma M\ mentions h Vars M, std.append a M b) Bound,
      mentions (app [L, Rt]) Vars Used,
      if (std.forall Used (i\ std.mem! Bound i))
         (Head = {{ @Unify positive lp:PL lp:PR }})
         (Head = {{ @Rewrites positive lp:PL lp:PR }}))
     (code-of Ts (tk-rel R) Code, pats-of Ts Vars Args PArgs,
      Head = {{ @Derive positive lp:Code lp:PArgs }}),
  C = {{ @Clause positive lp:Body lp:Head }}.

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
  std.map2 Ks KTys (k\ ty\ e\ sigma Tys Ss\ arg-types ty Tys, std.map Tys sort-term Ss,
    e = pr (tk-con k) Ss) Es,
  std.append Acc Es Acc1, datatype-tables Is Acc1 Out.

pred number i:list (pair tkey (list term)), i:int, i:list inductive, o:list table.
number [] _ _ [].
number [pr K Ss | Rest] N Dts [table K N Ss Out | Ts] :-
  if (K = tk-con C, std.exists Dts (d\ coq.env.indc C _ _ _ Ty, con-of d Ty))
     (Out = {{ OId }}) (Out = {{ ORel }}),
  M is N + 1, number Rest M Dts Ts.

pred undup i:list inductive, i:list inductive, o:list inductive.
undup [] Acc Out :- std.rev Acc Out.
undup [X | Xs] Acc Out :- std.mem! Acc X, !, undup Xs Acc Out.
undup [X | Xs] Acc Out :- undup Xs [X | Acc] Out.

pred con-of i:inductive, i:term.
con-of D (prod _ _ F) :- !, pi x\ con-of D (F x).
con-of D (global (indt D)).

pred decl-of i:table, o:term.
decl-of (table _ N Ss Out) {{ Decl lp:P lp:SL lp:Out }} :-
  int->pos N P, list->term {{ sort }} Ss SL.

% ---------------------------------------------------------------------------------------------
% The command

main [str Name, str "from" | RelNames] :- !,
  std.map RelNames (a\ i\ sigma N\ a = str N, coq.locate N (indt i)) Is,
  std.map Is rel-info Rels,
  std.filter Rels (r\ r = rel _ _ ff _) Relational,
  std.map Relational (r\ e\ sigma I Ss\ r = rel I _ _ Ss, e = pr (tk-rel I) Ss) RelKeys,
  std.fold Rels [] (r\ a\ b\ sigma I KTys\ r = rel I _ _ _,
    coq.env.indt I _ _ _ _ _ KTys,
    std.fold KTys a (input-keys Rels r) b) InputKeys,
  std.map Rels (r\ ds\ sigma I NP Ar Tys\ r = rel I NP _ _, coq.env.indt I _ _ _ Ar _ _,
    index-types NP Ar Tys, std.flatten {std.map Tys datatypes-of-type} ds) DtLists,
  std.flatten DtLists Dts0, undup Dts0 [] Dts,
  datatype-tables Dts [] DtKeys,
  std.flatten [RelKeys, InputKeys, DtKeys] Keys,
  number Keys 1 Dts Tables,
  std.map Tables decl-of Decls, list->term {{ decl }} Decls DeclT,
  std.map-filter Tables (t\ c\ sigma K N\ t = table K N _ _, std.exists InputKeys (p\ sigma S\ p = pr K S),
    int->pos N c) InputCodes,
  list->term {{ positive }} InputCodes InputT,
  std.fold Rels [] (r\ a\ b\ sigma I KTys Cs\ r = rel I _ _ _,
    coq.env.indt I _ _ _ _ _ KTys,
    std.map KTys (clause-of Tables Rels r) Cs, std.flatten [a | Cs] b) ClauseList,
  list->term {{ clause positive }} ClauseList ClausesT,
  Spec = {{ @Spec positive lp:DeclT lp:InputT lp:ClausesT }},
  std.assert-ok! (coq.typecheck Spec {{ spec positive }}) "Egglog: ill-typed specification",
  coq.env.begin-module Name none,
  coq.env.add-const "spec" Spec {{ spec positive }} @transparent! SpecC,
  SpecT = global (const SpecC),
  coq.env.add-const "program" {{ @spec_program positive lp:SpecT }}
    {{ program positive }} @transparent! _,
  coq.env.add-const "rewrites" {{ @spec_rewrites positive lp:SpecT }}
    {{ list (rewrite positive) }} @transparent! _,
  coq.env.end-module _.
main _ :- coq.error "Usage: Egglog <name> from <relation> .. <relation>.".

}}.
#[synterp] Elpi Accumulate lp:{{
main [str Name, str "from" | _] :- !, coq.env.begin-module Name none, coq.env.end-module _.
main _.
}}.
Elpi Export Egglog.
