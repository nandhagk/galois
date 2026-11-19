(** * Patterns and premises in the derive command

    This file declares the Elpi file [egglog.patterns] of the command [Egglog] of [Derive.v].
    It reads a constructor of a relation as a clause of the specification. An argument of a
    premise or of the conclusion is a pattern. A list in an argument of a relation, an input
    row or a primitive is a value, and a list in an argument of a constructor of a datatype is
    a chain of nodes. A premise reads a relation, an input table or the result of a primitive.
    The conclusion derives a row, assigns a lattice value or equates two terms. A closure law
    of an equation, such as reflexivity or the congruence of a constructor, has no clause. The
    congruence relates two arguments by the equation itself, by [Forall2] of it, by an
    equality, or by [Forall2 (pair_rel ra rb)] of two lists of pairs.

    For example, the constructor [path_step x y z : path edges x y -> In (y, z) edges ->
    path edges x z] is the clause whose body is [[Holds path_code [PVar 1; PVar 2];
    Holds edges_code [PVar 2; PVar 3]]] and whose head is [Derive path_code [PVar 1; PVar 3]].

    Builds on: the specifications, the definitions that derived programs call, the tables of
    [egglog.reading] and [egglog.lists], and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Syntax.
From Galois.Front Require Import Spec DeriveHelpers.

(** * Patterns and premises *)

Elpi File egglog.patterns lp:{{

% ---------------------------------------------------------------------------------------------
% Patterns

pred var-index i:list (pair term int), i:term, o:int.
var-index [pr X I | _] X I :- !.
var-index [_ | Vs] X I :- var-index Vs X I.

pred pat-of i:list table, i:list (pair term int), i:term, o:term.
pat-of _ Vars X {{ @PVar positive lp:P }} :- var-index Vars X I, !, int->pos I P.
pat-of Ts _ {{ @nil lp:E }} {{ @PNode positive lp:Code (@nil (pat positive)) }} :- !,
  list-code Ts (tk-nil E) Code.
pat-of Ts Vars {{ @cons lp:E lp:X lp:T }} {{ @PNode positive lp:Code lp:PArgs }} :- !,
  list-code Ts (tk-cons E) Code,
  elem-pats Ts Vars E X Ps, pat-of Ts Vars T PT, std.append Ps [PT] All,
  list->term {{ pat positive }} All PArgs.
pat-of Ts Vars (app [global (indc K) | Args]) {{ @PNode positive lp:Code lp:PArgs }} :-
  find-table Ts (tk-con K) _ _ O, O = {{ OId }}, !, code-of Ts (tk-con K) Code,
  std.map Args (pat-of Ts Vars) Ps, list->term {{ pat positive }} Ps PArgs.
pat-of Ts _ (global (indc K)) {{ @PNode positive lp:Code (@nil (pat positive)) }} :-
  find-table Ts (tk-con K) _ _ O, O = {{ OId }}, !, code-of Ts (tk-con K) Code.
pat-of Ts Vars (app [global GR | Args]) {{ @POp positive lp:Code lp:PArgs }} :-
  prim-of GR Code, !, pats-of Ts Vars Args PArgs.
pat-of _ Vars T {{ @PVal positive lp:E }} :-
  not (std.exists Vars (v\ sigma X\ v = pr X _, occurs X T)),
  coq.typecheck T Ty ok, value-type Ty, !, enc-by-ty Ty T E.
pat-of _ _ T _ :- coq.error "Egglog: cannot read the term" {coq.term->string T}.

% The patterns of the arguments of a relation, an input row or a primitive. A list there is a
% value, so a list term is the value of its encoding.
pred pats-of i:list table, i:list (pair term int), i:list term, o:term.
pats-of Ts Vars Args L :-
  std.map Args (value-pat Ts Vars) Ps, list->term {{ pat positive }} Ps L.

pred value-pat i:list table, i:list (pair term int), i:term, o:term.
value-pat _ Vars X {{ @PVal positive lp:E }} :- list-term X, coq.typecheck X Ty ok,
  value-type Ty, !,
  if (std.exists Vars (v\ sigma Y\ v = pr Y _, occurs Y X))
     (coq.error "Egglog: a list value in a pattern is a variable or a list without variables,"
       "and" {coq.term->string X} "is neither.")
     (enc-by-ty Ty X E).
value-pat Ts Vars X P :- pat-of Ts Vars X P.

% A term written as a list is the empty list or an element in front of a list.
pred list-term i:term.
list-term {{ @nil _ }}.
list-term {{ @cons _ _ _ }}.

% The patterns of a list element: the two sides of a pair, or the element itself.
pred elem-pats i:list table, i:list (pair term int), i:term, i:term, o:list term.
elem-pats Ts Vars {{ prod _ _ }} {{ @pair _ _ lp:A lp:B }} [PA, PB] :- !,
  pat-of Ts Vars A PA, pat-of Ts Vars B PB.
elem-pats _ _ {{ prod _ _ }} X _ :- !,
  coq.error "Egglog: an element of a list of pairs is written as a pair (a, b) in a pattern,"
    "and" {coq.term->string X} "is not.".
elem-pats Ts Vars _ X [P] :- pat-of Ts Vars X P.

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
premise-of Ts Rels _ Vars (app [global (indt R) | All]) P :-
  find-rel Rels R NP ff, !, drop NP All Args, code-of Ts (tk-rel R) Code,
  if (lattice-of R _ _)
     (split-last Args Keys Val, pats-of Ts Vars Keys PKeys, pat-of Ts Vars Val PVal,
      P = {{ @Equals positive lp:Code lp:PKeys lp:PVal }})
     (pats-of Ts Vars Args PArgs, P = {{ @Holds positive lp:Code lp:PArgs }}).
premise-of Ts _ _ Vars (app [global (indt Eq), _, app [global GR | Args], V])
    {{ @Computes positive lp:Code lp:PArgs lp:PV }} :-
  coq.locate "eq" (indt Eq), prim-of GR Code, !,
  pats-of Ts Vars Args PArgs, pat-of Ts Vars V PV.
premise-of _ _ _ _ H _ :- coq.error "Egglog: cannot read the premise" {coq.term->string H}.

% A hypothesis of a closure law of an equational relation R relates two terms by R, or two
% arguments that the congruence takes alike. These are two lists by [Forall2 R], two equal
% arguments, or two lists of pairs by [Forall2 (pair_rel RA RB)], where each of [RA] and [RB] is
% the equality or R.
kind lawhyp type.
type hyp-rel term -> term -> lawhyp.
type hyp-all term -> term -> lawhyp.

pred law-hyp i:inductive, i:int, i:term, o:lawhyp.
law-hyp _ _ {{ @eq _ lp:A lp:B }} (hyp-all A B) :- !.
law-hyp R NP {{ @Forall2 _ _ (@pair_rel _ _ lp:RA lp:RB) lp:Xs lp:Ys }} (hyp-all Xs Ys) :-
  side-rel R NP RA, side-rel R NP RB, !.
law-hyp R NP (app [global (indt R) | HA]) (hyp-rel A B) :- !, drop NP HA [A, B].
law-hyp R NP {{ @Forall2 _ _ lp:Rel lp:Xs lp:Ys }} (hyp-all Xs Ys) :- rel-applied R NP Rel.

% The relation R applied to its parameters.
pred rel-applied i:inductive, i:int, i:term.
rel-applied R 0 (global (indt R)) :- !.
rel-applied R NP (app [global (indt R) | Ps]) :- std.length Ps NP.

% The relation between the sides of two pairs in a congruence law.
pred side-rel i:inductive, i:int, i:term.
side-rel _ _ {{ @eq _ }} :- !.
side-rel R NP Rel :- rel-applied R NP Rel.

% A closure law of an equational relation R: reflexivity, symmetry, transitivity or the
% congruence of one constructor, whose list arguments are related by [Forall2 R].
pred closure-law i:inductive, i:int, i:list term, i:term.
closure-law R NP Hyps (app [global (indt R) | All]) :-
  drop NP All [L, Rt],
  std.map Hyps (law-hyp R NP) Pairs,
  closure-shape Pairs L Rt.

pred closure-shape i:list lawhyp, i:term, i:term.
closure-shape [] X X :- !.
closure-shape [hyp-rel A B] B A :- !.
closure-shape [hyp-rel A B, hyp-rel B C] A C :- !.
closure-shape Pairs (app [K | As]) (app [K | Bs]) :- cong-args Pairs As Bs.

pred cong-args i:list lawhyp, i:list term, i:list term.
cong-args [] [] [] :- !.
cong-args Ps [A | As] [A | Bs] :- !, cong-args Ps As Bs.
cong-args [hyp-rel A B | Ps] [A | As] [B | Bs] :- cong-args Ps As Bs.
cong-args [hyp-all A B | Ps] [A | As] [B | Bs] :- cong-args Ps As Bs.

pred mentions i:term, i:list (pair term int), o:list int.
mentions T Vars Is :- std.filter Vars (v\ sigma X\ v = pr X _, occurs X T) Ws,
  std.map Ws (w\ i\ w = pr _ i) Is.

% The variables that the premises bind, in premise order: the variables of relation and input
% premises outside primitive applications, and the result of each equation premise whose
% arguments are bound.
pred bound-vars i:list term, i:list (pair term int), i:list int, o:list int.
bound-vars [] _ B B.
bound-vars [H | Hs] Vars B Out :- premise-binds H Vars B B1, bound-vars Hs Vars B1 Out.

pred premise-binds i:term, i:list (pair term int), i:list int, o:list int.
premise-binds (app [global (indt Eq), _, app [global GR | Args], V]) Vars B Out :-
  coq.locate "eq" (indt Eq), prim-code GR _ _, !,
  mentions (app [global GR | Args]) Vars Used,
  if (std.forall Used (i\ std.mem! B i), var-index Vars V I) (Out = [I | B]) (Out = B).
premise-binds H Vars B Out :- table-vars Vars H Is, std.append Is B Out.

% The variables of a term outside primitive applications.
pred table-vars i:list (pair term int), i:term, o:list int.
table-vars Vars X [I] :- var-index Vars X I, !.
table-vars _ (app [global GR | _]) [] :- prim-code GR _ _, !.
table-vars Vars (app [_ | Args]) Is :- !, std.map Args (table-vars Vars) Iss, std.flatten Iss Is.
table-vars _ _ [].

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
      bound-vars Hyps Vars [] Bound,
      mentions (app [L, Rt]) Vars Used,
      if (std.forall Used (i\ std.mem! Bound i))
         (Head = {{ @Unify positive lp:PL lp:PR }})
         (Head = {{ @Rewrites positive lp:PL lp:PR }}))
     (code-of Ts (tk-rel R) Code,
      if (lattice-of R _ _)
         (split-last Args Keys Val, pats-of Ts Vars Keys PKeys, pat-of Ts Vars Val PVal,
          Head = {{ @Assign positive lp:Code lp:PKeys lp:PVal }})
         (pats-of Ts Vars Args PArgs, Head = {{ @Derive positive lp:Code lp:PArgs }})),
  C = {{ @Clause positive lp:Body lp:Head }}.

}}.
