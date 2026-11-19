(** * Containers in the derive command

    This file declares the Elpi file [egglog.containers] of the command [Egglog] of
    [Derive.v]. It reads containers that the earlier parts do not: a datatype that holds
    another datatype, a list whose elements are lists, a pair that a pattern writes as one
    variable in a list, a list value in a pattern of a relation, and the congruence laws of
    lists of values and of pairs. The command runs with the rules of [with-containers], which
    take precedence over the rules of the earlier parts. Each rule handles one such case and
    leaves every other case to the earlier parts.

    For example, the constructor [Block (body : list stmt)] of a datatype [block] adds the
    datatype [stmt] to the program, with the tables of its constructors, and the encoder of
    [block] encodes each statement of [body] as the encoder of [stmt] does.

    Builds on: the parts of the command before it, the definitions that derived programs call,
    and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Front Require Import Spec DeriveHelpers.

(** * Containers *)

Elpi File egglog.containers lp:{{

% ---------------------------------------------------------------------------------------------
% The rules

% Run a goal with the rules of containers. Each rule is tried before the rules of the earlier
% parts for the same predicate, and a rule whose case does not apply leaves the call to them.
pred with-containers i:prop.
with-containers G :-
  (pi T Ds\ datatypes-of-type T Ds :- reachable-of T Ds, !) =>
  (pi Ts D Fix\ encoder Ts D Fix :- not (encoding D), !, (encoding D => encoder Ts D Fix)) =>
  (pi Ts D F Ty X E\ encode-arg Ts D F Ty X E :- container-arg Ts D F Ty X E, !) =>
  (pi Ts Encs Ty X E\ binder-expr Ts Encs Ty X E :- list-binder Ts Encs Ty X E, !) =>
  (pi Ts Vars Args L\ pats-of Ts Vars Args L :- !, value-pats Ts Vars Args L) =>
  (pi N T F Vars Hyps K\ walk (prod N T F) Vars Hyps K :- split-walk N T F Vars Hyps K, !) =>
  (pi Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps N T F B\
    eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps (prod N T F) (fun N T B) :-
      split-eq-fire Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps N T F B, !) =>
  (pi R NP H L\ law-hyp R NP H L :- container-law-hyp R NP H L, !) =>
  (pi Ty P\ prove "egglog_congruent" Ty P :- !, prove "egglog_congruent_containers" Ty P) =>
  G.

% ---------------------------------------------------------------------------------------------
% Datatypes of the program

% The datatypes of a relation index of type T: the datatype T, and every datatype that it
% reaches through the arguments of its constructors and the elements of their lists, in the
% order of a walk from T.
pred reachable-of i:term, o:list inductive.
reachable-of T Ds :- datatype T I, reachable-datatypes [I] [] Ds.

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
% Encoders

% The datatypes whose encoders the command is building.
pred encoding o:inductive.

% The expression of a constructor argument of the datatype D that the earlier parts do not
% read. A list, also of values, is a chain of cons nodes, and a term of another datatype D2 is
% the encoder of D2 applied to it. The encoder of D2 comes inside the encoder of D, so D2 must
% not hold D.
pred container-arg i:list table, i:inductive, i:term, i:term, i:term, o:term.
container-arg Ts D F Ty X (app [Enc, X]) :- list-of Ty E, !,
  list-encoder Ts (encode-arg Ts D F) E Enc.
container-arg Ts D _ Ty X (app [Fix, X]) :- datatype Ty D2, not (D2 = D), !,
  if (encoding D2)
     (coq.error "Egglog: the datatypes" {coq.gref->id (indt D)} "and"
       {coq.gref->id (indt D2)} "hold each other, and the command encodes no datatypes that"
       "hold each other.")
     (encoder Ts D2 Fix).

% The term of a binder of a list type in the environment of an equational clause is the chain of
% its cons nodes, also for a list of values.
pred list-binder i:list table, i:list (pair inductive term), i:term, i:term, o:term.
list-binder Ts Encs Ty X (app [Enc, X]) :- list-of Ty E,
  list-encoder Ts (binder-expr Ts Encs) E Enc.

% ---------------------------------------------------------------------------------------------
% List values in patterns

% The patterns of the arguments of a relation, an input row or a primitive. A list there is a
% value, so a list term is the value of its encoding.
pred value-pats i:list table, i:list (pair term int), i:list term, o:term.
value-pats Ts Vars Args L :-
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

% The proof of a fire lemma of an equation, where the two variables of the pair are the terms of
% its projections. A relation reads a list only as a value, where a variable element stops the
% command, so a fire lemma of a relation has no such pair.
pred split-eq-fire i:list table, i:inductive, i:int, i:list (pair inductive term), i:term,
  i:term, i:term, i:term, i:term, i:list term, i:list term, i:list term, i:name, i:term,
  i:(term -> term), o:(term -> term).
split-eq-fire Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps N T F B :- split-pair T F A B2, !,
  pi x\ sigma EA EB Vals1\ decl x N T =>
    (binder-expr Ts Encs A {{ @fst lp:A lp:B2 lp:x }} EA,
     binder-expr Ts Encs B2 {{ @snd lp:A lp:B2 lp:x }} EB,
     std.append Vals [EA, EB] Vals1,
     eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals1 Hyps (F x) (B x)).

% ---------------------------------------------------------------------------------------------
% Congruence laws of lists of values and of pairs

% A hypothesis of a closure law of the equational relation R that relates two arguments. It is
% their equality, or [Forall2 (pair_rel RA RB)] for two lists of pairs, where each of [RA] and
% [RB] is the equality or R.
pred container-law-hyp i:inductive, i:int, i:term, o:lawhyp.
container-law-hyp _ _ {{ @eq _ lp:A lp:B }} (hyp-all A B).
container-law-hyp R NP {{ @Forall2 _ _ (@pair_rel _ _ lp:RA lp:RB) lp:Xs lp:Ys }}
    (hyp-all Xs Ys) :-
  side-rel R NP RA, side-rel R NP RB.

% The relation between the sides of two pairs in a congruence law.
pred side-rel i:inductive, i:int, i:term.
side-rel _ _ {{ @eq _ }} :- !.
side-rel R NP Rel :- rel-applied R NP Rel.

}}.
