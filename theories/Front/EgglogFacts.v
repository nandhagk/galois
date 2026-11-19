(** * Facts and encoders in the derive command

    This file declares the Elpi file [egglog.facts] of the command [Egglog] of [Derive.v].
    It defines the input rows of a program as a function of the parameters of its first
    relation, the meaning of each table as a relation on rows, and the encoder of each
    datatype, which writes a term of the datatype as an expression of the engine. An input
    list holds pairs of values or constructors of an input type. Each pair is a row of the
    input table of the list, and each constructor that a premise reads is a row of the table
    of that constructor.

    For example, [Path.facts edges] holds the row [(Path.edges_code, [x; y])] for each pair
    [(x, y)] of [edges], and [Vectors.encode_math] encodes a term of the datatype [math].

    Builds on: the Egglog model of expressions, the tables of [egglog.reading] and
    [egglog.lists], and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Model.

Import List.ListNotations.

(** * Facts and encoders *)

Elpi File egglog.facts lp:{{

% ---------------------------------------------------------------------------------------------
% Input sources and facts

kind source type.
type source tkey -> term -> source.   % the list (tk-src Head or tk-param I) and its element type

pred add-source i:list term, i:term, i:list source, o:list source.
add-source Ps H Acc Out :- in-premise H Elem Coll, !, source-key Ps Coll Key,
  coq.typecheck Elem Ty ok,
  if (std.exists Acc (s\ sigma T\ s = source Key T)) (Out = Acc)
     (std.append Acc [source Key Ty] Out).
add-source _ _ Acc Acc.

pred sources-of i:rel, i:term, i:list source, o:list source.
sources-of (rel _ NP _ _) KTy Acc Out :-
  with-params NP KTy [] (ps\ sigma Inst\
    coq.subst-prod ps KTy Inst,
    walk Inst [] [] (_\ hyps\ _\ std.fold hyps Acc (add-source ps) Out)).

pred source-coll i:list term, i:tkey, o:term.
source-coll Ps (tk-param I) P :- !, J is I - 1, std.nth J Ps P.
source-coll Ps (tk-src Head) (app [Head | Ps]).

pred mk-lams i:list term, i:list term, i:(list term -> term -> prop), o:term.
mk-lams [] Acc K T :- std.rev Acc Xs, K Xs T.
mk-lams [Ty | Tys] Acc K (fun `x` Ty B) :- pi x\ decl x `x` Ty => mk-lams Tys [x | Acc] K (B x).

pred row-list i:option term, i:term, o:term.
row-list none _ {{ @nil (positive * list positive) }}.
row-list (some Code) Vals
    {{ @cons (positive * list positive) (lp:Code, lp:Vals) (@nil (positive * list positive)) }}.

pred branch-of i:list table, i:constructor, i:term, o:term.
branch-of Ts K KTy B :- arg-types KTy Tys,
  if (find-table Ts (tk-con K) _ _ _) (code-of Ts (tk-con K) Code, Row = some Code)
     (Row = none),
  mk-lams Tys [] (xs\ body\ sigma Vals\ enc-list xs Vals, row-list Row Vals body) B.

pred rows-of i:list table, i:list term, i:source, o:term.
rows-of Ts Ps (source Key {{ prod lp:A lp:B }}) T :- !, check-value A, check-value B,
  code-of Ts Key Code,
  source-coll Ps Key Coll, PTy = {{ prod lp:A lp:B }},
  (pi p\ sigma E1 E2\ enc-by-ty A {{ @fst lp:A lp:B lp:p }} E1,
     enc-by-ty B {{ @snd lp:A lp:B lp:p }} E2, Row p = {{ (lp:Code, [lp:E1; lp:E2]) }}),
  RowF = fun `p` PTy Row,
  T = {{ @map lp:PTy (positive * list positive) lp:RowF lp:Coll }}.
rows-of Ts Ps (source Key (global (indt I))) T :- !, source-coll Ps Key Coll,
  coq.env.indt I _ _ _ _ Ks KTys,
  std.map2 Ks KTys (branch-of Ts) Bs,
  ElemTy = global (indt I),
  RetTy = {{ list (positive * list positive) }},
  F = fun `e` ElemTy (e\ match e (fun `e` ElemTy _\ RetTy) Bs),
  T = {{ @flat_map lp:ElemTy (positive * list positive) lp:F lp:Coll }}.
rows-of _ _ (source _ Ty) _ :- coq.error "Egglog: an input list has elements of type"
  {coq.term->string Ty} "which is neither an inductive nor a pair".

pred concat-rows i:list term, o:term.
concat-rows [] {{ @nil (positive * list positive) }}.
concat-rows [T] T :- !.
concat-rows [T | Ts] {{ @app (positive * list positive) lp:T lp:R }} :- concat-rows Ts R.

pred abs-params i:int, i:term, i:list term, i:(list term -> term -> prop), o:term.
abs-params 0 _ Acc K T :- !, std.rev Acc Ps, K Ps T.
abs-params N (prod Name Ty F) Acc K (fun Name Ty B) :- M is N - 1,
  pi p\ decl p Name Ty => abs-params M (F p) [p | Acc] K (B p).

pred mk-exists i:list term, i:list term, i:(list term -> term -> prop), o:term.
mk-exists [] Acc K T :- std.rev Acc Xs, K Xs T.
mk-exists [Ty | Tys] Acc K {{ @ex lp:Ty lp:F }} :-
  F = fun `x` Ty B, pi x\ decl x `x` Ty => mk-exists Tys [x | Acc] K (B x).

% The meaning of the rows of a relation over values: [r] is its code and [vs] its indices.
pred rel-disjunct i:list table, i:list term, i:term, i:term, i:rel, o:term.
rel-disjunct Ts Ps R0 VS (rel R NP _ _) D :-
  code-of Ts (tk-rel R) Code, coq.env.indt R _ _ _ Ar _ _, index-types NP Ar Tys,
  mk-exists Tys [] (xs\ b\ sigma Vs Args RApp\ enc-list xs Vs,
    std.append Ps xs Args, RApp = app [global (indt R) | Args],
    b = {{ lp:VS = lp:Vs /\ lp:RApp }}) Ex,
  D = {{ lp:R0 = lp:Code /\ lp:Ex }}.

pred disj i:list term, o:term.
disj [T] T :- !.
disj [T | Ts] {{ lp:T \/ lp:R }} :- disj Ts R.

pred mk-rel-fun i:list table, i:list term, i:list rel, i:term, o:term.
mk-rel-fun Ts Ps Relational FB
    (fun `r` {{ positive }} r\ fun `vs` {{ list positive }} vs\ B r vs) :-
  pi r vs\ sigma Ds Inp\ std.map Relational (rel-disjunct Ts Ps r vs) Ds,
    Inp = {{ In (lp:r, lp:vs) lp:FB }}, disj [Inp | Ds] (B r vs).

pred mk-inputs-fun i:term, o:term.
mk-inputs-fun FB
    (fun `r` {{ positive }} r\ fun `vs` {{ list positive }} vs\ {{ In (lp:r, lp:vs) lp:FB }}).

pred facts-body i:list table, i:list source, i:list term, o:term.
facts-body Ts Sources Ps FB :- std.map Sources (rows-of Ts Ps) Rows, concat-rows Rows FB.

% ---------------------------------------------------------------------------------------------
% Encoders of datatypes

% The expression of a constructor argument: the encoder [F] on the datatype [D], a literal on a
% value, and a chain of cons nodes on a list.
pred encode-arg i:list table, i:inductive, i:term, i:term, i:term, o:term.
encode-arg _ D F Ty X {{ lp:F lp:X }} :- Ty = global (indt D), !.
encode-arg _ _ _ Ty X {{ @Model.ELit positive lp:E }} :- value-type Ty, !, enc-by-ty Ty X E.
encode-arg Ts D F Ty X (app [Enc, X]) :- list-of Ty E, !,
  list-encoder Ts (encode-arg Ts D F) E Enc.
encode-arg _ _ _ Ty _ _ :- coq.error "Egglog: a datatype argument has type"
  {coq.term->string Ty} "which is neither a value type, the datatype itself nor a list".

pred encode-branch i:list table, i:inductive, i:term, i:constructor, i:term, o:term.
encode-branch Ts D F K KTy B :- arg-types KTy Tys, code-of Ts (tk-con K) Code,
  mk-lams Tys [] (xs\ body\ sigma Es L\ std.map2 Tys xs (encode-arg Ts D F) Es,
    list->term {{ @Model.expr positive }} Es L, body = {{ @Model.EApp positive lp:Code lp:L }}) B.

pred encoder i:list table, i:inductive, o:term.
encoder Ts D Fix :-
  T = global (indt D), RetTy = {{ @Model.expr positive }},
  coq.env.indt D _ _ _ _ Ks KTys,
  (pi f\ std.map2 Ks KTys (encode-branch Ts D f) (Bs f)),
  Fix = fix `encode` 0 {{ lp:T -> lp:RetTy }}
          (f\ fun `t` T (t\ match t (fun `t` T _\ RetTy) (Bs f))).

pred define-encoder i:list table, i:inductive, o:pair inductive term.
define-encoder Ts D (pr D (global (const C))) :- encoder Ts D Fix,
  std.assert-ok! (coq.elaborate-skeleton Fix Ty FixE) "Egglog: an ill-typed encoder",
  Name is "encode_" ^ {coq.gref->id (indt D)},
  coq.env.add-const Name FixE Ty @transparent! C.

}}.
