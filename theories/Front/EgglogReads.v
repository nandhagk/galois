(** * Equations beside relations in the derive command

    This file declares the Elpi file [egglog.reads] of the command [Egglog] of [Derive.v]. A
    program may have relations over values, lattice tables among them, beside equations, and a
    clause of an equation may read the rows of the relations and the values of the lattice
    tables. The relations get their glue as in a program without equations, and the lemma
    [closed] skips the clauses of the equations, which derive no row. An instance of an equation
    is then a read congruence of [SpecReads.v] over the derived rows, or over the rows and the
    merges of the meaning of lattice reads in a program with lattice tables. An instance of a
    rewrite is also a read step, by its lemma [<C>_steps]. A pair that a list of a clause holds
    as a variable is two terms of the environment of these lemmas, as it is in [egglog.glue].
    The tactics of [DeriveReads.v] prove these lemmas.

    For example, [Egglog Folds from known fold] reads the relation [known] and the equation
    [fold], and [Folds.fold_congruent] says that [fold prog t u] gives
    [read_congruent prim Folds.spec (derived prim Folds.spec (Folds.inputs prog)) no_values
    (Folds.encode_term t) (Folds.encode_term u)].

    Builds on: the meaning of equations that read derived rows, the meaning of lattice reads, the
    glue of [egglog.glue], the lattice tables of [egglog.lattice], and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Model.
From Galois.Front Require Import Spec SpecFacts SpecLattice SpecReads DeriveLattice.

(** * Equations beside relations *)

Elpi File egglog.reads lp:{{

% ---------------------------------------------------------------------------------------------
% Relations over values beside equations

% The glue of the relations over values of a program without lattice tables. Beside an
% equation, the lemma [closed] skips the clauses of the equation, which derive no row.
pred define-value-glue i:list table, i:list rel, i:list term, i:term, i:term, i:term.
define-value-glue Ts Rels ClauseList Spec Inputs Relation :-
  std.exists Rels (r\ r = rel _ _ tt _), !,
  define-mixed-glue Ts Rels ClauseList Spec Inputs Relation.
define-value-glue Ts Rels ClauseList Spec Inputs Relation :-
  define-glue Ts Rels ClauseList Spec Inputs Relation.

% The glue of the relations over values of a program with equations, as in define-glue, a
% group of relations that read each other at a time.
pred define-mixed-glue i:list table, i:list rel, i:list term, i:term, i:term, i:term.
define-mixed-glue Ts Rels ClauseList Spec Inputs Relation :-
  std.filter Rels (r\ r = rel _ _ ff _) Relational,
  Relational = [rel R1 NP _ _ | _], !,
  coq.env.indt R1 _ _ _ Arity1 _ _,
  std.forall Relational (define-fires Ts Rels ClauseList Spec Inputs),
  closed-type Spec Inputs Relation NP Arity1 ClosedTy,
  prove "egglog_mixed_closed" ClosedTy ClosedP,
  coq.env.add-const "closed" ClosedP ClosedTy @opaque! ClosedC,
  read-groups Relational Groups,
  std.forall Groups (g\ std.forall g
    (define-spec Ts Rels g Spec Inputs Relation (global (const ClosedC)))).
define-mixed-glue _ _ _ _ _ _.

% ---------------------------------------------------------------------------------------------
% Equations that read relations over values

% The glue of the equations of a program. Without relations over values, an instance of an
% equation is a congruence of the input rows. Beside relations over values, it is a read
% congruence over the meaning of the relations.
pred define-equation-glue i:list table, i:list rel, i:list rel, i:list term,
  i:list (pair inductive term), i:term, i:term.
define-equation-glue Ts Rels _ ClauseList Encs Spec Inputs :-
  not (std.exists Rels (r\ r = rel _ _ ff _)), !,
  std.forall Rels (define-eq-glue Ts Rels ClauseList Encs Spec Inputs).
define-equation-glue Ts Rels Lattices ClauseList Encs Spec Inputs :-
  std.forall Rels (define-read-glue Ts Rels Lattices ClauseList Encs Spec Inputs).

% The rows and the read values that the premises of an equation read: the derived rows and no
% value without lattice tables, and the rows and the merges of the meaning of lattice reads with
% them.
pred read-meaning i:list rel, i:term, i:term, i:term, o:term, o:term.
read-meaning [] Prim Spec I {{ @derived positive lp:Prim lp:Spec lp:I }}
    {{ @no_values positive }} :- !.
read-meaning _ Prim Spec I {{ @lat_derived positive lp:Prim (prim_merge lp:Prim) lp:Spec lp:I }}
    {{ @lat_merged positive lp:Prim (prim_merge lp:Prim) lp:Spec lp:I }}.

% The constructor of the rows of the meaning that takes an input row.
pred read-input i:list rel, i:term, i:term, i:term, o:term.
read-input [] Prim Spec I {{ @derived_input positive lp:Prim lp:Spec lp:I }} :- !.
read-input _ Prim Spec I
    {{ @lat_derived_input positive lp:Prim (prim_merge lp:Prim) lp:Spec lp:I }}.

% A lemma of a clause of an equation: the fire lemma, which concludes a read congruence, or the
% step lemma of a rewrite, which concludes a read step.
kind readlemma type.
type read-fires readlemma.
type read-steps readlemma.

% The conclusion of a lemma of a clause of an equation, between the encodings of its two sides.
pred read-conclusion i:readlemma, i:term, i:term, i:term, i:term, i:term, i:term, o:term.
read-conclusion read-fires Prim Spec PR QR TL TR
    {{ @read_congruent positive lp:Prim lp:Spec lp:PR lp:QR lp:TL lp:TR }}.
read-conclusion read-steps Prim Spec PR QR TL TR
    {{ @read_step positive lp:Prim lp:Spec lp:PR lp:QR lp:TL lp:TR }}.

% The type of a lemma of a clause of an equation: the constructor type with the conclusion read
% as a read congruence or a read step of the encodings of its two sides.
pred read-fire-type i:readlemma, i:inductive, i:int, i:list (pair inductive term), i:list rel,
  i:term, i:term, i:term, i:term, o:term.
read-fire-type K R NP Encs Lats Prim Spec I (prod N Ty F) (prod N Ty F1) :- !,
  pi x\ decl x N Ty => read-fire-type K R NP Encs Lats Prim Spec I (F x) (F1 x).
read-fire-type K R NP Encs Lats Prim Spec I (app [global (indt R) | All]) C :-
  drop NP All [L, Rt], coq.env.indt R _ _ _ Ar _ _, index-types NP Ar [T, _],
  enc-of Encs T Enc, TL = app [Enc, L], TR = app [Enc, Rt],
  read-meaning Lats Prim Spec I PR QR, read-conclusion K Prim Spec PR QR TL TR C.

% The proof of a lemma of a clause of an equation: lambdas over the binders and the premises,
% and the clause applied to the environment of the terms of the binders. A pair that a list
% holds as a variable is two terms of the environment, as split-read-fire says.
pred read-fire-proof i:readlemma, i:list table, i:inductive, i:int,
  i:list (pair inductive term), i:list rel, i:term, i:term, i:term, i:term, i:term,
  i:list term, i:list term, i:term, o:term.
read-fire-proof K Ts R NP Encs Lats Prim Spec I Ck Kn Vals Hyps (prod N T F) (fun N T B) :-
  split-read-fire K Ts R NP Encs Lats Prim Spec I Ck Kn Vals Hyps N T F B, !.
read-fire-proof K Ts R NP Encs Lats Prim Spec I Ck Kn Vals Hyps (prod N Ty F) (fun N Ty B) :- !,
  pi x\ sigma Vals1 Hyps1 E\ decl x N Ty =>
    if (is-prop Ty)
       (std.append Hyps [x] Hyps1,
        read-fire-proof K Ts R NP Encs Lats Prim Spec I Ck Kn Vals Hyps1 (F x) (B x))
       (binder-expr Ts Encs Ty x E, std.append Vals [E] Vals1,
        read-fire-proof K Ts R NP Encs Lats Prim Spec I Ck Kn Vals1 Hyps (F x) (B x)).
read-fire-proof K _ R NP Encs Lats Prim Spec I Ck Kn Vals Hyps (app [global (indt R) | All]) P :-
  drop NP All [L, Rt], coq.env.indt R _ _ _ Ar _ _, index-types NP Ar [T, _],
  enc-of Encs T Enc, TL = app [Enc, L], TR = app [Enc, Rt],
  read-meaning Lats Prim Spec I PR QR, read-input Lats Prim Spec I Input,
  list->term {{ @Model.expr positive }} Vals EnvL,
  Env = {{ @env_of (@Model.expr positive) lp:EnvL }},
  Ck = {{ @Clause positive lp:BodyT lp:Head }},
  if (Head = {{ @Unify positive lp:PL lp:PRt }})
     (Which = {{ or_introl eq_refl }})
     (Head = {{ @Rewrites positive lp:PL lp:PRt }}, Which = {{ or_intror eq_refl }}),
  read-body-proof Prim PR QR Input Env Hyps BodyT BodyP,
  read-clause-proof K Prim Spec PR QR Ck Env PL PRt TL TR Kn Which BodyP P.

% The proof of a lemma of a clause of an equation, where the two variables of the pair are the
% terms of its projections, as in split-eq-fire.
pred split-read-fire i:readlemma, i:list table, i:inductive, i:int,
  i:list (pair inductive term), i:list rel, i:term, i:term, i:term, i:term, i:term,
  i:list term, i:list term, i:name, i:term, i:(term -> term), o:(term -> term).
split-read-fire K Ts R NP Encs Lats Prim Spec I Ck Kn Vals Hyps N T F B :-
  split-pair T F A B2, !,
  pi x\ sigma Vals1\ decl x N T =>
    (pair-vals Ts Encs A B2 x Vals Vals1,
     read-fire-proof K Ts R NP Encs Lats Prim Spec I Ck Kn Vals1 Hyps (F x) (B x)).

% The clause of a read congruence or of a read step, applied to the proof of its body.
pred read-clause-proof i:readlemma, i:term, i:term, i:term, i:term, i:term, i:term, i:term,
  i:term, i:term, i:term, i:term, i:term, i:term, o:term.
read-clause-proof read-fires Prim Spec PR QR Ck Env PL PRt TL TR Kn Which BodyP
    {{ @read_clause positive lp:Prim lp:Spec lp:PR lp:QR lp:Ck lp:Env lp:PL lp:PRt lp:TL lp:TR
         lp:Kn lp:Which lp:BodyP _ _ }}.
read-clause-proof read-steps Prim Spec PR QR Ck Env PL PRt TL TR Kn _ BodyP
    {{ @read_step_clause positive lp:Prim lp:Spec lp:PR lp:QR lp:Ck lp:Env lp:PL lp:PRt lp:TL
         lp:TR lp:Kn eq_refl lp:BodyP _ _ }}.

% The premises of a clause of an equation read rows, values and primitives, with one hole for
% the row, the value or the result of each, and two holes for the table and the row of an input
% premise.
pred read-body-proof i:term, i:term, i:term, i:term, i:term, i:list term, i:term, o:term.
read-body-proof Prim PR QR _ Env [] _
    {{ @Forall_nil _ (@read_premise positive lp:Prim lp:PR lp:QR lp:Env) }}.
read-body-proof Prim PR QR Input Env [H | Hs] {{ @cons _ lp:Prem lp:Rest }} P :-
  read-body-proof Prim PR QR Input Env Hs Rest RestP,
  read-premise-proof Input H Prem PP,
  P = {{ @Forall_cons _ (@read_premise positive lp:Prim lp:PR lp:QR lp:Env) lp:Prem lp:Rest
          lp:PP lp:RestP }}.

pred read-premise-proof i:term, i:term, i:term, o:term.
read-premise-proof _ H {{ @Computes _ _ _ _ }}
    {{ ex_intro _ lp:Vs (ex_intro _ lp:W (conj _ (conj _ _))) }} :- !,
  coq.typecheck H Ty ok, computes-values Ty Vs W.
read-premise-proof _ _ {{ @Equals _ _ _ _ }}
    {{ ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl _))) }} :- !.
read-premise-proof Input H _ {{ ex_intro _ _ (conj eq_refl (lp:Input _ _ _ _)) }} :-
  coq.typecheck H Ty ok, in-premise Ty _ _, !.
read-premise-proof _ _ _ {{ ex_intro _ _ (conj eq_refl _) }}.

% forall prim params t u, R params t u -> read_congruent prim spec rows values (enc t) (enc u)
pred read-congruent-type i:list (pair inductive term), i:list rel, i:term, i:term, i:rel,
  o:term.
read-congruent-type Encs Lats Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, index-types NP Arity [T, _], enc-of Encs T Enc,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Args RApp I TL TR A B PR QR\ std.append ps xs Args,
        RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        xs = [A, B], TL = app [Enc, A], TR = app [Enc, B],
        read-meaning Lats prim Spec I PR QR,
        c = prod `H` RApp
          (_\ {{ @read_congruent positive lp:prim lp:Spec lp:PR lp:QR lp:TL lp:TR }})) t) ty) Ty.

% Define the lemma K of the clause Ck of the constructor C0 of an equation, where Kn proves
% that Ck is a clause of the program: the fire lemma <C0>_fires, which joins the hint database
% egglog_fire, or the step lemma <C0>_steps of a rewrite.
pred define-read-lemma i:readlemma, i:list table, i:rel, i:list (pair inductive term),
  i:list rel, i:term, i:term, i:term, i:term, i:term, i:constructor.
define-read-lemma K Ts (rel R NP _ _) Encs Lats Spec Inputs Ck Kn KTy C0 :-
  bind-prim tt (prim\ ty\ params-binders NP KTy tt [] (ps\ t\ sigma Inst I\
    coq.subst-prod ps KTy Inst, I = app [Inputs | ps],
    read-fire-type K R NP Encs Lats prim Spec I Inst t) ty) Ty,
  bind-prim ff (prim\ pf\ params-binders NP KTy ff [] (ps\ t\ sigma Inst I\
    coq.subst-prod ps KTy Inst, I = app [Inputs | ps],
    read-fire-proof K Ts R NP Encs Lats prim Spec I Ck Kn [] [] Inst t) pf) P,
  prove "egglog_read_leaf" Ty P,
  if (K = read-fires) (Suffix = "_fires") (Suffix = "_steps"),
  Name is {coq.gref->id (indc C0)} ^ Suffix,
  coq.env.add-const Name P Ty @opaque! C,
  if (K = read-fires) (coq.hints.add-resolve (const C) "egglog_fire" 0 _) true.

% Define the fire lemma of each clause of an equation that reads relations over values, the step
% lemma of each rewrite, and the lemma that each instance of the equation is a read congruence.
pred define-read-glue i:list table, i:list rel, i:list rel, i:list term,
  i:list (pair inductive term), i:term, i:term, i:rel.
define-read-glue Ts Rels Lats ClauseList Encs Spec Inputs (rel R NP tt Ss) :- !,
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Cs Ck\
    clause-of Ts Rels (rel R NP tt Ss) kty Cs,
    if (Cs = [Ck])
       (sigma Idx Kn\ position ClauseList Ck Idx, in-proof Idx Kn,
        define-read-lemma read-fires Ts (rel R NP tt Ss) Encs Lats Spec Inputs Ck Kn kty k,
        if (Ck = {{ @Clause positive _ (@Rewrites positive _ _) }})
           (define-read-lemma read-steps Ts (rel R NP tt Ss) Encs Lats Spec Inputs Ck Kn kty k)
           true)
       true),
  read-congruent-type Encs Lats Spec Inputs (rel R NP tt Ss) CTy,
  prove "egglog_read_congruent" CTy CP,
  coq.env.add-const {calc ({coq.gref->id (indt R)} ^ "_congruent")} CP CTy @opaque! _.
define-read-glue _ _ _ _ _ _ _ _.

}}.
