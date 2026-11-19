(** * Glue lemmas in the derive command

    This file declares the Elpi file [egglog.glue] of the command [Egglog] of [Derive.v]. The
    command proves that each relation over values holds exactly when its row is derived, and
    that each instance of an equation is a congruence of the encodings of its two sides. Each
    constructor with a clause gets a fire lemma, which says that its clause derives the
    conclusion from the premises. The tactics of [DeriveTactics.v] and [DeriveCongruence.v]
    prove the fire lemmas, the lemma [closed] and the lemmas [<R>_back] and [<R>_congruent], and
    the command calls them by name. The lemma [<R>_derived] says that each instance of [R] has
    its derived row. The command builds its proof as a fixpoint that takes an instance apart
    and applies the fire lemmas. The relations that read each other, as the relations of a
    mutual inductive can, share one fixpoint, which calls itself on each premise over one of
    them.

    For example, [Path.path_step_fires] says that the clause of [path_step] derives the row of
    [path edges x z] from the rows of [path edges x y] and [In (y, z) edges], and
    [Path.path_spec] says that [path edges x y] holds exactly when its row is derived.

    Builds on: the specifications and their derived rows, the runner's check of sorts, the
    groups of [egglog.reading], the patterns of [egglog.patterns], and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Model.
From Galois.Front Require Import Spec SpecFacts RunnerSig.

(** * Glue lemmas *)

Elpi File egglog.glue lp:{{

% ---------------------------------------------------------------------------------------------
% Glue: each relational constructor fires its clause

% The position of an element in a list, from 0.
pred position i:list term, i:term, o:int.
position [X | _] X 0 :- !.
position [_ | L] X N :- position L X M, N is M + 1.

% A proof that the N-th element of a concrete list is in it.
pred in-proof i:int, o:term.
in-proof 0 {{ or_introl eq_refl }} :- !.
in-proof N {{ or_intror lp:P }} :- M is N - 1, in-proof M P.

% The type of a fire lemma: the constructor type with each relational premise and the
% conclusion read as derived rows.
pred fire-type i:list table, i:list rel, i:term, i:term, i:term, i:term, o:term.
fire-type Ts Rels Prim Spec I (prod N Ty F) (prod N Ty1 F1) :- !,
  derived-of Ts Rels Prim Spec I Ty Ty1,
  pi x\ decl x N Ty => fire-type Ts Rels Prim Spec I (F x) (F1 x).
fire-type Ts Rels Prim Spec I C C1 :- derived-of Ts Rels Prim Spec I C C1.

pred derived-of i:list table, i:list rel, i:term, i:term, i:term, i:term, o:term.
derived-of Ts Rels Prim Spec I (app [global (indt R) | All])
    {{ @derived positive lp:Prim lp:Spec lp:I lp:Code lp:Vs }} :-
  find-rel Rels R NP ff, !, drop NP All Idx, code-of Ts (tk-rel R) Code,
  enc-list Idx Vs.
derived-of _ _ _ _ _ T T.

% The proof of a fire lemma: lambdas over the binders and premises, and the clause applied to
% the environment of the binders.
pred fire-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term int), i:list (pair term term), i:term, o:term.
fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars Hyps (prod N Ty F) (fun N Ty1 B) :- !,
  derived-of Ts Rels Prim Spec I Ty Ty1,
  pi x\ sigma Hyps1 L J Vars1\ decl x N Ty1 =>
    if (is-prop Ty)
       (std.append Hyps [pr x Ty1] Hyps1,
        fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars Hyps1 (F x) (B x))
       (std.length Vars L, J is L + 1, std.append Vars [pr x J] Vars1,
        fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars1 Hyps (F x) (B x)).
fire-proof Ts Rels Prim Spec I Ck Kn Ps Vars Hyps (app [global (indt R) | All]) P :-
  find-rel Rels R NP ff, drop NP All Idx, code-of Ts (tk-rel R) Code,
  enc-list Idx Vs,
  std.map Vars (v\ x\ v = pr x _) Xs, enc-list Xs EnvL,
  Env = {{ @env_of positive lp:EnvL }},
  Ck = {{ @Clause positive lp:BodyT (@Derive positive _ lp:ArgsP) }},
  body-proof Ts Rels Prim Spec I Env Ps Hyps BodyT BodyP,
  P = {{ @derived_clause positive lp:Prim lp:Spec lp:I lp:Ck lp:Env lp:Code lp:ArgsP lp:Vs
          lp:Kn eq_refl lp:BodyP _ }}.

pred body-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term term), i:term, o:term.
body-proof _ _ Prim Spec I Env _ [] _ {{ @derived_nil positive lp:Prim lp:Spec lp:I lp:Env }}.
body-proof Ts Rels Prim Spec I Env Ps [pr _ Ty | Hs]
    {{ @cons _ (@Computes _ lp:Q lp:Args lp:V) lp:Rest }} P :- !,
  body-proof Ts Rels Prim Spec I Env Ps Hs Rest RestP,
  computes-values Ty Vs W,
  P = {{ @derived_computes positive lp:Prim lp:Spec lp:I lp:Env lp:Q lp:Args lp:V lp:Vs lp:W
          lp:Rest _ _ _ lp:RestP }}.
body-proof Ts Rels Prim Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Holds _ lp:Code lp:Args) lp:Rest }} P :-
  body-proof Ts Rels Prim Spec I Env Ps Hs Rest RestP,
  hyp-row Ts Rels Prim Spec I Ps H Ty Code Vs Row,
  P = {{ @derived_row positive lp:Prim lp:Spec lp:I lp:Env lp:Code lp:Args lp:Vs lp:Rest _
          lp:Row lp:RestP }}.

% The derived row of a premise: an input row, or the premise itself for a relation.
pred hyp-row i:list table, i:list rel, i:term, i:term, i:term, i:list term, i:term, i:term,
  o:term, o:term, o:term.
hyp-row Ts _ Prim Spec I Ps _ Ty Code Vs Row :- in-premise Ty Elem Coll, !,
  input-key Ps Elem Coll Key Args _, code-of Ts Key Code, enc-list Args Vs,
  Row = {{ @derived_input positive lp:Prim lp:Spec lp:I lp:Code lp:Vs
            _ _ }}.
hyp-row _ _ _ _ _ _ H {{ @derived positive _ _ _ lp:Code lp:Vs }} Code Vs H.

% The engine accepts the sorts of the lowered program, or the command stops before it defines
% anything.
pred check-sorts i:string, i:term.
check-sorts Name Spec :-
  coq.reduction.vm.norm {{ @spec_ok positive lp:Spec }} {{ bool }} B,
  if (B = {{ true }}) true
     (coq.error {calc ("Egglog: the engine rejects the sorts of the program " ^ Name ^ ".")}
       "A primitive in a premise argument must apply to variables that a relation premise"
       "binds, and an equation premise must compute its result from such variables.").

pred run-tactic i:string, i:sealed-goal.
run-tactic Name G :- coq.ltac.open (g\ gl\ coq.ltac.call Name [] g gl ok) G [].

% Prove a type with an Ltac tactic, which runs on every hole of the proof term.
pred prove i:string, i:term, o:term.
prove Name Ty P :-
  std.assert-ok! (coq.typecheck P Ty) "Egglog: an ill-typed proof",
  coq.ltac.collect-goals P Goals _,
  if (std.forall Goals (run-tactic Name)) true
     (coq.error "Egglog: the tactic" Name "failed").

% Prove a type with an Ltac tactic, which runs on every hole of the proof term, or stop the
% command with a message.
pred prove-or i:string, i:term, o:term, i:string.
prove-or Name Ty P Msg :-
  std.assert-ok! (coq.typecheck P Ty) "Egglog: an ill-typed proof",
  coq.ltac.collect-goals P Goals _,
  if (std.forall Goals (run-tactic Name)) true (coq.error Msg).

% The first N binders of a type, as products when IsProd is tt and as abstractions otherwise,
% around the term that K builds from the parameters.
pred params-binders i:int, i:term, i:bool, i:list term, i:(list term -> term -> prop), o:term.
params-binders 0 _ _ Acc K T :- !, std.rev Acc Ps, K Ps T.
params-binders N (prod Name Ty F) IsProd Acc K Out :- M is N - 1,
  if (IsProd = tt) (Out = prod Name Ty B) (Out = fun Name Ty B),
  pi p\ decl p Name Ty => params-binders M (F p) IsProd [p | Acc] K (B p).

% The type and proof of the fire lemma of one constructor, whose clause is the Idx-th.
pred fire-lemma i:list table, i:list rel, i:term, i:term, i:int, i:term, i:term, i:int,
  o:term, o:term.
fire-lemma Ts Rels Spec Inputs NP KTy Ck Idx Ty P :-
  in-proof Idx Kn,
  bind-prim tt (prim\ ty\ params-binders NP KTy tt [] (ps\ t\ sigma Inst I\
    coq.subst-prod ps KTy Inst, I = app [Inputs | ps], fire-type Ts Rels prim Spec I Inst t) ty) Ty,
  bind-prim ff (prim\ p\ params-binders NP KTy ff [] (ps\ t\ sigma Inst I\
    coq.subst-prod ps KTy Inst, I = app [Inputs | ps],
    fire-proof Ts Rels prim Spec I Ck Kn ps [] [] Inst t) p) P.

pred idx-binders i:term, i:bool, i:list term, i:(list term -> term -> prop), o:term.
idx-binders (prod N0 Ty F) IsProd Acc K Out :- !, std.length Acc I, idx-name N0 I N,
  if (IsProd = tt) (Out = prod N Ty B) (Out = fun N Ty B),
  pi x\ decl x N Ty => idx-binders (F x) IsProd [x | Acc] K (B x).
idx-binders _ _ Acc K T :- std.rev Acc Xs, K Xs T.

% The name of an index binder: its own name, or a letter by its position when it has none.
pred idx-name i:name, i:int, o:name.
idx-name N I M :- coq.name->id N "_", I < 8, !,
  std.nth I ["a", "b", "c", "d", "e", "f", "g", "h"] S, coq.id->name S M.
idx-name N _ N.

% forall prim params idx, R params idx -> derived prim spec (inputs params) code idx
pred complete-type i:list table, i:term, i:term, i:rel, o:term.
complete-type Ts Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp I\ enc-list xs Vs,
        std.append ps xs Args, RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        c = prod `H` RApp
          (_\ {{ @derived positive lp:prim lp:Spec lp:I lp:Code lp:Vs }})) t) ty) Ty.

% forall params idx, relation params code idx -> R params idx
pred back-type i:list table, i:term, i:rel, o:term.
back-type Ts Relation (rel R NP _ _) T :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp Rel\ enc-list xs Vs,
      std.append ps xs Args, RApp = app [global (indt R) | Args],
      Rel = app [Relation | {std.append ps [Code, Vs]}], c = prod `H` Rel (_\ RApp)) t) T.

% forall prim params r vs, derived prim spec (inputs params) r vs -> relation params r vs
pred closed-type i:term, i:term, i:term, i:int, i:term, o:term.
closed-type Spec Inputs Relation NP Arity Ty :-
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma I Rel\ I = app [Inputs | ps],
      Rel = app [Relation | ps],
      t = {{ forall (r : positive) (vs : list positive),
               @derived positive lp:prim lp:Spec lp:I r vs -> lp:Rel r vs }}) ty) Ty.

% The equivalence of R with its derived rows, from the two directions.
pred spec-proof i:list table, i:rel, i:term, i:term, i:term, i:term, o:term.
spec-proof Ts (rel R NP _ _) Complete Back Closed _Inputs P :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  bind-prim ff (prim\ pf\ sigma PA\ prim-args prim PA,
    params-binders NP Arity ff [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst ff [] (xs\ c\ sigma Vs Args C1 B1 K1 CA KA\
        enc-list xs Vs,
        std.append ps xs Args, std.append PA Args CA, std.append PA ps KA,
        C1 = app [Complete | CA], B1 = app [Back | Args], K1 = app [Closed | KA],
        c = {{ conj lp:C1 (fun h => lp:B1 (lp:K1 lp:Code lp:Vs h)) }}) t) pf) P.

% forall prim params idx, R params idx <-> derived prim spec (inputs params) code idx
pred spec-type i:list table, i:term, i:term, i:rel, o:term.
spec-type Ts Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp I\ enc-list xs Vs,
        std.append ps xs Args, RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        c = {{ lp:RApp <-> @derived positive lp:prim lp:Spec lp:I lp:Code lp:Vs }}) t) ty) Ty.

% ---------------------------------------------------------------------------------------------
% One fixpoint for each group proves that each instance of a relation has its meaning

% The name of the lemma that each instance of the relation S has its meaning. It is
% [<S>_assigned] for a lattice relation and [<S>_derived] for any other relation over values.
pred complete-name i:inductive, o:string.
complete-name S N :- lattice-of S _ _, !, N is {coq.gref->id (indt S)} ^ "_assigned".
complete-name S N :- N is {coq.gref->id (indt S)} ^ "_derived".

% A lemma that the command has defined in the module of the program.
pred module-const i:string, o:term.
module-const N (global GR) :- coq.locate N GR, !.
module-const N _ :- coq.error "Egglog: the module of the program has no lemma" N.

% The constructor of a branch of a case, from the constructor applied to the parameters.
pred branch-constructor i:term, o:constructor.
branch-constructor (global (indc K)) K :- !.
branch-constructor (app [global (indc K) | _]) K.

% The position of a relation in its group, counted from N.
pred group-position i:list rel, i:inductive, i:int, o:int.
group-position [rel R _ _ _ | _] R N N :- !.
group-position [_ | Rs] R N M :- N1 is N + 1, group-position Rs R N1 M.

% The proof P of type Ty that each instance of the relation R of the group Group has its
% meaning, which is the lemma [complete-name R]. [Mean Prim S Ps Xs M] gives the meaning M of
% the instance of S at the parameters Ps and the indices Xs. The proof is the function of R in
% a fixpoint that has one function for each relation of the group. Each function takes an
% instance of its relation apart and applies the fire lemma of its constructor. A premise over
% a relation of the group is a subterm of the instance, so the fixpoint calls itself on it, as
% a fixpoint over a mutual inductive does. The lemma of its relation proves a premise over a
% relation of an earlier group.
pred complete-proof i:list rel, i:list rel,
  i:(pred i:term, i:inductive, i:list term, i:list term, o:term), i:rel, i:term, o:term.
complete-proof Rels Group Mean (rel R NP _ _) Ty P :-
  coq.env.indt R _ _ _ Arity _ _, index-count NP Arity Rno, group-position Group R 0 Idx,
  bind-prim ff (prim\ p\ sigma PA\ prim-args prim PA,
    params-binders NP Arity ff [] (ps\ t\ sigma MF\
      fix-block Rels Group Group [] Mean prim PA ps MF, t = mfix Idx Rno MF) p) P,
  complete-name R Name,
  std.assert-ok! (coq.typecheck P Ty) {calc ("Egglog: the proof of " ^ Name ^ " is ill-typed")}.

% The functions of the fixpoint of a group, one for each relation of Rest, and then their bodies.
% Scope maps each relation of the group before Rest to its function.
pred fix-block i:list rel, i:list rel, i:list rel, i:list (pair inductive term),
  i:(pred i:term, i:inductive, i:list term, i:list term, o:term), i:term, i:list term,
  i:list term, o:mfix-block.
fix-block Rels Group [rel S NP _ _ | Rest] Scope Mean Prim PA Ps (mfix-ty Name Rno Ty F) :-
  coq.env.indt S _ _ _ Arity _ _, index-count NP Arity Rno,
  fix-type Mean Prim Ps S Arity Ty,
  complete-name S N, coq.id->name N Name,
  pi f\ decl f Name Ty => fix-block Rels Group Rest [pr S f | Scope] Mean Prim PA Ps (F f).
fix-block Rels Group [] Scope Mean Prim PA Ps (mfix-bo Bodies) :-
  std.map Group (fix-body Rels Scope Mean Prim PA Ps) Bodies.

% forall idx, S params idx -> its meaning
pred fix-type i:(pred i:term, i:inductive, i:list term, i:list term, o:term), i:term,
  i:list term, i:inductive, i:term, o:term.
fix-type Mean Prim Ps S Arity Ty :-
  coq.subst-prod Ps Arity Inst,
  idx-binders Inst tt [] (xs\ c\ sigma Args SApp M\ std.append Ps xs Args,
    SApp = app [global (indt S) | Args], Mean Prim S Ps xs M,
    c = prod `H` SApp (_\ M)) Ty.

% The function of the relation S in the fixpoint of its group. It takes an instance of S apart
% and applies the fire lemma of each constructor to the proofs of the premises.
pred fix-body i:list rel, i:list (pair inductive term),
  i:(pred i:term, i:inductive, i:list term, i:list term, o:term), i:term, i:list term,
  i:list term, i:rel, o:term.
fix-body Rels Scope Mean Prim PA Ps (rel S _ _ _) B :-
  coq.env.indt S _ _ _ Arity _ _, coq.subst-prod Ps Arity Inst,
  idx-binders Inst ff [] (xs\ c\ sigma Args SApp Case\ std.append Ps xs Args,
    SApp = app [global (indt S) | Args], c = fun `H` SApp Case,
    pi h\ decl h `H` SApp =>
      coq.build-match h SApp
        (_\ vs\ _\ m\ sigma Zs\ split-last vs Zs _, Mean Prim S Ps Zs m)
        (k\ _\ vs\ tys\ b\ fire-branch Rels Scope PA Ps k vs tys b)
        (Case h)) B.

% The branch of a constructor applies its fire lemma to the primitive function, the parameters
% and the arguments of the constructor, with the proof of its meaning in place of each premise.
pred fire-branch i:list rel, i:list (pair inductive term), i:list term, i:list term, i:term,
  i:list term, i:list term, o:term.
fire-branch Rels Scope PA Ps K Vs Tys B :-
  branch-constructor K C,
  module-const {calc ({coq.gref->id (indc C)} ^ "_fires")} Fire,
  std.map2 Vs Tys (premise-proof Rels Scope PA Ps) Args,
  std.flatten [PA, Ps, Args] All, coq.mk-app Fire All B.

% The proof of the meaning of a premise V of type Ty. The function of its relation proves a
% premise over a relation of the group, the lemma of its relation proves a premise over another
% relation over values, and every other premise is its own proof.
pred premise-proof i:list rel, i:list (pair inductive term), i:list term, i:list term, i:term,
  i:term, o:term.
premise-proof Rels Scope PA Ps V (app [global (indt S) | All]) P :-
  find-rel Rels S NP ff, !, drop NP All Ys,
  if (std.lookup! Scope S F)
     (std.append Ys [V] As, coq.mk-app F As P)
     (complete-name S N, module-const N C, std.flatten [PA, Ps, Ys, [V]] As,
      coq.mk-app C As P).
premise-proof _ _ _ _ V _ V.

% The meaning of an instance of a relation over values in a program without lattice tables is
% its derived row.
pred derived-meaning i:list table, i:term, i:term, i:term, i:inductive, i:list term,
  i:list term, o:term.
derived-meaning Ts Spec Inputs Prim S Ps Xs
    {{ @derived positive lp:Prim lp:Spec lp:I lp:Code lp:Vs }} :-
  code-of Ts (tk-rel S) Code, enc-list Xs Vs, I = app [Inputs | Ps].

% ---------------------------------------------------------------------------------------------
% Glue of the relations over values of a program

% Define the glue of the relational relations of a program, a group of relations that read
% each other at a time.
pred define-glue i:list table, i:list rel, i:list term, i:term, i:term, i:term.
define-glue Ts Rels ClauseList Spec Inputs Relation :-
  std.filter Rels (r\ r = rel _ _ ff _) Relational,
  Relational = [rel R1 NP _ _ | _], !,
  coq.env.indt R1 _ _ _ Arity1 _ _,
  std.forall Relational (define-fires Ts Rels ClauseList Spec Inputs),
  closed-type Spec Inputs Relation NP Arity1 ClosedTy,
  prove "egglog_closed" ClosedTy ClosedP,
  coq.env.add-const "closed" ClosedP ClosedTy @opaque! ClosedC,
  read-groups Relational Groups,
  std.forall Groups (g\ std.forall g
    (define-spec Ts Rels g Spec Inputs Relation (global (const ClosedC)))).

define-glue _ _ _ _ _ _.

pred define-fires i:list table, i:list rel, i:list term, i:term, i:term, i:rel.
define-fires Ts Rels ClauseList Spec Inputs (rel R NP Eq Ss) :-
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Ck Idx Ty P C Name\
    clause-of Ts Rels (rel R NP Eq Ss) kty [Ck], position ClauseList Ck Idx,
    fire-lemma Ts Rels Spec Inputs NP kty Ck Idx Ty P,
    prove "egglog_leaf" Ty P,
    Name is {coq.gref->id (indc k)} ^ "_fires",
    coq.env.add-const Name P Ty @opaque! C,
    coq.hints.add-resolve (const C) "egglog_fire" 0 _).

pred define-spec i:list table, i:list rel, i:list rel, i:term, i:term, i:term, i:term, i:rel.
define-spec Ts Rels Group Spec Inputs Relation Closed (rel R NP Eq Ss) :-
  RName = {coq.gref->id (indt R)},
  complete-type Ts Spec Inputs (rel R NP Eq Ss) CTy,
  complete-proof Rels Group (derived-meaning Ts Spec Inputs) (rel R NP Eq Ss) CTy CP,
  coq.env.add-const {calc (RName ^ "_derived")} CP CTy @opaque! CC,
  coq.hints.add-resolve (const CC) "egglog_fire" 0 _,
  back-type Ts Relation (rel R NP Eq Ss) BTy,
  prove "egglog_back" BTy BP,
  coq.env.add-const {calc (RName ^ "_back")} BP BTy @opaque! BC,
  spec-proof Ts (rel R NP Eq Ss) (global (const CC)) (global (const BC)) Closed Inputs SP,
  spec-type Ts Spec Inputs (rel R NP Eq Ss) STy,
  std.assert-ok! (coq.elaborate-skeleton SP STy SP1) "Egglog: the glue lemma failed",
  coq.env.add-const {calc (RName ^ "_spec")} SP1 STy @opaque! _.

% ---------------------------------------------------------------------------------------------
% Glue of an equational relation: each relation instance is a congruence of encodings

pred enc-of i:list (pair inductive term), i:term, o:term.
enc-of Encs (global (indt D)) E :- std.exists Encs (p\ p = pr D E), !.

% The type of the fire lemma of an equational constructor.
pred eq-fire-type i:inductive, i:int, i:list (pair inductive term), i:term, i:term, i:term,
  i:term, o:term.
eq-fire-type R NP Encs Prim Spec I (prod N Ty F) (prod N Ty F1) :- !,
  pi x\ decl x N Ty => eq-fire-type R NP Encs Prim Spec I (F x) (F1 x).
eq-fire-type R NP Encs Prim Spec I (app [global (indt R) | All])
    {{ @congruent positive lp:Prim lp:Spec lp:I lp:TL lp:TR }} :-
  drop NP All [L, Rt], coq.env.indt R _ _ _ Ar _ _, index-types NP Ar [T, _],
  enc-of Encs T Enc, TL = app [Enc, L], TR = app [Enc, Rt].

% The term of a binder in the environment of an equational clause: a literal for a value, the
% encoder for a datatype, and the encoder of its lists for a list.
pred binder-expr i:list table, i:list (pair inductive term), i:term, i:term, o:term.
binder-expr _ _ Ty X {{ @Model.ELit positive lp:E }} :- value-type Ty, !, enc-by-ty Ty X E.
binder-expr _ Encs Ty X (app [Enc, X]) :- enc-of Encs Ty Enc, !.
binder-expr Ts Encs Ty X (app [Enc, X]) :- list-of Ty E,
  list-encoder Ts (binder-expr Ts Encs) E Enc.

pred eq-fire-proof i:list table, i:inductive, i:int, i:list (pair inductive term), i:term,
  i:term, i:term, i:term, i:term, i:list term, i:list term, i:list term, i:term, o:term.
eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps (prod N Ty F) (fun N Ty B) :- !,
  pi x\ sigma Vals1 Hyps1 E\ decl x N Ty =>
    if (is-prop Ty)
       (std.append Hyps [x] Hyps1,
        eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals Hyps1 (F x) (B x))
       (binder-expr Ts Encs Ty x E, std.append Vals [E] Vals1,
        eq-fire-proof Ts R NP Encs Prim Spec I Ck Kn Ps Vals1 Hyps (F x) (B x)).
eq-fire-proof _ R NP Encs Prim Spec I Ck Kn _ Vals Hyps (app [global (indt R) | All]) P :-
  drop NP All [L, Rt], coq.env.indt R _ _ _ Ar _ _, index-types NP Ar [T, _],
  enc-of Encs T Enc, TL = app [Enc, L], TR = app [Enc, Rt],
  list->term {{ @Model.expr positive }} Vals EnvL,
  Env = {{ @env_of (@Model.expr positive) lp:EnvL }},
  Ck = {{ @Clause positive lp:BodyT lp:Head }},
  if (Head = {{ @Unify positive lp:PL lp:PR }})
     (Which = {{ or_introl eq_refl }})
     (Head = {{ @Rewrites positive lp:PL lp:PR }}, Which = {{ or_intror eq_refl }}),
  eq-body-proof Prim I Env Hyps BodyT BodyP,
  P = {{ @congruent_clause positive lp:Prim lp:Spec lp:I lp:Ck lp:Env lp:PL lp:PR lp:TL lp:TR
          lp:Kn lp:Which lp:BodyP _ _ }}.

% The premises of a ground clause hold in the input rows: one hole per input row or primitive.
pred eq-body-proof i:term, i:term, i:term, i:list term, i:term, o:term.
eq-body-proof Prim I Env [] _ {{ @Forall_nil _ (@input_premise positive lp:Prim lp:I lp:Env) }}.
eq-body-proof Prim I Env [H | Hs] {{ @cons _ lp:Prem lp:Rest }} P :-
  eq-body-proof Prim I Env Hs Rest RestP,
  input-premise-proof H Prem PP,
  P = {{ @Forall_cons _ (@input_premise positive lp:Prim lp:I lp:Env) lp:Prem lp:Rest
          lp:PP lp:RestP }}.

pred input-premise-proof i:term, i:term, o:term.
input-premise-proof H {{ @Computes _ _ _ _ }}
    {{ ex_intro _ lp:Vs (ex_intro _ lp:W (conj _ (conj _ _))) }} :- !,
  coq.typecheck H Ty ok, computes-values Ty Vs W.
input-premise-proof _ _ {{ ex_intro _ _ (conj eq_refl _) }}.

% forall prim params t u, R params t u -> congruent prim spec (inputs params) (enc t) (enc u)
pred congruent-type i:list (pair inductive term), i:term, i:term, i:rel, o:term.
congruent-type Encs Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, index-types NP Arity [T, _], enc-of Encs T Enc,
  bind-prim tt (prim\ ty\
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Args RApp I TL TR A B\ std.append ps xs Args,
        RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        xs = [A, B], TL = app [Enc, A], TR = app [Enc, B],
        c = prod `H` RApp
          (_\ {{ @congruent positive lp:prim lp:Spec lp:I lp:TL lp:TR }})) t) ty) Ty.

pred define-eq-glue i:list table, i:list rel, i:list term, i:list (pair inductive term),
  i:term, i:term, i:rel.
define-eq-glue Ts Rels ClauseList Encs Spec Inputs (rel R NP tt Ss) :- !,
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Cs Ck\
    clause-of Ts Rels (rel R NP tt Ss) kty Cs,
    if (Cs = [Ck])
       (sigma Idx Kn Ty P C Name\ position ClauseList Ck Idx, in-proof Idx Kn,
        bind-prim tt (prim\ ty\ params-binders NP kty tt [] (ps\ t\ sigma Inst I\
          coq.subst-prod ps kty Inst, I = app [Inputs | ps],
          eq-fire-type R NP Encs prim Spec I Inst t) ty) Ty,
        bind-prim ff (prim\ pf\ params-binders NP kty ff [] (ps\ t\ sigma Inst I\
          coq.subst-prod ps kty Inst, I = app [Inputs | ps],
          eq-fire-proof Ts R NP Encs prim Spec I Ck Kn ps [] [] Inst t) pf) P,
        prove "egglog_leaf" Ty P,
        Name is {coq.gref->id (indc k)} ^ "_fires",
        coq.env.add-const Name P Ty @opaque! C,
        coq.hints.add-resolve (const C) "egglog_fire" 0 _)
       true),
  congruent-type Encs Spec Inputs (rel R NP tt Ss) CTy,
  prove "egglog_congruent" CTy CP,
  coq.env.add-const {calc ({coq.gref->id (indt R)} ^ "_congruent")} CP CTy @opaque! _.
define-eq-glue _ _ _ _ _ _ _.

}}.
