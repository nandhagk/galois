(** * Lattice tables in the derive command

    This file declares the Elpi file [egglog.lattice] of the command [Egglog] of [Derive.v].
    After [with Ops], the declaration [merge R g] makes [R] a lattice table, whose last index
    is its value and whose merge is the primitive [g] of [Ops]. A constructor of [R] assigns a
    value, and a premise over [R] reads the stored value. The file reads these declarations,
    defines the meaning of the lattice tables of a program, and proves its glue lemmas with the
    tactics of [DeriveLattice.v].

    For example, [Egglog Paths from dist with Ops merge dist Pos.min] makes [dist] a lattice
    table whose merge is [Pos.min], and [Paths.dist_spec] says that [dist edges a b d] holds
    exactly when the clauses assign [d] at the key [[a; b]].

    Builds on: the meaning of lattice reads, the merge of [DeriveLattice.v], the glue of
    [egglog.glue], and Elpi. *)

From Stdlib Require Import List PArith.
From elpi Require Import elpi.
From Galois.Front Require Import Spec SpecFacts SpecLattice DeriveLattice.

(** * Lattice tables *)

Elpi File egglog.lattice lp:{{

% ---------------------------------------------------------------------------------------------
% Lattice tables

% A declared lattice relation, with the code of its merge and the merge function.
kind latdecl type.
type latdecl inductive -> term -> term -> latdecl.

% Run a goal with the lattice relations in scope.
pred with-lattices i:list latdecl, i:prop.
with-lattices [] G :- G.
with-lattices [latdecl I C F | Rest] G :- lattice-of I C F => with-lattices Rest G.

% The declaration 'merge R g'. R is a relation that the command reads, and g is a primitive of
% the set after 'with' that takes two values of the type of the last index of R and returns
% one.
pred lattice-decl i:list inductive, i:pair string string, o:latdecl.
lattice-decl Is (pr RName GName) (latdecl I Code (global GR)) :-
  coq.locate-all RName RLocs,
  if (std.mem RLocs (loc-gref (indt I0)), std.mem! Is I0) (I = I0)
     (coq.error "Egglog: the lattice table" RName "is not a relation that the command reads."),
  coq.locate-all GName GLocs,
  if (std.mem GLocs (loc-gref GR0)) (GR = GR0)
     (coq.error "Egglog: the merge" GName "of" RName "is not a function."),
  if (prim-of GR Code0) (Code = Code0)
     (coq.error "Egglog: the merge" GName "of" RName
       "is not a primitive of the set after 'with'."),
  check-merge-type I RName GR GName.

% The merge of a lattice relation takes two values of the type of its last index and returns
% one of that type.
pred check-merge-type i:inductive, i:string, i:gref, i:string.
check-merge-type I RName GR GName :-
  coq.env.indt I _ NP _ Arity _ _, index-types NP Arity Tys,
  if (Tys = []) (coq.error "Egglog: the lattice table" RName "has no index for its value.")
     true,
  std.last Tys T,
  coq.env.typeof GR GTy,
  if (GTy = prod _ A (_\ prod _ B (_\ C)), coq.unify-eq A T ok, coq.unify-eq B T ok,
      coq.unify-eq C T ok) true
     (coq.error "Egglog: the merge" GName "of" RName "must have the type"
       {coq.term->string {{ lp:T -> lp:T -> lp:T }}}).

% Each relation is declared a lattice table at most once.
pred distinct-lattices i:list latdecl.
distinct-lattices [].
distinct-lattices [latdecl I _ _ | Rest] :-
  if (std.exists Rest (d\ d = latdecl I _ _))
     (coq.error "Egglog: the lattice table" {coq.gref->id (indt I)} "is declared twice.") true,
  distinct-lattices Rest.

% ---------------------------------------------------------------------------------------------
% The meaning of lattice tables

% The meaning of the rows of a program with lattice tables. It is a disjunction even when no
% relation over values has rows, so that the tactics read it in one way.
pred mk-lat-rel-fun i:list table, i:list term, i:list rel, i:term, o:term.
mk-lat-rel-fun Ts Ps Relational FB
    (fun `r` {{ positive }} r\ fun `vs` {{ list positive }} vs\ B r vs) :-
  pi r vs\ sigma Ds Inp\ std.map Relational (rel-disjunct Ts Ps r vs) Ds,
    Inp = {{ In (lp:r, lp:vs) lp:FB }},
    if (Ds = []) (B r vs = {{ lp:Inp \/ False }}) (disj [Inp | Ds] (B r vs)).

% The meaning of the values of a lattice relation: [f] is its code, [ks] its keys and [w] its
% value.
pred lat-disjunct i:list table, i:list term, i:term, i:term, i:term, i:rel, o:term.
lat-disjunct Ts Ps F0 KS W0 (rel R NP _ _) D :-
  code-of Ts (tk-rel R) Code, coq.env.indt R _ _ _ Ar _ _, index-types NP Ar Tys,
  mk-exists Tys [] (xs\ b\ sigma Keys Val Ks W Args RApp\ split-last xs Keys Val,
    enc-list Keys Ks, enc-term Val W, std.append Ps xs Args,
    RApp = app [global (indt R) | Args],
    b = {{ lp:KS = lp:Ks /\ lp:W0 = lp:W /\ lp:RApp }}) Ex,
  D = {{ lp:F0 = lp:Code /\ lp:Ex }}.

% The meaning of the lattice tables of a program, as a relation on codes, keys and values.
pred mk-lat-fun i:list table, i:list term, i:list rel, o:term.
mk-lat-fun Ts Ps Lattices
    (fun `f` {{ positive }} f\ fun `ks` {{ list positive }} ks\ fun `w` {{ positive }} w\
       B f ks w) :-
  pi f ks w\ sigma Ds\ std.map Lattices (lat-disjunct Ts Ps f ks w) Ds, disj Ds (B f ks w).

% ---------------------------------------------------------------------------------------------
% Glue of a program with lattice tables

% The meaning of the indices of a relation over values in a program with lattice tables: a
% value that the clauses assign at the keys for a lattice relation, and a row otherwise.
pred lat-meaning i:term, i:term, i:term, i:term, i:inductive, i:term, i:list term, o:term.
lat-meaning Prim Merge Spec I R Code Xs T :- lattice-of R _ _, !,
  split-last Xs Keys Val, enc-list Keys Ks, enc-term Val W,
  T = {{ @lat_assigned positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Ks lp:W }}.
lat-meaning Prim Merge Spec I _ Code Xs T :- enc-list Xs Vs,
  T = {{ @lat_derived positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Vs }}.

% A premise or the conclusion of a fire lemma, with a relation over values read by its meaning.
pred lat-derived-of i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, o:term.
lat-derived-of Ts Rels Prim Merge Spec I (app [global (indt R) | All]) T :-
  find-rel Rels R NP ff, !, drop NP All Idx, code-of Ts (tk-rel R) Code,
  lat-meaning Prim Merge Spec I R Code Idx T.
lat-derived-of _ _ _ _ _ _ T T.

% The type of a fire lemma: the constructor type with each premise and the conclusion over a
% relation over values read by its meaning.
pred lat-fire-type i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, o:term.
lat-fire-type Ts Rels Prim Merge Spec I (prod N Ty F) (prod N Ty1 F1) :- !,
  lat-derived-of Ts Rels Prim Merge Spec I Ty Ty1,
  pi x\ decl x N Ty => lat-fire-type Ts Rels Prim Merge Spec I (F x) (F1 x).
lat-fire-type Ts Rels Prim Merge Spec I C C1 :- lat-derived-of Ts Rels Prim Merge Spec I C C1.

% The proof of a fire lemma: lambdas over the binders and premises, and the clause of the
% constructor applied to the environment of the binders.
pred lat-fire-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:term, i:term,
  i:list term, i:list (pair term int), i:list (pair term term), i:term, o:term.
lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars Hyps (prod N Ty F) (fun N Ty1 B) :- !,
  lat-derived-of Ts Rels Prim Merge Spec I Ty Ty1,
  pi x\ sigma Hyps1 L J Vars1\ decl x N Ty1 =>
    if (is-prop Ty)
       (std.append Hyps [pr x Ty1] Hyps1,
        lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars Hyps1 (F x) (B x))
       (std.length Vars L, J is L + 1, std.append Vars [pr x J] Vars1,
        lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars1 Hyps (F x) (B x)).
lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn Ps Vars Hyps (app [global (indt R) | All]) P :-
  find-rel Rels R NP ff, drop NP All Idx, code-of Ts (tk-rel R) Code,
  std.map Vars (v\ x\ v = pr x _) Xs, enc-list Xs EnvL,
  Env = {{ @env_of positive lp:EnvL }},
  if (lattice-of R _ _)
     (split-last Idx Keys Val, enc-list Keys Ks, enc-term Val W,
      Ck = {{ @Clause positive lp:BodyT (@Assign positive _ lp:ArgsP lp:VP) }},
      lat-body-proof Ts Prim Merge Spec I Env Ps Hyps BodyT BodyP,
      P = {{ @lat_assigned_clause positive lp:Prim lp:Merge lp:Spec lp:I lp:Ck lp:Env lp:Code
              lp:ArgsP lp:VP lp:Ks lp:W lp:Kn eq_refl lp:BodyP _ _ }})
     (enc-list Idx Vs,
      Ck = {{ @Clause positive lp:BodyT (@Derive positive _ lp:ArgsP) }},
      lat-body-proof Ts Prim Merge Spec I Env Ps Hyps BodyT BodyP,
      P = {{ @lat_derived_clause positive lp:Prim lp:Merge lp:Spec lp:I lp:Ck lp:Env lp:Code
              lp:ArgsP lp:Vs lp:Kn eq_refl lp:BodyP _ }}).

% The proof of a body: a row for each relation premise, the merge of one assigned value for
% each read of a lattice table, and holes for the primitive premises.
pred lat-body-proof i:list table, i:term, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term term), i:term, o:term.
lat-body-proof _ Prim Merge Spec I Env _ [] _
    {{ @lat_body_nil positive lp:Prim lp:Merge lp:Spec lp:I lp:Env }}.
lat-body-proof Ts Prim Merge Spec I Env Ps [pr _ Ty | Hs]
    {{ @cons _ (@Computes _ lp:Q lp:Args lp:V) lp:Rest }} P :- !,
  lat-body-proof Ts Prim Merge Spec I Env Ps Hs Rest RestP,
  computes-values Ty Vs W,
  P = {{ @lat_body_computes positive lp:Prim lp:Merge lp:Spec lp:I lp:Env lp:Q lp:Args lp:V
          lp:Vs lp:W lp:Rest _ _ _ lp:RestP }}.
lat-body-proof Ts Prim Merge Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Equals _ lp:Code lp:Args lp:V) lp:Rest }} P :- !,
  lat-body-proof Ts Prim Merge Spec I Env Ps Hs Rest RestP,
  Ty = {{ @lat_assigned positive _ _ _ _ _ lp:Ks lp:W }},
  P = {{ @lat_body_read positive lp:Prim lp:Merge lp:Spec lp:I lp:Env lp:Code lp:Args lp:V
          lp:Ks lp:W lp:Rest _ _
          (@lat_merged_one positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Ks lp:W lp:H)
          lp:RestP }}.
lat-body-proof Ts Prim Merge Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Holds _ lp:Code lp:Args) lp:Rest }} P :-
  lat-body-proof Ts Prim Merge Spec I Env Ps Hs Rest RestP,
  lat-hyp-row Ts Prim Merge Spec I Ps Ty Code H Vs Row,
  P = {{ @lat_body_row positive lp:Prim lp:Merge lp:Spec lp:I lp:Env lp:Code lp:Args lp:Vs
          lp:Rest _ lp:Row lp:RestP }}.

% The row of a relation premise: an input row, or the premise itself for a relation over values.
pred lat-hyp-row i:list table, i:term, i:term, i:term, i:term, i:list term, i:term, i:term,
  i:term, o:term, o:term.
lat-hyp-row Ts Prim Merge Spec I Ps Ty Code _ Vs Row :- in-premise Ty Elem Coll, !,
  input-key Ps Elem Coll Key Args _, code-of Ts Key Code, enc-list Args Vs,
  Row = {{ @lat_derived_input positive lp:Prim lp:Merge lp:Spec lp:I lp:Code lp:Vs _ _ }}.
lat-hyp-row _ _ _ _ _ _ {{ @lat_derived positive _ _ _ _ lp:Code lp:Vs }} Code H Vs H.

% Define the fire lemma of each constructor of a relation over values.
pred define-lat-fires i:list table, i:list rel, i:list term, i:term, i:term, i:term, i:term,
  i:rel.
define-lat-fires Ts Rels ClauseList Prim Merge Spec Inputs (rel R NP Eq Ss) :-
  coq.env.indt R _ _ _ _ Ks KTys,
  std.forall2 Ks KTys (k\ kty\ sigma Ck Idx Kn Ty P C Name\
    clause-of Ts Rels (rel R NP Eq Ss) kty [Ck], position ClauseList Ck Idx, in-proof Idx Kn,
    params-binders NP kty tt [] (ps\ t\ sigma Inst I\ coq.subst-prod ps kty Inst,
      I = app [Inputs | ps], lat-fire-type Ts Rels Prim Merge Spec I Inst t) Ty,
    params-binders NP kty ff [] (ps\ t\ sigma Inst I\ coq.subst-prod ps kty Inst,
      I = app [Inputs | ps], lat-fire-proof Ts Rels Prim Merge Spec I Ck Kn ps [] [] Inst t) P,
    prove "egglog_leaf" Ty P,
    Name is {coq.gref->id (indc k)} ^ "_fires",
    coq.env.add-const Name P Ty @opaque! C,
    coq.hints.add-resolve (const C) "egglog_fire" 0 _).

% A body reads the lattice table with code [Code].
pred body-reads i:term, i:term.
body-reads {{ @cons _ (@Equals _ lp:C _ _) _ }} Code :- C = Code, !.
body-reads {{ @cons _ _ lp:Rest }} Code :- body-reads Rest Code.

% A clause that derives a row or assigns a value reads the lattice relation. The glue of an
% equation reads assigned values, so a read in an equation needs no closure under the merge.
pred read-lattice i:list table, i:list term, i:rel.
read-lattice Ts ClauseList (rel R _ _ _) :- code-of Ts (tk-rel R) Code,
  std.exists ClauseList (c\ sigma B H\ c = {{ @Clause positive lp:B lp:H }}, value-head H,
    body-reads B Code).

% The head of a clause of a relation over values.
pred value-head i:term.
value-head {{ @Derive _ _ _ }}.
value-head {{ @Assign _ _ _ _ }}.

% forall params keys a b, R params keys a -> R params keys b -> R params keys (g a b)
pred merges-type i:rel, i:term, o:term.
merges-type (rel R NP _ _) G Ty :-
  coq.env.indt R _ _ _ Arity _ _, index-types NP Arity Tys, std.last Tys VTy,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ merges-body R ps xs G VTy c) t) Ty.

pred merges-body i:inductive, i:list term, i:list term, i:term, i:term, o:term.
merges-body R Ps Xs G VTy (prod `other` VTy B) :-
  split-last Xs Keys A, std.append Ps Xs ArgsA,
  pi b\ sigma KB KM ArgsB ArgsM\
    std.append Keys [b] KB, std.append Ps KB ArgsB,
    std.append Keys [app [G, A, b]] KM, std.append Ps KM ArgsM,
    B b = prod `Ha` (app [global (indt R) | ArgsA])
      (_\ prod `Hb` (app [global (indt R) | ArgsB]) (_\ app [global (indt R) | ArgsM])).

% Prove a type with an Ltac tactic and its arguments, which runs on every hole of the proof
% term, and fail when the tactic fails.
pred prove-quietly i:string, i:list argument, i:term, o:term.
prove-quietly Name Args Ty P :-
  std.assert-ok! (coq.typecheck P Ty) "Egglog: an ill-typed proof",
  coq.ltac.collect-goals P Goals _,
  std.forall Goals (g\ coq.ltac.open (g1\ gl\ coq.ltac.call Name Args g1 gl ok) g []).

% The closure of a lattice relation under its merge: by the tactic egglog_merges, or else by the
% lemma Name that the client proved before the command.
pred prove-merges i:string, i:term, o:term.
prove-merges _ Ty P :- prove-quietly "egglog_merges" [] Ty P, !.
prove-merges Name Ty P :-
  coq.locate-all Name Locs, std.mem Locs (loc-gref GR),
  prove-quietly "egglog_merges_by" [trm (global GR)] Ty P, !.

% Define the lemma that a lattice relation that a clause reads is closed under its merge.
pred define-merges i:rel.
define-merges (rel R NP Eq Ss) :-
  lattice-of R _ G, merges-type (rel R NP Eq Ss) G Ty,
  RName = {coq.gref->id (indt R)},
  Name = {calc (RName ^ "_merges")},
  if (prove-merges Name Ty P) true
     (coq.error {calc ("Egglog: a clause reads the lattice table " ^ RName ^ ", so " ^ RName ^
       " must be closed under its merge. The merge must return one of its two arguments, a" ^
       " constructor of " ^ RName ^ " must merge two of its values, or a lemma proved before" ^
       " the command must give the closure. Name the lemma " ^ Name ^ " or add it to the" ^
       " hint database egglog_merges.")}),
  coq.env.add-const Name P Ty @opaque! C,
  coq.hints.add-resolve (const C) "egglog_merges" 0 _.

% forall params, (forall r vs, lat_derived .. r vs -> relation params r vs) /\
%   (forall f ks w, lat_assigned .. f ks w -> lattice params f ks w)
pred lat-closed-type i:term, i:term, i:term, i:term, i:term, i:term, i:int, i:term, o:term.
lat-closed-type Prim Merge Spec Inputs Relation Lattice NP Arity Ty :-
  params-binders NP Arity tt [] (ps\ t\ sigma I Rel Lat\ I = app [Inputs | ps],
    Rel = app [Relation | ps], Lat = app [Lattice | ps],
    t = {{ (forall (r : positive) (vs : list positive),
              @lat_derived positive lp:Prim lp:Merge lp:Spec lp:I r vs -> lp:Rel r vs) /\
           (forall (f : positive) (ks : list positive) (w : positive),
              @lat_assigned positive lp:Prim lp:Merge lp:Spec lp:I f ks w -> lp:Lat f ks w) }})
    Ty.

% forall params idx, R params idx -> its meaning
pred lat-complete-type i:list table, i:term, i:term, i:term, i:term, i:rel, o:term.
lat-complete-type Ts Prim Merge Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Args RApp I M\ std.append ps xs Args,
      RApp = app [global (indt R) | Args], I = app [Inputs | ps],
      lat-meaning Prim Merge Spec I R Code xs M,
      c = prod `H` RApp (_\ M)) t) Ty.

% The meaning of a relation over values among the tables of a program: its lattice for a
% lattice relation, and its relation otherwise.
pred table-meaning i:term, i:term, i:inductive, i:list term, i:term, i:list term, o:term.
table-meaning _ Lattice R Ps Code Xs M :- lattice-of R _ _, !,
  split-last Xs Keys Val, enc-list Keys Ks, enc-term Val W,
  std.append Ps [Code, Ks, W] Args, M = app [Lattice | Args].
table-meaning Relation _ _ Ps Code Xs M :- enc-list Xs Vs,
  std.append Ps [Code, Vs] Args, M = app [Relation | Args].

% forall params idx, the meaning of the tables holds of the indices -> R params idx
pred lat-back-type i:list table, i:term, i:term, i:rel, o:term.
lat-back-type Ts Relation Lattice (rel R NP _ _) T :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Args RApp Mean\ std.append ps xs Args,
      RApp = app [global (indt R) | Args],
      table-meaning Relation Lattice R ps Code xs Mean,
      c = prod `H` Mean (_\ RApp)) t) T.

% forall params idx, R params idx <-> its meaning
pred lat-spec-type i:list table, i:term, i:term, i:term, i:term, i:rel, o:term.
lat-spec-type Ts Prim Merge Spec Inputs (rel R NP _ _) Ty :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Args RApp I M\ std.append ps xs Args,
      RApp = app [global (indt R) | Args], I = app [Inputs | ps],
      lat-meaning Prim Merge Spec I R Code xs M,
      c = {{ lp:RApp <-> lp:M }}) t) Ty.

% The half of the lemma [closed] that gives the meaning of the tables for a relation over
% values.
pred closed-part i:inductive, i:term, i:term, i:list term, o:term.
closed-part R K Code Xs {{ proj2 lp:K lp:Code lp:Ks lp:W }} :- lattice-of R _ _, !,
  split-last Xs Keys Val, enc-list Keys Ks, enc-term Val W.
closed-part _ K Code Xs {{ proj1 lp:K lp:Code lp:Vs }} :- enc-list Xs Vs.

% The equivalence of a relation over values with its meaning, from the two directions.
pred lat-spec-proof i:list table, i:rel, i:term, i:term, i:term, o:term.
lat-spec-proof Ts (rel R NP _ _) Complete Back Closed P :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity ff [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst ff [] (xs\ c\ sigma Args C1 B1 K1 Sel\ std.append ps xs Args,
      C1 = app [Complete | Args], B1 = app [Back | Args], K1 = app [Closed | ps],
      closed-part R K1 Code xs Sel,
      c = {{ conj lp:C1 (fun h => lp:B1 (lp:Sel h)) }}) t) P.

% Define the glue of a relation over values: its meaning from the relation, the relation from
% the meaning of the tables, and their equivalence.
pred define-lat-spec i:list table, i:list rel, i:list rel, i:term, i:term, i:term, i:term,
  i:term, i:term, i:term, i:rel.
define-lat-spec Ts Rels Group Prim Merge Spec Inputs Relation Lattice Closed (rel R NP Eq Ss) :-
  RName = {coq.gref->id (indt R)},
  if (lattice-of R _ _) (Suffix = "_assigned", BackTac = "egglog_lat_back")
     (Suffix = "_derived", BackTac = "egglog_back_lat"),
  lat-complete-type Ts Prim Merge Spec Inputs (rel R NP Eq Ss) CTy,
  complete-proof Rels Group (prim\ s\ ps\ xs\ m\ sigma Code\ code-of Ts (tk-rel s) Code,
      lat-meaning prim Merge Spec (app [Inputs | ps]) s Code xs m)
    (rel R NP Eq Ss) CTy CP,
  coq.env.add-const {calc (RName ^ Suffix)} CP CTy @opaque! CC,
  coq.hints.add-resolve (const CC) "egglog_fire" 0 _,
  lat-back-type Ts Relation Lattice (rel R NP Eq Ss) BTy,
  prove BackTac BTy BP,
  coq.env.add-const {calc (RName ^ "_back")} BP BTy @opaque! BC,
  lat-spec-proof Ts (rel R NP Eq Ss) (global (const CC)) (global (const BC)) Closed SP,
  lat-spec-type Ts Prim Merge Spec Inputs (rel R NP Eq Ss) STy,
  std.assert-ok! (coq.elaborate-skeleton SP STy SP1) "Egglog: the glue lemma failed",
  coq.env.add-const {calc (RName ^ "_spec")} SP1 STy @opaque! _.

% Define the glue of a program with lattice tables: the fire lemmas, the closure of each lattice
% relation that a clause reads under its merge, the lemma [closed], and the glue of each
% relation over values, a group of relations that read each other at a time.
pred define-lat-glue i:list table, i:list rel, i:list rel, i:list term, i:term, i:term, i:term,
  i:term.
define-lat-glue Ts Rels Lattices ClauseList Spec Inputs Relation Lattice :-
  fixed-prim Prim, Merge = {{ prim_merge lp:Prim }},
  std.filter Rels (r\ r = rel _ _ ff _) ValueRels,
  std.forall ValueRels (define-lat-fires Ts Rels ClauseList Prim Merge Spec Inputs),
  std.filter Lattices (read-lattice Ts ClauseList) Read,
  std.forall Read define-merges,
  Rels = [rel R1 NP _ _ | _], coq.env.indt R1 _ _ _ Arity1 _ _,
  lat-closed-type Prim Merge Spec Inputs Relation Lattice NP Arity1 ClosedTy,
  prove "egglog_lat_closed" ClosedTy ClosedP,
  coq.env.add-const "closed" ClosedP ClosedTy @opaque! ClosedC,
  read-groups ValueRels Groups,
  std.forall Groups (g\ std.forall g (define-lat-spec Ts Rels g Prim Merge Spec Inputs Relation
    Lattice (global (const ClosedC)))).

}}.
