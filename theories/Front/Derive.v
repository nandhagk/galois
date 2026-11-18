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
From Galois.Front Require Import Spec SpecFacts LowerSig.

Import List.ListNotations.

(** * Glue tactics

    The command proves, for each relation [R] over values, that [R] holds exactly when its row
    is derived. These tactics prove the generated lemmas. [egglog_member] and
    [egglog_unmember] move between an input element and its row. [egglog_clause] shows that
    one clause, applied to rows of the relation, gives a row of the relation. *)

Create HintDb egglog_fire discriminated.

(** A row is in the rows of the inputs when its element is in its input list. *)
Ltac egglog_member :=
  lazymatch goal with
  | |- In _ (_ ++ _) => apply in_or_app; first [left; egglog_member | right; egglog_member]
  | |- In _ (flat_map _ ?l) =>
      apply in_flat_map;
      match goal with
      | H : In ?c l |- _ => exists c; split; [exact H | simpl; left; reflexivity]
      end
  | |- In _ (map _ ?l) =>
      apply in_map_iff;
      match goal with
      | H : In ?c l |- _ => exists c; split; [reflexivity | exact H]
      end
  end.

(** Prove an input membership or a row of the inputs, the holes of a fire lemma. *)
Ltac egglog_leaf := first [simpl; tauto | red; egglog_member].

(** Each constructor of a relation derives its row, by induction and the fire lemmas. *)
Ltac egglog_complete :=
  intros; match goal with H : _ |- _ => induction H end; eauto with egglog_fire.

(** A row in the rows of the inputs comes from an element of an input list. *)
Ltac egglog_unmember H :=
  lazymatch type of H with
  | In _ (_ ++ _) =>
      apply in_app_or in H; destruct H as [H | H]; egglog_unmember H
  | In _ (flat_map _ _) =>
      let c := fresh "c" in
      let Hc := fresh "Hc" in
      apply in_flat_map in H; destruct H as [c [Hc H]]; destruct c; simpl in H;
      repeat match type of H with
             | _ \/ _ => destruct H as [H | H]
             | False => contradiction
             end;
      try (inversion H; subst; clear H)
  | In _ (map _ _) =>
      let p := fresh "p" in
      let Hp := fresh "Hp" in
      apply in_map_iff in H; destruct H as [p [H Hp]]; destruct p; simpl in H;
      inversion H; subst; clear H
  | _ => idtac
  end.

(** Case on every lookup of an environment [e : positive -> option _] in the hypotheses. *)
Ltac egglog_env :=
  simpl in *;
  repeat match goal with
  | H : context [?e ?i] |- _ =>
      lazymatch type of e with
      | positive -> option _ =>
          let v := fresh "v" in
          let E := fresh "E" in
          remember (e i) as v eqn:E in *; clear E; destruct v; simpl in *; try discriminate
      end
  end;
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  end.

(** A hypothesis [Hrel] that a row is in the relation of a program: an input element, or a
    row of a relation over values. *)
Ltac egglog_row Hrel :=
  red in Hrel; destruct Hrel as [Hrel | Hrel];
  [ egglog_unmember Hrel
  | repeat match type of Hrel with
           | _ \/ _ => destruct Hrel as [Hrel | Hrel]
           end;
    let Hcode := fresh "Hcode" in
    let Hvs := fresh "Hvs" in
    destruct Hrel as [Hcode Hrel]; try discriminate Hcode;
    repeat match type of Hrel with
           | exists _, _ => destruct Hrel as [? Hrel]
           end;
    destruct Hrel as [Hvs Hrel]; inversion Hvs; subst; clear Hvs ].

(** The relation of a program holds of a row of a relation over values when the relation
    holds of its indices. *)
Ltac egglog_conclude :=
  repeat match goal with |- exists _, _ => eexists end;
  split; [reflexivity | solve [econstructor; eauto]].

Ltac egglog_pick :=
  first
    [ split; [reflexivity | egglog_conclude]
    | left; split; [reflexivity | egglog_conclude]
    | right; egglog_pick ].

(** One clause, applied to rows of the relation of a program, gives a row of it. *)
Ltac egglog_clause Hc Hh Hb Hvals :=
  simpl in Hc;
  repeat match goal with
         | Hc : _ = _ \/ _ |- _ => destruct Hc as [Hc | Hc]
         | Hc : False |- _ => contradiction
         end;
  match goal with Hc : _ = ?c |- _ => subst c end;
  simpl in Hh, Hb, Hvals;
  match goal with
  | Hh : Derive _ _ = Derive _ _ |- _ => injection Hh; clear Hh; intros; subst
  end;
  repeat match goal with
         | Hb : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in Hb; destruct Hb as [? Hb]
         | Hb : Forall _ [] |- _ => clear Hb
         end;
  repeat match goal with
         | H : premise_in _ _ _ (Holds _ _) |- _ =>
             let vs := fresh "vs" in
             let Hv := fresh "Hv" in
             let Hrel := fresh "Hrel" in
             simpl in H; destruct H as [vs [Hv Hrel]]
         end;
  egglog_env;
  repeat match goal with
         | Hrel : _ |- _ =>
             lazymatch type of Hrel with
             | ?Rel _ ?r ?vs =>
                 lazymatch type of Rel with
                 | _ -> positive -> list positive -> Prop => egglog_row Hrel
                 end
             end
         end;
  red; right; egglog_pick.

(** Every derived row is in the relation of the program. *)
Ltac egglog_closed :=
  intros;
  match goal with
  | H : derived ?prim ?s ?I ?r ?vs |- ?P ?r ?vs =>
      revert H; apply (derived_least prim s I P);
      [ let Hin := fresh "Hin" in intros ? ? _ Hin; red; left; exact Hin
      | let Hc := fresh "Hc" in
        let Hh := fresh "Hh" in
        let Hb := fresh "Hb" in
        let Hvals := fresh "Hvals" in
        intros ? ? ? ? ? Hc Hh Hb Hvals; egglog_clause Hc Hh Hb Hvals ]
  end.

(** A row of the relation of a program for a relation over values gives the relation. *)
Ltac egglog_back :=
  intros;
  match goal with Hrel : _ |- _ => egglog_row Hrel end;
  assumption.

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

pred row-list i:option term, i:list term, o:term.
row-list none _ {{ @nil (positive * list positive) }}.
row-list (some Code) Xs
    {{ @cons (positive * list positive) (lp:Code, lp:Vals) (@nil (positive * list positive)) }} :-
  list->term {{ positive }} Xs Vals.

pred branch-of i:list table, i:constructor, i:term, o:term.
branch-of Ts K KTy B :- arg-types KTy Tys,
  if (find-table Ts (tk-con K) N _ _) (int->pos N Code, Row = some Code) (Row = none),
  mk-lams Tys [] (xs\ body\ row-list Row xs body) B.

pred rows-of i:list table, i:list term, i:source, o:term.
rows-of Ts Ps (source Key {{ prod lp:A lp:B }}) T :- !, code-of Ts Key Code,
  source-coll Ps Key Coll,
  T = {{ @map (lp:A * lp:B) (positive * list positive)
           (fun p => (lp:Code, [@fst lp:A lp:B p; @snd lp:A lp:B p])) lp:Coll }}.
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
  mk-exists Tys [] (xs\ b\ sigma Vs Args RApp\ list->term {{ positive }} xs Vs,
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
  list->term {{ positive }} Idx Vs.
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
  list->term {{ positive }} Idx Vs,
  std.map Vars (v\ x\ v = pr x _) Xs, list->term {{ positive }} Xs EnvL,
  Env = {{ @env_of positive lp:EnvL }},
  Ck = {{ @Clause positive lp:BodyT (@Derive positive _ lp:ArgsP) }},
  body-proof Ts Rels Prim Spec I Env Ps Hyps BodyT BodyP,
  P = {{ @derived_clause positive lp:Prim lp:Spec lp:I lp:Ck lp:Env lp:Code lp:ArgsP lp:Vs
          lp:Kn eq_refl lp:BodyP eq_refl }}.

pred body-proof i:list table, i:list rel, i:term, i:term, i:term, i:term, i:list term,
  i:list (pair term term), i:term, o:term.
body-proof _ _ Prim Spec I Env _ [] _ {{ @derived_nil positive lp:Prim lp:Spec lp:I lp:Env }}.
body-proof Ts Rels Prim Spec I Env Ps [pr H Ty | Hs]
    {{ @cons _ (@Holds _ lp:Code lp:Args) lp:Rest }} P :-
  body-proof Ts Rels Prim Spec I Env Ps Hs Rest RestP,
  hyp-row Ts Rels Prim Spec I Ps H Ty Code Vs Row,
  P = {{ @derived_row positive lp:Prim lp:Spec lp:I lp:Env lp:Code lp:Args lp:Vs lp:Rest eq_refl
          lp:Row lp:RestP }}.

% The derived row of a premise: an input row, or the premise itself for a relation.
pred hyp-row i:list table, i:list rel, i:term, i:term, i:term, i:list term, i:term, i:term,
  o:term, o:term, o:term.
hyp-row Ts _ Prim Spec I Ps _ Ty Code Vs Row :- in-premise Ty Elem Coll, !,
  input-key Ps Elem Coll Key Args _, code-of Ts Key Code, list->term {{ positive }} Args Vs,
  Row = {{ @derived_input positive lp:Prim lp:Spec lp:I lp:Code lp:Vs
            _ _ }}.
hyp-row _ _ _ _ _ _ H {{ @derived positive _ _ _ lp:Code lp:Vs }} Code Vs H.

pred run-tactic i:string, i:sealed-goal.
run-tactic Name G :- coq.ltac.open (g\ gl\ coq.ltac.call Name [] g gl ok) G [].


% Prove a type with an Ltac tactic, which runs on every hole of the proof term.
pred prove i:string, i:term, o:term.
prove Name Ty P :-
  std.assert-ok! (coq.typecheck P Ty) "Egglog: an ill-typed proof",
  coq.ltac.collect-goals P Goals _,
  if (std.forall Goals (run-tactic Name)) true
     (coq.error "Egglog: the tactic" Name "failed").



pred params-binders i:int, i:term, i:bool, i:list term, i:(list term -> term -> prop), o:term.
params-binders 0 _ _ Acc K T :- !, std.rev Acc Ps, K Ps T.
params-binders N (prod Name Ty F) IsProd Acc K Out :- M is N - 1,
  if (IsProd = tt) (Out = prod Name Ty B) (Out = fun Name Ty B),
  pi p\ decl p Name Ty => params-binders M (F p) IsProd [p | Acc] K (B p).

pred prim-type o:term.
prim-type {{ positive -> list positive -> option positive }}.

% The type and proof of the fire lemma of one constructor, whose clause is the Idx-th.
pred fire-lemma i:list table, i:list rel, i:term, i:term, i:int, i:term, i:term, i:int,
  o:term, o:term.
fire-lemma Ts Rels Spec Inputs NP KTy Ck Idx (prod `prim` PT TyF) (fun `prim` PT PF) :-
  prim-type PT, in-proof Idx Kn,
  (pi prim\ decl prim `prim` PT =>
     params-binders NP KTy tt [] (ps\ t\ sigma Inst I\ coq.subst-prod ps KTy Inst,
       I = app [Inputs | ps], fire-type Ts Rels prim Spec I Inst t) (TyF prim)),
  (pi prim\ decl prim `prim` PT =>
     params-binders NP KTy ff [] (ps\ t\ sigma Inst I\ coq.subst-prod ps KTy Inst,
       I = app [Inputs | ps], fire-proof Ts Rels prim Spec I Ck Kn ps [] [] Inst t) (PF prim)).

pred idx-binders i:term, i:bool, i:list term, i:(list term -> term -> prop), o:term.
idx-binders (prod N Ty F) IsProd Acc K Out :- !,
  if (IsProd = tt) (Out = prod N Ty B) (Out = fun N Ty B),
  pi x\ decl x N Ty => idx-binders (F x) IsProd [x | Acc] K (B x).
idx-binders _ _ Acc K T :- std.rev Acc Xs, K Xs T.

% forall prim params idx, R params idx -> derived prim spec (inputs params) code idx
pred complete-type i:list table, i:term, i:term, i:rel, o:term.
complete-type Ts Spec Inputs (rel R NP _ _) (prod `prim` PT TyF) :-
  coq.env.indt R _ _ _ Arity _ _, prim-type PT, code-of Ts (tk-rel R) Code,
  (pi prim\ decl prim `prim` PT =>
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp I\ list->term {{ positive }} xs Vs,
        std.append ps xs Args, RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        c = prod `H` RApp (_\ {{ @derived positive lp:prim lp:Spec lp:I lp:Code lp:Vs }})) t)
    (TyF prim)).

% forall params idx, relation params code idx -> R params idx
pred back-type i:list table, i:term, i:rel, o:term.
back-type Ts Relation (rel R NP _ _) T :-
  coq.env.indt R _ _ _ Arity _ _, code-of Ts (tk-rel R) Code,
  params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
    idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp Rel\ list->term {{ positive }} xs Vs,
      std.append ps xs Args, RApp = app [global (indt R) | Args],
      Rel = app [Relation | {std.append ps [Code, Vs]}], c = prod `H` Rel (_\ RApp)) t) T.

% forall prim params r vs, derived prim spec (inputs params) r vs -> relation params r vs
pred closed-type i:term, i:term, i:term, i:int, i:term, o:term.
closed-type Spec Inputs Relation NP Arity (prod `prim` PT TyF) :- prim-type PT,
  (pi prim\ decl prim `prim` PT =>
    params-binders NP Arity tt [] (ps\ t\ sigma I Rel\ I = app [Inputs | ps],
      Rel = app [Relation | ps],
      t = {{ forall (r : positive) (vs : list positive),
               @derived positive lp:prim lp:Spec lp:I r vs -> lp:Rel r vs }}) (TyF prim)).

% The equivalence of R with its derived rows, from the two directions.
pred spec-proof i:list table, i:rel, i:term, i:term, i:term, i:term, o:term.
spec-proof Ts (rel R NP _ _) Complete Back Closed _Inputs P :-
  coq.env.indt R _ _ _ Arity _ _, prim-type PT, code-of Ts (tk-rel R) Code,
  P = fun `prim` PT PF,
  (pi prim\ decl prim `prim` PT =>
    params-binders NP Arity ff [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst ff [] (xs\ c\ sigma Vs Args C1 B1 K1\ list->term {{ positive }} xs Vs,
        std.append ps xs Args,
        C1 = app [Complete, prim | Args], B1 = app [Back | Args],
        K1 = app [Closed, prim | ps],
        c = {{ conj lp:C1 (fun h => lp:B1 (lp:K1 lp:Code lp:Vs h)) }}) t) (PF prim)).

% forall prim params idx, R params idx <-> derived prim spec (inputs params) code idx
pred spec-type i:list table, i:term, i:term, i:rel, o:term.
spec-type Ts Spec Inputs (rel R NP _ _) (prod `prim` PT TyF) :-
  coq.env.indt R _ _ _ Arity _ _, prim-type PT, code-of Ts (tk-rel R) Code,
  (pi prim\ decl prim `prim` PT =>
    params-binders NP Arity tt [] (ps\ t\ sigma Inst\ coq.subst-prod ps Arity Inst,
      idx-binders Inst tt [] (xs\ c\ sigma Vs Args RApp I\ list->term {{ positive }} xs Vs,
        std.append ps xs Args, RApp = app [global (indt R) | Args], I = app [Inputs | ps],
        c = {{ lp:RApp <-> @derived positive lp:prim lp:Spec lp:I lp:Code lp:Vs }}) t)
    (TyF prim)).

% Define the glue of the relational relations of a program.
pred define-glue i:list table, i:list rel, i:list term, i:term, i:term, i:term.
define-glue Ts Rels ClauseList Spec Inputs Relation :-
  std.filter Rels (r\ r = rel _ _ ff _) Relational,
  Relational = [rel R1 NP _ _ | _], !,
  coq.env.indt R1 _ _ _ Arity1 _ _,
  std.forall Relational (define-fires Ts Rels ClauseList Spec Inputs),
  closed-type Spec Inputs Relation NP Arity1 ClosedTy,
  prove "egglog_closed" ClosedTy ClosedP,
  coq.env.add-const "closed" ClosedP ClosedTy @opaque! ClosedC,
  std.forall Relational (define-spec Ts Spec Inputs Relation (global (const ClosedC))).

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

pred define-spec i:list table, i:term, i:term, i:term, i:term, i:rel.
define-spec Ts Spec Inputs Relation Closed (rel R NP Eq Ss) :-
  RName = {coq.gref->id (indt R)},
  complete-type Ts Spec Inputs (rel R NP Eq Ss) CTy,
  prove "egglog_complete" CTy CP,
  coq.env.add-const {calc (RName ^ "_derived")} CP CTy @opaque! CC,
  back-type Ts Relation (rel R NP Eq Ss) BTy,
  prove "egglog_back" BTy BP,
  coq.env.add-const {calc (RName ^ "_back")} BP BTy @opaque! BC,
  spec-proof Ts (rel R NP Eq Ss) (global (const CC)) (global (const BC)) Closed Inputs SP,
  spec-type Ts Spec Inputs (rel R NP Eq Ss) STy,
  std.assert-ok! (coq.elaborate-skeleton SP STy SP1) "Egglog: the glue lemma failed",
  coq.env.add-const {calc (RName ^ "_spec")} SP1 STy @opaque! _.

% -{93}
% The name of the code constant of a table.
pred code-name i:table, o:string.
code-name (table (tk-rel R) _ _ _) N :- !, N is {coq.gref->id (indt R)} ^ "_code".
code-name (table (tk-con K) _ _ _) N :- !, N is {coq.gref->id (indc K)} ^ "_code".
code-name (table (tk-src (global GR)) _ _ _) N :- !, N is {coq.gref->id GR} ^ "_code".
code-name (table (tk-param I) _ _ _) N :- N is "input" ^ {std.any->string I} ^ "_code".

pred define-code i:table.
define-code T :- T = table _ N _ _, code-name T Name, int->pos N P,
  coq.env.add-const Name P {{ positive }} @transparent! _.

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
  std.forall Tables define-code,
  coq.env.add-const "spec" Spec {{ spec positive }} @transparent! SpecC,
  SpecT = global (const SpecC),
  coq.env.add-const "program" {{ @spec_program positive lp:SpecT }}
    {{ program positive }} @transparent! _,
  coq.env.add-const "rewrites" {{ @spec_rewrites positive lp:SpecT }}
    {{ list (rewrite positive) }} @transparent! _,
  std.fold Rels [] (r\ a\ b\ sigma I KTys\ r = rel I _ _ _, coq.env.indt I _ _ _ _ _ KTys,
    std.fold KTys a (sources-of r) b) Sources,
  Rels = [rel R1 NP1 _ _ | _], coq.env.indt R1 _ _ _ Arity1 _ _,
  abs-params NP1 Arity1 [] (ps\ fb\ facts-body Tables Sources ps fb) FactsT,
  std.assert-ok! (coq.elaborate-skeleton FactsT FactsTy FactsE) "Egglog: ill-typed facts",
  coq.env.add-const "facts" FactsE FactsTy @transparent! _,
  abs-params NP1 Arity1 [] (ps\ f\ sigma FB\ facts-body Tables Sources ps FB,
    mk-inputs-fun FB f) InputsT,
  std.assert-ok! (coq.elaborate-skeleton InputsT InputsTy InputsE) "Egglog: ill-typed inputs",
  coq.env.add-const "inputs" InputsE InputsTy @transparent! InputsC,
  abs-params NP1 Arity1 [] (ps\ f\ sigma FB\ facts-body Tables Sources ps FB,
    mk-rel-fun Tables ps Relational FB f) RelationT,
  std.assert-ok! (coq.elaborate-skeleton RelationT RelTy RelationE)
    "Egglog: ill-typed relation",
  coq.env.add-const "relation" RelationE RelTy @transparent! RelationC,
  define-glue Tables Rels ClauseList SpecT (global (const InputsC))
    (global (const RelationC)),
  coq.env.end-module _.
main _ :- coq.error "Usage: Egglog <name> from <relation> .. <relation>.".

}}.
#[synterp] Elpi Accumulate lp:{{
main [str Name, str "from" | _] :- !, coq.env.begin-module Name none, coq.env.end-module _.
main _.
}}.
Elpi Export Egglog.
