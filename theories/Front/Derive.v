(** * Deriving engine programs from inductives

    The command [Egglog P from R1 .. Rn.] reads the inductive relations [R1] to [Rn] and
    defines a module [P] with the specification of their constructors ([P.spec]), its engine
    program ([P.program]), the input rows of their parameters ([P.inputs], [P.facts]) and the
    meaning of each table ([P.relation]). A relation over values is a table. A relation [R t u]
    over a datatype is an equation, and the constructors of the datatype are tables. A premise
    [In e (f q)] reads an input table, and a premise [Ri ..] reads a relation. Variables are
    numbered in binder order, and every table code and variable number is generated. The
    command [Egglog Value T M.] registers the encoder module [M] of a value type [T], and the
    values of [T] enter the engine through [M.encode]. After [with Ops], the declaration
    [merge R g] makes [R] a lattice table, whose last index is its value and whose merge is the
    primitive [g] of [Ops]. A constructor of [R] assigns a value, and a premise over [R] reads
    the stored value. An argument of type [list T] of a constructor of a datatype is a class,
    which the tables [nil_T] and [cons_T] build as a chain of nodes, and the law
    [Forall2 R xs ys -> R (C xs) (C ys)] is the congruence of [C] in such an argument. The
    declaration [ruleset S C1 .. Ck] defines [P.S] as the positions of the rules of [C1] to
    [Ck] in increasing order. [P.default] holds the positions of the rules that no ruleset
    lists, and [P.all] holds the positions of all rules.

    The command is an Elpi program in parts. Each part is an Elpi file that its own Rocq file
    declares, and the command accumulates the parts in this order, so that each part reads the
    predicates of the parts before it.
    - [EgglogPrimitives.v] reads value types and primitives.
    - [EgglogReading.v] reads inductives.
    - [EgglogLists.v] reads lists and rulesets.
    - [EgglogTables.v] collects and numbers the tables.
    - [EgglogPatterns.v] reads clauses.
    - [EgglogFacts.v] defines the facts and the encoders.
    - [EgglogGlue.v] proves the glue lemmas.
    - [EgglogLattice.v] reads lattice tables and proves their glue lemmas.
    The tactics of [DerivePrimitives.v], [DeriveTactics.v], [DeriveCongruence.v] and
    [DeriveLattice.v] prove the generated lemmas, and the command calls them by name. This file
    exports them with the definitions of [DeriveHelpers.v], so a client that imports [Derive]
    has everything that the command uses.

    For example, [Egglog Andersen from may_points.] defines [Andersen.spec] with one clause per
    constructor of [may_points], and [Andersen.facts q] lists the input rows of [q].

    Builds on: the specifications, their lowering, the meaning of lattice reads, the parts of
    the command, and Elpi. *)

From Stdlib Require Import PArith.
From elpi Require Import elpi.
From Argent Require Import Time.
From Galois.Egglog Require Import Syntax.
From Galois.Front Require Import Spec LowerSig.
From Galois.Front Require Export DeriveHelpers DerivePrimitives DeriveTactics DeriveCongruence
  DeriveLattice.
From Galois.Front Require EgglogPrimitives EgglogReading EgglogLists EgglogTables EgglogPatterns
  EgglogFacts EgglogGlue EgglogLattice.

(** * The command

    The command accumulates the databases of value types and primitives, the library of Argent
    that derives time functions, and the parts of its program. [main] reads the arguments of
    the command, and [derive-module] defines the members of the module of a program. *)

Elpi Command Egglog.
Elpi Accumulate Db egglog.prims.
Elpi Accumulate Db egglog.values.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate File egglog.primitives.
Elpi Accumulate File egglog.reading.
Elpi Accumulate File egglog.lists.
Elpi Accumulate File egglog.tables.
Elpi Accumulate File egglog.patterns.
Elpi Accumulate File egglog.facts.
Elpi Accumulate File egglog.glue.
Elpi Accumulate File egglog.lattice.
Elpi Accumulate lp:{{

% ---------------------------------------------------------------------------------------------
% The command

main [str "Primitives", str Name | Fs] :- !,
  std.map Fs (a\ g\ sigma N\ a = str N, coq.locate N g) GRs,
  coq.env.begin-module Name none,
  define-prims GRs 1 Codes Calls,
  (pi p vs\ prim-body Calls p vs (B p vs)),
  PrimT = fun `p` {{ positive }} (p\ fun `vs` {{ list positive }} (vs\ B p vs)),
  std.assert-ok! (coq.elaborate-skeleton PrimT PTy PrimE) "Egglog: an ill-typed primitive set",
  coq.env.add-const "prim" PrimE PTy @transparent! PrimC,
  coq.env.end-module _,
  std.forall Codes (c\ sigma GR Code\ c = pr GR Code,
    coq.elpi.accumulate library "egglog.prims"
      (clause _ _ (prim-code GR Code (global (const PrimC))))).
main [str Name, str "from" | Rest] :- !,
  split-with Rest RelNames Opt Decls,
  program-decls Decls Opt Merges RsDecls,
  if (Opt = some Set)
     (coq.locate {calc (Set ^ ".prim")} PrimGR,
      (fixed-prim (global PrimGR) => derive-program Name RelNames Merges RsDecls))
     (derive-program Name RelNames Merges RsDecls).
main [str "Value", str Ty, str Mod] :- !, register-value Ty Mod.
main _ :- coq.error "Usage: Egglog <name> from <relation> .. <relation> [with <primitives>"
  "[merge <relation> <function>] ..] [ruleset <name> <constructor> .. <constructor>] .., or"
  "Egglog Primitives <name> <function> .. <function>.".

% The relations, the primitive set after 'with', and the declarations that follow them.
pred split-with i:list argument, o:list argument, o:option string, o:list argument.
split-with [] [] none [].
split-with [str "with", str Set | Ds] [] (some Set) Ds :- !.
split-with [str K | Ds] [] none [str K | Ds] :- decl-keyword K, !.
split-with [A | As] [A | Bs] O Ds :- split-with As Bs O Ds.

% A word that starts a declaration after the relations.
pred decl-keyword i:string.
decl-keyword "merge".
decl-keyword "ruleset".

% The declarations after the relations and the primitive set: 'merge R g' declares a lattice
% table, which needs a primitive set, and 'ruleset S C1 .. Ck' declares a ruleset.
pred program-decls i:list argument, i:option string, o:list (pair string string),
  o:list rsdecl.
program-decls [] _ [] [] :- !.
program-decls [str "merge" | _] none _ _ :- !,
  coq.error "Egglog: the merge of a lattice table is a primitive, so a lattice table needs a"
    "primitive set. Write 'with <primitives> merge <relation> <function>'.".
program-decls [str "merge", str R, str G | Rest] (some Set) [pr R G | Ms] Rs :- !,
  program-decls Rest (some Set) Ms Rs.
program-decls [str "ruleset", str S | Rest] Opt Ms [rsdecl S Cs | Rs] :- !,
  ruleset-names Rest Cs Rest1, program-decls Rest1 Opt Ms Rs.
program-decls [str "with" | _] _ _ _ :- !,
  coq.error "Egglog: 'with <primitives>' comes right after the relations.".
program-decls _ _ _ _ :-
  coq.error "Egglog: after the relations and 'with <primitives>', each lattice table is"
    "declared as 'merge <relation> <function>' and each ruleset as"
    "'ruleset <name> <constructor> .. <constructor>'.".

% The constructors of a ruleset, up to the next declaration.
pred ruleset-names i:list argument, o:list string, o:list argument.
ruleset-names [str K | Rest] [] [str K | Rest] :- (decl-keyword K ; K = "with"), !.
ruleset-names [str C | Rest] [C | Cs] Out :- !, ruleset-names Rest Cs Out.
ruleset-names Rest [] Rest.

pred derive-program i:string, i:list argument, i:list (pair string string), i:list rsdecl.
derive-program Name RelNames Merges RsDecls :-
  std.map RelNames (a\ i\ sigma N\ a = str N, coq.locate N (indt i)) Is,
  std.map Merges (lattice-decl Is) Decls,
  distinct-lattices Decls,
  std.map RsDecls (ruleset-of Is) Rulesets,
  distinct-rulesets Rulesets,
  with-lattices Decls (derive-relations Name Is Rulesets).

% Derive the program of the relations, with the lattice tables in scope.
pred derive-relations i:string, i:list inductive, i:list ruleset.
derive-relations Name Is Rulesets :-
  std.map Is rel-info Rels,
  if (std.exists Rels (r\ r = rel _ _ tt _), lattice-of _ _ _)
     (coq.error "Egglog: a program with lattice tables reads no equation.") true,
  std.filter Rels (r\ r = rel _ _ ff _) ValueRels,
  std.filter ValueRels (r\ sigma I\ r = rel I _ _ _, not (lattice-of I _ _)) Relational,
  std.filter ValueRels (r\ sigma I\ r = rel I _ _ _, lattice-of I _ _) Lattices,
  std.map ValueRels (r\ e\ sigma I Ss\ r = rel I _ _ Ss, e = pr (tk-rel I) Ss) RelKeys,
  std.fold Rels [] (r\ a\ b\ sigma I KTys\ r = rel I _ _ _,
    coq.env.indt I _ _ _ _ _ KTys,
    std.fold KTys a (input-keys Rels r) b) InputKeys,
  std.map Rels (r\ ds\ sigma I NP Ar Tys\ r = rel I NP _ _, coq.env.indt I _ _ _ Ar _ _,
    index-types NP Ar Tys, std.flatten {std.map Tys datatypes-of-type} ds) DtLists,
  std.flatten DtLists Dts0, undup Dts0 [] Dts,
  datatype-tables Dts [] DtKeys,
  std.flatten [RelKeys, InputKeys, DtKeys] Keys,
  number Keys 1 Dts Tables,
  std.fold Rels [] (r\ a\ b\ sigma I KTys\ r = rel I _ _ _, coq.env.indt I _ _ _ _ _ KTys,
    std.fold KTys a (sources-of r) b) Sources,
  std.forall Sources time-source,
  Rels = [rel R1 NP1 _ _ | _], coq.env.indt R1 _ _ _ Arity1 _ _,
  param-names NP1 Arity1 PNames,
  coq.env.begin-module Name none,
  std.map Tables (define-code PNames) Consts,
  with-codes Consts
    (derive-module Name Rels Relational Lattices InputKeys Dts Tables Sources NP1 Arity1
      Rulesets).

% Derive the time function of a generated constant beside it, with Argent.
pred time-function i:string.
time-function S :- new_safe M, (verify-memo M => timefun S _).

% Derive the time function of a projection that an input table reads, unless it has one. It
% runs before the module of the program opens, beside the projection.
pred time-source i:source.
time-source (source (tk-src (global GR)) _) :- not (timed GR _), !,
  coq.gref->path GR Path, std.string.concat "." {std.append Path [{coq.gref->id GR}]} S,
  time-function S.
time-source _.

% Run a goal with the code constants of the tables.
pred with-codes i:list (pair tkey term), i:prop.
with-codes [] G :- G.
with-codes [pr K C | Rest] G :- code-const K C => with-codes Rest G.

% The constants of the module of a program, after its code constants.
pred derive-module i:string, i:list rel, i:list rel, i:list rel,
  i:list (pair tkey (list term)), i:list inductive, i:list table, i:list source, i:int, i:term,
  i:list ruleset.
derive-module Name Rels Relational Lattices InputKeys Dts Tables Sources NP1 Arity1 Rulesets :-
  std.map Tables (decl-of Tables) Decls, list->term {{ decl }} Decls DeclT,
  std.map-filter Tables (t\ c\ sigma K\ t = table K _ _ _,
    std.exists InputKeys (p\ sigma S\ p = pr K S), code-of Tables K c) InputCodes,
  list->term {{ positive }} InputCodes InputT,
  std.map Rels (r\ kcs\ sigma I Ks KTys\ r = rel I _ _ _, coq.env.indt I _ _ _ _ Ks KTys,
    std.map2 Ks KTys (k\ kty\ kc\ sigma Cs\ clause-of Tables Rels r kty Cs, kc = pr k Cs) kcs)
    KClauseLists,
  std.flatten KClauseLists KClauses,
  std.flatten {std.map KClauses (kc\ cs\ kc = pr _ cs)} ClauseList,
  list->term {{ clause positive }} ClauseList ClausesT,
  Spec = {{ @Spec positive lp:DeclT lp:InputT lp:ClausesT }},
  std.assert-ok! (coq.typecheck Spec {{ spec positive }}) "Egglog: ill-typed specification",
  check-sorts Name Spec,
  coq.env.add-const "spec" Spec {{ spec positive }} @transparent! SpecC,
  SpecT = global (const SpecC),
  coq.env.add-const "program" {{ @spec_program positive lp:SpecT }}
    {{ program positive }} @transparent! _,
  rule-positions KClauses 0 Positions,
  define-rulesets Rulesets Positions,
  abs-params NP1 Arity1 [] (ps\ fb\ facts-body Tables Sources ps fb) FactsT,
  std.assert-ok! (coq.elaborate-skeleton FactsT FactsTy FactsE) "Egglog: ill-typed facts",
  coq.env.add-const "facts" FactsE FactsTy @transparent! _,
  time-function "facts",
  abs-params NP1 Arity1 [] (ps\ f\ sigma FB\ facts-body Tables Sources ps FB,
    mk-inputs-fun FB f) InputsT,
  std.assert-ok! (coq.elaborate-skeleton InputsT InputsTy InputsE) "Egglog: ill-typed inputs",
  coq.env.add-const "inputs" InputsE InputsTy @transparent! InputsC,
  abs-params NP1 Arity1 [] (ps\ f\ sigma FB\ facts-body Tables Sources ps FB,
    if (Lattices = []) (mk-rel-fun Tables ps Relational FB f)
       (mk-lat-rel-fun Tables ps Relational FB f)) RelationT,
  std.assert-ok! (coq.elaborate-skeleton RelationT RelTy RelationE)
    "Egglog: ill-typed relation",
  coq.env.add-const "relation" RelationE RelTy @transparent! RelationC,
  if (Lattices = [])
     (define-glue Tables Rels ClauseList SpecT (global (const InputsC))
        (global (const RelationC)))
     (abs-params NP1 Arity1 [] (ps\ f\ mk-lat-fun Tables ps Lattices f) LatticeT,
      std.assert-ok! (coq.elaborate-skeleton LatticeT LatticeTy LatticeE)
        "Egglog: ill-typed lattice",
      coq.env.add-const "lattice" LatticeE LatticeTy @transparent! LatticeC,
      define-lat-glue Tables Rels Lattices ClauseList SpecT (global (const InputsC))
        (global (const RelationC)) (global (const LatticeC))),
  std.map Dts (define-encoder Tables) Encs,
  std.forall Dts (d\ time-function {calc ("encode_" ^ {coq.gref->id (indt d)})}),
  std.forall Rels (define-eq-glue Tables Rels ClauseList Encs SpecT (global (const InputsC))),
  coq.env.end-module _.

}}.
#[synterp] Elpi Accumulate lp:{{
main [str "Primitives", str Name | _] :- !, coq.env.begin-module Name none, coq.env.end-module _.
main [str Name, str "from" | _] :- !, coq.env.begin-module Name none, coq.env.end-module _.
main [str "Value", _, _] :- !.
main _.
}}.
Elpi Export Egglog.
