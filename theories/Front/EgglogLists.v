(** * Lists and rulesets in the derive command

    This file declares the Elpi file [egglog.lists] of the command [Egglog] of [Derive.v]. An
    argument of type [list T] of a constructor of a datatype is a class, which the tables
    [nil_T] and [cons_T] build as a chain of nodes. A cons node takes the components of an
    element and the class of the rest of the list. The components of a pair are its two sides,
    and any other element is its own component. A component is a value, a class of a datatype
    of the program, or a list, which is a class as well. The declaration [ruleset S C1 .. Ck]
    defines [P.S] as the positions of the rules of [C1] to [Ck].

    For example, the constructor [MyVec (xs : list math)] adds the tables [nil_math] and
    [cons_math], and the encoder of [math] writes [[a; b]] as two cons nodes in front of a nil
    node. The constructor [Rows (xss : list (list math))] adds the tables [nil_list_math] and
    [cons_list_math] of the outer list as well.

    Builds on: the Egglog syntax and model, the reading of [egglog.reading], and Elpi. *)

From Stdlib Require Import PArith.
From elpi Require Import elpi.
From Galois.Egglog Require Import Syntax Model.

(** * Lists and rulesets *)

Elpi File egglog.lists lp:{{

% ---------------------------------------------------------------------------------------------
% Lists in datatypes

% The type of a component of a list element is a value type, a datatype, or a list type whose
% elements have components of these kinds.
pred elem-part i:term.
elem-part T :- value-type T, !.
elem-part T :- datatype T _, !.
elem-part T :- list-of T E, elem-ok E.

% The elements of a list in a datatype have components of the kinds of [elem-part].
pred elem-ok i:term.
elem-ok E :- std.forall {elem-parts E} elem-part.

pred check-elem i:inductive, i:term.
check-elem _ E :- elem-ok E, !.
check-elem D E :-
  coq.error "Egglog: a list in the datatype" {coq.gref->id (indt D)} "has elements of type"
    {coq.term->string E} "which is neither a value type, a datatype, a list of these nor a"
    "pair of these.".

% The sort of an argument of a constructor of the datatype D. A list is a class, the chain of its
% cons nodes.
pred con-arg-sort i:inductive, i:term, o:term.
con-arg-sort D T {{ SId }} :- list-of T E, !, check-elem D E.
con-arg-sort _ T S :- sort-term T S.

% The sort of a component of a list element. A list is a class, as in a constructor.
pred part-sort i:term, o:term.
part-sort T {{ SId }} :- list-of T _, !.
part-sort T S :- sort-term T S.

% The name of an element type in the names of its list tables.
pred type-name i:term, o:string.
type-name {{ prod lp:A lp:B }} N :- !, N is {type-name A} ^ "_" ^ {type-name B}.
type-name {{ list lp:A }} N :- !, N is "list_" ^ {type-name A}.
type-name {{ option lp:A }} N :- !, N is "option_" ^ {type-name A}.
type-name (global GR) N :- coq.gref->id GR N.

% The tables nil and cons of the element type of each list argument of a constructor, unless an
% earlier constructor added them. A cons node takes the components of an element and the rest
% of the list. A component that is a list adds the tables of its own elements after them.
pred list-tables i:term, i:list (pair tkey (list term)), o:list (pair tkey (list term)).
list-tables KTy Acc Out :- arg-types KTy Tys, std.fold Tys Acc add-list-tables Out.

pred add-list-tables i:term, i:list (pair tkey (list term)), o:list (pair tkey (list term)).
add-list-tables T Acc Out :- list-of T E, not (std.exists Acc (p\ sigma S\ p = pr (tk-nil E) S)),
  !, std.map {elem-parts E} part-sort Ss, std.append Ss [{{ SId }}] ConsSorts,
  std.append Acc [pr (tk-nil E) [], pr (tk-cons E) ConsSorts] Acc1,
  std.fold {elem-parts E} Acc1 add-list-tables Out.
add-list-tables _ Acc Acc.

% The code of a list table, which a constructor of a datatype of the program declares.
pred list-code i:list table, i:tkey, o:term.
list-code Ts K Code :- find-table Ts K _ _ _, !, code-of Ts K Code.
list-code _ _ _ :- coq.error "Egglog: a pattern holds a list of a type that no constructor of a"
  "datatype of the program holds.".

% ---------------------------------------------------------------------------------------------
% Encoders of lists

% The encoder of the lists of the element type E. It is a fixpoint that maps the empty list to
% the node of the nil table, and an element in front of a list to the node of the cons table
% over the expressions of the components of the element and of the rest. [Part Ty X Expr] gives
% the expression [Expr] of a component [X] of type [Ty].
pred list-encoder i:list table, i:(pred i:term, i:term, o:term), i:term, o:term.
list-encoder Ts Part E Fix :-
  code-of Ts (tk-nil E) NilCode, code-of Ts (tk-cons E) ConsCode,
  LTy = {{ list lp:E }}, RetTy = {{ @Model.expr positive }},
  (pi go x rest\ decl x `x` E => decl rest `rest` LTy =>
     cons-expr Part E ConsCode go x rest (Cons go x rest)),
  Fix = fix `encode_list` 0 {{ lp:LTy -> lp:RetTy }} (go\ fun `l` LTy (l\
    match l (fun `l` LTy _\ RetTy)
      [{{ @Model.EApp positive lp:NilCode (@nil (@Model.expr positive)) }},
       fun `x` E (x\ fun `rest` LTy (rest\ Cons go x rest))])).

% The cons node of the element [X] in front of the list [Rest], where [Go] encodes the rest. The
% components of a pair are its two projections, so that the node of a pair that a clause binds
% as a variable [p] is the node of the components [fst p] and [snd p].
pred cons-expr i:(pred i:term, i:term, o:term), i:term, i:term, i:term, i:term, i:term,
  o:term.
cons-expr Part {{ prod lp:A lp:B }} Code Go X Rest {{ @Model.EApp positive lp:Code lp:L }} :- !,
  Part A {{ @fst lp:A lp:B lp:X }} EA, Part B {{ @snd lp:A lp:B lp:X }} EB,
  list->term {{ @Model.expr positive }} [EA, EB, app [Go, Rest]] L.
cons-expr Part E Code Go X Rest {{ @Model.EApp positive lp:Code lp:L }} :-
  Part E X EX, list->term {{ @Model.expr positive }} [EX, app [Go, Rest]] L.

% ---------------------------------------------------------------------------------------------
% Rulesets

% The declaration 'ruleset S C1 .. Ck': the name of the ruleset and the names of its constructors.
kind rsdecl type.
type rsdecl string -> list string -> rsdecl.

% A ruleset: its name and its constructors.
kind ruleset type.
type ruleset string -> list constructor -> ruleset.

% A member of the module of every program, whose name no ruleset takes.
pred program-member i:string.
program-member "spec".
program-member "program".
program-member "facts".
program-member "inputs".
program-member "relation".
program-member "lattice".
program-member "closed".
program-member "default".
program-member "all".

% The constructors of a declared ruleset. Each name is a constructor of a relation that the
% command reads.
pred ruleset-of i:list inductive, i:rsdecl, o:ruleset.
ruleset-of Is (rsdecl S Names) (ruleset S Ks) :-
  if (program-member S)
     (coq.error {calc ("Egglog: the ruleset " ^ S ^
       " has the name of a member that the module of every program defines.")})
     true,
  std.map Names (ruleset-member Is S) Ks.

pred ruleset-member i:list inductive, i:string, i:string, o:constructor.
ruleset-member Is S Name K :-
  coq.locate-all Name Locs,
  if (std.mem Locs (loc-gref (indc K0)), coq.env.indc->indt K0 I0 _, std.mem! Is I0) (K = K0)
     (coq.error {calc ("Egglog: the ruleset " ^ S ^ " lists " ^ Name ^
       ", which is no constructor of the relations that the command reads.")}).

% No two rulesets have one name, and no constructor is listed twice, in one ruleset or in two.
pred distinct-rulesets i:list ruleset.
distinct-rulesets [].
distinct-rulesets [ruleset S Ks | Rest] :-
  if (std.mem! Rest (ruleset S _))
     (coq.error {calc ("Egglog: the ruleset " ^ S ^ " is declared twice.")}) true,
  distinct-members S Ks Rest,
  distinct-rulesets Rest.

% No constructor of the ruleset S is listed again in S or in a later ruleset.
pred distinct-members i:string, i:list constructor, i:list ruleset.
distinct-members _ [] _.
distinct-members S [K | Ks] Rest :-
  coq.gref->id (indc K) KName,
  if (std.mem! Ks K)
     (coq.error {calc ("Egglog: the ruleset " ^ S ^ " lists " ^ KName ^ " twice.")}) true,
  if (std.exists Rest (r\ sigma Ks2\ r = ruleset S2 Ks2, std.mem! Ks2 K))
     (coq.error {calc ("Egglog: the constructor " ^ KName ^ " is in the rulesets " ^ S ^
       " and " ^ S2 ^ ", and a rule belongs to one ruleset at most.")})
     true,
  distinct-members S Ks Rest.

% The position of the rule of each constructor that has a clause. Each clause lowers to the rule
% at its own position, and a closure law of an equation has no clause.
pred rule-positions i:list (pair constructor (list term)), i:int, o:list (pair constructor int).
rule-positions [] _ [].
rule-positions [pr K [_] | Rest] N [pr K N | Ps] :- !, M is N + 1, rule-positions Rest M Ps.
rule-positions [pr _ [] | Rest] N Ps :- rule-positions Rest N Ps.

% A constructor that a ruleset lists has a rule.
pred has-rule i:string, i:list (pair constructor int), i:constructor.
has-rule _ Positions K :- std.mem! Positions (pr K _), !.
has-rule S _ K :- coq.gref->id (indc K) KName,
  coq.error {calc ("Egglog: the ruleset " ^ S ^ " lists " ^ KName ^
    ", a closure law of an equation, which has no rule.")}.

% Define a constant that lists rule positions, in increasing order.
pred define-positions i:string, i:list int.
define-positions Name Ns :-
  std.map Ns int->N Ts, list->term {{ N }} Ts T,
  coq.env.add-const Name T {{ list N }} @transparent! _.

% Define the rule positions of each ruleset, of the constructors that no ruleset lists
% ([default]) and of every constructor ([all]).
pred define-rulesets i:list ruleset, i:list (pair constructor int).
define-rulesets Rulesets Positions :-
  std.forall Rulesets (r\ sigma S Ks Ns\ r = ruleset S Ks,
    std.forall Ks (has-rule S Positions),
    std.map-filter Positions (p\ n\ sigma K\ p = pr K n, std.mem! Ks K) Ns,
    define-positions S Ns),
  std.map-filter Positions (p\ n\ sigma K\ p = pr K n,
    not (std.exists Rulesets (r\ sigma Ks\ r = ruleset _ Ks, std.mem! Ks K))) Default,
  define-positions "default" Default,
  std.map Positions (p\ n\ p = pr _ n) All,
  define-positions "all" All.

}}.
