(** * Values and primitives in the derive command

    This file declares the Elpi file [egglog.primitives] of the command [Egglog] of
    [Derive.v], with the databases of registered value types and primitives. A value type is
    [positive], a type that [Egglog Value T M] registers with its encoder module [M], or a pair,
    an option or a list of value types, whose encoder the command builds from the encoders of
    their parts. A derived term holds the encoding of a value, which is a positive. The command
    [Egglog Primitives S f1 .. fn] defines a code for each function and the primitive function
    of the set [S], which tests each code in turn. A function may take any number of arguments.

    For example, once [Egglog Value Z ZEncode] registers [Z], [enc-term] writes a term [z] of
    type [Z] as [ZEncode.encode z] and a term [p] of type [Z * bool] as
    [encode_pair ZEncode.encode BoolEncode.encode p], and [Egglog Primitives Keys Pos.eqb]
    defines the code [Keys.eqb_code] and the primitive function [Keys.prim].

    Builds on: the definitions that derived programs call, and Elpi. *)

From Stdlib Require Import PArith.
From elpi Require Import elpi.
From Galois.Front Require Import DeriveHelpers.

(** * Registries

    The command reads the registered value types and primitives from these databases.
    [Egglog Value] and [Egglog Primitives] add to them. *)

Elpi Db egglog.values lp:{{
  % A registered value type: the type, its encoder and its decoder.
  pred value-enc o:term, o:term, o:term.
}}.

Elpi Db egglog.prims lp:{{
  % A registered primitive: its function, its code and the primitive function of its set.
  pred prim-code o:gref, o:term, o:term.
}}.

(** * Values and primitives *)

Elpi File egglog.primitives lp:{{

% ---------------------------------------------------------------------------------------------
% Value types

% A value type is positive, a registered type, or a pair, an option or a list of value types.
pred value-type i:term.
value-type T :- type-coder T _ _.

% The encoder and the decoder of a value type. Those of a pair, an option and a list come from
% the encoders and decoders of their parts.
pred type-coder i:term, o:term, o:term.
type-coder T {{ id_encode }} {{ id_decode }} :- coq.locate "positive" GR, T = global GR, !.
type-coder T Enc Dec :- value-enc T Enc Dec, !.
type-coder {{ prod lp:A lp:B }} {{ @encode_pair lp:A lp:B lp:EA lp:EB }}
    {{ @decode_pair lp:A lp:B lp:DA lp:DB }} :- !,
  type-coder A EA DA, type-coder B EB DB.
type-coder {{ option lp:A }} {{ @encode_option lp:A lp:EA }} {{ @decode_option lp:A lp:DA }} :-
  !, type-coder A EA DA.
type-coder {{ list lp:A }} {{ @encode_list lp:A lp:EA }} {{ @decode_list lp:A lp:DA }} :-
  type-coder A EA DA.

% The engine value of a value of type Ty: the value itself of positive, and its encoder applied
% otherwise.
pred enc-by-ty i:term, i:term, o:term.
enc-by-ty Ty X X :- coq.locate "positive" GR, Ty = global GR, !.
enc-by-ty Ty X Y :- type-coder Ty Enc _, !, coq.mk-app Enc [X] Y.
enc-by-ty _ X X.

% The engine value of a value term, by the type of the term.
pred enc-term i:term, o:term.
enc-term X Y :- coq.typecheck X Ty ok, enc-by-ty Ty X Y.

% The decoder of a value type.
pred dec-of-type i:term, o:term.
dec-of-type Ty Dec :- type-coder Ty _ Dec, !.
dec-of-type Ty _ :- coq.error "Egglog: a primitive has type" {coq.term->string Ty}
  "which is not a value type".

% The encoder of a value type.
pred enc-of-type i:term, o:term.
enc-of-type Ty Enc :- type-coder Ty Enc _, !.
enc-of-type Ty _ :- coq.error "Egglog: a primitive has type" {coq.term->string Ty}
  "which is not a value type".

% The type of a value of a table, which must be a value type.
pred check-value i:term.
check-value T :- value-type T, !.
check-value T :- coq.error "Egglog: the type" {coq.term->string T}
  "is not a value type. A value type is positive, a type that Egglog Value registers, or a"
  "pair, an option or a list of value types.".

% ---------------------------------------------------------------------------------------------
% Numerals and lists

pred int->pos i:int, o:term.
int->pos 1 {{ xH }} :- !.
int->pos N {{ xO lp:P }} :- 0 is N mod 2, !, M is N div 2, int->pos M P.
int->pos N {{ xI lp:P }} :- M is N div 2, int->pos M P.

pred int->N i:int, o:term.
int->N 0 {{ N0 }} :- !.
int->N N {{ Npos lp:P }} :- int->pos N P.

pred list->term i:term, i:list term, o:term.
list->term Ty [] {{ @nil lp:Ty }}.
list->term Ty [X | Xs] {{ @cons lp:Ty lp:X lp:T }} :- list->term Ty Xs T.

% The list of engine values of a list of value terms.
pred enc-list i:list term, o:term.
enc-list Xs L :- std.map Xs enc-term Es, list->term {{ positive }} Es L.

% ---------------------------------------------------------------------------------------------
% Primitives

% The primitive function of a program: the fixed one of its primitive set, or a bound one.
pred fixed-prim o:term.
pred bind-prim i:bool, i:(term -> term -> prop), o:term.
bind-prim _ K Out :- fixed-prim F, !, K F Out.
bind-prim IsProd K Out :- prim-type PT,
  if (IsProd = tt) (Out = prod `prim` PT B) (Out = fun `prim` PT B),
  pi prim\ decl prim `prim` PT => K prim (B prim).

% The code of a primitive in the primitive set that the command names after [with]. A
% primitive of another set, or of no named set, stops the command.
pred prim-of i:gref, o:term.
prim-of GR Code :- fixed-prim F, prim-code GR Code F, !.
prim-of GR _ :- prim-code GR _ _, !, coq.error "Egglog:" {coq.gref->id GR}
  "is a primitive of a set that the command does not name after 'with'".

% The arguments and the result of a primitive premise [f x1 .. xn = w].
pred computes-values i:term, o:term, o:term.
computes-values (app [global (indt _), _, app [_ | Xs], W0]) Vs W :-
  enc-list Xs Vs, enc-term W0 W.

% The primitive function among the arguments of a lemma that quantifies over it.
pred prim-args i:term, o:list term.
prim-args _ [] :- fixed-prim _, !.
prim-args P [P].

% The types of the arguments of a function type.
pred arg-types i:term, o:list term.
arg-types (prod _ Ty F) [Ty | Tys] :- !, pi x\ arg-types (F x) Tys.
arg-types _ [].

% The call of a function of type Ty on engine values, without the function. A step [prim_arg]
% decodes each argument, and a step [prim_ret] encodes the result.
pred prim-chain i:term, o:term.
prim-chain (prod _ A (_\ B)) {{ @prim_arg lp:A lp:B lp:D lp:K }} :- !,
  dec-of-type A D, prim-chain B K.
prim-chain R {{ @prim_ret lp:R lp:E }} :- enc-of-type R E.

% The body of the primitive function of a set: a test of each code in turn.
pred prim-body i:list (pair term term), i:term, i:term, o:term.
prim-body [] _ _ {{ @None positive }}.
prim-body [pr Code Call | Rest] P Vs {{ prim_case lp:P lp:Code lp:Call lp:Vs lp:R }} :-
  prim-body Rest P Vs R.

pred define-prims i:list gref, i:int, o:list (pair gref term), o:list (pair term term).
define-prims [] _ [] [].
define-prims [GR | GRs] N [pr GR (global (const C)) | Cs] [pr (global (const C)) Call | Bs] :-
  int->pos N P, Name is {coq.gref->id GR} ^ "_code",
  coq.env.add-const Name P {{ positive }} @transparent! C,
  coq.env.typeof GR Ty, prim-chain Ty K, coq.mk-app K [global GR] Call,
  M is N + 1, define-prims GRs M Cs Bs.

pred prim-type o:term.
prim-type {{ positive -> list positive -> option positive }}.

% ---------------------------------------------------------------------------------------------
% Registering value types

% Register a value type with its encoder module: a later program encodes the values of the type.
% The tactic simpl leaves the encoder alone, so that the encoding of a literal keeps the form
% [encode c], which the glue tactics decode and compare with other encodings.
pred register-value i:string, i:string.
register-value Ty Mod :-
  coq.locate Ty TyGR, T = global TyGR,
  if (value-type T) (coq.error "Egglog:" Ty "is already a value type") true,
  coq.locate {calc (Mod ^ ".encode")} EncGR, Enc = global EncGR,
  coq.locate {calc (Mod ^ ".decode")} DecGR, Dec = global DecGR,
  coq.locate {calc (Mod ^ ".decode_encode")} LemGR, Lem = global LemGR,
  std.assert-ok! (coq.typecheck Enc {{ lp:T -> positive }})
    "Egglog: the encoder is not a function from the type to positive",
  std.assert-ok! (coq.typecheck Dec {{ positive -> option lp:T }})
    "Egglog: the decoder is not a function from positive to the type",
  std.assert-ok! (coq.typecheck Lem {{ forall x : lp:T, lp:Dec (lp:Enc x) = Some x }})
    "Egglog: decode_encode does not say that decoding undoes encoding",
  std.assert-ok! (coq.elaborate-skeleton {{ @encode_inj_of lp:T lp:Enc lp:Dec lp:Lem }} InjTy InjE)
    "Egglog: the injectivity lemma is ill-typed",
  coq.env.add-const {calc (Mod ^ "_encode_inj")} InjE InjTy @opaque! InjC,
  coq.hints.add-resolve (const InjC) "egglog_inj" 0 _,
  coq.hints.add-resolve LemGR "egglog_decode" 0 _,
  (@global! => coq.arguments.set-simplification EncGR never),
  coq.elpi.accumulate library "egglog.values" (clause _ _ (value-enc T Enc Dec)).

}}.
