(** * Stack-disciplined interprocedural graphs

    Edge kinds specify the call-site stack change of each taken transition.
    For example, a return requires and removes the matching top call site.
    Builds on: ProgramLink. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink.
Import List.ListNotations.

Module Icfg.

(** Internal edges preserve the stack, calls push and returns pop a matching site. *)
Inductive kind (P : Type) :=
  | Internal
  | Call (p : P)
  | Return (p : P).
Arguments Internal {P}.
Arguments Call {P}.
Arguments Return {P}.

(** An interprocedural presentation adds charged edge kinds to an ordinary CFG. *)
Record t (N E P : Type) := Make {
  cfg : Cfg.t N E;
  site_enc : encoding P;
  kind_c : E -> Cost.t (kind P)
}.
Arguments Make {N E P}.
Arguments cfg {N E P}.
Arguments site_enc {N E P}.
Arguments kind_c {N E P}.

Definition edge_kind {N E P} (c : t N E P) e := Cost.value (kind_c c e).

(** Pure kind readers charge one primitive tick. *)
Definition of_pure {N E P} cfg enc kind : t N E P :=
  Make cfg enc (Cost.lift (fun _ => 1%N) kind).

End Icfg.

Module IcfgLink.

(** An ICFG link supplies the concrete call-site stack beside the ordinary link. *)
Record t (S O N E P : Type) := Make {
  link : Link.t S O N E;
  stack : S -> list P
}.
Arguments Make {S O N E P}.
Arguments link {S O N E P}.
Arguments stack {S O N E P}.

End IcfgLink.

(** Reachable taken edges obey their stack kind and stationary steps preserve the stack. *)
Record icfg_laws {S O N E P} (m : semantics S O) (c : Icfg.t N E P)
    (il : IcfgLink.t S O N E P) : Prop := {
  icfg_link_ok : link_laws m (Cfg.graph (Icfg.cfg c)) (IcfgLink.link il);
  initial_stack : forall s, initial m s -> IcfgLink.stack il s = [];
  taken_stack : forall e, on_steps m (fun s l s' =>
    Link.taken (IcfgLink.link il) s l s' e ->
    match Icfg.edge_kind c e with
    | Icfg.Internal => IcfgLink.stack il s' = IcfgLink.stack il s
    | Icfg.Call p => IcfgLink.stack il s' = p :: IcfgLink.stack il s
    | Icfg.Return p => IcfgLink.stack il s = p :: IcfgLink.stack il s'
    end);
  stays_stack : on_steps m (fun s l s' => Link.stays (IcfgLink.link il) s l s' ->
    IcfgLink.stack il s' = IcfgLink.stack il s)
}.
Arguments icfg_link_ok {S O N E P m c il}.
Arguments initial_stack {S O N E P m c il}.
Arguments taken_stack {S O N E P m c il}.
Arguments stays_stack {S O N E P m c il}.
