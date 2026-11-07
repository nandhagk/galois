(** * Open SSA presentations

    SSA definitions and client guards are separate from concrete valuations.
    For example, a block parameter receives an argument from a taken incoming edge.
    Builds on: ProgramLink and BaseEncoding. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink.

(** Values are computed, received as block parameters, or unconstrained. *)
Inductive definition (N V K : Type) : Type :=
  | Op (o : K) (args : list V)
  | Param (b : N) (i : nat)
  | Arbitrary.
Arguments Op {N V K}.
Arguments Param {N V K}.
Arguments Arbitrary {N V K}.

Module Ssa.

(** An SSA presentation contains computational inventories and costed syntax readers. *)
Record t (N E V K G : Type) := Make {
  cfg : Cfg.t N E;
  val_enc : encoding V;
  values : list V;
  def_c : V -> Cost.t (definition N V K);
  home_c : V -> Cost.t N;
  params_c : N -> Cost.t (list V);
  args_c : E -> Cost.t (list V);
  guards_c : E -> Cost.t (list (G * list V))
}.
Arguments Make {N E V K G}.
Arguments cfg {N E V K G}.
Arguments val_enc {N E V K G}.
Arguments values {N E V K G}.
Arguments def_c {N E V K G}.
Arguments home_c {N E V K G}.
Arguments params_c {N E V K G}.
Arguments args_c {N E V K G}.
Arguments guards_c {N E V K G}.

Definition def {N E V K G} (p : t N E V K G) x := Cost.value (def_c p x).
Definition home {N E V K G} (p : t N E V K G) x := Cost.value (home_c p x).
Definition params {N E V K G} (p : t N E V K G) n := Cost.value (params_c p n).
Definition args {N E V K G} (p : t N E V K G) e := Cost.value (args_c p e).
Definition guards {N E V K G} (p : t N E V K G) e := Cost.value (guards_c p e).

(** Pure client syntax readers charge one primitive tick on every call. *)
Definition of_pure {N E V K G} cfg enc values def home params args guards : t N E V K G :=
  Make cfg enc values (Cost.lift (fun _ => 1%N) def)
    (Cost.lift (fun _ => 1%N) home) (Cost.lift (fun _ => 1%N) params)
    (Cost.lift (fun _ => 1%N) args) (Cost.lift (fun _ => 1%N) guards).

End Ssa.

Module SsaLink.

(** A concrete valuation augments a graph link without changing the presentation. *)
Record t (S O N E V C : Type) := Make {
  link : Link.t S O N E;
  val : S -> V -> option C
}.
Arguments Make {S O N E V C}.
Arguments link {S O N E V C}.
Arguments val {S O N E V C}.

End SsaLink.

(** Every operation used as a guard operand agrees with its arguments in the source state. *)
Definition guard_ops_consistent {S O N E V K G C} (p : Ssa.t N E V K G)
    (sl : SsaLink.t S O N E V C) (eval : K -> list C -> option C) s e : Prop :=
  forall g ys x o args, In (g, ys) (Ssa.guards p e) -> In x ys ->
    Ssa.def p x = Op o args ->
    exists cs c, Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs /\
      SsaLink.val sl s x = Some c /\ eval o cs = Some c.

(** Concrete steps preserve bindings or expose their constructive definition origins.
    Guard clauses generalize legacy singleton subjects to every client guard operand.
    Edge and value quantifiers commute past the common step premises. *)
Record ssa_laws {S O N E V K G C} (m : semantics S O) (p : Ssa.t N E V K G)
    (sl : SsaLink.t S O N E V C) (eval : K -> list C -> option C)
    (holds : G -> list C -> Prop) : Prop := {
  link_ok : link_laws m (Cfg.graph (Ssa.cfg p)) (SsaLink.link sl);
  param_defs : forall x b i, Ssa.def p x = Param b i ->
    nth_error (Ssa.params p b) i = Some x;
  guards_hold : forall e, on_steps m (fun s l s' =>
    Link.taken (SsaLink.link sl) s l s' e ->
    forall g ys, In (g, ys) (Ssa.guards p e) ->
    exists cs, Forall2 (fun y c => SsaLink.val sl s y = Some c) ys cs /\ holds g cs);
  guard_op_defined : forall e, on_steps m (fun s l s' =>
    Link.taken (SsaLink.link sl) s l s' e -> guard_ops_consistent p sl eval s e);
  value_origin : forall x c, on_steps m (fun s l s' =>
    SsaLink.val sl s' x = Some c -> SsaLink.val sl s x = Some c \/
    (exists o args cs, Ssa.def p x = Op o args /\
      Forall2 (fun y d => SsaLink.val sl s y = Some d) args cs /\ eval o cs = Some c) \/
    (exists e b i z, Ssa.def p x = Param b i /\ Link.taken (SsaLink.link sl) s l s' e /\
      Graph.target (Cfg.graph (Ssa.cfg p)) e = b /\ nth_error (Ssa.args p e) i = Some z /\
      SsaLink.val sl s z = Some c) \/ Ssa.def p x = Arbitrary);
  coverage : forall s x c, reachable_state m s -> SsaLink.val sl s x = Some c ->
    In x (Ssa.values p)
}.
Arguments link_ok {S O N E V K G C m p sl eval holds}.
Arguments param_defs {S O N E V K G C m p sl eval holds}.
Arguments guards_hold {S O N E V K G C m p sl eval holds}.
Arguments guard_op_defined {S O N E V K G C m p sl eval holds}.
Arguments value_origin {S O N E V K G C m p sl eval holds}.
Arguments coverage {S O N E V K G C m p sl eval holds}.
