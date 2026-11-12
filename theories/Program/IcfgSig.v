(** * Interprocedural edge presentations

    Edge kinds describe stack changes independently of a concrete machine.
    For example, a return removes the same call site that its matching call pushed.
    Builds on: Program.CfgSig and Program.SemanticsSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig.
From Galois.Program Require Import CfgSig SemanticsSig.

Inductive edge_kind (S : Type) : Type :=
  | Intra
  | Call (site : S)
  | Return (site : S)
  | CallToReturn (site : S).

Arguments Intra {S}.
Arguments Call {S}.
Arguments Return {S}.
Arguments CallToReturn {S}.

(** A call pushes its site, a return pops it, and summary edges retain the stack. *)
Definition stack_change {S} (k : edge_kind S) (before after : list S) : Prop :=
  match k with
  | Intra => after = before
  | Call site => after = site :: before
  | Return site => before = site :: after
  | CallToReturn _ => after = before
  end.

Module Type ICFG_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (S : KEY_OPS).
  Parameter kind : P.t -> E.t -> edge_kind S.t.
End ICFG_OPS.

Module Type ICFG_SPEC (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (S : KEY_OPS) (Import I : ICFG_OPS P N E C S).
  Definition matched p e before after := stack_change (kind p e) before after.
End ICFG_SPEC.

Module Type ICFG (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (S : KEY) :=
  ICFG_OPS P N E C S <+ ICFG_SPEC P N E C S.

Module Type ICFG_TIME (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (S : KEY_T) (Import I : ICFG P N E C S).
  Parameter T_kind : P.t -> E.t -> N.
End ICFG_TIME.

Module Type ICFG_T (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (S : KEY_T) :=
  ICFG P N E C S <+ ICFG_TIME P N E C S.

Module Type ICFG_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (S : KEY) (I : ICFG P N E C S)
    (M : SEMANTICS P) (L : CFG_LINK P N E C M).
  Parameter stack : M.state -> list S.t.
  (** An initial state has no suspended call site. *)
  Parameter initial_stack : forall p s, M.initial p s -> stack s = nil.
  (** Every reachable taken edge performs exactly its declared stack change. *)
  Parameter taken_stack : forall p s t e,
    reachable (M.initial p) (M.step p) s -> M.step p s t ->
    L.taken p s t e -> stack_change (I.kind p e) (stack s) (stack t).
End ICFG_LINK.
