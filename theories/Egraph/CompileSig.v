(** * Compilation of flat rewrites to engine rules

    Compilation names intermediate pattern nodes and joins them through engine atoms.
    For example, a binary application introduces an atom for its two child classes.
    Builds on: Egraph syntax and Egglog models and value signatures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Egraph Require Import Syntax.

Module Type COMPILE_OPS (V : VALUE_OPS).
  Parameter compile : list (positive * decl) -> list (rewrite V.t) -> program V.t.
  Parameter flatten_lhs : rewrite V.t -> list (atom V.t).
  Parameter root_var : rewrite V.t -> positive.
End COMPILE_OPS.

Module Type COMPILE_SPEC (V : VALUE) (Import C : COMPILE_OPS V).
  Definition subst := positive -> option (@Model.expr V.t).
  Definition represents_subst (w : Model.view (V := V.t)) (tau : subst)
      (s : Model.env (V := V.t)) : Prop :=
    forall h e, tau h = Some e -> exists c, s h = Some c /\ represents w c e.
  Definition cond_in_view (w : Model.view (V := V.t)) (tau : subst)
      (conditions : list (atom V.t)) : Prop :=
    exists s, represents_subst w tau s /\ matches V.prim w conditions s.
  Definition instantiates (tau : subst) (p : fpat V.t) (e : @Model.expr V.t) : Prop :=
    unfolds_pat tau (nodes V.t p) (root V.t p) e.
End COMPILE_SPEC.

Module Type COMPILE_LAWS (V : VALUE) (Import C : COMPILE_OPS V)
    (Import CS : COMPILE_SPEC V C).
  (** Compiling valid rewrites gives valid engine rules in the same algebra. *)
  Parameter compile_valid : forall (M : model (V := V.t)) ds rws,
    Forall (valid_rw V.prim V.merge M (lookup_kind (map snd ds))) rws ->
    valid V.prim V.merge M (compile ds rws).
  (** Flattened matches represent the left pattern and satisfy its conditions. *)
  Parameter flatten_sound : forall w rw s, matches V.prim w (flatten_lhs rw) s ->
    exists tau c e, s (root_var rw) = Some (Id c) /\
      instantiates tau (lhs V.t rw) e /\ represents w (Id c) e /\
      cond_in_view w tau (cond V.t rw).
End COMPILE_LAWS.

Module Type COMPILE (V : VALUE) := COMPILE_OPS V <+ COMPILE_SPEC V <+ COMPILE_LAWS V.

Module Type COMPILE_TIME (V : VALUE_T) (Import C : COMPILE V).
  Parameter T_compile : list (positive * decl) -> list (rewrite V.t) -> N.
  Parameter T_flatten_lhs : rewrite V.t -> N.
  Parameter T_root_var : rewrite V.t -> N.
End COMPILE_TIME.

Module Type COMPILE_T (V : VALUE_T) := COMPILE V <+ COMPILE_TIME V.

Module Type COMPILE_PLAN (V : VALUE_T) (Import C : COMPILE_T V).
  Parameter compile_rule : rewrite V.t -> rule V.t.
  Parameter flatten_pat : fpat V.t -> positive -> list (atom V.t).
  Parameter T_compile_rule : rewrite V.t -> N.
  Parameter T_flatten_pat : fpat V.t -> positive -> N.
  (** A compiled rule is valid whenever its source rewrite is valid. *)
  Parameter F1_compile_rule_valid : forall (M : model (V := V.t))
    (ds : list (positive * decl)) rw s,
    valid_rw V.prim V.merge M (lookup_kind (map snd ds)) rw ->
    Forall (model_atom V.prim M (lookup_kind (map snd ds)) s)
      (query V.t (compile_rule rw)) ->
    model_actions V.prim M (lookup_kind (map snd ds)) s (actions V.t (compile_rule rw)).
  (** Compiling a rewrite list keeps its declared kinds and compiled rules. *)
  Parameter F2_compile_program : forall ds rws,
    decls V.t (compile ds rws) = map snd ds /\
    rules V.t (compile ds rws) = map compile_rule rws.
  (** Flattening the left side uses the rewrite's chosen root variable. *)
  Parameter F3_flatten_spec : forall rw,
    flatten_lhs rw = flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw.
  (** Pattern instantiation retains each represented hole under the same substitution. *)
  Parameter F4_inst_represents : forall w tau s p e root_id c,
    represents_subst w tau s -> instantiates tau p e -> s root_id = Some (Id c) ->
    matches V.prim w (flatten_pat p root_id) s -> represents w (Id c) e.
End COMPILE_PLAN.

Module Type COMPILE_ALL (V : VALUE_T) := COMPILE_T V <+ COMPILE_PLAN V.
