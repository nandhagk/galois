(** * Compilation of flat rewrites to engine rules

    Compilation names intermediate pattern nodes and joins them through engine atoms.
    For example, a binary application introduces an atom for its two child classes.
    Builds on: Egraph syntax and Egglog models and value signatures. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig DatabaseSig Syntax Model Sorts.
From Galois.Egraph Require Import Syntax.

Module Type COMPILE_OPS (V : VALUE_OPS).
  Parameter compile : list decl -> list (rewrite V.t) -> list (rule V.t) -> program V.t.
  Parameter compile_rule : rewrite V.t -> rule V.t.
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
  (** The variables of a context are bound to cells that represent their terms. *)
  Definition represents_on (g : ctx) (w : Model.view (V := V.t)) (tau : subst)
      (s : Model.env (V := V.t)) : Prop :=
    forall h t e, g h = Some t -> tau h = Some e ->
      exists c, s h = Some c /\ represents w c e.
  (** Identifier equality is an equivalence, a key has one output, and two identifiers that
      occur in rows and are equal in the view are identical. *)
  Definition canonical_view (w : Model.view (V := V.t)) : Prop :=
    (forall i, same w i i) /\ (forall i j, same w i j -> same w j i) /\
    (forall i j k, same w i j -> same w j k -> same w i k) /\
    (forall f k o1 o2, row w f k o1 -> row w f k o2 -> o1 = o2) /\
    (forall f k o f' k' o' i j, row w f k o -> row w f' k' o' ->
      In (Id i) (k ++ option_list o) -> In (Id j) (k' ++ option_list o') ->
      same w i j -> i = j).
End COMPILE_SPEC.

Module Type COMPILE_LAWS (V : VALUE) (Import C : COMPILE_OPS V)
    (Import CS : COMPILE_SPEC V C).
  (** Compilation keeps the declarations, compiles each rewrite to one rule and appends the
      analysis rules. *)
  Parameter compile_program : forall ds rws ans,
    decls V.t (compile ds rws ans) = ds /\
    rules V.t (compile ds rws ans) = map compile_rule rws ++ ans.
  (** A compiled rewrite queries its flattened left side. *)
  Parameter compile_query : forall rw, query V.t (compile_rule rw) = flatten_lhs rw.
  (** Well-sorted rewrites and analysis rules compile to a well-sorted program. *)
  Parameter compile_sorted : forall ds rws ans, rules_ok ds rws ans ->
    program_ok (compile ds rws ans).
  (** Valid rewrites and analysis rules, with lattice functions closed under their merges,
      compile to a program that is valid on well-sorted environments of the same model. *)
  Parameter compile_valid : forall (M : model (V := V.t)) ds rws ans, rules_ok ds rws ans ->
    Forall (valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds)) rws ->
    Forall (rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds)) ans ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    valid_sorted V.prim V.merge M (compile ds rws ans).
  (** A match of a flattened left side represents an instance in the class of its root. *)
  Parameter flatten_sound : forall ds w rw g s,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    view_sorted (lookup_sorts ds) w -> (forall f, kind w f = lookup_kind ds f) ->
    (forall i, same w i i) -> matches V.prim w (flatten_lhs rw) s ->
    exists tau c e, s (root_var rw) = Some (Id c) /\
      instantiates tau (lhs V.t rw) e /\ represents w (Id c) e /\
      cond_in_view w tau (cond V.t rw).
  (** A canonical view matches every represented left side whose condition holds. *)
  Parameter flatten_complete : forall ds w rw g tau c e,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g -> canonical_view w ->
    instantiates tau (lhs V.t rw) e -> represents w (Id c) e ->
    cond_in_view w tau (cond V.t rw) ->
    exists s j, matches V.prim w (flatten_lhs rw) s /\ represents_on g w tau s /\
      s (root_var rw) = Some (Id j) /\ same w c j.
  (** A present compiled right side represents its instance in the class of the matched
      root. *)
  Parameter present_represents : forall ds w rw g s tau c r,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    view_sorted (lookup_sorts ds) w -> (forall f, kind w f = lookup_kind ds f) ->
    canonical_view w -> matches V.prim w (flatten_lhs rw) s ->
    s (root_var rw) = Some (Id c) -> represents_on g w tau s ->
    instantiates tau (rhs V.t rw) r ->
    present V.prim V.merge w s (actions V.t (compile_rule rw)) ->
    represents w (Id c) r.
End COMPILE_LAWS.

Module Type COMPILE (V : VALUE) := COMPILE_OPS V <+ COMPILE_SPEC V <+ COMPILE_LAWS V.

Module Type COMPILE_TIME (V : VALUE_T) (Import C : COMPILE V).
  Parameter T_compile : list decl -> list (rewrite V.t) -> list (rule V.t) -> N.
  Parameter T_compile_rule T_flatten_lhs T_root_var : rewrite V.t -> N.
  Parameter c_compile : N.
  (** Compilation reads every rewrite once and passes the analysis rules through. *)
  Parameter T_compile_le : forall ds rws ans,
    (T_compile ds rws ans <= c_compile *
      N.of_nat (fold_right (fun rw n => (rewrite_size rw + n)%nat) 0 rws +
        length ans + 1)%nat)%N.
End COMPILE_TIME.

Module Type COMPILE_T (V : VALUE_T) := COMPILE V <+ COMPILE_TIME V.

Module Type COMPILE_PLAN (V : VALUE_T) (Import C : COMPILE_T V).
  Parameter flatten_pat : fpat V.t -> positive -> list (atom V.t).
  Parameter T_flatten_pat : fpat V.t -> positive -> N.
  Parameter k_compile : N.
  (** A compiled rewrite is valid on well-sorted environments when the rewrite is valid. *)
  Parameter F1_compile_rule_valid : forall (M : model (V := V.t)) ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds) rw ->
    rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  (** A well-sorted rewrite compiles to a well-sorted rule. *)
  Parameter F2_compile_rule_sorted : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    rule_ok (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  (** Flattening the left side uses the rewrite's chosen root variable. *)
  Parameter F3_flatten_spec : forall rw,
    flatten_lhs rw = flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw.
  (** Pattern instantiation retains each represented hole under the same substitution. *)
  Parameter F4_inst_represents : forall w tau s p e root_id c, app_rooted p ->
    represents_subst w tau s -> instantiates tau p e -> s root_id = Some (Id c) ->
    matches V.prim w (flatten_pat p root_id) s -> represents w (Id c) e.
  (** Compiling a list pays for each rewrite and one step per rewrite. *)
  Parameter T1_compile_split : forall ds rws ans,
    (T_compile ds rws ans <= fold_right (fun rw n => T_compile_rule rw + n) 0 rws +
      k_compile * N.of_nat (length rws + length ans + 1))%N.
  (** Compiling one rewrite is linear in its size. *)
  Parameter T2_compile_rule_le : forall rw,
    (T_compile_rule rw <= k_compile * N.of_nat (rewrite_size rw + 1))%N.
End COMPILE_PLAN.

Module Type COMPILE_ALL (V : VALUE_T) := COMPILE_T V <+ COMPILE_PLAN V.
