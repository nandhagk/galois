(** * Placeholder rewrite compilation

    These operations provide the interfaces for compiling flat rewrites.
    For example, the placeholder compiler emits an empty program.
    Builds on: CompileSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig DatabaseSig Syntax Model Sorts.
From Galois.Egraph Require Import Syntax CompileSig.

Import List.ListNotations.

Module CompileCode (V : VALUE_OPS) <: COMPILE_OPS V.
  (* STUB-CODE *)
  Definition compile (_ : list decl) (_ : list (rewrite V.t)) (_ : list (rule V.t))
      : program V.t := Program V.t [] [].
  (* STUB-CODE *)
  Definition compile_rule (_ : rewrite V.t) : rule V.t := Rule V.t [] [].
  (* STUB-CODE *)
  Definition flatten_lhs (_ : rewrite V.t) : list (atom V.t) := [].
  (* STUB-CODE *)
  Definition root_var (_ : rewrite V.t) : positive := 1%positive.
End CompileCode.

Module Compile (V : VALUE) <: COMPILE V.
  Include CompileCode V.
  Include COMPILE_SPEC V.
  Lemma compile_program : forall ds rws ans,
    decls V.t (compile ds rws ans) = ds /\
    rules V.t (compile ds rws ans) = map compile_rule rws ++ ans.
  Proof. Admitted. (* STUB *)

  Lemma compile_query : forall rw, query V.t (compile_rule rw) = flatten_lhs rw.
  Proof. Admitted. (* STUB *)

  Lemma compile_sorted : forall ds rws ans, rules_ok ds rws ans ->
    program_ok (compile ds rws ans).
  Proof. Admitted. (* STUB *)

  Lemma compile_valid : forall (M : model (V := V.t)) ds rws ans, rules_ok ds rws ans ->
    Forall (valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds)) rws ->
    Forall (rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds)) ans ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    valid_sorted V.prim V.merge M (compile ds rws ans).
  Proof. Admitted. (* STUB *)

  Lemma flatten_sound : forall ds w rw g s,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    view_sorted (lookup_sorts ds) w -> (forall f, kind w f = lookup_kind ds f) ->
    (forall i, same w i i) -> matches V.prim w (flatten_lhs rw) s ->
    exists tau c e, s (root_var rw) = Some (Id c) /\
      instantiates tau (lhs V.t rw) e /\ represents w (Id c) e /\
      cond_in_view w tau (cond V.t rw).
  Proof. Admitted. (* STUB *)

  Lemma flatten_complete : forall ds w rw g tau c e,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g -> canonical_view w ->
    instantiates tau (lhs V.t rw) e -> represents w (Id c) e ->
    cond_in_view w tau (cond V.t rw) ->
    exists s j, matches V.prim w (flatten_lhs rw) s /\ represents_on g w tau s /\
      s (root_var rw) = Some (Id j) /\ same w c j.
  Proof. Admitted. (* STUB *)

  Lemma present_represents : forall ds w rw g s tau c r,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    view_sorted (lookup_sorts ds) w -> (forall f, kind w f = lookup_kind ds f) ->
    canonical_view w -> matches V.prim w (flatten_lhs rw) s ->
    s (root_var rw) = Some (Id c) -> represents_on g w tau s ->
    instantiates tau (rhs V.t rw) r ->
    present V.prim V.merge w s (actions V.t (compile_rule rw)) ->
    represents w (Id c) r.
  Proof. Admitted. (* STUB *)

End Compile.

Module CompileT (V : VALUE_T) <: COMPILE_ALL V.
  Include Compile V.
  TimeFun compile.
  TimeFun compile_rule.
  TimeFun flatten_lhs.
  TimeFun root_var.
  (* STUB-CODE *)
  Definition flatten_pat (_ : fpat V.t) (_ : positive) : list (atom V.t) := [].
  TimeFun flatten_pat.
  Definition c_compile : N := 1. (* STUB *)
  Definition k_compile : N := 1. (* STUB *)
  Lemma T_compile_le : forall ds rws ans,
    (T_compile ds rws ans <= c_compile *
      N.of_nat (fold_right (fun rw n => (rewrite_size rw + n)%nat) 0 rws +
        length ans + 1)%nat)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_compile_rule_valid : forall (M : model (V := V.t)) ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds) rw ->
    rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof. Admitted. (* STUB *)

  Lemma F2_compile_rule_sorted : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    rule_ok (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof. Admitted. (* STUB *)

  Lemma F3_flatten_spec : forall rw,
    flatten_lhs rw = flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw.
  Proof. Admitted. (* STUB *)

  Lemma F4_inst_represents : forall w tau s p e root_id c, app_rooted p ->
    represents_subst w tau s -> instantiates tau p e -> s root_id = Some (Id c) ->
    matches V.prim w (flatten_pat p root_id) s -> represents w (Id c) e.
  Proof. Admitted. (* STUB *)

  Lemma T1_compile_split : forall ds rws ans,
    (T_compile ds rws ans <= fold_right (fun rw n => T_compile_rule rw + n) 0 rws +
      k_compile * N.of_nat (length rws + length ans + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_compile_rule_le : forall rw,
    (T_compile_rule rw <= k_compile * N.of_nat (rewrite_size rw + 1))%N.
  Proof. Admitted. (* STUB *)

End CompileT.
