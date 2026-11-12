(** * Placeholder rewrite compilation

    These operations provide the interfaces for compiling flat rewrites.
    For example, the placeholder compiler emits an empty program.
    Builds on: CompileSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Egraph Require Import Syntax CompileSig.

Import List.ListNotations.

Module CompileCode (V : VALUE_OPS) <: COMPILE_OPS V.
  (* STUB-CODE *)
  Definition compile (_ : list (positive * decl)) (_ : list (rewrite V.t)) : program V.t :=
    Program V.t [] [].
  (* STUB-CODE *)
  Definition flatten_lhs (_ : rewrite V.t) : list (atom V.t) := [].
  (* STUB-CODE *)
  Definition root_var (_ : rewrite V.t) : positive := 1%positive.
End CompileCode.

Module Compile (V : VALUE) <: COMPILE V.
  Include CompileCode V.
  Include COMPILE_SPEC V.
  Lemma compile_valid : forall (M : model (V := V.t)) ds rws,
    Forall (valid_rw V.prim V.merge M (lookup_kind (map snd ds))) rws ->
    valid V.prim V.merge M (compile ds rws).
  Proof. Admitted.
  Lemma flatten_sound : forall w rw s, matches V.prim w (flatten_lhs rw) s ->
    exists tau c e, s (root_var rw) = Some (Id c) /\
      instantiates tau (lhs V.t rw) e /\ represents w (Id c) e /\
      cond_in_view w tau (cond V.t rw).
  Proof. Admitted.
End Compile.

Module CompileT (V : VALUE_T) <: COMPILE_ALL V.
  Include Compile V.
  TimeFun compile.
  TimeFun flatten_lhs.
  TimeFun root_var.
  (* STUB-CODE *)
  Definition compile_rule (_ : rewrite V.t) : rule V.t := Rule V.t [] [].
  (* STUB-CODE *)
  Definition flatten_pat (_ : fpat V.t) (_ : positive) : list (atom V.t) := [].
  TimeFun compile_rule.
  TimeFun flatten_pat.
  Lemma F1_compile_rule_valid : forall (M : model (V := V.t))
    (ds : list (positive * decl)) rw s,
    valid_rw V.prim V.merge M (lookup_kind (map snd ds)) rw ->
    Forall (model_atom V.prim M (lookup_kind (map snd ds)) s)
      (query V.t (compile_rule rw)) ->
    model_actions V.prim M (lookup_kind (map snd ds)) s (actions V.t (compile_rule rw)).
  Proof. Admitted. (* STUB *)
  Lemma F2_compile_program : forall ds rws,
    decls V.t (compile ds rws) = map snd ds /\
    rules V.t (compile ds rws) = map compile_rule rws.
  Proof. Admitted. (* STUB *)
  Lemma F3_flatten_spec : forall rw,
    flatten_lhs rw = flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw.
  Proof. Admitted. (* STUB *)
  Lemma F4_inst_represents : forall w tau s p e root_id c,
    represents_subst w tau s -> instantiates tau p e -> s root_id = Some (Id c) ->
    matches V.prim w (flatten_pat p root_id) s -> represents w (Id c) e.
  Proof. Admitted. (* STUB *)
End CompileT.
