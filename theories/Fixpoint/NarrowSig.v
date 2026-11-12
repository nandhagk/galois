(** * Checked narrowing passes

    Narrowing refines a candidate and falls back when checking fails.
    For example, a failed candidate check keeps the input store.
    Builds on: Fixpoint.CheckSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig.

Module Type NARROW_OPS (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (C : CHECK_OPS L S).
  Parameter narrow_candidate : S.prog -> kmap S.key L.t -> kmap S.key L.t.
  Parameter narrow_pass : S.prog -> kmap S.key L.t -> kmap S.key L.t.
  Parameter refine : S.prog -> nat -> kmap S.key L.t -> kmap S.key L.t.
End NARROW_OPS.

Module Type NARROW_LAWS (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S)
    (Import R : NARROW_OPS L S C).
  (** A pass accepts the candidate precisely when its check succeeds. *)
  Parameter narrow_pass_spec : forall p m,
    narrow_pass p m = if C.check p (narrow_candidate p m)
      then narrow_candidate p m else m.
  (** Refinement performs the requested number of checked passes. *)
  Parameter refine_spec : forall p n m,
    refine p n m = Nat.iter n (narrow_pass p) m.
  (** Checked narrowing keeps a post-solution. *)
  Parameter narrow_pass_post : forall p m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (narrow_pass p m)).
  (** A pass lowers every lookup value. *)
  Parameter narrow_pass_below : forall p m x,
    L.leb (C.look (narrow_pass p m) x) (C.look m x) = true.
  (** Monotone systems accept the narrowing candidate of a post-solution. *)
  Parameter narrow_pass_exact_mono : forall p, S.monotone p -> forall m,
    S.post_solution p (C.look m) -> C.check p (narrow_candidate p m) = true.
  (** Repeated checked passes keep a post-solution. *)
  Parameter refine_post : forall p n m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (refine p n m)).
  (** Repeated passes lower every lookup value. *)
  Parameter refine_below : forall p n m x,
    L.leb (C.look (refine p n m) x) (C.look m x) = true.
End NARROW_LAWS.

Module Type NARROW (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S) :=
  NARROW_OPS L S C <+ NARROW_LAWS L S C.

Module Type NARROW_TIME (L : WLATTICE_T) (S : SYSTEM_T L) (C : CHECK_T L S)
    (Import R : NARROW L S C).
  Parameter T_narrow_candidate : S.prog -> kmap S.key L.t -> N.
  Parameter T_narrow_pass : S.prog -> kmap S.key L.t -> N.
  Parameter T_refine : S.prog -> nat -> kmap S.key L.t -> N.
  (* spec: T_eval_all *)
  Parameter T_eval_all : S.prog -> kmap S.key L.t -> N.
  (** Repeated narrowing pays one evaluation and check per pass. *)
  Parameter T_narrow_passes_le : forall p k m,
    (T_refine p k m <= N.of_nat k * (T_eval_all p m + C.T_check p m + 1))%N.
End NARROW_TIME.

Module Type NARROW_T (L : WLATTICE_T) (S : SYSTEM_T L) (C : CHECK_T L S) :=
  NARROW L S C <+ NARROW_TIME L S C.
