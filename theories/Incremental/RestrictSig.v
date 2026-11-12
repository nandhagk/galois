(** * Seeded restrictions of local systems

    Restrictions select rows and seed the values supplied by the frozen domain.
    For example, a selected row can read a previously solved predecessor through a seed.
    Builds on: LatticeSig and SystemSig. *)

From Stdlib Require Import List PArith.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.

Module Type RESTRICT_OPS (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key).
  Parameter mk : S.prog -> list (S.key * L.t) -> list S.row -> RS.prog.
End RESTRICT_OPS.

Module Type RESTRICT_SPEC (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key)
    (Import X : RESTRICT_OPS L S RS).
End RESTRICT_SPEC.

Module Type RESTRICT_LAWS (L : LATTICE) (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (Import X : RESTRICT_OPS L S RS).
  (** Restricted post-solutions cover every selected primary and side write and every seed. *)
  Parameter restrict_post : forall p fz rs s, RS.post_solution (mk p fz rs) s ->
    (forall r, In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true) /\
    (forall x v, In (x, v) fz -> L.leb v (s x) = true).
  (** Original post-solutions above the seeds satisfy the restriction. *)
  Parameter restrict_complete : forall p fz rs s, S.post_solution p s ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (forall x v, In (x, v) fz -> L.leb v (s x) = true) ->
    RS.post_solution (mk p fz rs) s.
  (** Selecting declared rows and adding seeds gives a well-formed restricted program. *)
  Parameter mk_wf : forall p fz rs, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) -> RS.wf (mk p fz rs).
End RESTRICT_LAWS.

Module Type RESTRICT (L : LATTICE) (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key) :=
  RESTRICT_OPS L S RS <+ RESTRICT_SPEC L S RS <+ RESTRICT_LAWS L S RS.

Module Type RESTRICT_TIME (L : LATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (Import X : RESTRICT L S RS).
  Parameter T_mk : S.prog -> list (S.key * L.t) -> list S.row -> nat.
  Parameter c_res : nat.
  (** Restriction construction pays for selected row codes and frozen bindings. *)
  Parameter T_mk_le : forall p fz rs,
    T_mk p fz rs <= c_res *
      (fold_right Nat.add 0
        (map (fun r => Pos.size_nat (S.row_code r) + 1) rs) +
       fold_right Nat.add 0
        (map (fun xv => S.key_bits (fst xv) + L.size (snd xv) + 1) fz) + 1).
End RESTRICT_TIME.

Module Type RESTRICT_T (L : LATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key) :=
  RESTRICT L S RS <+ RESTRICT_TIME L S RS.

Module Type RESTRICT_PLAN (L : LATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (Import X : RESTRICT_T L S RS).
  (** Restricted post-solutions accept every declared write of every selected row. *)
  Parameter restrict_writes : forall p fz rs s r, RS.post_solution (mk p fz rs) s ->
    In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true.
End RESTRICT_PLAN.

Module Type RESTRICT_ALL (L : LATTICE_T) (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key) :=
  RESTRICT_T L S RS <+ RESTRICT_PLAN L S RS.
