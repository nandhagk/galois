(** * Incremental layer headers

    These headers pass the original and restricted systems as separate dependencies.
    Operations, contracts and solver and checker dependencies wait for task 5.3.

    For example, a restriction can change the program carrier while keeping the key carrier.
    Builds on: LatticeSig and SystemSig and RestrictSig. *)

From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Incremental Require Import RestrictSig.

Module Type INCREMENTAL_OPS (L : WLATTICE_OPS)
    (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key)
    (R : RESTRICT_OPS L S RS).
  Parameter t : Type.
End INCREMENTAL_OPS.

Module Type INCREMENTAL_SPEC (L : WLATTICE_OPS)
    (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key)
    (R : RESTRICT_OPS L S RS)
    (Import X : INCREMENTAL_OPS L S RS R).
End INCREMENTAL_SPEC.

Module Type INCREMENTAL_LAWS (L : WLATTICE)
    (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (R : RESTRICT L S RS)
    (Import X : INCREMENTAL_OPS L S RS R).
End INCREMENTAL_LAWS.

Module Type INCREMENTAL (L : WLATTICE)
    (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (R : RESTRICT L S RS) :=
  INCREMENTAL_OPS L S RS R <+ INCREMENTAL_SPEC L S RS R <+ INCREMENTAL_LAWS L S RS R.

Module Type INCREMENTAL_TIME (L : WLATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS)
    (Import X : INCREMENTAL L S RS R).
End INCREMENTAL_TIME.

Module Type INCREMENTAL_T (L : WLATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) :=
  INCREMENTAL L S RS R <+ INCREMENTAL_TIME L S RS R.

Module Type INCREMENTAL_PLAN (L : WLATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS)
    (Import X : INCREMENTAL_T L S RS R).
End INCREMENTAL_PLAN.

Module Type INCREMENTAL_ALL (L : WLATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (R : RESTRICT_T L S RS) :=
  INCREMENTAL_T L S RS R <+ INCREMENTAL_PLAN L S RS R.
