(** * Restrict layer headers

    These headers pass the original and restricted systems as separate dependencies.
    Operations and contracts are placeholders for task 5.3.

    For example, a restriction can change the program carrier while keeping the key carrier.
    Builds on: LatticeSig and SystemSig. *)

From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.

Module Type RESTRICT_OPS (L : LATTICE_OPS)
    (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key).
  Parameter t : Type.
End RESTRICT_OPS.

Module Type RESTRICT_SPEC (L : LATTICE_OPS)
    (S : LOCAL_SYSTEM_OPS L)
    (RS : LOCAL_SYSTEM_OPS L with Definition key := S.key)
    (Import X : RESTRICT_OPS L S RS).
End RESTRICT_SPEC.

Module Type RESTRICT_LAWS (L : LATTICE)
    (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key)
    (Import X : RESTRICT_OPS L S RS).
End RESTRICT_LAWS.

Module Type RESTRICT (L : LATTICE)
    (S : LOCAL_SYSTEM L)
    (RS : LOCAL_SYSTEM L with Definition key := S.key) :=
  RESTRICT_OPS L S RS <+ RESTRICT_SPEC L S RS <+ RESTRICT_LAWS L S RS.

Module Type RESTRICT_TIME (L : LATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (Import X : RESTRICT L S RS).
End RESTRICT_TIME.

Module Type RESTRICT_T (L : LATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key) :=
  RESTRICT L S RS <+ RESTRICT_TIME L S RS.

Module Type RESTRICT_PLAN (L : LATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key)
    (Import X : RESTRICT_T L S RS).
End RESTRICT_PLAN.

Module Type RESTRICT_ALL (L : LATTICE_T)
    (S : LOCAL_SYSTEM_T L)
    (RS : LOCAL_SYSTEM_T L with Definition key := S.key) :=
  RESTRICT_T L S RS <+ RESTRICT_PLAN L S RS.
