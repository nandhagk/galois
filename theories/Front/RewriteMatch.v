(** * Matching the left side of a rewrite

    A represented instance of a pattern matches the query atoms of the pattern in a canonical
    database. Each constructor of the instance has a row whose key holds the cells of its
    arguments, and two cells that represent one term in a canonical database are equal, so a
    variable that occurs twice gets one cell.
    For example, the instance [Add (Num 1) (Num 2)] of [PNode add [PVar 1; PVar 2]] matches with
    variables 1 and 2 bound to the classes of [Num 1] and [Num 2].

    Builds on: the rewrite signature and the database contracts. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig RewriteSig.

Import List.ListNotations.

Module RewriteMatch (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) <: REWRITE_MATCH_PLAN V I J D R X.
  Lemma query_pat_complete : forall db next (p : pat V.t) e t i,
    (pat_top p < next)%positive -> D.wf db -> D.canonical db ->
    pat_term V.prim e p = Some t -> represents (D.view db) (Id i) t ->
    exists env, matches V.prim (D.view db) (fst (fst (query_pat next p))) env /\
      term_value env (snd (fst (query_pat next p))) (Id (D.repr db i)) /\
      (forall x u, In x (pat_vars p) -> e x = Some u ->
        exists c, env x = Some c /\ represents (D.view db) c u).
  Proof.
  Admitted. (* STUB *)
End RewriteMatch.
