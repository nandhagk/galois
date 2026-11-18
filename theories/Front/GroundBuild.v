(** * Saturated ground runs build their instances

    At saturation, the rule of a union clause has built both sides of each instance whose body
    holds in the input rows, in one class. The outcome keeps the input rows, so the query of
    the rule matches the instance, and the closed rule has its actions present. They build
    cells that represent both sides and join them.
    For example, a saturated run of Steensgaard's program builds [Deref (Cell x)] and [Cell a]
    in one class for each address constraint [Addr x a].

    Builds on: the ground signature, the runner facts, the lowering laws and the run
    contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec SpecFacts LowerSig RunnerSig CongruenceRefSig GroundSig.

Import List.ListNotations.

Module GroundBuild (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (R : RUN V I J D) (X : RUNNER V I J D R) (F : RUNNER_FACTS V I J D R X) (LW : LOWER_LAWS)
    <: GROUND_BUILD_PLAN V I J D R X.
  (* STUB: the outcome keeps the input rows by [F.solve_keeps], so the query of the rule of the
     clause matches by [LW.query_body_matches] and [LW.checks_last_matches]. Saturation closes
     the rule, so its actions are present, and [LW.query_body_lets] and
     [LW.build_pats_represents] give cells that represent both sides in one class. *)
  Lemma instance_built : forall (s : spec V.t) rows lim db c e l r tl tr,
    spec_ok s = true -> ground s = true -> rows_ok s rows = true ->
    X.solve (spec_program s) rows lim = (Saturated, db) ->
    In c (clauses s) -> head c = Unify l r ->
    Forall (input_premise V.prim (rows_in rows) e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    exists i j, represents (D.view db) (Id i) tl /\ represents (D.view db) (Id j) tr /\
      same (D.view db) i j.
  Proof.
  Admitted. (* STUB *)
End GroundBuild.
