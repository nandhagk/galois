(** * Source-rule preparation and indexed firing

    This entry point collects positive atoms, prepares their indexes and fires through Join.
    For example, a nonrecursive stratum seed uses the completed lower relations in this pipeline.
    Builds on: DatalogJoinPrepareCost, DatalogJoinFireCost and DatalogJoinProof. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Datalog Require Import DatalogSyntax DatalogRelation DatalogFire
  DatalogJoin DatalogJoinProof DatalogJoinPrepareCost DatalogJoinFireCost.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module PreparedFire.

(** Source classification and both indexed phases belong to the same charged computation. *)
Definition fire_c {P} (prog : program P) (r : rule P) (env : P -> Cost.t relation) :=
  let* ps := positive_atoms_c (body r) in
  let* plan := Join.prepare_c prog ps env in
  Join.fire_c r env plan.

Definition fire {P} prog r env := Cost.value (@fire_c P prog r env).

(** Preparing and firing a source rule retains the reference firing membership. *)
Theorem fire_agrees {P} (prog : program P) r env ts :
  member ts (fire prog r env) = member ts (fire_rule prog r env).
Proof.
  unfold fire, fire_c; repeat rewrite Cost.value_bind.
  change (member ts
    (Join.fire r env (Join.prepare prog (positive_atoms (body r)) env)) =
    member ts (fire_rule prog r env)).
  apply JoinProof.join_fire_agrees, JoinProof.prepare_ready.
Qed.

(** Safe source firing returns precisely the heads of valuations satisfying all body literals. *)
Theorem fire_exact {P} (prog : program P) r env :
  safe_rule r -> forall ts,
  member ts (fire prog r env) = true <->
  exists sigma, ts = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
      member (map (inst sigma) (args a)) (Cost.value (env (pred a))) = true) /\
    (forall a, In (LNeg a) (body r) ->
      member (map (inst sigma) (args a)) (Cost.value (env (pred a))) = false).
Proof.
  intros Hsafe ts; rewrite fire_agrees; apply fire_rule_exact, Hsafe.
Qed.

Lemma positive_atoms_cost {P} (ls : list (literal P)) :
  Cost.ticks (positive_atoms_c ls) = N.of_nat (length ls).
Proof.
  apply DatalogFire.positive_atoms_cost.
Qed.

(** The source pipeline retains its body scan, all prepared atom occurrences and actual join work. *)
Definition pipeline_work {P} (prog : program P) (r : rule P) env
    a b h rows v c s e w :=
  N.of_nat (length (body r)) +
    N.of_nat (length (positive_atoms (body r))) *
      JoinPrepareCost.prepare_unit_cost a b rows c s e w +
    (Join.work (Join.prepare prog (positive_atoms (body r)) env) + 1) *
      JoinFireCost.fire_unit_cost (length (body r)) a h v c e w.

(** Complete source firing has a numeric bound with primitive duties for preparation and probing. *)
Theorem fire_cost {P} (prog : program P) r env a b h rows v c s e w :
  JoinPrepareCost.prepare_primitives [] (positive_atoms (body r)) env a b rows c s e w ->
  JoinFireCost.fire_primitives r env (Join.prepare prog (positive_atoms (body r)) env)
    a h v c e w ->
  Cost.ticks (fire_c prog r env) <= pipeline_work prog r env a b h rows v c s e w.
Proof.
  intros Hprepare Hfire.
  pose proof (JoinPrepareCost.join_prepare_cost prog _ env a b rows c s e w Hprepare)
    as Hpreparation.
  pose proof (JoinFireCost.join_fire_cost r env _ a h v c e w Hfire) as Hfiring.
  unfold fire_c; repeat rewrite Cost.ticks_bind.
  change (Cost.ticks (positive_atoms_c (body r)) +
    (Cost.ticks (Join.prepare_c prog (positive_atoms (body r)) env) +
    Cost.ticks (Join.fire_c r env (Join.prepare prog (positive_atoms (body r)) env))) <=
    pipeline_work prog r env a b h rows v c s e w).
  rewrite positive_atoms_cost; unfold pipeline_work; lia.
Qed.

(** Source inventories, plans and primitive budgets can vary throughout the pipeline family. *)
Theorem fire_bigO {X P} (prog : X -> program P) (r : X -> rule P)
    (env : X -> P -> Cost.t relation) (a b h : X -> nat) (rows v c s e w : X -> N) :
  (forall x, JoinPrepareCost.prepare_primitives [] (positive_atoms (body (r x))) (env x)
    (a x) (b x) (rows x) (c x) (s x) (e x) (w x)) ->
  (forall x, JoinFireCost.fire_primitives (r x) (env x)
    (Join.prepare (prog x) (positive_atoms (body (r x))) (env x))
      (a x) (h x) (v x) (c x) (e x) (w x)) ->
  bigO (fun x => pipeline_work (prog x) (r x) (env x)
    (a x) (b x) (h x) (rows x) (v x) (c x) (s x) (e x) (w x))
    (fun x => Cost.ticks (fire_c (prog x) (r x) (env x))).
Proof.
  intros Hprepare Hfire; exists 1; intro x.
  pose proof (fire_cost (prog x) (r x) (env x) (a x) (b x) (h x)
    (rows x) (v x) (c x) (s x) (e x) (w x) (Hprepare x) (Hfire x)); nia.
Qed.

Arguments fire_c {P} prog r env : simpl never.

End PreparedFire.
Import PreparedFire.
