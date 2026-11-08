(** * Local discovery and checked partial soundness

    Completed discovery is the least contributor-closed region containing the requested roots.
    For example, nominal targets of side contributors belong to that same closure.
    Builds on: FixpointLocal, FixpointLocalDiscover and the public partial checker. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointIndex FixpointPartial FixpointAnalysis FixpointSolver FixpointTotal
  FixpointLocalDiscover FixpointLocal.
Import List.ListNotations.

Module LocalProof.

(** Left projection retains precisely the unknown-tagged vertices. *)
Theorem lefts_member {X C} (vs : list (X + C)) x :
  In x (Cost.value (Local.lefts_c vs)) <-> In (inl x) vs.
Proof.
  induction vs as [|[y|c] vs IH]; cbn [Local.lefts_c]; autorewrite with galois_cost.
  - reflexivity.
  - cbn [In]; rewrite IH; intuition congruence.
  - cbn [In]; rewrite IH; intuition discriminate.
Qed.

(** Right projection retains precisely the row-tagged vertices. *)
Theorem rights_member {X C} (vs : list (X + C)) c :
  In c (Cost.value (Local.rights_c vs)) <-> In (inr c) vs.
Proof.
  induction vs as [|[x|d] vs IH]; cbn [Local.rights_c]; autorewrite with galois_cost.
  - reflexivity.
  - cbn [In]; rewrite IH; intuition discriminate.
  - cbn [In]; rewrite IH; intuition congruence.
Qed.

Local Lemma of_list_member {X} EX (HE : encoding_laws EX) x (xs : list X) :
  FinSet.mem EX x (FinSet.of_list EX xs) = true <-> In x xs.
Proof.
  rewrite FinSet.mem_of_list, existsb_exists; split.
  - intros [y [Hy Heq]]; apply (eqb_true_iff EX HE) in Heq; now subst y.
  - intro Hx; exists x; split; [exact Hx|apply eqb_refl].
Qed.

(** Projecting a well-formed tagged region retains precisely its unknown and row members. *)
Theorem project_members {X C} EX EC (HE : encoding_laws EX) (HC : encoding_laws EC)
    (vertices : FinSet.t (X + C)) :
  FinSet.wf (sum_encoding EX EC) vertices ->
  (forall x, FinSet.mem EX x (Local.unknowns (Local.project EX EC vertices)) = true <->
    FinSet.mem (sum_encoding EX EC) (inl x) vertices = true) /\
  (forall c, FinSet.mem EC c (Local.selected (Local.project EX EC vertices)) = true <->
    FinSet.mem (sum_encoding EX EC) (inr c) vertices = true).
Proof.
  intro Hwf; rewrite Local.project_equation.
  cbn [Local.unknowns Local.selected]; split; intro v.
  - rewrite of_list_member by exact HE.
    rewrite lefts_member, (FinSet.elements_spec _ (sum_encoding_laws EX EC HE HC) _ _ Hwf).
    reflexivity.
  - rewrite of_list_member by exact HC.
    rewrite rights_member, (FinSet.elements_spec _ (sum_encoding_laws EX EC HE HC) _ _ Hwf).
    reflexivity.
Qed.

(** Both projected sets are canonical even when the original candidate's representation is raw. *)
Theorem project_wf {X C} EX EC (vertices : FinSet.t (X + C)) :
  FinSet.wf EX (Local.unknowns (Local.project EX EC vertices)) /\
  FinSet.wf EC (Local.selected (Local.project EX EC vertices)).
Proof.
  rewrite Local.project_equation.
  split; apply FinSet.wf_of_list.
Qed.

(** A declared local region covers roots, their contributors and every selected row's metadata. *)
Definition closed {X C A} (a : Analysis.t X C A) ix roots (r : Local.region X C) : Prop :=
  (forall x, In x roots -> FinSet.mem (Analysis.key_enc a) x (Local.unknowns r) = true) /\
  (forall x c, FinSet.mem (Analysis.key_enc a) x (Local.unknowns r) = true ->
    In c (contributors_of (Analysis.key_enc a) ix x) ->
    FinSet.mem (Analysis.row_enc a) c (Local.selected r) = true) /\
  forall c, FinSet.mem (Analysis.row_enc a) c (Local.selected r) = true ->
    forall x, In x (System.target (Analysis.system a) c ::
      side_targets (Analysis.static a) c ++ deps (Analysis.static a) c) ->
    FinSet.mem (Analysis.key_enc a) x (Local.unknowns r) = true.

Local Lemma indexed_result {X C A} (a : Analysis.t X C A) ix roots fuel r :
  Cost.value (Local.discover_indexed_c a ix roots fuel) = inr r ->
  exists vertices, LocalDiscover.run a ix roots fuel = inr vertices /\
    r = Local.project (Analysis.key_enc a) (Analysis.row_enc a) vertices.
Proof.
  unfold Local.discover_indexed_c; rewrite Cost.value_bind.
  fold (LocalDiscover.run a ix roots fuel).
  destruct (LocalDiscover.run a ix roots fuel) as [state|vertices];
    autorewrite with galois_cost; [discriminate|].
  intro Heq; injection Heq as <-; exists vertices; split; reflexivity.
Qed.

(** Completed indexed discovery has full declared closure and root coverage. *)
Theorem local_discover_closed {X C A} (a : Analysis.t X C A) ix roots fuel r :
  Analysis.laws a ->
  Cost.value (Local.discover_indexed_c a ix roots fuel) = inr r ->
  FinSet.wf (Analysis.key_enc a) (Local.unknowns r) /\
  FinSet.wf (Analysis.row_enc a) (Local.selected r) /\ closed a ix roots r.
Proof.
  intros HL Hdiscovered.
  destruct (indexed_result a ix roots fuel r Hdiscovered) as [vertices [Hrun ->]].
  unfold LocalDiscover.run, LocalDiscover.run_c in Hrun.
  rewrite Cost.value_bind, value_map_c in Hrun.
  destruct (LocalDiscover.completed_closed _ (sum_encoding_laws _ _
    (Analysis.key_laws HL) (Analysis.row_laws HL)) _ _ _ vertices Hrun)
    as [Hwf [Hroots Hedges]].
  destruct (project_members _ _ (Analysis.key_laws HL) (Analysis.row_laws HL)
    vertices Hwf) as [Hx Hc].
  destruct (project_wf (Analysis.key_enc a) (Analysis.row_enc a) vertices) as [Hwx Hwc].
  split; [exact Hwx|]; split; [exact Hwc|]; split.
  - intros x Hin; apply Hx, Hroots, in_map, Hin.
  - split.
    + intros x c Hin Hcontrib; apply Hc.
      apply (Hedges (inl x)); [apply Hx, Hin|].
      fold (LocalDiscover.adjacent a ix (inl x)).
      rewrite LocalDiscover.adjacent_equation; apply in_map, Hcontrib.
    + intros c Hin x Hout; apply Hx.
      apply (Hedges (inr c)); [apply Hc, Hin|].
      fold (LocalDiscover.adjacent a ix (inr c)).
      rewrite LocalDiscover.adjacent_equation; apply in_map, Hout.
Qed.

(** Public completed discovery returns a well-formed closed region covering roots. *)
Theorem public_discover_closed {X C A} (a : Analysis.t X C A) roots fuel r :
  Analysis.laws a -> Local.discover a roots fuel = inr r ->
  FinSet.wf (Analysis.key_enc a) (Local.unknowns r) /\
  FinSet.wf (Analysis.row_enc a) (Local.selected r) /\
  closed a (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots r.
Proof.
  intros HL Hrun; unfold Local.discover, Local.discover_c in Hrun.
  rewrite Cost.value_bind in Hrun.
  exact (local_discover_closed a _ roots fuel r HL Hrun).
Qed.

(** Every root-containing declared contributor closure contains the actual discovered region. *)
Theorem local_discover_least {X C A} (a : Analysis.t X C A) ix roots fuel r E :
  Analysis.laws a ->
  (forall x, In x roots -> FinSet.mem (Analysis.key_enc a) x E = true) ->
  (forall x c, FinSet.mem (Analysis.key_enc a) x E = true ->
    In c (contributors_of (Analysis.key_enc a) ix x) ->
    forall y, In y (System.target (Analysis.system a) c ::
      side_targets (Analysis.static a) c ++ deps (Analysis.static a) c) ->
      FinSet.mem (Analysis.key_enc a) y E = true) ->
  Cost.value (Local.discover_indexed_c a ix roots fuel) = inr r ->
  forall x, FinSet.mem (Analysis.key_enc a) x (Local.unknowns r) = true ->
    FinSet.mem (Analysis.key_enc a) x E = true.
Proof.
  intros HL Hroots Hclosed Hdiscovered x Hx.
  destruct (indexed_result a ix roots fuel r Hdiscovered) as [vertices [Hrun Hr]].
  subst r.
  unfold LocalDiscover.run, LocalDiscover.run_c in Hrun.
  rewrite Cost.value_bind, value_map_c in Hrun.
  set (P := fun v : X + C =>
    match v with
    | inl x => FinSet.mem (Analysis.key_enc a) x E = true
    | inr c => forall y, In y (System.target (Analysis.system a) c ::
        side_targets (Analysis.static a) c ++ deps (Analysis.static a) c) ->
        FinSet.mem (Analysis.key_enc a) y E = true
    end).
  assert (HP : LocalDiscover.closed
    (fun v => Cost.value (LocalDiscover.adjacent_c a ix v)) (map (@inl X C) roots) P).
  { split.
    - intros v Hv; apply in_map_iff in Hv as [y [<- Hy]]; apply Hroots, Hy.
    - intros [y|c] v Hv Hedge.
      + fold (LocalDiscover.adjacent a ix (inl y)) in Hedge.
        rewrite LocalDiscover.adjacent_equation in Hedge.
        apply in_map_iff in Hedge as [c [<- Hc]]; exact (Hclosed y c Hv Hc).
      + fold (LocalDiscover.adjacent a ix (inr c)) in Hedge.
        rewrite LocalDiscover.adjacent_equation in Hedge.
        apply in_map_iff in Hedge as [y [<- Hy]]; exact (Hv y Hy). }
  destruct (LocalDiscover.completed_closed _ (sum_encoding_laws _ _
    (Analysis.key_laws HL) (Analysis.row_laws HL)) _ _ _ vertices Hrun) as [Hwf _].
  destruct (project_members _ _ (Analysis.key_laws HL) (Analysis.row_laws HL)
    vertices Hwf) as [Hmembers _].
  exact (LocalDiscover.completed_least _ (sum_encoding_laws _ _
    (Analysis.key_laws HL) (Analysis.row_laws HL)) _ _ _ vertices P HP Hrun (inl x)
    (proj1 (Hmembers x) Hx)).
Qed.

(** The checked entry validates both closed-partial semantics and coverage of every root. *)
Theorem local_checked_sound {X C A} (a : Analysis.t X C A) HT roots fuel r :
  Analysis.laws a -> Local.checked a HT roots fuel = Outcome.Solved r ->
  FinSet.wf (Analysis.key_enc a) (Local.explored r) /\
  closed_partial (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (Analysis.static a) (Local.explored r)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values r)) /\
  forall x, In x roots -> FinSet.mem (Analysis.key_enc a) x (Local.explored r) = true.
Proof.
  intros HL Hchecked; unfold Local.checked, Local.checked_c in Hchecked.
  rewrite !Cost.value_bind in Hchecked.
  fold (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))
    in Hchecked.
  destruct (Cost.value (Local.run_indexed_c a HT
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel))
    as [candidate|have|why] eqn:Hrun; autorewrite with galois_cost in Hchecked;
    try discriminate.
  apply (Local.check_sound a _ roots candidate r HL
    (index_system_laws _ (Analysis.key_laws HL) _ _)), Hchecked.
Qed.

End LocalProof.
Import LocalProof.
