(** * Constructed two-phase certified tabulation

    The jump certificate supplies the same captured map to value preparation and certification.
    For example, value execution starts only after the actual jump phase returns Certified.
    Builds on: FrameworkTabJumpClosure, FrameworkTabValueClosure and both complete cost bounds. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabulate FrameworkTabValues FrameworkTabEncodingCost FrameworkTabPrepareCost
  FrameworkTabRunCost FrameworkTabCheckCost FrameworkTabValueRunCost FrameworkTabValueCheckCost
  FrameworkTabJumpProgress FrameworkTabJumpClosure FrameworkTabValueProgress
  FrameworkTabValueClosure.
Import Cost.Notations.

Module TabComplete.

(** Two-phase outcomes retain actual jump failures and the dependent value-phase outcome. *)
Inductive outcome {N E P D A F} (I : Ide.t N E P D A F) start a0 :=
  | JumpExhausted (state : Tab.state N E P D F)
  | JumpRejected (state : Tab.state N E P D F)
  | Values (jumps : {js : Map.t positive F | jump_post I (fst start) (Jump.lookup I js)})
      (values : TabValues.outcome I (proj1_sig jumps) start a0).
Arguments JumpExhausted {N E P D A F I start a0}.
Arguments JumpRejected {N E P D A F I start a0}.
Arguments Values {N E P D A F I start a0}.

(** Composition runs each existing constructed phase once and retains its actual outcome. *)
Definition complete_c {N E P D A F} (I : Ide.t N E P D A F) start a0
    (HF : height (Micro.lat (Ide.micro I))) (HA : height (Ide.values I)) :=
  let* result := TabJumpProgress.complete_c I (fst start) HF in
  match result with
  | Tab.Exhausted state => Cost.ret (JumpExhausted state)
  | Tab.Rejected state => Cost.ret (JumpRejected state)
  | Tab.Certified jumps =>
    Cost.map (Values jumps) (TabValueProgress.complete_c I (proj1_sig jumps) start a0 HA)
  end.

Definition complete {N E P D A F} (I : Ide.t N E P D A F) start a0
    (HF : height (Micro.lat (Ide.micro I))) (HA : height (Ide.values I)) :=
  Cost.value (complete_c I start a0 HF HA).

(** The plain result observes the same actual jump outcome and dependent value run. *)
Theorem complete_equation {N E P D A F} (I : Ide.t N E P D A F) start a0
    (HF : height (Micro.lat (Ide.micro I))) (HA : height (Ide.values I)) :
  complete I start a0 HF HA =
    match TabJumpProgress.complete I (fst start) HF with
    | Tab.Exhausted state => JumpExhausted state
    | Tab.Rejected state => JumpRejected state
    | Tab.Certified jumps =>
      Values jumps (TabValueProgress.complete I (proj1_sig jumps) start a0 HA)
    end.
Proof.
  unfold complete, complete_c; rewrite Cost.value_bind.
  change (Cost.value (TabJumpProgress.complete_c I (fst start) HF))
    with (TabJumpProgress.complete I (fst start) HF).
  destruct (TabJumpProgress.complete I (fst start) HF);
    rewrite ?Cost.value_ret, ?Cost.value_map; reflexivity.
Qed.

(** The overall polynomial factor is fixed independently of all client carriers and inputs. *)
Definition tab_k : N := 1.

(** The named overall factor covers the sum of the individually derived phase bounds. *)
Theorem tab_k_positive : (1 <= tab_k)%N.
Proof.
  reflexivity.
Qed.

(** The combined polynomial retains each phase's own height and primitive callback price. *)
Definition charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w mf ma hf ha :=
  (tab_k * (TabRunCost.complete_charge I ko ks kt kk kf kw q e w mf hf +
    TabCheckCost.checker_charge I ko ks kt kk kf kw q e w mf +
    TabValueRunCost.complete_charge I ko ks kt kk kf kw q e w ma ha +
    TabValueCheckCost.checker_charge I ko ks kt kk kf kw q e w ma))%N.

(** Both actual certified phases compose without an owned price or successful-outcome premise. *)
Theorem tabulate_cost {N E P D A F} (I : Ide.t N E P D A F) start a0 e w mf ma
    ko ks kt kk kf kw q (HF : height (Micro.lat (Ide.micro I))) (HA : height (Ide.values I)) :
  TabRunCost.primitives I (fst start) e w mf ->
  TabValueRunCost.primitives I start e w ma ->
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (forall edge, List.In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) edge) e w) ->
  (forall d, List.In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w) ->
  (Cost.ticks (complete_c I start a0 HF HA) <=
    charge I ko ks kt kk kf kw q e w mf ma (N.of_nat (bound HF)) (N.of_nat (bound HA)))%N.
Proof.
  intros HPF HPA HV HK HC Hnodes Hfacts.
  pose proof (TabCheckCost.complete_cost I (fst start) e w mf
    ko ks kt kk kf kw q HF HPF HV HK HC Hnodes Hfacts) as Hjump.
  unfold complete_c; rewrite Cost.ticks_bind.
  change (Cost.value (TabJumpProgress.complete_c I (fst start) HF))
    with (TabJumpProgress.complete I (fst start) HF).
  pose proof tab_k_positive as Hfactor.
  destruct (TabJumpProgress.complete I (fst start) HF) as [exhausted|rejected|jumps].
  - rewrite Cost.ticks_ret; unfold charge; nia.
  - rewrite Cost.ticks_ret; unfold charge; nia.
  - rewrite Cost.ticks_map.
    pose proof (TabValueCheckCost.complete_cost I (proj1_sig jumps) start a0 e w ma
      ko ks kt kk kf kw q HA HPA HV (TabRunCost.edge HPF) HC) as Hvalue.
    unfold charge; nia.
Qed.

(** Separate lawful heights reach actual certificates in both phases of the same combined run. *)
Theorem complete_certified {N E P D A F} (I : Ide.t N E P D A F) start a0
    (HF : height (Micro.lat (Ide.micro I))) (HA : height (Ide.values I)) :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Micro.lat (Ide.micro I)) -> lattice_laws (Ide.values I) ->
  exists jumps values, complete I start a0 HF HA = Values jumps (TabValues.Certified values).
Proof.
  intros HN HE HD HFL HAL.
  assert (HV : encoding_laws (IdeValue.key_enc I)).
  { apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD]. }
  assert (HK : encoding_laws (Jump.enc I)) by (apply jkey_enc_laws; assumption).
  assert (HAE : encoding_laws (Tab.arc_enc I)) by (apply Tab.arc_enc_laws; assumption).
  assert (HI : encoding_laws (Tab.incoming_enc I)) by (apply Tab.incoming_enc_laws; assumption).
  destruct (TabJumpClosure.complete_certified I (fst start) HF HV HK HAE HI HFL)
    as [jumps Hjump].
  destruct (TabValueClosure.complete_certified I (proj1_sig jumps) start a0 HA HN HE HD HAL)
    as [values Hvalue].
  exists jumps, values; rewrite complete_equation, Hjump, Hvalue; reflexivity.
Qed.

(** The actual two-phase family has a single primitive-derived big-O bound without carrier sizes. *)
Theorem tabulate_bigO {X N E P D A F} (I : X -> Ide.t N E P D A F)
    (start : X -> N * option D) (a0 : X -> A)
    (e w mf ma ko ks kt kk kf kw q : X -> BinNums.N)
    (HF : forall x, height (Micro.lat (Ide.micro (I x))))
    (HA : forall x, height (Ide.values (I x))) :
  (forall x, TabRunCost.primitives (I x) (fst (start x)) (e x) (w x) (mf x)) ->
  (forall x, TabValueRunCost.primitives (I x) (start x) (e x) (w x) (ma x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x, encoding_laws (Jump.enc (I x))) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  (forall x edge, List.In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds (I x)))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) edge) (e x) (w x)) ->
  (forall x d, List.In d (Ifds.facts (Ide.ifds (I x))) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds (I x))) d (e x) (w x)) ->
  bigO
    (fun x => charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
      (e x) (w x) (mf x) (ma x) (N.of_nat (bound (HF x))) (N.of_nat (bound (HA x))))
    (fun x => Cost.ticks (complete_c (I x) (start x) (a0 x) (HF x) (HA x))).
Proof.
  intros HPF HPA HV HK HC Hnodes Hfacts; exists 1%N; intro x.
  pose proof (tabulate_cost (I x) (start x) (a0 x) (e x) (w x) (mf x) (ma x)
    (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x) (HF x) (HA x)
    (HPF x) (HPA x) (HV x) (HK x) (HC x) (Hnodes x) (Hfacts x)); lia.
Qed.

End TabComplete.
