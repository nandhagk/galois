(** * Semantic gen/kill laws

    Local generation, framing and agreement laws give the four dense soundness shapes.
    For example, unwritten variables keep their values in a backward may analysis.
    Builds on: FrameworkBitvector, FrameworkDenseForward, FrameworkDenseAgreement
    and FrameworkDenseWitness. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSemantics ProgramSteps ProgramLink
  ProgramRuns ProgramSimulation.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector FrameworkDenseForward
  FrameworkDenseAgreement FrameworkDenseWitness.
Import List.ListNotations.

Module GenkillSound.

(** May membership observes the final representation-valid carrier. *)
Definition member {U} {enc : encoding U} (a : set_t enc) u :=
  FinSet.mem enc u (set_raw a) = true.

(** All contains every fact observationally and is still a distinct unreachable value. *)
Definition must_member {U} {enc : encoding U} (a : must_t enc) u :=
  match a with
  | All => True
  | Only a => member a u
  end.

(** List conversion reflects source membership under the fact encoding laws. *)
Theorem member_list {U} (enc : encoding U) (HU : encoding_laws enc) xs u :
  member (set_of_list enc xs) u <-> In u xs.
Proof.
  unfold member; rewrite set_of_list_raw, FinSet.mem_of_list, existsb_exists.
  split.
  - intros [v [Hv Heq]]; apply (eqb_true_iff enc HU) in Heq; subst v; exact Hv.
  - intro Hu; exists u; split; [exact Hu|apply eqb_refl].
Qed.

(** Prepared transfers implement source gen/kill membership on every listed edge. *)
Theorem transfer_member {N E U} (P : Bitvector.t N E U) e a u :
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> In e (Cfg.edges (Bitvector.cfg P)) ->
  (member (Bitvector.may_transfer (Bitvector.prepare P) e a) u <->
    (member a u /\ ~ In u (Bitvector.kill P e)) \/ In u (Bitvector.gen P e)).
Proof.
  intros HE HU He; unfold member; rewrite Bitvector.may_transfer_raw.
  rewrite FinSet.mem_union by
    (try apply FinSet.wf_diff;
     first [exact (proj2_sig a) |
       exact (proj2_sig (Bitvector.kill_set (Bitvector.prepare P) e)) |
       exact (proj2_sig (Bitvector.gen_set (Bitvector.prepare P) e))]).
  rewrite FinSet.mem_diff by
    first [exact (proj2_sig a) |
      exact (proj2_sig (Bitvector.kill_set (Bitvector.prepare P) e))].
  rewrite Bitvector.prepare_gen_mem, Bitvector.prepare_kill_mem by assumption.
  rewrite orb_true_iff, andb_true_iff, negb_true_iff.
  change ((member a u /\
    FinSet.mem (Bitvector.fact_enc P) u
      (set_raw (set_of_list (Bitvector.fact_enc P) (Bitvector.kill P e))) = false) \/
    member (set_of_list (Bitvector.fact_enc P) (Bitvector.gen P e)) u <->
    (member a u /\ ~ In u (Bitvector.kill P e)) \/ In u (Bitvector.gen P e)).
  rewrite member_list by exact HU.
  assert (Hkill :
    FinSet.mem (Bitvector.fact_enc P) u
      (set_raw (set_of_list (Bitvector.fact_enc P) (Bitvector.kill P e))) = false <->
      ~ In u (Bitvector.kill P e)).
  { rewrite <- (member_list _ HU); unfold member.
    destruct (FinSet.mem _ _ _); intuition discriminate. }
  rewrite Hkill; reflexivity.
Qed.

(** Finite must transfer retains the same membership equation and strict All case. *)
Theorem must_transfer_equation {N E U} (P : Bitvector.t N E U) e a :
  Bitvector.must_transfer (Bitvector.prepare P) e a =
    match a with
    | All => All
    | Only a => Only (Bitvector.may_transfer (Bitvector.prepare P) e a)
    end.
Proof.
  destruct a; reflexivity.
Qed.

(** May membership is monotone in the actual collection order. *)
Theorem member_monotone {U} (enc : encoding U) (HU : encoding_laws enc) :
  DenseWitness.holds_monotone (may enc) (@member U enc).
Proof.
  intros a b u Hab Hu; exact (proj1 (may_leb enc HU a b) Hab u Hu).
Qed.

(** Must membership is antitone, including the fresh unreachable All case. *)
Theorem must_member_antitone {U} (enc : encoding U) (HU : encoding_laws enc) :
  DenseWitness.holds_antitone (must enc) (@must_member U enc).
Proof.
  intros [|a] [|b] u Hab Hu; try exact I.
  - discriminate.
  - exact (proj1 (may_leb enc HU b a) Hab u Hu).
Qed.

(** The may engine's finite-height invariant is support in the declared universe. *)
Theorem may_height_on {N E U} (P : Bitvector.t N E U) :
  encoding_laws (Bitvector.fact_enc P) ->
  height_on (may (Bitvector.fact_enc P))
    (within_set (Bitvector.fact_enc P) (Bitvector.universe P)).
Proof.
  intro HU; apply may_height; exact HU.
Defined.

(** The must engine counts the extra strict step from All to finite supported facts. *)
Theorem must_height_on {N E U} (P : Bitvector.t N E U) :
  encoding_laws (Bitvector.fact_enc P) ->
  height_on (must (Bitvector.fact_enc P))
    (within_must (Bitvector.fact_enc P) (Bitvector.universe P)).
Proof.
  intro HU; apply must_height; exact HU.
Defined.

(** Supported source generation preserves the may engine's universe invariant. *)
Theorem transfer_within {N E U} (P : Bitvector.t N E U) e a :
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.supported P ->
  In e (Cfg.edges (Bitvector.cfg P)) ->
  within_set (Bitvector.fact_enc P) (Bitvector.universe P) a ->
  within_set (Bitvector.fact_enc P) (Bitvector.universe P)
    (Bitvector.may_transfer (Bitvector.prepare P) e a).
Proof.
  intros HE HU [Hedges Hseeds] He Ha u Hu.
  apply (transfer_member P e a u HE HU He) in Hu.
  destruct Hu as [[Hu _]|Hu]; [apply Ha; exact Hu|exact (proj1 (Hedges e He) u Hu)].
Qed.

(** Strict All and finite supported transfers preserve the must engine's invariant. *)
Theorem must_transfer_within {N E U} (P : Bitvector.t N E U) e a :
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.supported P ->
  In e (Cfg.edges (Bitvector.cfg P)) ->
  within_must (Bitvector.fact_enc P) (Bitvector.universe P) a ->
  within_must (Bitvector.fact_enc P) (Bitvector.universe P)
    (Bitvector.must_transfer (Bitvector.prepare P) e a).
Proof.
  intros HE HU Hsupport He Ha; rewrite must_transfer_equation.
  destruct a; [exact I|eapply transfer_within; eassumption].
Qed.

(** Present source boundaries cover every entry used by forward induction. *)
Definition entry_boundaries {N E U} (P : Bitvector.t N E U) :=
  forall n, In n (Graph.entries (Cfg.graph (Bitvector.cfg P))) ->
    exists xs, Bitvector.boundary P n = Some xs.

Lemma may_boundary_covers {N E U} (P : Bitvector.t N E U) :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  Bitvector.dir P = Forward -> entry_boundaries P ->
  DenseForward.boundary_covers (Bitvector.may_dense P (Bitvector.prepare P)).
Proof.
  intros HN Hdir Hcovers n Hn.
  destruct (Hcovers n Hn) as [xs Hb]; exists (set_of_list (Bitvector.fact_enc P) xs).
  change (Bitvector.boundary_set (Bitvector.prepare P) n =
    Some (set_of_list (Bitvector.fact_enc P) xs)).
  rewrite Bitvector.prepare_boundary_source by
    (try exact HN; unfold Bitvector.seeds; rewrite Hdir; exact Hn).
  rewrite Hb; reflexivity.
Qed.

Lemma must_boundary_covers {N E U} (P : Bitvector.t N E U) :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  Bitvector.dir P = Forward -> entry_boundaries P ->
  DenseForward.boundary_covers (Bitvector.must_dense P (Bitvector.prepare P)).
Proof.
  intros HN Hdir Hcovers n Hn.
  destruct (may_boundary_covers P HN Hdir Hcovers n Hn) as [a Ha].
  change (Bitvector.boundary_set (Bitvector.prepare P) n = Some a) in Ha.
  exists (Only a).
  change (option_map Only (Bitvector.boundary_set (Bitvector.prepare P) n) = Some (Only a)).
  rewrite Ha; reflexivity.
Qed.

(** Agreement laws retain the legacy frame, input determinacy, no-stay and ending clauses. *)
Record bv_agree_laws {S O N E U C} (m : semantics S O) (en : endings S)
    (P : Bitvector.t N E U) (lk : Link.t S O N E) (get : S -> U -> C) : Prop := {
  agree_no_stays : forall s l s', ~ Link.stays lk s l s';
  agree_frame : forall e u, on_steps m (fun s l s' =>
    Link.taken lk s l s' e -> ~ In u (Bitvector.kill P e) -> get s' u = get s u);
  agree_inputs : forall t e, on_steps m (fun s l s' =>
    reachable_state m t -> Link.point lk t = Link.point lk s ->
    Link.taken lk s l s' e ->
    (forall u, In u (Bitvector.gen P e) -> get s u = get t u) ->
    exists t', step m t l t' /\ Link.taken lk t l t' e /\
      forall u, In u (Bitvector.kill P e) -> get s' u = get t' u);
  agree_endings : forall s t, reachable_state m s -> reachable_state m t ->
    Link.point lk t = Link.point lk s ->
    (forall xs u, Bitvector.boundary P (Link.point lk s) = Some xs ->
      In u xs -> get s u = get t u) ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
      (stopped en s <-> stopped en t)
}.

(** Store agreement is indexed by the solution's actual may carrier. *)
Definition store_agreement {S U C} (enc : encoding U) (get : S -> U -> C) :
    agreement (set_t enc) S :=
  {| agree := fun a s t => forall u, member a u -> get s u = get t u |}.

Lemma store_agreement_laws {S U C} enc (HU : encoding_laws enc) (get : S -> U -> C) :
  agreement_laws (may enc) (store_agreement enc get).
Proof.
  constructor.
  - intros a s u _; reflexivity.
  - intros a b s t Hab Hagree u Hu; apply Hagree.
    exact (member_monotone enc HU a b u Hab Hu).
Qed.

Lemma agreement_step {S O N E U C} m en (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (get : S -> U -> C) sigma :
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) ->
  link_laws m (Cfg.graph (Bitvector.cfg P)) lk -> bv_agree_laws m en P lk get ->
  DenseAgreement.step_agrees m (Bitvector.may_dense P (Bitvector.prepare P)) lk
    (store_agreement (Bitvector.fact_enc P) get) (reachable_state m) sigma.
Proof.
  intros HE HU Hlink Hlaw; destruct Hlaw as [Hnostay Hframe Hinputs Hends]; split.
  - intros e t s l s' Hs Hstep _ Ht Hpoint Htaken Hagree.
    destruct (link_taken_edge m (Bitvector.cfg P) lk s l s' e
      Hlink Hs Hstep Htaken) as [He _].
    destruct (Hinputs t e s l s' Hs Hstep Ht Hpoint Htaken) as [t' [Htstep [Htaken' Hdefs]]].
    + intros u Hu; apply Hagree; apply transfer_member; [exact HE|exact HU|exact He|].
      right; exact Hu.
    + exists t'; split; [exact Htstep|]; split; [exact Htaken'|].
      intros u Hu; destruct (in_dec (eqb_dec _ HU) u
        (Bitvector.kill P e)) as [Hkill|Hkill].
      * exact (Hdefs u Hkill).
      * rewrite (Hframe e u s l s' Hs Hstep Htaken Hkill),
          (Hframe e u t l t' Ht Htstep Htaken' Hkill).
        apply Hagree; apply transfer_member; [exact HE|exact HU|exact He|].
        left; split; assumption.
  - intros t s l s' Hs Hstep _ _ _ Hstay _.
    exfalso; exact (Hnostay s l s' Hstay).
Qed.

(** Initially agreeing stores have the same behaviour for a backward may post-solution. *)
Theorem backward_may_sound {S O N E U C} m en (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (get : S -> U -> C) sigma s0 t0 :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.dir P = Backward ->
  link_laws m (Cfg.graph (Bitvector.cfg P)) lk -> bv_agree_laws m en P lk get ->
  post_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) sigma ->
  initial m s0 -> initial m t0 -> Link.point lk t0 = Link.point lk s0 ->
  (forall u, member (sigma (Link.point lk s0)) u -> get s0 u = get t0 u) ->
  same_behaviour m en s0 m en t0.
Proof.
  intros HN HE HU Hdir Hlink Hlaw Hpost Hs Ht Hpoint Hagree.
  eapply (DenseAgreement.agreement_same_behaviour m en
    (Bitvector.may_dense P (Bitvector.prepare P)) lk
    (fun _ => store_agreement (Bitvector.fact_enc P) get) (reachable_state m) sigma).
  - exact Hdir.
  - apply may_laws; exact HU.
  - exact Hlink.
  - apply store_agreement_laws; exact HU.
  - intros a s t Ha u Hu; symmetry; exact (Ha u Hu).
  - apply DenseAgreement.reachable_invariant.
  - eapply agreement_step; eassumption.
  - intros s t Hr Ht' Hpt Hexit; apply (agree_endings _ _ _ _ _ Hlaw s t Hr Ht' Hpt).
    intros xs u Hb Hu; apply Hexit.
    unfold DenseAgreement.exit_fact.
    change (member
      (match Bitvector.boundary_set (Bitvector.prepare P) (Link.point lk s) with
       | Some a => a
       | None => set_empty (Bitvector.fact_enc P)
       end) u).
    rewrite Bitvector.prepare_boundary_source by
      (try exact HN; unfold Bitvector.seeds; rewrite Hdir;
       eapply reachable_point_in_nodes; eassumption).
    rewrite Hb; apply member_list; assumption.
  - exact Hpost.
  - exact Hs.
  - exact Ht.
  - exact Hpoint.
  - exact Hagree.
Qed.

(** Invariant laws describe generation and survival of individual state facts. *)
Record bv_inv_laws {S O N E U} (m : semantics S O) (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (holds : U -> S -> Prop) : Prop := {
  inv_boundary : entry_boundaries P;
  inv_seed : forall s xs u, initial m s ->
    Bitvector.boundary P (Link.point lk s) = Some xs -> In u xs -> holds u s;
  inv_gen : forall e u, on_steps m (fun s l s' =>
    Link.taken lk s l s' e -> In u (Bitvector.gen P e) -> holds u s');
  inv_frame : forall e u, on_steps m (fun s l s' =>
    Link.taken lk s l s' e -> ~ In u (Bitvector.kill P e) -> holds u s -> holds u s');
  inv_stay : forall u, on_steps m (fun s l s' =>
    Link.stays lk s l s' -> holds u s -> holds u s')
}.

(** Every reachable state satisfies every fact of a forward must post-solution. *)
Theorem forward_must_sound {S O N E U} m (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (holds : U -> S -> Prop) sigma :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.dir P = Forward ->
  link_laws m (Cfg.graph (Bitvector.cfg P)) lk -> bv_inv_laws m P lk holds ->
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  forall s, reachable_state m s ->
    gamma (must_gamma (Bitvector.fact_enc P) holds) (sigma (Link.point lk s)) s.
Proof.
  intros HN HE HU Hdir Hlink [Hcovers Hseed Hgen Hframe Hstay] Hpost.
  eapply (DenseForward.forward_invariant_sound m
    (Bitvector.must_dense P (Bitvector.prepare P)) lk (fun _ => must_gamma _ holds)).
  - exact Hdir.
  - apply must_laws; exact HU.
  - exact Hlink.
  - apply must_gamma_laws; exact HU.
  - apply must_boundary_covers; assumption.
  - intros s a Hs Ha.
    change (option_map Only
      (Bitvector.boundary_set (Bitvector.prepare P) (Link.point lk s)) = Some a) in Ha.
    rewrite Bitvector.prepare_boundary_source in Ha by
      (try exact HN; unfold Bitvector.seeds; rewrite Hdir; apply (entry_points Hlink); exact Hs).
    destruct (Bitvector.boundary P (Link.point lk s)) as [xs|] eqn:Hb;
      [|discriminate].
    inversion Ha; subst a; intros u Hu; eapply Hseed; try eassumption.
    exact (proj1 (member_list _ HU xs u) Hu).
  - intros e s l s' Hr Hstep Htaken Ha.
    destruct (link_taken_edge m (Bitvector.cfg P) lk s l s' e
      Hlink Hr Hstep Htaken) as [He _].
    change (gamma (must_gamma _ holds)
      (Bitvector.must_transfer (Bitvector.prepare P) e (sigma (Link.point lk s))) s').
    rewrite must_transfer_equation.
    destruct (sigma (Link.point lk s)) as [|a]; [contradiction|].
    intros u Hu; apply transfer_member in Hu; [|exact HE|exact HU|exact He].
    destruct Hu as [[Hu Hkill]|Hu].
    + eapply Hframe; try eassumption; apply Ha; exact Hu.
    + eapply Hgen; eassumption.
  - intros s l s' Hr Hstep Hstays Ha.
    destruct (sigma (Link.point lk s)) as [|a]; [contradiction|].
    intros u Hu; eapply Hstay; try eassumption; apply Ha; exact Hu.
  - exact Hpost.
Qed.

(** Cover laws decompose each new history fact into generation or an un-killed old fact. *)
Record bv_cover_laws {S O N E U} (m : semantics S O) (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (W : S -> list E -> S -> U -> Prop) : Prop := {
  cover_boundary : entry_boundaries P;
  cover_seed : forall s xs u, initial m s ->
    Bitvector.boundary P (Link.point lk s) = Some xs -> W s [] s u -> In u xs;
  cover_edge : forall e s0 es u, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    W s0 (es ++ [e]) s' u ->
    (W s0 es s u /\ ~ In u (Bitvector.kill P e)) \/ In u (Bitvector.gen P e));
  cover_stay : forall s0 es u, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.stays lk s l s' ->
    W s0 es s' u -> W s0 es s u)
}.

(** Every locally produced history fact occurs in a forward may post-solution. *)
Theorem forward_may_cover {S O N E U} m (P : Bitvector.t N E U)
    (lk : Link.t S O N E) W sigma :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.dir P = Forward ->
  link_laws m (Cfg.graph (Bitvector.cfg P)) lk -> bv_cover_laws m P lk W ->
  post_solution (Analysis.lat (Bitvector.may_analysis P))
    (Analysis.system (Bitvector.may_analysis P)) sigma ->
  forall s0 es s u, initial m s0 -> run_edges m lk s0 es s ->
    W s0 es s u -> member (sigma (Link.point lk s)) u.
Proof.
  intros HN HE HU Hdir Hlink [Hcovers Hseed Hedge Hstay] Hpost.
  eapply (DenseWitness.forward_cover_sound m
    (Bitvector.may_dense P (Bitvector.prepare P)) lk member W sigma).
  - exact Hdir.
  - apply may_laws; exact HU.
  - exact Hlink.
  - apply member_monotone; exact HU.
  - apply may_boundary_covers; assumption.
  - intros s a u Hs Ha Hw.
    change (Bitvector.boundary_set (Bitvector.prepare P) (Link.point lk s) = Some a) in Ha.
    rewrite Bitvector.prepare_boundary_source in Ha by
      (try exact HN; unfold Bitvector.seeds; rewrite Hdir; apply (entry_points Hlink); exact Hs).
    destruct (Bitvector.boundary P (Link.point lk s)) as [xs|] eqn:Hb;
      [|discriminate].
    inversion Ha; subst a; apply member_list; [exact HU|eapply Hseed; eassumption].
  - intros e s0 es a s l s' Hr Hstep Hi Hrun Htaken Hfacts u Hw.
    destruct (link_taken_edge m (Bitvector.cfg P) lk s l s' e
      Hlink Hr Hstep Htaken) as [He _].
    apply transfer_member; [exact HE|exact HU|exact He|].
    destruct (Hedge e s0 es u s l s' Hr Hstep Hi Hrun Htaken Hw)
      as [[Hold Hkill]|Hgen].
    + left; split; [apply Hfacts; exact Hold|exact Hkill].
    + right; exact Hgen.
  - intros s0 es a s l s' Hr Hstep Hi Hrun Hstays Hfacts u Hw.
    apply Hfacts; eapply Hstay; eassumption.
  - exact Hpost.
Qed.

(** Continuation laws build witnesses from generation or an un-killed suffix witness. *)
Record bv_witness_laws {S O N E U} (m : semantics S O) (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (Q : S -> Prop)
    (W : S -> list E -> S -> U -> Prop) : Prop := {
  witness_boundary : forall t, reachable_state m t -> Q t ->
    exists xs, Bitvector.boundary P (Link.point lk t) = Some xs;
  witness_terminal : forall t xs u, reachable_state m t -> Q t ->
    Bitvector.boundary P (Link.point lk t) = Some xs -> In u xs -> W t [] t u;
  witness_gen : forall e es t u, on_steps m (fun s l s' =>
    run_edges m lk s' es t -> Q t -> Link.taken lk s l s' e ->
    In u (Bitvector.gen P e) -> W s (e :: es) t u);
  witness_frame : forall e es t u, on_steps m (fun s l s' =>
    run_edges m lk s' es t -> Q t -> Link.taken lk s l s' e ->
    ~ In u (Bitvector.kill P e) -> W s' es t u -> W s (e :: es) t u);
  witness_stay : forall es t u, on_steps m (fun s l s' =>
    run_edges m lk s' es t -> Q t -> Link.stays lk s l s' ->
    W s' es t u -> W s es t u)
}.

(** A fresh All carries a marker that cannot survive a finite selected continuation. *)
Definition marked_member {U} {enc : encoding U} (a : must_t enc) (u : option U) :=
  match a, u with
  | All, _ => True
  | Only _, None => False
  | Only a, Some u => member a u
  end.

Lemma marked_member_antitone {U} enc (HU : encoding_laws enc) :
  DenseWitness.holds_antitone (must enc) (@marked_member U enc).
Proof.
  intros [|a] [|b] [u|] Hab Hu; try exact I; try contradiction; try discriminate.
  exact (proj1 (may_leb enc HU b a) Hab u Hu).
Qed.

Local Lemma marked_transfer_rule {N E U} (P : Bitvector.t N E U)
    (HE : encoding_laws (Cfg.edge_enc (Bitvector.cfg P)))
    (HU : encoding_laws (Bitvector.fact_enc P)) e a (A B : U -> Prop) :
  In e (Cfg.edges (Bitvector.cfg P)) ->
  (forall u, In u (Bitvector.gen P e) -> B u) ->
  (forall u, ~ In u (Bitvector.kill P e) -> A u -> B u) ->
  (forall v, marked_member a v -> match v with Some u => A u | None => False end) ->
  forall v, marked_member (Bitvector.must_transfer (Bitvector.prepare P) e a) v ->
    match v with Some u => B u | None => False end.
Proof.
  intros He Hgen Hframe Hfacts v Hv; rewrite must_transfer_equation in Hv.
  destruct a as [|a].
  - exfalso; exact (Hfacts None I).
  - destruct v as [u|]; [|contradiction].
    apply (transfer_member P e a u HE HU He) in Hv.
    destruct Hv as [[Hold Hkill]|Hgenerated].
    + apply Hframe; [exact Hkill|exact (Hfacts (Some u) Hold)].
    + apply Hgen; exact Hgenerated.
Qed.

(** History invariant laws retain the prefix witness needed for availability. *)
Record bv_history_laws {S O N E U} (m : semantics S O) (P : Bitvector.t N E U)
    (lk : Link.t S O N E) (W : S -> list E -> S -> U -> Prop) : Prop := {
  history_boundary : entry_boundaries P;
  history_seed : forall s xs u, initial m s ->
    Bitvector.boundary P (Link.point lk s) = Some xs -> In u xs -> W s [] s u;
  history_gen : forall e s0 es u, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    In u (Bitvector.gen P e) -> W s0 (es ++ [e]) s' u);
  history_frame : forall e s0 es u, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.taken lk s l s' e ->
    ~ In u (Bitvector.kill P e) -> W s0 es s u -> W s0 (es ++ [e]) s' u);
  history_stay : forall s0 es u, on_steps m (fun s l s' =>
    initial m s0 -> run_edges m lk s0 es s -> Link.stays lk s l s' ->
    W s0 es s u -> W s0 es s' u)
}.

(** Forward must facts have prefix witnesses under local generation and frame laws. *)
Theorem forward_must_history {S O N E U} m (P : Bitvector.t N E U)
    (lk : Link.t S O N E) W sigma :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.dir P = Forward ->
  link_laws m (Cfg.graph (Bitvector.cfg P)) lk -> bv_history_laws m P lk W ->
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  forall s0 es s u, initial m s0 -> run_edges m lk s0 es s ->
    must_member (sigma (Link.point lk s)) u -> W s0 es s u.
Proof.
  intros HN HE HU Hdir Hlink [Hcovers Hseed Hgen Hframe Hstay] Hpost.
  assert (Hsound : forall s0 es s v, initial m s0 -> run_edges m lk s0 es s ->
    marked_member (sigma (Link.point lk s)) v ->
    match v with Some u => W s0 es s u | None => False end).
  { eapply (DenseWitness.forward_witness_sound m
      (Bitvector.must_dense P (Bitvector.prepare P)) lk marked_member
      (fun s0 es s v => match v with Some u => W s0 es s u | None => False end) sigma).
    - exact Hdir.
    - apply must_laws; exact HU.
    - exact Hlink.
    - apply marked_member_antitone; exact HU.
    - apply must_boundary_covers; assumption.
    - intros s a v Hi Ha Hv.
      change (option_map Only
        (Bitvector.boundary_set (Bitvector.prepare P) (Link.point lk s)) = Some a) in Ha.
      rewrite Bitvector.prepare_boundary_source in Ha by
        (try exact HN; unfold Bitvector.seeds; rewrite Hdir; apply (entry_points Hlink); exact Hi).
      destruct (Bitvector.boundary P (Link.point lk s)) as [xs|] eqn:Hb; [|discriminate].
      inversion Ha; subst a; destruct v as [u|]; [|contradiction].
      eapply Hseed; try eassumption; exact (proj1 (member_list _ HU xs u) Hv).
    - intros e s0 es a s l s' Hr Hstep Hi Hrun Htaken Hfacts v Hv.
      destruct (link_taken_edge m (Bitvector.cfg P) lk s l s' e
        Hlink Hr Hstep Htaken) as [He _].
      change (marked_member (Bitvector.must_transfer (Bitvector.prepare P) e a) v) in Hv.
      eapply (marked_transfer_rule P HE HU e a (fun u => W s0 es s u)); try eassumption.
      + intros u Hu; eapply Hgen; eassumption.
      + intros u Hkill Hw; eapply Hframe; eassumption.
    - intros s0 es a s l s' Hr Hstep Hi Hrun Hstays Hfacts [u|] Hv.
      + eapply Hstay; try eassumption; exact (Hfacts (Some u) Hv).
      + exact (Hfacts None Hv).
    - exact Hpost. }
  intros s0 es s u Hi Hrun Hu; apply (Hsound s0 es s (Some u)); assumption.
Qed.

(** Backward must membership supplies a witness on every selected finite continuation. *)
Theorem backward_must_witness {S O N E U} m (P : Bitvector.t N E U)
    (lk : Link.t S O N E) Q W sigma :
  encoding_laws (Cfg.node_enc (Bitvector.cfg P)) ->
  encoding_laws (Cfg.edge_enc (Bitvector.cfg P)) ->
  encoding_laws (Bitvector.fact_enc P) -> Bitvector.dir P = Backward ->
  link_laws m (Cfg.graph (Bitvector.cfg P)) lk -> bv_witness_laws m P lk Q W ->
  post_solution (Analysis.lat (Bitvector.must_analysis P))
    (Analysis.system (Bitvector.must_analysis P)) sigma ->
  forall s es t u, reachable_state m s -> run_edges m lk s es t -> Q t ->
    must_member (sigma (Link.point lk s)) u -> W s es t u.
Proof.
  intros HN HE HU Hdir Hlink [Hboundary Hterminal Hgen Hframe Hstay] Hpost.
  assert (Hsound : forall s es t v, reachable_state m s -> run_edges m lk s es t ->
    Q t -> marked_member (sigma (Link.point lk s)) v ->
    match v with Some u => W s es t u | None => False end).
  { eapply (DenseWitness.backward_witness_sound m
    (Bitvector.must_dense P (Bitvector.prepare P)) lk marked_member Q
    (fun s es t v => match v with Some u => W s es t u | None => False end) sigma).
  - exact Hdir.
  - apply must_laws; exact HU.
  - exact Hlink.
  - apply marked_member_antitone; exact HU.
  - intros t v Hr HQ Hu.
    destruct (Hboundary t Hr HQ) as [xs Hb].
    unfold DenseAgreement.exit_fact in Hu.
    change (marked_member
      (match option_map Only
        (Bitvector.boundary_set (Bitvector.prepare P) (Link.point lk t)) with
       | Some a => a | None => All end) v) in Hu.
    rewrite Bitvector.prepare_boundary_source in Hu by
      (try exact HN; unfold Bitvector.seeds; rewrite Hdir;
       eapply reachable_point_in_nodes; eassumption).
    rewrite Hb in Hu; destruct v as [u|]; cbn [option_map marked_member] in Hu.
    + eapply Hterminal; try eassumption; exact (proj1 (member_list _ HU xs u) Hu).
    + contradiction.
  - intros e es t a s l s' Hr Hstep Hrun HQ Htaken Hfacts v Hu.
    destruct (link_taken_edge m (Bitvector.cfg P) lk s l s' e
      Hlink Hr Hstep Htaken) as [He _].
    change (marked_member (Bitvector.must_transfer (Bitvector.prepare P) e a) v) in Hu.
    eapply (marked_transfer_rule P HE HU e a (fun u => W s' es t u)); try eassumption.
    + intros u Hgenerated; eapply Hgen; eassumption.
    + intros u Hkill Hw; eapply Hframe; eassumption.
  - intros es t a s l s' Hr Hstep Hrun HQ Hstays Hfacts [u|] Hu.
    + eapply Hstay; try eassumption; exact (Hfacts (Some u) Hu).
    + exact (Hfacts None Hu).
  - exact Hpost. }
  intros s es t u Hr Hrun HQ Hu.
  apply (Hsound s es t (Some u)); assumption.
Qed.

End GenkillSound.
