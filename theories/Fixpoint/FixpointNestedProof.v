(** * Nested traversal soundness and reachability

    A clean outer pass retains every constraint as pending or already satisfied.
    For example, a side update after an earlier component invalidates the whole outer pass.
    Builds on: FixpointNested, FixpointLeast and the public evaluator and update contracts. *)

From Stdlib Require Import List Bool Arith NArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver FixpointLeast FixpointNested.
Import List.ListNotations Cost.Notations.

Module NestedProof.

(** One satisfied row bounds its primary return and every side contribution. *)
Definition constraint_satisfied {X C A} (L : lattice A) (S : System.t X C A) c s :=
  leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true /\
    forall x b, In (x, b) (Query.sides (System.rhs S c) s) -> leb L b (s x) = true.

Local Lemma rule_stationary {X A} (EX : encoding X) (L : lattice A) op m x b :
  snd (Update.rule EX L op m x b) = false -> leb L b (lookup EX L m x) = true.
Proof.
  rewrite Update.rule_equation.
  destruct (leb L b (lookup EX L m x)); cbn; congruence.
Qed.

(** The output-fold equation exposes its sole shared update and the per-key change counter. *)
Theorem updates_equation {X C A} (a : Analysis.t X C A) hs delay outs m counts :
  Nested.updates a hs delay outs m counts =
  match outs with
  | [] => (m, counts, false)
  | (x, value) :: rest =>
    let count := Map.find_or (Analysis.key_enc a) 0%N x counts in
    let first := Update.rule (Analysis.key_enc a) (Analysis.lat a)
      (Nested.op_c a hs delay x count) m x value in
    let counts' := if snd first then
      Map.set (Analysis.key_enc a) x (N.succ count) counts else counts in
    let next := Nested.updates a hs delay rest (fst first) counts' in
    (fst (fst next), snd (fst next), snd first || snd next)
  end.
Proof.
  destruct outs as [|[x value] rest]; [reflexivity|].
  unfold Nested.updates at 1; cbn [Nested.updates_c]; autorewrite with galois_cost.
  fold (Map.find_or (Analysis.key_enc a) 0%N x counts).
  fold (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    (Nested.op_c a hs delay x (Map.find_or (Analysis.key_enc a) 0%N x counts)) m x value).
  destruct (snd (Update.rule _ _ _ _ _ _)); reflexivity.
Qed.

Section Outputs.
Context {X C A : Type} (a : Analysis.t X C A) (hs : FinSet.t X) (delay : N).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.

(** Arbitrary operators retain the assignment when their complete output fold is stationary. *)
Theorem updates_stationary outs m counts :
  snd (Nested.updates a hs delay outs m counts) = false ->
  fst (fst (Nested.updates a hs delay outs m counts)) = m /\
  forall x b, In (x, b) outs -> leb L b (lookup EX L m x) = true.
Proof.
  revert m counts; induction outs as [|[x b] rest IH]; intros m counts Hstable.
  - split; [reflexivity|intros y d Hin; contradiction].
  - rewrite updates_equation in Hstable |- *.
    cbn [snd fst] in Hstable |- *.
    apply orb_false_iff in Hstable as [Hfirst Hnext].
    pose proof (Update.rule_unchanged EX L _ m x b Hfirst) as Heq.
    destruct (IH _ _ Hnext) as [Hmap Hbounds].
    split; [exact (eq_trans Hmap Heq)|].
    intros y d [Hpair|Hin].
    + injection Hpair as <- <-.
      exact (rule_stationary _ _ _ _ _ _ Hfirst).
    + rewrite <- Heq; exact (Hbounds y d Hin).
Qed.

(** The assignment projection stays well formed independently of policy choices. *)
Theorem updates_wf outs m counts :
  Map.wf EX m -> Map.wf EX (fst (fst (Nested.updates a hs delay outs m counts))).
Proof.
  revert m counts; induction outs as [|[x b] rest IH]; intros m counts Hwf;
    rewrite updates_equation; [exact Hwf|].
  cbn [fst]; apply IH, Update.rule_wf, Hwf.
Qed.

(** A joining policy returns the lattice join while retaining the operator's actual charges. *)
Theorem op_join x count old value :
  Analysis.joining a ->
  Cost.value (Nested.op_c a hs delay x count old value) = join L old value.
Proof.
  intro Hjoining; unfold Nested.op_c; autorewrite with galois_cost.
  fold (Policy.widen_at (Analysis.policy a) x).
  rewrite Hjoining, andb_false_r; reflexivity.
Qed.

Local Lemma rule_join m counts x b :
  Analysis.joining a ->
  Update.rule EX L (Nested.op_c a hs delay x counts) m x b =
    Update.rule EX L (join_c L) m x b.
Proof.
  intro Hjoining; rewrite !Update.rule_equation.
  rewrite op_join by exact Hjoining; reflexivity.
Qed.

(** Joining folds agree with the shared output fold on both the assignment and change flag. *)
Theorem updates_join outs m counts :
  Analysis.joining a ->
  (fst (fst (Nested.updates a hs delay outs m counts)),
    snd (Nested.updates a hs delay outs m counts)) =
  Update.apply EX L (join_c L) outs m.
Proof.
  intro Hjoining; revert m counts; induction outs as [|[x b] rest IH];
    intros m counts; rewrite updates_equation, Update.apply_equation; [reflexivity|].
  fold EX L.
  cbn zeta.
  rewrite rule_join by exact Hjoining.
  specialize (IH (fst (Update.rule EX L (join_c L) m x b))
    (if snd (Update.rule EX L (join_c L) m x b) then
      Map.set EX x (N.succ (Map.find_or EX 0%N x counts)) counts else counts)).
  apply (f_equal (fun r => (fst r, snd (Update.rule EX L (join_c L) m x b) || snd r)))
    in IH.
  exact IH.
Qed.

End Outputs.

(** Coverage reflection uses lawful keys and does not require static summaries. *)
Theorem cover_spec {X C A} (a : Analysis.t X C A) root :
  encoding_laws (Analysis.key_enc a) ->
  (Cost.value (Nested.cover_c a
    (FinSet.of_list (Analysis.key_enc a) (Nested.vertices root))
    (System.constraints (Analysis.system a))) = true <->
  forall c, In c (System.constraints (Analysis.system a)) ->
    In (System.target (Analysis.system a) c) (Nested.vertices root)).
Proof.
  intro HE; generalize (System.constraints (Analysis.system a)) as cs.
  intro cs; induction cs as [|c rest IH].
  - cbn [Nested.cover_c]; split; intros; [contradiction|reflexivity].
  - cbn [Nested.cover_c]; autorewrite with galois_cost.
    fold (System.target (Analysis.system a) c).
    fold (FinSet.mem (Analysis.key_enc a) (System.target (Analysis.system a) c)
      (FinSet.of_list (Analysis.key_enc a) (Nested.vertices root))).
    rewrite FinSet.mem_of_list.
    assert (Hmem : existsb
      (eqb (Analysis.key_enc a) (System.target (Analysis.system a) c))
      (Nested.vertices root) = true <->
      In (System.target (Analysis.system a) c) (Nested.vertices root)).
    { rewrite existsb_exists; split.
      - intros [x [Hx Hsame]]; apply (eqb_true_iff _ HE) in Hsame; now subst x.
      - intro Hin; exists (System.target (Analysis.system a) c); split; [exact Hin|].
        apply eqb_refl. }
    destruct (existsb _ _) eqn:Hcovered.
    + rewrite IH; pose proof (proj1 Hmem eq_refl) as Hin; cbn.
      split.
      * intros Hall d [<-|Hd]; [exact Hin|exact (Hall d Hd)].
      * intros Hall d Hd; apply Hall; now right.
    + split; [discriminate|].
      intro Hall; specialize (Hall c (or_introl eq_refl)).
      apply (proj2 Hmem) in Hall; discriminate.
Qed.

Section Sound.
Context {X C A : Type} (a : Analysis.t X C A) (root : Nested.code X)
  (ix : sys_index X C) (hs : FinSet.t X) (delay : N).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.

(** Pending constraints occur in the current pointer, a suspended suffix, or the ready bucket. *)
Definition pending (s : Nested.State.t X C A) (c : C) : Prop :=
  In c (Nested.State.ready s) \/
  exists x, (In x (Nested.vertices (Nested.State.pointer s)) \/
    exists f, In f (Nested.State.frames s) /\ In x (Nested.vertices (Nested.Frame.rest f))) /\
    In c (contributors_of EX ix x).

(** A clean pass has already satisfied every constraint that is no longer pending. *)
Definition sound_state (s : Nested.State.t X C A) : Prop :=
  (Nested.State.outer s <= Nested.State.epoch s)%N /\
  (Nested.State.outer s = Nested.State.epoch s ->
    forall c, In c (System.constraints S) ->
      pending s c \/ constraint_satisfied L S c (lookup EX L (Nested.State.values s))).

Hypothesis Hcover : forall c, In c (System.constraints S) ->
  exists x, In x (Nested.vertices root) /\ In c (contributors_of EX ix x).

Local Lemma root_sound m counts epoch evals :
  sound_state (Nested.State.Make m counts root [] [] epoch epoch evals).
Proof.
  cbn [sound_state]; split; [apply N.le_refl|].
  intros _ c Hc; left; right; destruct (Hcover c Hc) as [x [Hx Hrow]].
  exists x; split; [now left|exact Hrow].
Qed.

Local Lemma evaluated_sound s c rest :
  Nested.State.ready s = c :: rest -> sound_state s ->
  let out := fst (Eval.outputs S c (lookup EX L (Nested.State.values s))) in
  let next := Nested.updates a hs delay out
    (Nested.State.values s) (Nested.State.counters s) in
  sound_state (Nested.State.Make
    (fst (fst next)) (snd (fst next))
    (Nested.State.pointer s) rest (Nested.State.frames s)
    (if snd next then N.succ (Nested.State.epoch s) else Nested.State.epoch s)
    (Nested.State.outer s) (N.succ (Nested.State.evals s))).
Proof.
  intros Hready [Hepoch Hsound].
  cbn zeta.
  set (out := fst (Eval.outputs S c (lookup EX L (Nested.State.values s)))).
  set (next := Nested.updates a hs delay out (Nested.State.values s) (Nested.State.counters s)).
  destruct (snd next) eqn:Hchanged.
  - cbv beta iota delta [sound_state Nested.State.outer Nested.State.epoch].
    split.
    + eapply N.le_trans; [exact Hepoch|apply N.le_succ_diag_r].
    + intro Heq; exfalso.
      change (Nested.State.outer s = N.succ (Nested.State.epoch s)) in Heq.
      rewrite Heq in Hepoch.
      exact (N.nle_succ_diag_l _ Hepoch).
  - destruct (updates_stationary a hs delay out _ _ Hchanged) as [Hmap Hbounds].
    change (fst (fst next) = Nested.State.values s) in Hmap.
    cbv beta iota delta [sound_state Nested.State.values Nested.State.outer Nested.State.epoch].
    split; [exact Hepoch|].
    rewrite Hmap; intros Heq d Hd.
    destruct (Hsound Heq d Hd) as [[Hin|Hpending]|Hsatisfied].
    + rewrite Hready in Hin; destruct Hin as [<-|Hin]; [right|left; now left].
      split.
      * apply Hbounds; unfold out; rewrite Eval.outputs_spec; now left.
      * intros x b Hb; apply Hbounds; unfold out; rewrite Eval.outputs_spec; now right.
    + left; right; exact Hpending.
    + now right.
Qed.

(** One actual transition preserves the clean-pass invariant. *)
Theorem step_sound s next :
  sound_state s ->
  Nested.step a root ix hs delay s = inl next -> sound_state next.
Proof.
  intros Hsound Hstep.
  unfold Nested.step, Nested.step_c in Hstep.
  destruct (Nested.State.ready s) as [|c rest] eqn:Hready.
  2: {
    autorewrite with galois_cost in Hstep.
    rewrite (Eval.outputs_c_spec S c _ (lookup EX L (Nested.State.values s))) in Hstep
      by reflexivity.
    fold (Nested.updates a hs delay
      (fst (Eval.outputs S c (lookup EX L (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)) in Hstep.
    injection Hstep as <-; apply evaluated_sound; assumption.
  }
  destruct Hsound as [Hepoch Hsound].
  destruct (Nested.State.pointer s) as [|x rest|h body rest] eqn:Hpointer.
  - destruct (Nested.State.frames s) as [|f rest] eqn:Hframes.
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s));
        [discriminate|].
      injection Hstep as <-; apply root_sound.
    + destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
        injection Hstep as <-; split; [exact Hepoch| |exact Hepoch|];
        intros Heq c Hc; destruct (Hsound Heq c Hc) as [Hpending|Hsat];
        [left|now right|left|now right];
        unfold pending in Hpending |- *; rewrite Hready, Hpointer, Hframes in Hpending;
        cbn in Hpending |- *.
      * destruct Hpending as [Hbad|[y [[Hbad|[g [[<-|Hg] Hy]]] Hrow]]];
          try contradiction.
        -- right; exists y; split; [now left|exact Hrow].
        -- right; exists y; split; [right; exists g; auto|exact Hrow].
      * destruct Hpending as [Hbad|[y [[Hbad|[g [[<-|Hg] Hy]]] Hrow]]];
          try contradiction.
        -- right; exists y; split; [right; exists
             (Nested.Frame.Make (Nested.Frame.head f) (Nested.Frame.body f)
               (Nested.Frame.rest f) (Nested.State.epoch s)); cbn; auto|exact Hrow].
        -- right; exists y; split; [right; exists g; cbn; auto|exact Hrow].
  - autorewrite with galois_cost in Hstep.
    fold (contributors_of EX ix x) in Hstep.
    injection Hstep as <-; split; [exact Hepoch|].
    intros Heq c Hc; destruct (Hsound Heq c Hc) as [Hpending|Hsat]; [left|now right].
    unfold pending in Hpending |- *; rewrite Hready, Hpointer in Hpending; cbn in *.
    destruct Hpending as [Hbad|[y [[[<-|Hy]|Hframe] Hrow]]]; try contradiction.
    + left; exact Hrow.
    + right; exists y; split; [now left|exact Hrow].
    + right; exists y; split; [now right|exact Hrow].
  - injection Hstep as <-; split; [exact Hepoch|].
    intros Heq c Hc; destruct (Hsound Heq c Hc) as [Hpending|Hsat]; [left|now right].
    unfold pending in Hpending |- *; rewrite Hready, Hpointer in Hpending; cbn in *.
    destruct Hpending as [Hbad|[x [[[<-|Hx]|Hframe] Hrow]]]; try contradiction.
    + right; exists h; split; [left; now left|exact Hrow].
    + apply in_app_iff in Hx as [Hx|Hx]; right; exists x; split; try exact Hrow.
      * left; now right.
      * right; exists (Nested.Frame.Make h body rest (Nested.State.epoch s)); cbn; auto.
    + right; exists x; split; [|exact Hrow].
      right; destruct Hframe as [f [Hf Hx]]; exists f; cbn; auto.
Qed.

(** A stopping transition has discharged every primary and side contribution. *)
Theorem step_solved s m :
  sound_state s -> Nested.step a root ix hs delay s = inr m ->
  post_solution L S (lookup EX L m).
Proof.
  intros [Hepoch Hsound] Hstop; unfold Nested.step, Nested.step_c in Hstop.
  destruct (Nested.State.ready s) as [|c rest] eqn:Hready.
  2: { autorewrite with galois_cost in Hstop; discriminate. }
  destruct (Nested.State.pointer s) eqn:Hpointer; try discriminate.
  destruct (Nested.State.frames s) as [|f rest] eqn:Hframes.
  2: { destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s)); discriminate. }
  destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s)) eqn:Hclean;
    [|discriminate].
  injection Hstop as <-; apply N.eqb_eq in Hclean.
  intros c Hc; destruct (Hsound Hclean c Hc) as [Hpending|Hsat]; [|exact Hsat].
  unfold pending in Hpending; rewrite Hready, Hpointer, Hframes in Hpending.
  cbn in Hpending; firstorder.
Qed.

End Sound.

(** Run induction transports local continuation and stopping obligations to the real iterator. *)
Theorem runs_property {S R} (step : S -> Cost.t (S + R)) (I : S -> Prop) (P : R -> Prop) :
  (forall s, I s ->
    match Cost.value (step s) with inl next => I next | inr r => P r end) ->
  forall n s result, runs step n s result -> I s ->
    match result with inl next => I next | inr r => P r end.
Proof.
  intros Hstep n s result Hrun; induction Hrun as
    [s|n s r Hstop|n s next result Hnext Hrun IH]; intro HI.
  - exact HI.
  - specialize (Hstep s HI); now rewrite Hstop in Hstep.
  - apply IH; specialize (Hstep s HI); now rewrite Hnext in Hstep.
Qed.

Section Reached.
Context {X C A : Type} (a : Analysis.t X C A) (root : Nested.code X)
  (ix : sys_index X C) (hs : FinSet.t X) (delay : N)
  (Hix : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix)
  (Hjoining : Analysis.joining a).
Let EX := Analysis.key_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.

(** The computational state retains a path of listed shared raises from the empty assignment. *)
Definition reached_state (s : Nested.State.t X C A) : Prop :=
  Map.wf EX (Nested.State.values s) /\
  incl (Nested.State.ready s) (System.constraints S) /\
  clos_refl_trans (assignment X A) (raise EX L S) Map.empty (Nested.State.values s).

Local Lemma step_reached s :
  reached_state s ->
  match Nested.step a root ix hs delay s with
  | inl next => reached_state next
  | inr m => Map.wf EX m /\
    clos_refl_trans (assignment X A) (raise EX L S) Map.empty m
  end.
Proof.
  intros [Hwf [Hready Hpath]]; unfold Nested.step, Nested.step_c.
  destruct (Nested.State.ready s) as [|c rest] eqn:Hrows.
  2: {
    autorewrite with galois_cost.
    rewrite (Eval.outputs_c_spec S c _ (lookup EX L (Nested.State.values s))) by reflexivity.
    fold (Nested.updates a hs delay
      (fst (Eval.outputs S c (lookup EX L (Nested.State.values s))))
      (Nested.State.values s) (Nested.State.counters s)).
    assert (Hmap :
      fst (fst (Nested.updates a hs delay
        (fst (Eval.outputs S c (lookup EX L (Nested.State.values s))))
        (Nested.State.values s) (Nested.State.counters s))) =
      fst (raise_result EX L S c (Nested.State.values s))).
    { rewrite raise_equation.
      exact (f_equal (@fst (assignment X A) bool)
        (updates_join a hs delay
          (fst (Eval.outputs S c (lookup EX L (Nested.State.values s))))
          (Nested.State.values s) (Nested.State.counters s) Hjoining)). }
    unfold reached_state; cbn; rewrite Hmap; split.
    - rewrite raise_equation; apply Update.apply_wf, Hwf.
    - split.
      + intros d Hd; apply Hready; now right.
      + eapply rt_trans; [exact Hpath|].
        apply rt_step; split; [exact Hwf|].
        exists c; split; [apply Hready; now left|reflexivity].
  }
  assert (Hnone : incl [] (System.constraints S)) by (intros c Hin; contradiction).
  destruct (Nested.State.pointer s) as [|x rest|h body rest].
  - destruct (Nested.State.frames s) as [|f rest].
    + destruct (N.eqb (Nested.State.outer s) (Nested.State.epoch s));
        cbn; [now split|unfold reached_state; cbn; auto].
    + destruct (N.eqb (Nested.Frame.epoch f) (Nested.State.epoch s));
        unfold reached_state; cbn; auto.
  - autorewrite with galois_cost.
    fold (contributors_of EX ix x).
    unfold reached_state; cbn; split; [exact Hwf|].
    split; [|exact Hpath].
    intros c Hc; exact (proj1 (proj1 (contributors_agree Hix x c) Hc)).
  - unfold reached_state; cbn; auto.
Qed.

End Reached.

(** Coverage guarding makes every solved result sound even for a malformed supplied code. *)
Theorem nested_sound {X C A} (a : Analysis.t X C A) root fuel m :
  encoding_laws (Analysis.key_enc a) ->
  Nested.run a root fuel = Outcome.Solved m ->
  post_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros HE Hrun; rewrite Nested.run_equation in Hrun.
  destruct (Cost.value (Nested.cover_c a _ _)) eqn:Hcovered; [|discriminate].
  pose proof (proj1 (cover_spec a root HE) Hcovered) as Htargets.
  set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) in *.
  set (hs := FinSet.of_list (Analysis.key_enc a) (Nested.heads root)) in *.
  set (delay := N.of_nat (Policy.delay (Analysis.policy a))) in *.
  assert (Hcover : forall c, In c (System.constraints (Analysis.system a)) ->
    exists x, In x (Nested.vertices root) /\ In c (contributors_of (Analysis.key_enc a) ix x)).
  { intros c Hc; exists (System.target (Analysis.system a) c); split.
    - apply Htargets, Hc.
    - apply (contributors_agree (index_system_laws _ HE _ _)); split; [exact Hc|now left]. }
  pose proof (runs_property (Nested.step_c a root ix hs delay)
    (sound_state a ix) (fun m =>
      post_solution (Analysis.lat a) (Analysis.system a)
        (lookup (Analysis.key_enc a) (Analysis.lat a) m))) as Hloop.
  specialize (Hloop ltac:(intros s HI;
    fold (Nested.step a root ix hs delay s);
    destruct (Nested.step a root ix hs delay s) as [next|done] eqn:Hstep;
    [exact (step_sound a root ix hs delay Hcover s next HI Hstep)|
     exact (step_solved a root ix hs delay s done HI Hstep)])).
  specialize (Hloop _ _ _ (iterate_value (Nested.step_c a root ix hs delay) fuel
    (Nested.start root)) (root_sound a root ix Hcover Map.empty Map.empty 0%N 0%N)).
  destruct (Cost.value (iterate _ _ _)) as [last|done]; [discriminate|].
  injection Hrun as <-; exact Hloop.
Qed.

(** Joining nested execution is a path of actual shared raises, including repeated rows. *)
Theorem nested_reached {X C A} (a : Analysis.t X C A) root fuel m :
  encoding_laws (Analysis.key_enc a) -> Analysis.joining a ->
  Nested.run a root fuel = Outcome.Solved m ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros HE Hjoining Hrun; rewrite Nested.run_equation in Hrun.
  destruct (Cost.value (Nested.cover_c a _ _)); [|discriminate].
  set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) in *.
  set (hs := FinSet.of_list (Analysis.key_enc a) (Nested.heads root)) in *.
  set (delay := N.of_nat (Policy.delay (Analysis.policy a))) in *.
  pose proof (runs_property (Nested.step_c a root ix hs delay)
    (reached_state a) (fun m => Map.wf (Analysis.key_enc a) m /\
      clos_refl_trans (assignment X A)
        (raise (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)) Map.empty m)
    (step_reached a root ix hs delay (index_system_laws _ HE _ _) Hjoining)
    _ _ _ (iterate_value (Nested.step_c a root ix hs delay) fuel (Nested.start root)))
    as Hloop.
  specialize (Hloop ltac:(split; [apply Map.wf_empty|]; split;
    [intros c Hin; contradiction|apply rt_refl])).
  destruct (Cost.value (iterate _ _ _)) as [last|done]; [discriminate|].
  injection Hrun as <-; exists done; split; [exact (proj2 Hloop)|reflexivity].
Qed.

(** Every nested code defines a lawful solver because coverage is checked before execution. *)
Theorem nested_solver_laws {X C A} (root : Nested.code X) :
  Solver.laws (@Nested.solver X C A root).
Proof.
  constructor; intros a fuel m Hl.
  - apply nested_sound, (Analysis.key_laws Hl).
  - intros Hlub Hjoining; apply nested_reached;
      [apply (Analysis.key_laws Hl)|exact Hjoining].
Qed.

(** A solved joining candidate is least under monotonicity and the separate join laws. *)
Theorem nested_reached_least {X C A} (a : Analysis.t X C A) root fuel m :
  Analysis.laws a -> lub_laws (Analysis.lat a) ->
  monotone_system (Analysis.lat a) (Analysis.system a) -> Analysis.joining a ->
  Nested.run a root fuel = Outcome.Solved m ->
  least_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros Hl Hlub Hmono Hjoining Hrun.
  eapply (reached_least (Analysis.key_enc a) (Analysis.key_laws Hl)).
  - apply (Analysis.lattice_law Hl).
  - exact Hlub.
  - exact Hmono.
  - exact (nested_reached a root fuel m (Analysis.key_laws Hl) Hjoining Hrun).
  - exact (nested_sound a root fuel m (Analysis.key_laws Hl) Hrun).
Qed.

End NestedProof.
Import NestedProof.
