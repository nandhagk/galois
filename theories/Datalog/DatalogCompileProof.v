(** * Compiled-stratum laws and finite support

    The compiled system is monotone because negation reads immutable lower relations.
    For example, increasing a current positive relation cannot retract a fired tuple.
    Builds on: DatalogCompile, DatalogModel and FixpointLeast. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointAnalysis FixpointAnalyze FixpointSolver FixpointKleene.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogModel
  DatalogRelation DatalogFire DatalogCompile.
Import List.ListNotations.
Local Open Scope nat_scope.

(** Representation compares public tuple memberships with the declarative ground model. *)
Definition represents {P} (db : P -> relation) (M : ground_atom P -> Prop) :=
  forall p ts, member ts (db p) = true <-> M (p, ts).

Lemma rule_constraints_equation {P} (st : stratification P) k i rs :
  rule_constraints st k i rs =
  match rs with
  | [] => []
  | r :: rest =>
    if Nat.eqb (level st (pred (head r))) k
    then Constraint.FromRule i (pred (head r)) :: rule_constraints st k (S i) rest
    else rule_constraints st k (S i) rest
  end.
Proof.
  destruct rs as [|r rest]; [reflexivity |].
  unfold rule_constraints at 1; cbn [rule_constraints_c].
  repeat rewrite Cost.value_bind; reflexivity.
Qed.

Lemma rule_constraints_spec {P} (st : stratification P) k start rs c :
  In c (rule_constraints st k start rs) <->
  exists j r, nth_error rs j = Some r /\ level st (pred (head r)) = k /\
    c = Constraint.FromRule (start + j) (pred (head r)).
Proof.
  revert start; induction rs as [|r rs IH]; intro start; rewrite rule_constraints_equation.
  - split; [contradiction | intros [[|j] [r [Hbad _]]]; discriminate].
  - destruct (Nat.eqb (level st (pred (head r))) k) eqn:Hlevel.
    + apply Nat.eqb_eq in Hlevel; cbn [In]; rewrite IH; split.
      * intros [Heq | [j [r' [Hnth [Hl Heq]]]]].
        -- exists 0, r; cbn; repeat split; auto; now rewrite Nat.add_0_r.
        -- exists (S j), r'; cbn; repeat split; auto.
           rewrite Heq; f_equal; lia.
      * intros [[|j] [r' [Hnth [Hl Heq]]]].
        -- cbn in Hnth; injection Hnth as <-; left; rewrite Heq, Nat.add_0_r; reflexivity.
        -- right; exists j, r'; split; [exact Hnth | split; [exact Hl |]].
           rewrite Heq; f_equal; lia.
    + rewrite IH; split.
      * intros [j [r' [Hnth [Hl Heq]]]]; exists (S j), r'; cbn.
        repeat split; auto; rewrite Heq; f_equal; lia.
      * intros [[|j] [r' [Hnth [Hl Heq]]]].
        -- cbn in Hnth; injection Hnth as <-; rewrite Hl, Nat.eqb_refl in Hlevel; discriminate.
        -- exists j, r'; split; [exact Hnth | split; [exact Hl |]].
           rewrite Heq; f_equal; lia.
Qed.

Lemma stratum_constraints_equation {P} (prog : program P) facts st k :
  stratum_constraints prog facts st k =
    rule_constraints st k 0 (rules prog) ++
    map (fun f => Constraint.FromFact (fst f))
      (filter (fun f => Nat.eqb (level st (fst f)) k) facts).
Proof.
  unfold stratum_constraints, stratum_constraints_c; repeat rewrite Cost.value_bind.
  rewrite value_app_c, value_map_c, value_filter_c; reflexivity.
Qed.

Lemma rule_constraint_view {P} (prog : program P) facts st k i h :
  In (Constraint.FromRule i h) (stratum_constraints prog facts st k) ->
  exists r, In r (rules prog) /\ h = pred (head r) /\ level st h = k /\
    rule_at (rules prog) i = Some r.
Proof.
  rewrite stratum_constraints_equation, in_app_iff; intros [Hin | Hbad].
  - apply rule_constraints_spec in Hin as [j [r [Hnth [Hl Heq]]]].
    cbn in Heq; injection Heq as Hindex Hhead; subst i h.
    exists r; repeat split; try assumption.
    + apply nth_error_In in Hnth; exact Hnth.
    + rewrite rule_at_spec; exact Hnth.
  - apply in_map_iff in Hbad as [f [Hbad _]]; discriminate.
Qed.

Lemma rule_constraint_member {P} (prog : program P) facts st k r :
  In r (rules prog) -> level st (pred (head r)) = k ->
  exists i, In (Constraint.FromRule i (pred (head r)))
    (stratum_constraints prog facts st k) /\ rule_at (rules prog) i = Some r.
Proof.
  intros Hr Hl; apply In_nth_error in Hr as [i Hi].
  exists i; split; [|rewrite rule_at_spec; exact Hi].
  rewrite stratum_constraints_equation; apply in_app_iff; left.
  apply rule_constraints_spec; exists i, r; auto.
Qed.

Lemma fact_constraint_member {P} (prog : program P) facts st k p ts :
  In (p, ts) facts -> level st p = k ->
  In (Constraint.FromFact p) (stratum_constraints prog facts st k).
Proof.
  intros Hfact Hl; rewrite stratum_constraints_equation; apply in_app_iff; right.
  apply in_map_iff; exists (p, ts); split; [reflexivity |].
  apply filter_In; split; [exact Hfact | cbn; rewrite Hl; apply Nat.eqb_refl].
Qed.

Lemma fact_constraint_level {P} (prog : program P) facts st k p :
  In (Constraint.FromFact p) (stratum_constraints prog facts st k) -> level st p = k.
Proof.
  rewrite stratum_constraints_equation, in_app_iff; intros [Hbad | Hin].
  - apply rule_constraints_spec in Hbad as [i [r [_ [_ Hbad]]]]; discriminate.
  - apply in_map_iff in Hin as [[q ts] [Heq Hin]]; cbn in Heq; injection Heq as <-.
    apply filter_In in Hin as [_ Hl]; apply Nat.eqb_eq, Hl.
Qed.

Lemma read_value_grows {P} (E : encoding P) (HE : encoding_laws E) ds s u :
  fun_leb relation_lattice s u -> forall p,
  leb relation_lattice (read_value E ds (map s ds) p) (read_value E ds (map u ds) p) = true.
Proof.
  intros Hle p; destruct (in_dec (eqb_dec E HE) p ds) as [Hin | Hout].
  - rewrite !read_value_member by assumption; apply Hle.
  - rewrite !read_value_absent.
    + apply (leb_refl relation_laws).
    + intros q Hq; apply (eqb_false_iff E HE); intro Heq; subst q; contradiction.
    + intros q Hq; apply (eqb_false_iff E HE); intro Heq; subst q; contradiction.
Qed.

Lemma rule_env_grows {P} (prog : program P) (HE : encoding_laws (penc prog))
    st lower k s u r :
  fun_leb relation_lattice s u -> forall p,
  leb relation_lattice (Cost.value (rule_env prog st lower k s r p))
    (Cost.value (rule_env prog st lower k u r p)) = true.
Proof.
  intros Hle p.
  change (leb relation_lattice
    (stratum_env prog st lower k (level_dependencies st k r)
      (map s (level_dependencies st k r)) p)
    (stratum_env prog st lower k (level_dependencies st k r)
      (map u (level_dependencies st k r)) p) = true).
  rewrite !stratum_env_equation; destruct (Nat.eqb (level st p) k).
  - apply read_value_grows; assumption.
  - apply (leb_refl relation_laws).
Qed.

(** Rule firing is monotone in positives when the negative observations are fixed. *)
Theorem fire_rule_monotone {P} (prog : program P) r env env' :
  safe_rule r ->
  (forall a, In (LPos a) (body r) ->
    leb relation_lattice (Cost.value (env (pred a))) (Cost.value (env' (pred a))) = true) ->
  (forall a, In (LNeg a) (body r) -> forall ts,
    member ts (Cost.value (env (pred a))) = member ts (Cost.value (env' (pred a)))) ->
  leb relation_lattice (fire_rule prog r env) (fire_rule prog r env') = true.
Proof.
  intros Hsafe Hpos Hneg; apply relation_leb; intros ts Hmem.
  apply (proj1 (fire_rule_exact prog r env Hsafe ts)) in Hmem as [sigma [Hhead [Hp Hn]]].
  apply (proj2 (fire_rule_exact prog r env' Hsafe ts)).
  exists sigma; split; [exact Hhead | split].
  - intros a Ha; apply (proj1 (relation_leb _ _) (Hpos a Ha)), Hp, Ha.
  - intros a Ha.
    change (member (map (inst sigma) (args a)) (Cost.value (env' (pred a))) = false).
    rewrite <- (Hneg a Ha); apply Hn, Ha.
Qed.

(** Fixing all lower relations makes a well-formed stratified compiled system monotone. *)
Theorem stratum_system_monotone {P} (prog : program P) facts st lower k :
  encoding_laws (penc prog) -> program_wf prog facts -> stratified prog st ->
  monotone_system relation_lattice (stratum_system prog facts st lower k).
Proof.
  intros HE [Hrules _] [_ Hstrat] [i h | p] Hc.
  - destruct (rule_constraint_view prog facts st k i h Hc) as [r [Hr [Hh [Hl Hi]]]].
    subst h; split.
    + intros s u Hle.
      rewrite (rule_rhs_eval prog facts st lower k s i (pred (head r)) r Hi),
        (rule_rhs_eval prog facts st lower k u i (pred (head r)) r Hi).
      apply fire_rule_monotone.
      * exact (proj1 (Hrules r Hr)).
      * intros a _; apply rule_env_grows; assumption.
      * intros a Ha ts; rewrite !rule_env_lower; [reflexivity | |];
          pose proof (Hstrat r (LNeg a) Hr Ha); cbn in *; lia.
    + intros s u Hle x v Hin; rewrite stratum_sides_nil in Hin; contradiction.
  - split.
    + intros s u Hle; rewrite !stratum_rhs_equation; apply (leb_refl relation_laws).
    + intros s u Hle x v Hin; rewrite stratum_sides_nil in Hin; contradiction.
Qed.

(** Safety keeps every fired tuple in the proof-only source universe. *)
Theorem fire_rule_support {P} (prog : program P) facts r env :
  safe_rule r -> In r (rules prog) ->
  (forall p, within_set tuple_encoding (universe prog facts) (Cost.value (env p))) ->
  within_set tuple_encoding (universe prog facts) (fire_rule prog r env).
Proof.
  intros Hsafe Hr Henv ts Hmem.
  apply (proj1 (fire_rule_exact prog r env Hsafe ts)) in Hmem as [sigma [-> [Hpos _]]].
  apply head_universe; [exact Hsafe | exact Hr |].
  intros a Ha; exact (Henv (pred a) _ (Hpos a Ha)).
Qed.

Lemma read_value_support {P} (E : encoding P) ds vs U p :
  (forall v, In v vs -> within_set tuple_encoding U v) ->
  within_set tuple_encoding U (read_value E ds vs p).
Proof.
  revert vs; induction ds as [|q ds IH]; intros [|v vs] Hvs ts Hmem;
    try (change (member ts (bot relation_lattice) = true) in Hmem;
      rewrite relation_bot in Hmem; discriminate).
  unfold read_value in Hmem; cbn [read_value_c] in Hmem.
  repeat rewrite Cost.value_bind in Hmem; fold (eqb E p q) in Hmem.
  destruct (eqb E p q).
  - apply (Hvs v (or_introl eq_refl)), Hmem.
  - apply (IH vs); [intros w Hw; apply Hvs; now right | exact Hmem].
Qed.

Lemma rule_env_support {P} (prog : program P) facts st lower k s r :
  (forall p, within_set tuple_encoding (universe prog facts) (Cost.value (lower p))) ->
  (forall p, within_set tuple_encoding (universe prog facts) (s p)) ->
  forall p, within_set tuple_encoding (universe prog facts)
    (Cost.value (rule_env prog st lower k s r p)).
Proof.
  intros Hlower Hs p.
  change (within_set tuple_encoding (universe prog facts)
    (stratum_env prog st lower k (level_dependencies st k r)
      (map s (level_dependencies st k r)) p)).
  rewrite stratum_env_equation; destruct (Nat.eqb (level st p) k); [|apply Hlower].
  apply read_value_support; intros v Hv; apply in_map_iff in Hv as [q [<- _]]; apply Hs.
Qed.

(** Source safety and finite lower support give join-closed finite-height termination evidence. *)
Definition stratum_terminates {P} (prog : program P) facts st lower k
    (HE : encoding_laws (penc prog)) (Hwf : program_wf prog facts)
    (Hlower : forall p,
      within_set tuple_encoding (universe prog facts) (Cost.value (lower p))) :
    Terminates.t (stratum_analysis prog facts st lower k).
Proof.
  refine (@Terminates.Finite P (Constraint.t P) relation
    (stratum_analysis prog facts st lower k)
    (within_set tuple_encoding (universe prog facts))
    (relation_height_on (universe prog facts)) _ _ _).
  - exact (bot_inv (within_set_closed tuple_encoding (universe prog facts))).
  - exact (join_inv (within_set_closed tuple_encoding (universe prog facts))).
  - intros s Hs c Hc [p ts] Hin.
    change (In (p, ts) (fst (Eval.outputs (stratum_system prog facts st lower k) c s)))
      in Hin.
    rewrite Eval.outputs_spec, stratum_sides_nil in Hin; cbn [fst] in Hin.
    destruct Hin as [Heq | Hbad]; [|contradiction].
    injection Heq as <- <-.
    destruct c as [i h | p].
    + destruct (rule_constraint_view prog facts st k i h Hc) as [r [Hr [_ [_ Hi]]]].
      rewrite (rule_rhs_eval prog facts st lower k s i h r Hi).
      apply fire_rule_support; [exact (proj1 (proj1 Hwf r Hr)) | exact Hr |].
      apply rule_env_support; assumption.
    + rewrite stratum_rhs_equation; intros us Hus.
      apply (facts_at_exact prog HE) in Hus; apply fact_universe with (f := (p, us)), Hus.
Defined.

Lemma derives_support {P} (prog : program P) facts st k lower :
  program_wf prog facts -> stratified prog st ->
  (forall f, lower f -> In (snd f) (universe prog facts)) ->
  forall f, derives prog facts st k lower f -> In (snd f) (universe prog facts).
Proof.
  intros Hwf [_ Hstrat] Hlower f Hderive.
  induction Hderive as [f Hfact Hl | r sigma Hr Hl Hlow Hsame IH Hneg].
  - apply fact_universe, Hfact.
  - apply head_universe; [exact (proj1 (proj1 Hwf r Hr)) | exact Hr |].
    intros a Ha; pose proof (Hstrat r (LPos a) Hr Ha) as Hle; cbn in Hle.
    destruct (Nat.eq_dec (level st (pred a)) k) as [Heq | Hne].
    + exact (IH a Ha Heq).
    + apply (Hlower (ground sigma a)), Hlow; [exact Ha | lia].
Qed.

(** Every model tuple has source-universe support. *)
Theorem model_constants {P} (prog : program P) facts st :
  program_wf prog facts -> stratified prog st ->
  forall n f, model_below prog facts st n f -> In (snd f) (universe prog facts).
Proof.
  intros Hwf Hst n; induction n as [|n IH]; intros f Hmodel; [contradiction |].
  destruct Hmodel as [Hbelow | Hderive]; [apply IH, Hbelow |].
  eapply derives_support; eassumption.
Qed.
