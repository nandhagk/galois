(** * Priority worklist correctness

    The membership set agrees with live heap contents and every unqueued row is stable.
    For example, a changed read invalidates a row before the next empty-queue probe.
    Builds on: FixpointWorklist, FixpointLeast and the public heap and set contracts. *)

From Stdlib Require Import List Bool Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver FixpointLeast FixpointWorklist.
Import List.ListNotations.

Module WorklistProof.

(** Membership observes exactly the live keys, including on persistent heap versions. *)
Definition present {C} (EC : encoding C) (q : Heap.t C) c :=
  match Heap.priority EC c q with
  | Some _ => true
  | None => false
  end.

(** Structural validity couples the membership cache to the heap and validates both maps. *)
Record structural {X C A} (a : Analysis.t X C A) (s : Worklist.state X C A) : Prop := {
  values_wf : Map.wf (Analysis.key_enc a) (Worklist.current s);
  delays_wf : Map.wf (Analysis.key_enc a) (Worklist.delays s);
  heap_wf : Heap.wf (Analysis.row_enc a) (Worklist.queue s);
  queued_wf : FinSet.wf (Analysis.row_enc a) (Worklist.queued s);
  queued_live : forall c, FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) =
    present (Analysis.row_enc a) (Worklist.queue s) c
}.

Arguments values_wf {X C A a s}.
Arguments delays_wf {X C A a s}.
Arguments heap_wf {X C A a s}.
Arguments queued_wf {X C A a s}.
Arguments queued_live {X C A a s}.

(** Stability bounds every ordered output of a row at the current assignment. *)
Definition stable {X C A} (a : Analysis.t X C A) c m :=
  forall x value, In (x, value)
    (fst (Eval.outputs (Analysis.system a) c
      (lookup (Analysis.key_enc a) (Analysis.lat a) m))) ->
    leb (Analysis.lat a) value (lookup (Analysis.key_enc a) (Analysis.lat a) m x) = true.

(** The invariant includes index validity, finite queue support and stability outside the queue. *)
Record worklist_invariant {X C A} (a : Analysis.t X C A) ix s : Prop := {
  valid_index : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix;
  valid_state : structural a s;
  queue_listed : forall c, FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = true ->
    In c (System.constraints (Analysis.system a));
  unqueued_stable : forall c, In c (System.constraints (Analysis.system a)) ->
    FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = false ->
    stable a c (Worklist.current s)
}.

Arguments valid_index {X C A a ix s}.
Arguments valid_state {X C A a ix s}.
Arguments queue_listed {X C A a ix s}.
Arguments unqueued_stable {X C A a ix s}.

Section Queue.
Context {X C A : Type} (a : Analysis.t X C A)
  (HE : encoding_laws (Analysis.row_enc a)).
Let EC := Analysis.row_enc a.

Local Lemma present_push p c q d :
  Heap.wf EC q ->
  present EC (Heap.push EC p c q) d = eqb EC d c || present EC q d.
Proof.
  intro Hwf; unfold present; rewrite Heap.priority_push by exact Hwf.
  destruct (eqb EC d c), (Heap.priority EC c q); reflexivity.
Qed.

(** Single enqueue preserves structural validity and changes membership by set union. *)
Theorem enqueue_one_properties c s :
  structural a s ->
  structural a (Worklist.enqueue_one a c s) /\
  Worklist.current (Worklist.enqueue_one a c s) = Worklist.current s /\
  Worklist.delays (Worklist.enqueue_one a c s) = Worklist.delays s /\
  Worklist.evaluations (Worklist.enqueue_one a c s) = Worklist.evaluations s /\
  forall d, FinSet.mem EC d (Worklist.queued (Worklist.enqueue_one a c s)) =
    eqb EC d c || FinSet.mem EC d (Worklist.queued s).
Proof.
  intro Hs; rewrite Worklist.enqueue_one_equation; fold EC.
  destruct (FinSet.mem EC c (Worklist.queued s)) eqn:Hpresent.
  - split; [exact Hs|].
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    intro d; destruct (eqb EC d c) eqn:Heq; [|now rewrite orb_false_l].
    apply (eqb_true_iff EC HE) in Heq; subst d; now rewrite Hpresent.
  - split.
    + constructor; cbn [Worklist.current Worklist.delays Worklist.queue Worklist.queued].
      * exact (values_wf Hs).
      * exact (delays_wf Hs).
      * apply Heap.wf_push, (heap_wf Hs).
      * apply FinSet.wf_add, (queued_wf Hs).
      * intro d; rewrite FinSet.mem_add by exact (queued_wf Hs).
        rewrite present_push by exact (heap_wf Hs).
        now rewrite (queued_live Hs).
    + split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
      intro d; apply FinSet.mem_add, (queued_wf Hs).
Qed.

(** Enqueue preserves maps and counts, and its membership theorem retains all listed occurrences. *)
Theorem enqueue_properties cs s :
  structural a s ->
  structural a (Worklist.enqueue a cs s) /\
  Worklist.current (Worklist.enqueue a cs s) = Worklist.current s /\
  Worklist.delays (Worklist.enqueue a cs s) = Worklist.delays s /\
  Worklist.evaluations (Worklist.enqueue a cs s) = Worklist.evaluations s /\
  forall d, FinSet.mem EC d (Worklist.queued (Worklist.enqueue a cs s)) = true <->
    In d cs \/ FinSet.mem EC d (Worklist.queued s) = true.
Proof.
  revert s; induction cs as [|c cs IH]; intros s Hs; rewrite Worklist.enqueue_equation.
  - split; [exact Hs|].
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    cbn; tauto.
  - destruct (enqueue_one_properties c s Hs) as [Hone [Hm [Hd [He Hmem]]]].
    destruct (IH _ Hone) as [Hrest [Hm' [Hd' [He' Hmem']]]].
    split; [exact Hrest|].
    rewrite Hm', Hd', He', Hm, Hd, He.
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
    intro d; rewrite Hmem', Hmem, orb_true_iff, (eqb_true_iff EC HE).
    cbn; intuition congruence.
Qed.

(** Removing the popped key preserves the structural cache invariant. *)
Theorem popped_structural s p c q :
  structural a s -> Heap.pop EC (Worklist.queue s) = Some (p, c, q) ->
  structural a (Worklist.State (Worklist.current s) q
    (FinSet.remove EC c (Worklist.queued s)) (Worklist.delays s)
    (S (Worklist.evaluations s))).
Proof.
  intros Hs Hpop; constructor; cbn.
  - exact (values_wf Hs).
  - exact (delays_wf Hs).
  - eapply Heap.wf_pop; [exact (heap_wf Hs)|exact Hpop].
  - apply FinSet.wf_remove, (queued_wf Hs).
  - intro d; rewrite FinSet.mem_remove by exact (queued_wf Hs).
    unfold present; rewrite (Heap.pop_removes EC _ _ _ _ Hpop).
    destruct (eqb EC d c); [reflexivity|apply (queued_live Hs)].
Qed.

End Queue.

Section Updates.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let P := Analysis.policy a.
Let look := lookup EX L.
Let pending (s : Worklist.state X C A) c := FinSet.mem EC c (Worklist.queued s).

Local Lemma operation_bounds x n old value :
  leb L old (Cost.value (Worklist.operation_c a x n old value)) = true /\
  leb L value (Cost.value (Worklist.operation_c a x n old value)) = true.
Proof.
  rewrite Worklist.operation_equation; fold P L.
  destruct (Policy.widen_at P x), n;
    split; first [apply (join_upper_l (Analysis.lattice_law HL)) |
      apply (join_upper_r (Analysis.lattice_law HL)) |
      apply (widen_upper_l (Analysis.lattice_law HL)) |
      apply (widen_upper_r (Analysis.lattice_law HL))].
Qed.

(** A single update raises values, bounds its contribution and requeues every changed reader. *)
Theorem update_properties s x value :
  structural a s ->
  let next := Worklist.update a ix s (x, value) in
  structural a next /\
  fun_leb L (look (Worklist.current s)) (look (Worklist.current next)) /\
  leb L value (look (Worklist.current next) x) = true /\
  (forall c, pending s c = true -> pending next c = true) /\
  (forall c y, In c (readers_of EX ix y) -> pending next c = false ->
    look (Worklist.current next) y = look (Worklist.current s) y) /\
  (forall c, pending next c = true -> pending s c = true \/ In c (readers_of EX ix x)) /\
  Worklist.evaluations next = Worklist.evaluations s.
Proof.
  intro Hs; cbn zeta; rewrite Worklist.update_equation; cbn zeta; fold EX EC L P look.
  set (n := Map.find_or EX (Policy.delay P) x (Worklist.delays s)).
  set (op := Worklist.operation_c a x n).
  pose proof (Update.rule_spec EX L op (Worklist.current s) x value (values_wf Hs))
    as [Hflag Hlookup].
  fold look in Hflag, Hlookup.
  destruct (leb L value (look (Worklist.current s) x)) eqn:Hbelow.
  - cbn [negb] in Hflag; rewrite Hflag.
    split; [exact Hs|]; split.
    + intro y; apply (leb_refl (Analysis.lattice_law HL)).
    + split; [exact Hbelow|]; split; [tauto|]; split; [reflexivity|].
      split; [tauto|reflexivity].
  - cbn [negb] in Hflag; rewrite Hflag.
    assert (Hbase : structural a
      (Worklist.State (fst (Update.rule EX L op (Worklist.current s) x value))
        (Worklist.queue s) (Worklist.queued s)
        (Map.set EX x (Nat.pred n) (Worklist.delays s)) (Worklist.evaluations s))).
    { constructor; cbn.
      - apply Update.rule_wf, (values_wf Hs).
      - apply Map.wf_set, (delays_wf Hs).
      - exact (heap_wf Hs).
      - exact (queued_wf Hs).
      - apply (queued_live Hs). }
    destruct (enqueue_properties a (Analysis.row_laws HL) (readers_of EX ix x) _ Hbase)
      as [Hnext [Hm [_ [He Hmem]]]].
    cbn [Worklist.current Worklist.queued Worklist.evaluations] in Hm, He, Hmem.
    split; [exact Hnext|]; rewrite Hm; split.
    + intro y; rewrite Hlookup.
      destruct (eqb EX y x) eqn:Hy.
      * apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hy; subst y.
        exact (proj1 (operation_bounds x n (look (Worklist.current s) x) value)).
      * apply (leb_refl (Analysis.lattice_law HL)).
    + split.
      * rewrite Hlookup, eqb_refl.
        exact (proj2 (operation_bounds x n (look (Worklist.current s) x) value)).
      * split.
        -- intros c Hc; apply Hmem; now right.
        -- split.
           ++ intros c y Hreader Hnone; rewrite Hlookup.
              destruct (eqb EX y x) eqn:Hy; [|reflexivity].
              apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hy; subst y.
              assert (Hyes : pending
                (Worklist.enqueue a (readers_of EX ix x)
                  (Worklist.State (fst (Update.rule EX L op (Worklist.current s) x value))
                    (Worklist.queue s) (Worklist.queued s)
                    (Map.set EX x (Nat.pred n) (Worklist.delays s)) (Worklist.evaluations s))) c
                  = true) by (apply Hmem; now left).
              congruence.
           ++ split.
              ** intros c Hc; apply Hmem in Hc; tauto.
              ** exact He.
Qed.

(** Ordered output application bounds every contribution and preserves every unqueued read. *)
Theorem updates_properties outs s :
  structural a s ->
  let next := Worklist.updates a ix outs s in
  structural a next /\
  fun_leb L (look (Worklist.current s)) (look (Worklist.current next)) /\
  (forall x value, In (x, value) outs -> leb L value (look (Worklist.current next) x) = true) /\
  (forall c, pending s c = true -> pending next c = true) /\
  (forall c y, In c (readers_of EX ix y) -> pending next c = false ->
    look (Worklist.current next) y = look (Worklist.current s) y) /\
  (forall c, pending next c = true -> pending s c = true \/
    exists x value, In (x, value) outs /\ In c (readers_of EX ix x)) /\
  Worklist.evaluations next = Worklist.evaluations s.
Proof.
  revert s; induction outs as [|[x value] outs IH]; intros s Hs; cbn zeta;
    rewrite Worklist.updates_equation.
  - split; [exact Hs|]; split.
    + intro y; apply (leb_refl (Analysis.lattice_law HL)).
    + split; [intros y v Hin; contradiction|]; split; [tauto|].
      split; [reflexivity|]; split; [tauto|reflexivity].
  - destruct (update_properties s x value Hs)
      as [Hone [Hup1 [Hbound [Hkeep1 [Hsame1 [Hsupport1 He1]]]]]].
    destruct (IH _ Hone) as [Hnext [Hup [Hbounds [Hkeep [Hsame [Hsupport He]]]]]].
    split; [exact Hnext|]; split.
    + intro y; eapply (leb_trans (Analysis.lattice_law HL)); [apply Hup1|apply Hup].
    + split.
      * intros y v [Heq|Hin].
        -- injection Heq as <- <-.
           eapply (leb_trans (Analysis.lattice_law HL)); [exact Hbound|apply Hup].
        -- apply Hbounds, Hin.
      * split; [intros c Hc; apply Hkeep, Hkeep1, Hc|]; split.
        -- intros c y Hreader Hnone; rewrite (Hsame c y Hreader Hnone).
           apply (Hsame1 c y Hreader).
           destruct (pending (Worklist.update a ix s (x, value)) c) eqn:Hc;
             [pose proof (Hkeep c Hc); congruence|reflexivity].
        -- split.
           ++ intros c Hc; destruct (Hsupport c Hc) as [Hmid|[y [v [Hin Hr]]]].
              ** destruct (Hsupport1 c Hmid) as [Hold|Hr]; [now left|].
                 right; exists x, value; split; [now left|exact Hr].
              ** right; exists y, v; split; [now right|exact Hr].
           ++ now rewrite He, He1.
Qed.

End Updates.

Section Invariant.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let look := lookup EX L.
Let pending (s : Worklist.state X C A) c := FinSet.mem EC c (Worklist.queued s).

Local Lemma outputs_agree c m n :
  (forall x, In x (Query.reads (System.rhs S c) (look m)) -> look m x = look n x) ->
  Eval.outputs S c (look m) = Eval.outputs S c (look n).
Proof.
  intro Hsame.
  destruct (Query.query_determined (System.rhs S c) (look m) (look n) Hsame)
    as [Hv [Hr Hs]].
  rewrite !Eval.outputs_spec, Hv, Hr, Hs; reflexivity.
Qed.

(** Requeueing every changed reader preserves stability of rows left outside the queue. *)
Theorem step_invariant s next :
  worklist_invariant a ix s -> Worklist.step a ix s = inl next ->
  worklist_invariant a ix next.
Proof.
  intros Hinv Hstep; pose proof (valid_state Hinv) as Hs.
  rewrite Worklist.step_equation in Hstep.
  fold EX EC L S look in Hstep.
  destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|] eqn:Hpop;
    [|discriminate].
  set (base := Worklist.State (Worklist.current s) q
    (FinSet.remove EC c (Worklist.queued s)) (Worklist.delays s)
    (Datatypes.S (Worklist.evaluations s))).
  set (outs := fst (Eval.outputs S c (look (Worklist.current s)))).
  assert (Hresult : next = Worklist.updates a ix outs base).
  { injection Hstep as Hresult; symmetry; exact Hresult. }
  subst next.
  assert (Hbase : structural a base).
  { apply (popped_structural a s p c q Hs Hpop). }
  assert (Hc : In c (System.constraints S)).
  { apply (queue_listed Hinv c).
    rewrite (queued_live Hs); unfold present; fold EC.
    rewrite (Heap.pop_priority EC (Analysis.row_laws HL) _ _ _ _ (heap_wf Hs) Hpop).
    reflexivity. }
  destruct (updates_properties a HL ix outs base Hbase)
    as [Hnext [Hup [Hbounds [Hkeep [Hsame [Hsupport Hevals]]]]]].
  constructor; [exact HI|exact Hnext| |].
  - intros d Hd; destruct (Hsupport d Hd) as [Hold|[x [value [Hout Hreader]]]].
    + apply (queue_listed Hinv d).
      unfold pending, base in Hold; cbn [Worklist.queued] in Hold.
      rewrite FinSet.mem_remove in Hold by exact (queued_wf Hs).
      destruct (eqb EC d c); [discriminate|exact Hold].
    + exact (proj1 (proj1 (readers_agree HI x d) Hreader)).
  - intros d Hd Hnone.
    assert (Hread : forall x, In x (Query.reads (System.rhs S d)
      (look (Worklist.current s))) -> In d (readers_of EX ix x)).
    { intros x Hx; apply (readers_agree HI); split; [exact Hd|].
      exact (System.reads_within (Analysis.static_law HL) d _ x Hx). }
    assert (Hagree : forall x, In x (Query.reads (System.rhs S d)
      (look (Worklist.current s))) ->
      look (Worklist.current s) x = look (Worklist.updates a ix outs base).(Worklist.current) x).
    { intros x Hx; symmetry; exact (Hsame d x (Hread x Hx) Hnone). }
    unfold stable; fold EX L S look.
    rewrite <- (outputs_agree d _ _ Hagree).
    destruct (eqb EC d c) eqn:Hdc.
    + apply (eqb_true_iff EC (Analysis.row_laws HL)) in Hdc; subst d.
      exact Hbounds.
    + assert (Hbase_none : pending base d = false).
      { destruct (pending base d) eqn:Hmem; [|reflexivity].
        pose proof (Hkeep d Hmem); congruence. }
      assert (Hold : pending s d = false).
      { unfold pending, base in Hbase_none; cbn [Worklist.queued] in Hbase_none.
        rewrite FinSet.mem_remove, Hdc in Hbase_none by exact (queued_wf Hs).
        exact Hbase_none. }
      intros x value Hin.
      eapply (leb_trans (Analysis.lattice_law HL)).
      * exact (unqueued_stable Hinv d Hd Hold x value Hin).
      * exact (Hup x).
Qed.

(** An empty heap under the invariant yields a post-solution of every listed row. *)
Theorem step_solved_sound s m :
  worklist_invariant a ix s -> Worklist.step a ix s = inr m ->
  post_solution L S (look m).
Proof.
  intros Hinv Hstep; rewrite Worklist.step_equation in Hstep.
  fold EX EC L S look in Hstep.
  destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|] eqn:Hpop;
    [discriminate|].
  injection Hstep as <-.
  assert (Hempty : forall c, Heap.priority EC c (Worklist.queue s) = None).
  { exact (Heap.pop_none_priority EC (Analysis.row_laws HL) _
      (heap_wf (valid_state Hinv)) Hpop). }
  intros c Hc.
  assert (Hnone : pending s c = false).
  { unfold pending; rewrite (queued_live (valid_state Hinv)); unfold present.
    fold EC.
    now rewrite Hempty. }
  pose proof (unqueued_stable Hinv c Hc Hnone) as Hstable.
  unfold stable in Hstable; rewrite Eval.outputs_spec in Hstable; cbn [fst] in Hstable.
  split.
  - apply Hstable; now left.
  - intros x value Hin; apply Hstable; now right.
Qed.

(** Initialization establishes cache agreement and queues every listed constraint. *)
Theorem initial_invariant : worklist_invariant a ix (Worklist.initial a).
Proof.
  rewrite Worklist.initial_equation.
  set (empty := @Worklist.State X C A Map.empty Heap.empty FinSet.empty Map.empty 0).
  assert (Hempty : structural a empty).
  { constructor; cbn.
    - apply Map.wf_empty.
    - apply Map.wf_empty.
    - apply Heap.wf_empty.
    - apply FinSet.wf_empty.
    - intro c; rewrite FinSet.mem_empty; unfold present.
      now rewrite Heap.priority_empty. }
  destruct (enqueue_properties a (Analysis.row_laws HL)
    (System.constraints S) empty Hempty) as [Hs [_ [_ [_ Hmem]]]].
  constructor; [exact HI|exact Hs| |].
  - intros c Hc; apply Hmem in Hc; destruct Hc as [Hc|Hbad]; [exact Hc|].
    cbn [empty Worklist.queued] in Hbad.
    rewrite FinSet.mem_empty in Hbad; discriminate.
  - intros c Hc Hnone.
    assert (Hyes : FinSet.mem EC c
      (Worklist.queued (Worklist.enqueue a (System.constraints S) empty)) = true).
    { apply Hmem; now left. }
    fold S EC empty in Hnone; rewrite Hyes in Hnone; discriminate.
Qed.

(** Every actual binary-driver result retains the invariant or is a post-solution. *)
Theorem runs_sound fuel s result :
  runs (Worklist.step_c a ix) fuel s result -> worklist_invariant a ix s ->
  match result with
  | inl next => worklist_invariant a ix next
  | inr done => post_solution L S (look done)
  end.
Proof.
  intro Hrun; induction Hrun as [s|n s m Hstop|n s next result Hnext Hrun IH];
    intro Hinv.
  - exact Hinv.
  - exact (step_solved_sound s m Hinv Hstop).
  - apply IH; exact (step_invariant s next Hinv Hnext).
Qed.

End Invariant.

Section Joining.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HJ : Analysis.joining a)
  (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.

Local Lemma joining_rule (s : Worklist.state X C A) x value :
  Update.rule EX L (Worklist.operation_c a x
    (Map.find_or EX (Policy.delay (Analysis.policy a)) x (Worklist.delays s)))
    (Worklist.current s) x value =
  Update.rule EX L (join_c L) (Worklist.current s) x value.
Proof.
  rewrite !Update.rule_equation.
  destruct (leb L value (lookup EX L (Worklist.current s) x)); [reflexivity|].
  rewrite Worklist.operation_equation, HJ; reflexivity.
Qed.

Local Lemma update_joining s x value :
  structural a s ->
  Worklist.current (Worklist.update a ix s (x, value)) =
    fst (Update.rule EX L (join_c L) (Worklist.current s) x value).
Proof.
  intro Hs; rewrite Worklist.update_equation; cbn zeta; fold EX L.
  rewrite joining_rule.
  destruct (snd (Update.rule EX L (join_c L) (Worklist.current s) x value)) eqn:Hchange.
  - assert (Hbase : structural a
      (Worklist.State (fst (Update.rule EX L (join_c L) (Worklist.current s) x value))
        (Worklist.queue s) (Worklist.queued s)
        (Map.set EX x
          (Nat.pred (Map.find_or EX (Policy.delay (Analysis.policy a)) x (Worklist.delays s)))
          (Worklist.delays s)) (Worklist.evaluations s))).
    { constructor; cbn.
      - apply Update.rule_wf, (values_wf Hs).
      - apply Map.wf_set, (delays_wf Hs).
      - exact (heap_wf Hs).
      - exact (queued_wf Hs).
      - apply (queued_live Hs). }
    exact (proj1 (proj2
      (enqueue_properties a (Analysis.row_laws HL) (readers_of EX ix x) _ Hbase))).
  - symmetry; apply Update.rule_unchanged, Hchange.
Qed.

(** Joining output application agrees exactly with the shared update fold on maps. *)
Theorem updates_joining outs s :
  structural a s ->
  Worklist.current (Worklist.updates a ix outs s) =
    fst (Update.apply EX L (join_c L) outs (Worklist.current s)).
Proof.
  revert s; induction outs as [|[x value] outs IH]; intros s Hs.
  - rewrite Worklist.updates_equation, Update.apply_equation; reflexivity.
  - rewrite Worklist.updates_equation, Update.apply_equation; cbn [fst].
    rewrite IH.
    + now rewrite update_joining.
    + exact (proj1 (update_properties a HL ix s x value Hs)).
Qed.

(** Each continuing joining callback is one listed raise on the actual frozen inputs. *)
Theorem step_raise s next :
  worklist_invariant a ix s -> Worklist.step a ix s = inl next ->
  raise EX L S (Worklist.current s) (Worklist.current next).
Proof.
  intros Hinv Hstep; rewrite Worklist.step_equation in Hstep; fold EX EC L S in Hstep.
  destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|] eqn:Hpop;
    [|discriminate].
  injection Hstep as <-.
  split; [exact (values_wf (valid_state Hinv))|]; exists c; split.
  - apply (queue_listed Hinv c); rewrite (queued_live (valid_state Hinv)).
    unfold present; fold EC.
    rewrite (Heap.pop_priority EC (Analysis.row_laws HL) _ _ _ _
      (heap_wf (valid_state Hinv)) Hpop); reflexivity.
  - rewrite updates_joining.
    + rewrite raise_equation; reflexivity.
    + exact (popped_structural a s p c q (valid_state Hinv) Hpop).
Qed.

Local Lemma runs_reached n s result :
  runs (Worklist.step_c a ix) n s result ->
  worklist_invariant a ix s ->
  clos_refl_trans (assignment X A) (raise EX L S) Map.empty (Worklist.current s) ->
  match result with
  | inl next =>
    clos_refl_trans (assignment X A) (raise EX L S) Map.empty (Worklist.current next)
  | inr done => clos_refl_trans (assignment X A) (raise EX L S) Map.empty done
  end.
Proof.
  intro Hrun; induction Hrun as [s|n s m Hstop|n s next result Hnext Hrun IH];
    intros Hinv Hreach.
  - exact Hreach.
  - fold (Worklist.step a ix s) in Hstop.
    rewrite Worklist.step_equation in Hstop; fold EC in Hstop.
    destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|]; [discriminate|].
    injection Hstop as <-; exact Hreach.
  - apply IH.
    + exact (step_invariant a HL ix HI s next Hinv Hnext).
    + eapply rt_trans; [exact Hreach|apply rt_step].
      exact (step_raise s next Hinv Hnext).
Qed.

End Joining.

(** Initialization has an empty assignment and has evaluated no constraint. *)
Theorem initial_frames {X C A} (a : Analysis.t X C A) :
  encoding_laws (Analysis.row_enc a) ->
  Worklist.current (Worklist.initial a) = Map.empty /\
  Worklist.evaluations (Worklist.initial a) = 0.
Proof.
  intro HE; rewrite Worklist.initial_equation.
  set (s := @Worklist.State X C A Map.empty Heap.empty FinSet.empty Map.empty 0).
  assert (Hs : structural a s).
  { constructor; cbn.
    - apply Map.wf_empty.
    - apply Map.wf_empty.
    - apply Heap.wf_empty.
    - apply FinSet.wf_empty.
    - intro c; rewrite FinSet.mem_empty; unfold present; now rewrite Heap.priority_empty. }
  destruct (enqueue_properties a HE (System.constraints (Analysis.system a)) s Hs)
    as [_ [Hm [_ [He _]]]].
  split; assumption.
Qed.

(** Every unknown begins with the policy delay because the initialized counter map is empty. *)
Theorem initial_delays {X C A} (a : Analysis.t X C A) :
  encoding_laws (Analysis.row_enc a) ->
  Worklist.delays (Worklist.initial a) = Map.empty.
Proof.
  intro HE; rewrite Worklist.initial_equation.
  set (s := @Worklist.State X C A Map.empty Heap.empty FinSet.empty Map.empty 0).
  assert (Hs : structural a s).
  { constructor; cbn.
    - apply Map.wf_empty.
    - apply Map.wf_empty.
    - apply Heap.wf_empty.
    - apply FinSet.wf_empty.
    - intro c; rewrite FinSet.mem_empty; unfold present; now rewrite Heap.priority_empty. }
  exact (proj1 (proj2 (proj2
    (enqueue_properties a HE (System.constraints (Analysis.system a)) s Hs)))).
Qed.

(** Every solved priority run satisfies the full solver soundness and joining reachability laws. *)
Theorem worklist_solver_laws {X C A} : Solver.laws (@Worklist.solver X C A).
Proof.
  constructor.
  - intros a fuel m HL Hrun.
    change (Worklist.run a fuel = Outcome.Solved m) in Hrun.
    rewrite Worklist.run_equation in Hrun.
    set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
    assert (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
    { apply index_system_laws, (Analysis.key_laws HL). }
    pose proof (runs_sound a HL ix HI _ _ _
      (iterate_value (Worklist.step_c a ix) fuel (Worklist.initial a))
      (initial_invariant a HL ix HI)) as Hsound.
    fold ix in Hrun.
    destruct (Cost.value (iterate _ _ _)) as [next|done]; [discriminate|].
    injection Hrun as <-; exact Hsound.
  - intros a fuel m HL Hlub Hjoin Hrun.
    change (Worklist.run a fuel = Outcome.Solved m) in Hrun.
    rewrite Worklist.run_equation in Hrun.
    set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
    assert (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
    { apply index_system_laws, (Analysis.key_laws HL). }
    pose proof (proj1 (initial_frames a (Analysis.row_laws HL))) as Hempty.
    pose proof (runs_reached a HL Hjoin ix HI _ _ _
      (iterate_value (Worklist.step_c a ix) fuel (Worklist.initial a))
      (initial_invariant a HL ix HI) ltac:(rewrite Hempty; apply rt_refl)) as Hreached.
    fold ix in Hrun.
    destruct (Cost.value (iterate _ _ _)) as [next|done]; [discriminate|].
    injection Hrun as <-; exists done; split; [exact Hreached|reflexivity].
Qed.

(** A solved joining run of a monotone system is the reached least post-solution. *)
Theorem worklist_reached_least {X C A} (a : Analysis.t X C A) fuel m :
  Analysis.laws a -> lub_laws (Analysis.lat a) -> Analysis.joining a ->
  monotone_system (Analysis.lat a) (Analysis.system a) ->
  Worklist.run a fuel = Outcome.Solved m ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m) /\
  least_solution (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) m).
Proof.
  intros HL Hlub Hjoin Hmono Hrun.
  pose proof (Solver.solved_reached worklist_solver_laws a fuel m HL Hlub Hjoin Hrun)
    as Hreached.
  split; [exact Hreached|].
  apply (reached_least (Analysis.key_enc a) (Analysis.key_laws HL)
    (Analysis.lat a) (Analysis.system a) _ (Analysis.lattice_law HL) Hlub Hmono Hreached).
  exact (Solver.solved_sound worklist_solver_laws a fuel m HL Hrun).
Qed.

End WorklistProof.
Import WorklistProof.
