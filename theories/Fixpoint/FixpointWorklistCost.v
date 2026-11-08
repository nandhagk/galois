(** * Joining worklist credit

    Queue entries and unused invariant-relative ranks pay for actual constraint evaluations.
    For example, an output with three reader occurrences spends three credits when it changes.
    Builds on: FixpointWorklistProof, LatticeHeight and FixpointKleene's declared output list. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointIndex
  FixpointIndexCost FixpointAnalysis FixpointSolver FixpointKleene FixpointWorklist
  FixpointWorklistProof.
Import List.ListNotations WorklistProof.

Local Open Scope nat_scope.

Module WorklistCost.

(** The proof sum retains occurrence multiplicity. *)
Definition sum {B} (f : B -> nat) xs := fold_right (fun x n => f x + n) 0 xs.

(** Pointwise bounds lift to occurrence sums. *)
Theorem sum_le {B} (f g : B -> nat) xs :
  (forall x, In x xs -> f x <= g x) -> sum f xs <= sum g xs.
Proof.
  induction xs as [|x xs IH]; intro Hle; [reflexivity|].
  change (f x + sum f xs <= g x + sum g xs).
  apply Nat.add_le_mono.
  - apply Hle; now left.
  - apply IH; intros y Hy; apply Hle; now right.
Qed.

(** One selected occurrence pays its local drop and every other occurrence remains nonincreasing. *)
Theorem sum_drop {B} (f g : B -> nat) xs x amount :
  In x xs -> (forall y, In y xs -> g y <= f y) ->
  g x + amount <= f x -> sum g xs + amount <= sum f xs.
Proof.
  induction xs as [|y xs IH]; intros Hin Hle Hdrop; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst y; pose proof (sum_le g f xs (fun z Hz => Hle z (or_intror Hz))) as Htail.
    change (g x + sum g xs + amount <= f x + sum f xs); lia.
  - specialize (IH Hin (fun z Hz => Hle z (or_intror Hz)) Hdrop).
    pose proof (Hle y (or_introl eq_refl)) as Hhead.
    change (g y + sum g xs + amount <= f y + sum f xs); lia.
Qed.

Local Lemma subtraction_credit n old next :
  old < next -> next <= n -> n - next + 1 <= n - old.
Proof.
  lia.
Qed.

Local Lemma sum_capacity {B} (rank degree : B -> nat) xs height :
  sum (fun x => (height - rank x) * degree x) xs <= height * sum degree xs.
Proof.
  induction xs as [|x xs IH]; [change (0 <= height * 0); lia|].
  change ((height - rank x) * degree x +
    sum (fun y => (height - rank y) * degree y) xs <=
    height * (degree x + sum degree xs)).
  nia.
Qed.

(** C counts original constraint occurrences even though initialization deduplicates live keys. *)
Definition constraint_count {X C A} (a : Analysis.t X C A) :=
  length (System.constraints (Analysis.system a)).

(** Rank support contains declared output occurrences, including repeated targets and rows. *)
Definition unknowns {X C A} (a : Analysis.t X C A) :=
  Kleene.output_keys (Analysis.system a) (Analysis.static a)
    (System.constraints (Analysis.system a)).

(** D counts reader-bucket occurrences once per declared output occurrence in the rank support. *)
Definition dependency_count {X C A} (a : Analysis.t X C A) (ix : sys_index X C) :=
  sum (fun x => length (readers_of (Analysis.key_enc a) ix x)) (unknowns a).

(** D is the exact length of the corresponding flattened prepared reader lists. *)
Theorem dependency_count_spec {X C A} (a : Analysis.t X C A) ix :
  dependency_count a ix =
    length (flat_map (readers_of (Analysis.key_enc a) ix) (unknowns a)).
Proof.
  unfold dependency_count; induction (unknowns a) as [|x xs IH].
  - reflexivity.
  - cbn [sum fold_right flat_map]; rewrite length_app, <- IH; reflexivity.
Qed.

(** Prepared D agrees with declared reader incidences and retains repeated row occurrences. *)
Theorem dependency_declared_spec {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.key_enc a)) :
  dependency_count a
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) =
  length (flat_map (fun x =>
    filter (fun c => existsb (eqb (Analysis.key_enc a) x) (deps (Analysis.static a) c))
      (System.constraints (Analysis.system a))) (unknowns a)).
Proof.
  rewrite dependency_count_spec.
  assert (Hlists :
    flat_map (readers_of (Analysis.key_enc a)
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))) (unknowns a) =
    flat_map (fun x =>
      filter (fun c => existsb (eqb (Analysis.key_enc a) x) (deps (Analysis.static a) c))
        (System.constraints (Analysis.system a))) (unknowns a)).
  { induction (unknowns a) as [|x xs IH]; [reflexivity|].
    cbn [flat_map]; rewrite (readers_occurrences (Analysis.key_enc a) HE
      (Analysis.system a) (Analysis.static a) x), IH; reflexivity. }
  now rewrite Hlists.
Qed.

(** A member's nonnegative contribution is bounded by the complete occurrence sum. *)
Theorem sum_member {B} (f : B -> nat) xs x :
  In x xs -> f x <= sum f xs.
Proof.
  induction xs as [|y xs IH]; intro Hin; [contradiction|].
  change (f x <= f y + sum f xs).
  destruct Hin as [Heq|Hin]; [subst y; lia|specialize (IH Hin); lia].
Qed.

(** Every mutable output's actual reader bucket length is bounded by D. *)
Theorem reader_degree_bound {X C A} (a : Analysis.t X C A) ix x :
  In x (unknowns a) ->
  length (readers_of (Analysis.key_enc a) ix x) <= dependency_count a ix.
Proof.
  intro Hx; exact (sum_member
    (fun y => length (readers_of (Analysis.key_enc a) ix y)) (unknowns a) x Hx).
Qed.

(** Supported queues contain only declared rows and keep the structural membership coupling. *)
Definition queue_supported {X C A} (a : Analysis.t X C A) (s : Worklist.state X C A) :=
  structural a s /\ forall c,
    FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = true ->
    In c (System.constraints (Analysis.system a)).

(** Every live row after enqueue comes from the old support or the actual additions list. *)
Theorem enqueue_supported {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.row_enc a)) cs s :
  queue_supported a s -> incl cs (System.constraints (Analysis.system a)) ->
  queue_supported a (Worklist.enqueue a cs s).
Proof.
  intros [Hs Hlisted] Hcs.
  destruct (enqueue_properties a HE cs s Hs) as [Hnext [_ [_ [_ Hmem]]]].
  split; [exact Hnext|].
  intros c Hc; apply Hmem in Hc; destruct Hc as [Hnew|Hold].
  - apply Hcs, Hnew.
  - apply Hlisted, Hold.
Qed.

(** Any actual output fold preserves queue support through the public reader membership contract. *)
Theorem updates_supported {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) ix outs s :
  sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix ->
  queue_supported a s -> queue_supported a (Worklist.updates a ix outs s).
Proof.
  intros HI [Hs Hlisted].
  destruct (updates_properties a HL ix outs s Hs) as [Hnext [_ [_ [_ [_ [Hsupport _]]]]]].
  split; [exact Hnext|]; intros c Hc.
  destruct (Hsupport c Hc) as [Hold|[x [value [_ Hr]]]].
  - apply Hlisted, Hold.
  - exact (proj1 (proj1 (readers_agree HI x c) Hr)).
Qed.

(** Clean queues have no stale entries and their pending count equals their live size. *)
Definition clean {X C A} (s : Worklist.state X C A) :=
  Heap.stale (Worklist.queue s) = 0 /\
  Heap.pending_count (Worklist.queue s) = Heap.size (Worklist.queue s).

Local Lemma unqueued_absent {X C A} (a : Analysis.t X C A) s c :
  structural a s ->
  FinSet.mem (Analysis.row_enc a) c (Worklist.queued s) = false ->
  Heap.priority (Analysis.row_enc a) c (Worklist.queue s) = None.
Proof.
  intros Hs Hnone; rewrite (queued_live Hs) in Hnone; unfold present in Hnone.
  destruct (Heap.priority _ _ _) eqn:Hpriority; [discriminate|reflexivity].
Qed.

(** The membership guard makes every actual push absent and creates no stale entries. *)
Theorem enqueue_one_clean {X C A} (a : Analysis.t X C A) c s :
  structural a s -> clean s -> clean (Worklist.enqueue_one a c s).
Proof.
  intros Hs [Hzero Hcount]; rewrite Worklist.enqueue_one_equation.
  destruct (FinSet.mem (Analysis.row_enc a) c (Worklist.queued s)) eqn:Hmem.
  - now split.
  - pose proof (unqueued_absent a s c Hs Hmem) as Habsent.
    unfold clean; cbn [Worklist.queue].
    rewrite Heap.stale_push_absent, Heap.pending_count_push_absent by exact Habsent.
    rewrite Heap.size_push, Habsent by exact (heap_wf Hs).
    now rewrite Hzero, Hcount.
Qed.

(** Every repeated enqueue occurrence either skips or preserves zero staleness. *)
Theorem enqueue_clean {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.row_enc a)) cs s :
  structural a s -> clean s -> clean (Worklist.enqueue a cs s).
Proof.
  revert s; induction cs as [|c cs IH]; intros s Hs Hclean;
    rewrite Worklist.enqueue_equation.
  - exact Hclean.
  - apply IH.
    + exact (proj1 (enqueue_one_properties a HE c s Hs)).
    + exact (enqueue_one_clean a c s Hs Hclean).
Qed.

(** The shared update changes maps before propagating through the guarded clean enqueue. *)
Theorem update_clean {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.row_enc a)) ix s x value :
  structural a s -> clean s -> clean (Worklist.update a ix s (x, value)).
Proof.
  intros Hs Hclean; rewrite Worklist.update_equation; cbn zeta.
  set (n := Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a))
    x (Worklist.delays s)).
  set (op := Worklist.operation_c a x n).
  destruct (snd (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    op (Worklist.current s) x value)); [|exact Hclean].
  apply (enqueue_clean a HE).
  - constructor; cbn.
    + apply Update.rule_wf, (values_wf Hs).
    + apply Map.wf_set, (delays_wf Hs).
    + exact (heap_wf Hs).
    + exact (queued_wf Hs).
    + apply (queued_live Hs).
  - exact Hclean.
Qed.

(** Ordered primary and side propagation preserves clean queues across every intermediate map. *)
Theorem updates_clean {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) ix outs s :
  structural a s -> clean s -> clean (Worklist.updates a ix outs s).
Proof.
  revert s; induction outs as [|[x value] outs IH]; intros s Hs Hclean;
    rewrite Worklist.updates_equation.
  - exact Hclean.
  - apply IH.
    + exact (proj1 (update_properties a HL ix s x value Hs)).
    + exact (update_clean a (Analysis.row_laws HL) ix s x value Hs Hclean).
Qed.

(** The actual popped queue remains clean before the output fold starts. *)
Theorem popped_clean {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.row_enc a)) s p c q :
  structural a s -> clean s ->
  Heap.pop (Analysis.row_enc a) (Worklist.queue s) = Some (p, c, q) ->
  clean (Worklist.State (Worklist.current s) q
    (FinSet.remove (Analysis.row_enc a) c (Worklist.queued s)) (Worklist.delays s)
    (S (Worklist.evaluations s))).
Proof.
  intros Hs [Hzero Hcount] Hpop.
  destruct (Heap.pop_no_stale _ HE _ _ _ _ (heap_wf Hs) Hzero Hpop) as [Hnext Hpending].
  pose proof (Heap.size_pop _ HE _ _ _ _ (heap_wf Hs) Hpop) as Hsize.
  split; [exact Hnext|]; cbn [Worklist.queue]; lia.
Qed.

(** Initialization starts clean and no duplicate row declaration can create staleness. *)
Theorem initial_clean {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.row_enc a)) : clean (Worklist.initial a).
Proof.
  rewrite Worklist.initial_equation; apply (enqueue_clean a HE).
  - constructor; cbn.
    + apply Map.wf_empty.
    + apply Map.wf_empty.
    + apply Heap.wf_empty.
    + apply FinSet.wf_empty.
    + intro c; rewrite FinSet.mem_empty; unfold present; now rewrite Heap.priority_empty.
  - split; [apply Heap.stale_empty|].
    change (Heap.pending_count (@Heap.empty C) = Heap.size (@Heap.empty C)).
    rewrite (@Heap.size_empty C); reflexivity.
Qed.

(** A continuing priority callback preserves zero staleness through its actual returned heap. *)
Theorem step_clean {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) ix s next :
  structural a s -> clean s -> Worklist.step a ix s = inl next -> clean next.
Proof.
  intros Hs Hclean Hstep; rewrite Worklist.step_equation in Hstep.
  destruct (Heap.pop (Analysis.row_enc a) (Worklist.queue s))
    as [[[p c] q]|] eqn:Hpop; [|discriminate].
  injection Hstep as <-; apply (updates_clean a HL).
  - exact (popped_structural a s p c q Hs Hpop).
  - exact (popped_clean a (Analysis.row_laws HL) s p c q Hs Hclean Hpop).
Qed.

(** Structural enqueue adds at most one live entry per input occurrence. *)
Theorem enqueue_size {X C A} (a : Analysis.t X C A)
    (HE : encoding_laws (Analysis.row_enc a)) cs s :
  structural a s ->
  Heap.size (Worklist.queue (Worklist.enqueue a cs s)) <=
    Heap.size (Worklist.queue s) + length cs.
Proof.
  revert s; induction cs as [|c cs IH]; intros s Hs; rewrite Worklist.enqueue_equation.
  - cbn [length]; lia.
  - pose proof (enqueue_one_properties a HE c s Hs) as [Hone _].
    pose proof (IH _ Hone) as Hrest.
    assert (Hone_size : Heap.size (Worklist.queue (Worklist.enqueue_one a c s)) <=
      S (Heap.size (Worklist.queue s))).
    { rewrite Worklist.enqueue_one_equation.
      destruct (FinSet.mem (Analysis.row_enc a) c (Worklist.queued s)).
      - lia.
      - cbn [Worklist.queue]; rewrite Heap.size_push by exact (heap_wf Hs).
        destruct (Heap.priority (Analysis.row_enc a) c (Worklist.queue s)); lia. }
    cbn [length]; lia.
Qed.

Section Joining.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a) (HJ : Analysis.joining a)
  (ix : sys_index X C)
  (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let R := Terminates.hgt HT.
Let U := unknowns a.
Let degree x := length (readers_of EX ix x).
Let look := lookup EX L.

(** The rank domain is the actual invariant supplied by finite-height evidence. *)
Definition good (s : Worklist.state X C A) :=
  structural a s /\ forall x, Terminates.inv HT (look (Worklist.current s) x).

(** Remaining rank credit is weighted by actual prepared reader-bucket lengths. *)
Definition credit m := sum (fun x => (bound R - rank R (look m x)) * degree x) U.

(** Queue entries and unused weighted ranks form a single natural-number potential. *)
Definition potential (s : Worklist.state X C A) :=
  Heap.size (Worklist.queue s) + credit (Worklist.current s).

(** Every actual primary or side output belongs to the declared occurrence support. *)
Theorem output_unknown c m x value :
  In c (System.constraints S) ->
  In (x, value) (fst (Eval.outputs S c (look m))) -> In x U.
Proof.
  intros Hc Hin; unfold U, unknowns; rewrite Kleene.output_keys_spec, in_flat_map.
  exists c; split; [exact Hc|].
  rewrite Eval.outputs_spec in Hin; cbn [fst] in Hin.
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; now left|].
  right; apply (System.sides_within (Analysis.static_law HL) c (look m)).
  apply in_map_iff; exists (x, value); now split.
Qed.

Local Lemma rule_joining (s : Worklist.state X C A) x value :
  Update.rule EX L (Worklist.operation_c a x
    (Map.find_or EX (Policy.delay (Analysis.policy a)) x (Worklist.delays s)))
    (Worklist.current s) x value =
  Update.rule EX L (join_c L) (Worklist.current s) x value.
Proof.
  rewrite !Update.rule_equation; fold look.
  destruct (leb L value (look (Worklist.current s) x)); [reflexivity|].
  rewrite Worklist.operation_equation, HJ; reflexivity.
Qed.

(** Every invariant input update preserves its carrier invariant and does not increase potential. *)
Theorem update_credit s x value :
  good s -> In x U -> Terminates.inv HT value ->
  good (Worklist.update a ix s (x, value)) /\
  potential (Worklist.update a ix s (x, value)) <= potential s.
Proof.
  intros [Hs Hinv] Hx Hvalue.
  pose proof (update_properties a HL ix s x value Hs) as [Hnext _].
  rewrite Worklist.update_equation; cbn zeta; fold EX L look.
  rewrite rule_joining, Update.rule_equation.
  fold look.
  destruct (leb L value (look (Worklist.current s) x)) eqn:Hbelow.
  - cbn [snd]; split; [now split|reflexivity].
  - cbn [fst snd].
    fold (join L (look (Worklist.current s) x) value).
    set (base := Worklist.State
      (Map.set EX x (join L (look (Worklist.current s) x) value) (Worklist.current s))
      (Worklist.queue s) (Worklist.queued s)
      (Map.set EX x
        (Nat.pred (Map.find_or EX (Policy.delay (Analysis.policy a)) x (Worklist.delays s)))
        (Worklist.delays s)) (Worklist.evaluations s)).
    assert (Hb : structural a base).
    { constructor; cbn [base Worklist.current Worklist.delays Worklist.queue Worklist.queued].
      - apply Map.wf_set, (values_wf Hs).
      - apply Map.wf_set, (delays_wf Hs).
      - exact (heap_wf Hs).
      - exact (queued_wf Hs).
      - apply (queued_live Hs). }
    destruct (enqueue_properties a (Analysis.row_laws HL) (readers_of EX ix x) base Hb)
      as [Hstruct [Hm _]].
    assert (Hinv' : forall y, Terminates.inv HT (look (Worklist.current base) y)).
    { intro y; unfold base; cbn [Worklist.current]; unfold look.
      rewrite !lookup_equation, Map.get_set by exact (values_wf Hs).
      destruct (eqb EX y x) eqn:Hy.
      - apply Terminates.inv_join; [apply Hinv|exact Hvalue].
      - fold (lookup EX L (Worklist.current s) y); apply Hinv. }
    split.
    + split; [exact Hstruct|]; rewrite Hm; exact Hinv'.
    + pose proof (enqueue_size a (Analysis.row_laws HL) (readers_of EX ix x) base Hb)
        as Hqueue.
      assert (Hup : forall y, leb L (look (Worklist.current s) y)
        (look (Worklist.current base) y) = true).
      { intro y; unfold base; cbn [Worklist.current]; unfold look.
        rewrite !lookup_equation, Map.get_set by exact (values_wf Hs).
        destruct (eqb EX y x) eqn:Hy.
        - apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hy; subst y.
          apply (join_upper_l (Analysis.lattice_law HL)).
        - rewrite <- lookup_equation; apply (leb_refl (Analysis.lattice_law HL)). }
      assert (Hmono : forall y, In y U ->
        (bound R - rank R (look (Worklist.current base) y)) * degree y <=
        (bound R - rank R (look (Worklist.current s) y)) * degree y).
      { intros y Hy; pose proof (rank_monotone R _ _ (Hinv y) (Hinv' y) (Hup y)); nia. }
      assert (Hstrict : leb L (join L (look (Worklist.current s) x) value)
        (look (Worklist.current s) x) = false).
      { destruct (leb L (join L (look (Worklist.current s) x) value)
          (look (Worklist.current s) x)) eqn:Htest; [|reflexivity].
        pose proof (leb_trans (Analysis.lattice_law HL)
          value (join L (look (Worklist.current s) x) value) (look (Worklist.current s) x)
          (join_upper_r (Analysis.lattice_law HL) (look (Worklist.current s) x) value) Htest)
          as Hescape.
        fold L look in Hescape; rewrite Hbelow in Hescape; discriminate. }
      pose proof (join_rank_grows R _ _ (Hinv x) Hvalue Hstrict) as Hgrow.
      pose proof (rank_bounded R _ (Terminates.inv_join HT _ _ (Hinv x) Hvalue)) as Hbound.
      fold R L look in Hgrow, Hbound.
      assert (Hroom : bound R - rank R (join L (look (Worklist.current s) x) value) + 1 <=
        bound R - rank R (look (Worklist.current s) x)).
      { apply subtraction_credit; assumption. }
      assert (Hsame : look (Worklist.current base) x =
        join L (look (Worklist.current s) x) value).
      { unfold base; cbn [Worklist.current]; unfold look.
        rewrite lookup_equation, Map.get_set_same by exact (values_wf Hs).
        reflexivity. }
      pose proof (sum_drop
        (fun y => (bound R - rank R (look (Worklist.current s) y)) * degree y)
        (fun y => (bound R - rank R (look (Worklist.current base) y)) * degree y)
        U x (degree x) Hx Hmono ltac:(cbn beta; fold look; rewrite Hsame; nia)) as Hdrop.
      fold (credit (Worklist.current base)) (credit (Worklist.current s)) in Hdrop.
      change (Heap.size (Worklist.queue (Worklist.enqueue a (readers_of EX ix x) base)) <=
        Heap.size (Worklist.queue s) + degree x) in Hqueue.
      unfold potential; rewrite Hm; lia.
Qed.

(** An output fold spends rank credit for all reader occurrences it can enqueue. *)
Theorem updates_credit outs s :
  good s ->
  (forall x value, In (x, value) outs -> In x U /\ Terminates.inv HT value) ->
  good (Worklist.updates a ix outs s) /\
  potential (Worklist.updates a ix outs s) <= potential s.
Proof.
  revert s; induction outs as [|[x value] outs IH]; intros s Hgood Houts;
    rewrite Worklist.updates_equation.
  - split; [exact Hgood|reflexivity].
  - destruct (Houts x value (or_introl eq_refl)) as [Hx Hvalue].
    destruct (update_credit s x value Hgood Hx Hvalue) as [Hnext Hcredit].
    destruct (IH _ Hnext (fun y v Hin => Houts y v (or_intror Hin))) as [Hdone Hle].
    split; [exact Hdone|lia].
Qed.

(** A continuing callback is one evaluation and consumes at least one potential unit. *)
Theorem step_credit s next :
  worklist_invariant a ix s -> good s -> Worklist.step a ix s = inl next ->
  good next /\ potential next < potential s /\
  Worklist.evaluations next = Datatypes.S (Worklist.evaluations s).
Proof.
  intros Hinv [Hs Hgood] Hstep.
  rewrite Worklist.step_equation in Hstep; fold EX EC L S look in Hstep.
  destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|] eqn:Hpop;
    [|discriminate].
  assert (Hc : In c (System.constraints S)).
  { apply (queue_listed Hinv c); rewrite (queued_live Hs); unfold present; fold EC.
    rewrite (Heap.pop_priority EC (Analysis.row_laws HL) _ _ _ _ (heap_wf Hs) Hpop).
    reflexivity. }
  set (base := Worklist.State (Worklist.current s) q
    (FinSet.remove EC c (Worklist.queued s)) (Worklist.delays s)
    (Datatypes.S (Worklist.evaluations s))).
  set (outs := fst (Eval.outputs S c (look (Worklist.current s)))).
  assert (Hresult : next = Worklist.updates a ix outs base).
  { injection Hstep as Hresult; symmetry; exact Hresult. }
  subst next.
  assert (Hb : structural a base) by exact (popped_structural a s p c q Hs Hpop).
  destruct (updates_credit outs base
    (conj Hb Hgood)) as [Hdone Hle].
  - intros x value Hin; split.
    + exact (output_unknown c (Worklist.current s) x value Hc Hin).
    + exact (Terminates.inv_closed HT _ Hgood c Hc (x, value) Hin).
  - split; [exact Hdone|]; split.
    + pose proof (Heap.size_pop EC (Analysis.row_laws HL) _ _ _ _ (heap_wf Hs) Hpop) as Hsize.
      change (potential (Worklist.updates a ix outs base) <=
        Heap.size q + credit (Worklist.current s)) in Hle.
      unfold potential; unfold potential in Hle; lia.
    + exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
        (updates_properties a HL ix outs base Hb))))))).
Qed.

(** Starting from bottom establishes the carrier invariant required by relative height. *)
Theorem initial_good : good (Worklist.initial a).
Proof.
  split.
  - exact (valid_state (initial_invariant a HL ix HI)).
  - rewrite (proj1 (initial_frames a (Analysis.row_laws HL))).
    intro x; unfold look; rewrite lookup_empty; exact (Terminates.inv_bot HT).
Qed.

(** The initial queue and weighted credits are bounded by the actual C and D counts. *)
Theorem initial_potential :
  potential (Worklist.initial a) <= constraint_count a + bound R * dependency_count a ix.
Proof.
  assert (Hqueue : Heap.size (Worklist.queue (Worklist.initial a)) <= constraint_count a).
  { rewrite Worklist.initial_equation.
    set (s := @Worklist.State X C A Map.empty Heap.empty FinSet.empty Map.empty 0).
    assert (Hs : structural a s).
    { constructor; cbn.
      - apply Map.wf_empty.
      - apply Map.wf_empty.
      - apply Heap.wf_empty.
      - apply FinSet.wf_empty.
      - intro c; rewrite FinSet.mem_empty; unfold present; now rewrite Heap.priority_empty. }
    pose proof (enqueue_size a (Analysis.row_laws HL) (System.constraints S) s Hs) as Hsize.
    exact Hsize. }
  assert (Hcredit : credit (Worklist.current (Worklist.initial a)) <=
    bound R * dependency_count a ix).
  { unfold credit, dependency_count; apply sum_capacity. }
  unfold potential; lia.
Qed.

(** Successful callback prefixes spend one credit per evaluation and retain their exact count. *)
Theorem runs_credit n s next :
  runs (Worklist.step_c a ix) n s (inl next) ->
  worklist_invariant a ix s -> good s ->
  worklist_invariant a ix next /\ good next /\
  potential next + n <= potential s /\
  Worklist.evaluations next = Worklist.evaluations s + n.
Proof.
  intro Hrun; remember (inl next) as result eqn:Heq.
  induction Hrun as [s|n s m Hstop|n s mid result Hnext Hrun IH];
    intros Hinv Hgood.
  - injection Heq as <-; split; [exact Hinv|]; split; [exact Hgood|].
    split; lia.
  - discriminate.
  - destruct (step_credit s mid Hinv Hgood Hnext) as [Hmid [Hdrop Hevals]].
    destruct (IH Heq (step_invariant a HL ix HI s mid Hinv Hnext) Hmid)
      as [Hdone [Hgood' [Hcredit Hevals']]].
    split; [exact Hdone|]; split; [exact Hgood'|]; split; lia.
Qed.

(** Every actual evaluation prefix is bounded by C plus H times prepared reader occurrences. *)
Theorem worklist_evals_bound n next :
  runs (Worklist.step_c a ix) n (Worklist.initial a) (inl next) ->
  n <= constraint_count a + bound R * dependency_count a ix.
Proof.
  intro Hrun.
  destruct (runs_credit n _ next Hrun (initial_invariant a HL ix HI) initial_good)
    as [_ [_ [Hcredit _]]].
  pose proof initial_potential; lia.
Qed.

End Joining.

(** Fuel above the joining bound includes the mandatory final empty-queue probe. *)
Theorem worklist_fuel_enough {X C A} (a : Analysis.t X C A)
    (HL : Analysis.laws a) (HT : Terminates.t a) (HJ : Analysis.joining a) fuel :
  constraint_count a + bound (Terminates.hgt HT) *
    dependency_count a (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))
    < Pos.to_nat fuel ->
  exists m, Worklist.run a fuel = Outcome.Solved m.
Proof.
  intro Hfuel; rewrite Worklist.run_equation.
  set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  assert (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
  { apply index_system_laws, (Analysis.key_laws HL). }
  pose proof (iterate_value (Worklist.step_c a ix) fuel (Worklist.initial a)) as Hrun.
  destruct (Cost.value (iterate _ _ _)) as [next|done].
  - pose proof (worklist_evals_bound a HL HT HJ ix HI _ _ Hrun); fold ix in Hfuel; lia.
  - exists done; reflexivity.
Qed.

(** A solved run exposes its actual evaluated prefix and final non-evaluating empty probe. *)
Theorem worklist_actual_evaluations {X C A} (a : Analysis.t X C A)
    (HL : Analysis.laws a) (HT : Terminates.t a) (HJ : Analysis.joining a) fuel m :
  Worklist.run a fuel = Outcome.Solved m ->
  let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  exists used last,
    used <= constraint_count a + bound (Terminates.hgt HT) * dependency_count a ix /\
    Worklist.evaluations last = used /\
    runs (Worklist.step_c a ix) used (Worklist.initial a) (inl last) /\
    Worklist.step a ix last = inr m.
Proof.
  intro Hsolved; cbn zeta; rewrite Worklist.run_equation in Hsolved.
  set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  assert (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
  { apply index_system_laws, (Analysis.key_laws HL). }
  fold ix in Hsolved.
  destruct (Cost.value (iterate (Worklist.step_c a ix) fuel (Worklist.initial a)))
    as [next|done] eqn:Hresult; [discriminate|].
  injection Hsolved as <-.
  destruct (iterate_inr_stops (Worklist.step_c a ix) fuel (Worklist.initial a) done Hresult)
    as [used [last [_ [Hprefix Hstop]]]].
  exists used, last; split.
  - exact (worklist_evals_bound a HL HT HJ ix HI used last Hprefix).
  - destruct (runs_credit a HL HT HJ ix HI used _ last Hprefix
      (initial_invariant a HL ix HI) (initial_good a HL HT ix HI))
      as [_ [_ [_ Hevaluations]]].
    rewrite (proj2 (initial_frames a (Analysis.row_laws HL))) in Hevaluations.
    split; [exact Hevaluations|]; now split.
Qed.

Module Budget.

(** Primitive budgets bound callbacks and encodings on the finite declared domains. *)
Record t := Make {
  query_nodes : nat;
  output_count : nat;
  continuation_ticks : N;
  key_encoder : N;
  key_digits : N;
  row_encoder : N;
  row_digits : N;
  lattice_ticks : N;
  target_ticks : N;
  rhs_ticks : N;
  order_ticks : N;
  selected_ticks : N
}.

Definition key (b : t) : N := (1 + key_encoder b + key_digits b)%N.
Definition row (b : t) : N := (1 + row_encoder b + row_digits b)%N.
Definition heap (b : t) count :=
  HeapCost.heap_cost (S count) (row_encoder b + row_digits b)%N.
Definition evaluation (b : t) : N :=
  (2 + target_ticks b + rhs_ticks b +
    N.of_nat (query_nodes b) * (3 + key b + continuation_ticks b))%N.
Definition enqueue (b : t) count : N :=
  (3 + 2 * row b + target_ticks b + order_ticks b + heap b count)%N.
Definition update (b : t) count dependencies : N :=
  (5 * key b + 3 + 2 * lattice_ticks b + selected_ticks b +
    N.of_nat dependencies * enqueue b count)%N.
Definition step (b : t) count dependencies : N :=
  (heap b count + row b + evaluation b +
    N.of_nat (output_count b) * (1 + update b count dependencies))%N.

End Budget.
Import Budget.

(** The cost model bounds primitive fields and selected query paths on invariant assignments. *)
Record cost_model {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) (b : Budget.t) : Prop := {
  key_budget : forall x, Kleene.cost_key a x ->
    (Cost.ticks (encode_c (Analysis.key_enc a) x) <= Budget.key_encoder b)%N /\
    (key_bits (Analysis.key_enc a) x <= Budget.key_digits b)%N;
  row_budget : forall c, In c (System.constraints (Analysis.system a)) ->
    (Cost.ticks (encode_c (Analysis.row_enc a) c) <= Budget.row_encoder b)%N /\
    (key_bits (Analysis.row_enc a) c <= Budget.row_digits b)%N;
  lattice_budget : forall old value,
    (Cost.ticks (leb_c (Analysis.lat a) value old) <= Budget.lattice_ticks b)%N /\
    (Cost.ticks (join_c (Analysis.lat a) old value) <= Budget.lattice_ticks b)%N;
  callback_budget : forall c, In c (System.constraints (Analysis.system a)) ->
    (Cost.ticks (System.target_c (Analysis.system a) c) <= Budget.target_ticks b)%N /\
    (Cost.ticks (System.rhs_c (Analysis.system a) c) <= Budget.rhs_ticks b)%N /\
    (Cost.ticks (Policy.order_c (Analysis.policy a) (System.target (Analysis.system a) c)) <=
      Budget.order_ticks b)%N;
  selection_budget : forall x, In x (unknowns a) ->
    (Cost.ticks (Policy.widen_at_c (Analysis.policy a) x) <= Budget.selected_ticks b)%N;
  query_budget : forall m c, Map.wf (Analysis.key_enc a) m ->
    (forall x, Terminates.inv HT (lookup (Analysis.key_enc a) (Analysis.lat a) m x)) ->
    In c (System.constraints (Analysis.system a)) ->
    Query.within (Budget.continuation_ticks b)
      (lookup (Analysis.key_enc a) (Analysis.lat a) m)
      (Budget.query_nodes b) (System.rhs (Analysis.system a) c);
  outputs_budget : forall m c, Map.wf (Analysis.key_enc a) m ->
    (forall x, Terminates.inv HT (lookup (Analysis.key_enc a) (Analysis.lat a) m x)) ->
    In c (System.constraints (Analysis.system a)) ->
    length (fst (Eval.outputs (Analysis.system a) c
      (lookup (Analysis.key_enc a) (Analysis.lat a) m))) <= Budget.output_count b
}.

Arguments key_budget {X C A a HT b}.
Arguments row_budget {X C A a HT b}.
Arguments lattice_budget {X C A a HT b}.
Arguments callback_budget {X C A a HT b}.
Arguments selection_budget {X C A a HT b}.
Arguments query_budget {X C A a HT b}.
Arguments outputs_budget {X C A a HT b}.

Section PrimitiveCosts.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a) (HJ : Analysis.joining a)
  (b : Budget.t) (HB : cost_model a HT b).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.

(** Invariant key lookup is bounded independently of assignment size. *)
Theorem lookup_cost m x :
  Kleene.cost_key a x ->
  (Cost.ticks (lookup_c EX L m x) <= Budget.key b)%N.
Proof.
  intro Hx; destruct (key_budget HB x Hx) as [Henc Hbits].
  rewrite FixpointSystem.lookup_cost, Map.get_cost.
  fold (key_bits EX x); fold EX in Henc, Hbits.
  unfold Budget.key; lia.
Qed.

(** A write to a relevant key retains its encoder and full code-width charge. *)
Theorem write_cost {V} (m : Map.t X V) x value :
  Kleene.cost_key a x ->
  (Cost.ticks (Map.set_c EX x value m) <= Budget.key b)%N.
Proof.
  intro Hx; destruct (key_budget HB x Hx) as [Henc Hbits].
  rewrite Map.set_cost; fold (key_bits EX x); fold EX in Henc, Hbits.
  unfold Budget.key; lia.
Qed.

(** Each selected evaluation budget retains all system callbacks, lookups and continuations. *)
Theorem evaluation_cost m c :
  Map.wf EX m ->
  (forall x, Terminates.inv HT (lookup EX L m x)) ->
  In c (System.constraints S) ->
  (Cost.ticks (Eval.outputs_c S (lookup_c EX L m) c) <= Budget.evaluation b)%N.
Proof.
  intros Hwf Hinv Hc.
  assert (Hreads : forall x, In x (Query.reads (System.rhs S c) (lookup EX L m)) ->
    (Cost.ticks (lookup_c EX L m x) <= Budget.key b)%N).
  { intros x Hx; apply lookup_cost.
    right; exists c; split; [exact Hc|].
    exact (System.reads_within (Analysis.static_law HL) c _ x Hx). }
  pose proof (Query.run_c_cost_on (System.rhs S c) (lookup_c EX L m)
    (lookup EX L m) (Budget.query_nodes b) (Budget.continuation_ticks b)
    (Budget.key b) (query_budget HB m c Hwf Hinv Hc)
    (fun _ => eq_refl) Hreads) as Hquery.
  destruct (callback_budget HB c Hc) as [Htarget [Hrhs _]].
  fold S in Htarget, Hrhs.
  rewrite Eval.outputs_cost; unfold Budget.evaluation; lia.
Qed.

(** Joining keeps policy invocation ticks even though every policy answer selects join. *)
Theorem operation_cost x n old value :
  In x (unknowns a) ->
  (Cost.ticks (Worklist.operation_c a x n old value) <=
    1 + Budget.selected_ticks b + Budget.lattice_ticks b)%N.
Proof.
  intro Hx; rewrite Worklist.operation_cost, HJ.
  pose proof (selection_budget HB x Hx) as Hselected.
  pose proof (proj2 (lattice_budget HB old value)) as Hjoin.
  fold L in Hjoin |- *; lia.
Qed.

(** The shared rule's numeric budget includes both actual encodings and the delayed policy call. *)
Theorem rule_cost (s : Worklist.state X C A) x n value :
  In x (unknowns a) ->
  (Cost.ticks (Update.rule_c EX L (Worklist.operation_c a x n)
    (Worklist.current s) x value) <=
    2 * Budget.key b + 3 + 2 * Budget.lattice_ticks b + Budget.selected_ticks b)%N.
Proof.
  intro Hx.
  assert (Hkey : Kleene.cost_key a x) by now left.
  pose proof (lookup_cost (Worklist.current s) x Hkey) as Hlookup.
  pose proof (write_cost (Worklist.current s) x
    (Cost.value (Worklist.operation_c a x n (lookup EX L (Worklist.current s) x) value)) Hkey)
    as Hwrite.
  pose proof (proj1 (lattice_budget HB (lookup EX L (Worklist.current s) x) value))
    as Hcompare.
  pose proof (operation_cost x n (lookup EX L (Worklist.current s) x) value Hx) as Hop.
  rewrite Update.rule_cost; fold EX L in Hcompare |- *.
  destruct (leb L value (lookup EX L (Worklist.current s) x)); nia.
Qed.

(** Single-row enqueue separates public heap work from all other primitive charges. *)
Theorem enqueue_one_callee_cost c s :
  In c (System.constraints S) ->
  (Cost.ticks (Worklist.enqueue_one_c a c s) <=
    2 * Budget.row b + 2 + Budget.target_ticks b + Budget.order_ticks b +
    Cost.ticks (Heap.push_c EC
      (Policy.order (Analysis.policy a) (System.target S c)) c (Worklist.queue s)))%N.
Proof.
  intro Hc; destruct (row_budget HB c Hc) as [Henc Hbits].
  destruct (callback_budget HB c Hc) as [Htarget [_ Horder]].
  rewrite Worklist.enqueue_one_cost, FinSet.mem_cost, FinSet.add_cost.
  fold S in Htarget, Horder |- *.
  fold EC in Henc, Hbits |- *; fold (key_bits EC c).
  destruct (FinSet.mem EC c (Worklist.queued s)); unfold Budget.row; nia.
Qed.

Local Lemma live_listed s c p :
  queue_supported a s -> Heap.priority EC c (Worklist.queue s) = Some p ->
  In c (System.constraints S).
Proof.
  intros [Hs Hlisted] Hpriority; apply Hlisted.
  rewrite (queued_live Hs); unfold present; fold EC; now rewrite Hpriority.
Qed.

Local Lemma heap_data s :
  queue_supported a s -> clean s ->
  Heap.key_budget EC (Budget.row_encoder b + Budget.row_digits b)%N (Worklist.queue s) /\
  Heap.pending_count (Worklist.queue s) <= constraint_count a.
Proof.
  intros Hsupport [Hzero Hcount]; destruct Hsupport as [Hs Hlisted].
  split.
  - apply (Heap.key_budget_live EC (Analysis.row_laws HL) _ _ (heap_wf Hs) Hzero).
    intros c p Hpriority.
    destruct (row_budget HB c (live_listed s c p (conj Hs Hlisted) Hpriority))
      as [Henc Hbits].
    fold EC in Henc, Hbits; fold (key_bits EC c); split; lia.
  - rewrite Hcount; apply (Heap.size_support_bound EC (Analysis.row_laws HL)
      (System.constraints S) _ (heap_wf Hs)).
    intros c p; apply (live_listed s c p (conj Hs Hlisted)).
Qed.

(** Clean, supported heaps instantiate the owner's logarithmic worst-case pop contract. *)
Theorem pop_cost s :
  queue_supported a s -> clean s ->
  (Cost.ticks (Heap.pop_c EC (Worklist.queue s)) <=
    Budget.heap b (constraint_count a))%N.
Proof.
  intros Hsupport Hclean; destruct (heap_data s Hsupport Hclean) as [Hkeys Hcap].
  apply (HeapCost.pop_cost_no_stale EC (Analysis.row_laws HL) Map.cost_laws_hold).
  - exact (heap_wf (proj1 Hsupport)).
  - exact Hkeys.
  - exact (proj1 Hclean).
  - lia.
Qed.

Local Lemma push_heap_cost s c p :
  queue_supported a s -> clean s -> In c (System.constraints S) ->
  (Cost.ticks (Heap.push_c EC p c (Worklist.queue s)) <=
    Budget.heap b (constraint_count a))%N.
Proof.
  intros Hsupport Hclean Hc.
  destruct (heap_data s Hsupport Hclean) as [Hkeys Hcap].
  destruct (row_budget HB c Hc) as [Henc Hbits]; fold EC in Henc, Hbits.
  assert (Hencoder :
    (Cost.ticks (encode_c EC c) <= Budget.row_encoder b + Budget.row_digits b)%N) by lia.
  assert (Hdigits :
    (N.pos (Pos.size (encode EC c)) <= Budget.row_encoder b + Budget.row_digits b)%N).
  { fold (key_bits EC c); lia. }
  pose proof (HeapCost.push_cost EC Map.cost_laws_hold p c (Worklist.queue s)
    (Datatypes.S (constraint_count a)) (Budget.row_encoder b + Budget.row_digits b)%N
    (heap_wf (proj1 Hsupport)) Hkeys ltac:(lia) Hencoder Hdigits) as Hpush.
  rewrite (HeapCost.heap_potential_zero _ _ _ (proj1 Hclean)) in Hpush.
  unfold Budget.heap; lia.
Qed.

(** The enqueue constant composes both encodings, callbacks and the actual heap budget. *)
Theorem enqueue_one_cost c s :
  queue_supported a s -> clean s -> In c (System.constraints S) ->
  (1 + Cost.ticks (Worklist.enqueue_one_c a c s) <=
    Budget.enqueue b (constraint_count a))%N.
Proof.
  intros Hsupport Hclean Hc.
  pose proof (enqueue_one_callee_cost c s Hc) as Hcalls.
  pose proof (push_heap_cost s c
    (Policy.order (Analysis.policy a) (System.target S c)) Hsupport Hclean Hc) as Hheap.
  unfold Budget.enqueue; lia.
Qed.

(** Every enqueue occurrence receives a primitive budget under the clean queue invariant. *)
Theorem enqueue_cost cs s :
  queue_supported a s -> clean s -> incl cs (System.constraints S) ->
  (Cost.ticks (Worklist.enqueue_c a cs s) <=
    N.of_nat (length cs) * Budget.enqueue b (constraint_count a))%N.
Proof.
  revert s; induction cs as [|c cs IH]; intros s Hsupport Hclean Hlisted;
    rewrite Worklist.enqueue_cost.
  - cbn [length]; lia.
  - assert (Hc : In c (System.constraints S)) by (apply Hlisted; now left).
    assert (Hnext : queue_supported a (Worklist.enqueue_one a c s)).
    { assert (Hsingle : incl [c] (System.constraints S)).
      { intros d [<-|Hbad]; [exact Hc|contradiction]. }
      pose proof (enqueue_supported a (Analysis.row_laws HL) [c] s Hsupport Hsingle) as Hqueue.
      rewrite Worklist.enqueue_equation, Worklist.enqueue_equation in Hqueue; exact Hqueue. }
    pose proof (enqueue_one_clean a c s (proj1 Hsupport) Hclean) as Hclean'.
    pose proof (IH _ Hnext Hclean' (fun d Hd => Hlisted d (or_intror Hd))) as Htail.
    pose proof (enqueue_one_cost c s Hsupport Hclean Hc) as Hone.
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

Local Lemma key_lookup_cost {V} (m : Map.t X V) default x :
  Kleene.cost_key a x ->
  (Cost.ticks (Map.find_or_c EX default x m) <= Budget.key b)%N.
Proof.
  intro Hx; destruct (key_budget HB x Hx) as [Henc Hbits]; fold EX in Henc, Hbits.
  rewrite Map.find_or_cost, Map.get_cost; fold (key_bits EX x).
  unfold Budget.key; lia.
Qed.

(** Changed-output cost includes counter lookup/write, reader lookup and every bucket occurrence. *)
Theorem update_cost ix s x value :
  sys_index_laws EX S (Analysis.static a) ix ->
  queue_supported a s -> clean s -> In x (unknowns a) ->
  (Cost.ticks (Worklist.update_c a ix s (x, value)) <=
    Budget.update b (constraint_count a) (dependency_count a ix))%N.
Proof.
  intros HI Hsupport Hclean Hx; destruct Hsupport as [Hs Hlisted].
  assert (Hkey : Kleene.cost_key a x) by now left.
  set (n := Map.find_or EX (Policy.delay (Analysis.policy a)) x (Worklist.delays s)).
  set (result := Update.rule EX L (Worklist.operation_c a x n) (Worklist.current s) x value).
  pose proof (key_lookup_cost (Worklist.delays s) (Policy.delay (Analysis.policy a)) x Hkey)
    as Hfind.
  pose proof (rule_cost s x n value Hx) as Hrule.
  pose proof (write_cost (Worklist.delays s) x (Nat.pred n) Hkey) as Hcounter.
  assert (Hread : (Cost.ticks (readers_of_c EX ix x) <= Budget.key b)%N).
  { rewrite readers_cost, Map.get_cost; fold (key_bits EX x).
    destruct (key_budget HB x Hkey) as [Henc Hbits]; fold EX in Henc, Hbits.
    unfold Budget.key; lia. }
  rewrite Worklist.update_cost; cbn zeta; fold EX L n result.
  destruct (snd result) eqn:Hchange.
  - set (base := Worklist.State (fst result) (Worklist.queue s) (Worklist.queued s)
      (Map.set EX x (Nat.pred n) (Worklist.delays s)) (Worklist.evaluations s)).
    assert (Hbase : queue_supported a base).
    { split; [|exact Hlisted]; constructor; cbn [base Worklist.current Worklist.queue
        Worklist.queued Worklist.delays].
      - apply Update.rule_wf, (values_wf Hs).
      - apply Map.wf_set, (delays_wf Hs).
      - exact (heap_wf Hs).
      - exact (queued_wf Hs).
      - apply (queued_live Hs). }
    assert (Hcs : incl (readers_of EX ix x) (System.constraints S)).
    { intros c Hc; exact (proj1 (proj1 (readers_agree HI x c) Hc)). }
    pose proof (enqueue_cost (readers_of EX ix x) base Hbase Hclean Hcs) as Henqueue.
    pose proof (reader_degree_bound a ix x Hx) as Hdegree.
    fold EX in Hdegree.
    unfold Budget.update; nia.
  - unfold Budget.update; nia.
Qed.

(** The ordered output fold charges each occurrence under clean finite queue support. *)
Theorem updates_cost ix outs s :
  sys_index_laws EX S (Analysis.static a) ix ->
  queue_supported a s -> clean s ->
  (forall x value, In (x, value) outs -> In x (unknowns a)) ->
  (Cost.ticks (Worklist.updates_c a ix outs s) <=
    N.of_nat (length outs) *
      (1 + Budget.update b (constraint_count a) (dependency_count a ix)))%N.
Proof.
  intro HI; revert s; induction outs as [|[x value] outs IH];
    intros s Hsupport Hclean Houts; rewrite Worklist.updates_cost.
  - cbn [length]; lia.
  - pose proof (update_cost ix s x value HI Hsupport Hclean
      (Houts x value (or_introl eq_refl))) as Hone.
    assert (Hnext : queue_supported a (Worklist.update a ix s (x, value))).
    { pose proof (updates_supported a HL ix [(x, value)] s HI Hsupport) as Hnext.
      rewrite Worklist.updates_equation, Worklist.updates_equation in Hnext; exact Hnext. }
    pose proof (update_clean a (Analysis.row_laws HL) ix s x value (proj1 Hsupport) Hclean)
      as Hclean'.
    pose proof (IH _ Hnext Hclean' (fun y v Hy => Houts y v (or_intror Hy))) as Htail.
    cbn [length]; rewrite Nat2N.inj_succ; nia.
Qed.

(** A priority callback composes primitive work under actual invariant-relative query budgets. *)
Theorem step_cost ix s :
  worklist_invariant a ix s ->
  (forall x, Terminates.inv HT (lookup EX L (Worklist.current s) x)) ->
  clean s ->
  (Cost.ticks (Worklist.step_c a ix s) <=
    Budget.step b (constraint_count a) (dependency_count a ix))%N.
Proof.
  intros Hinv Hgood Hclean; pose proof (valid_state Hinv) as Hs.
  assert (Hsupport : queue_supported a s) by exact (conj Hs (queue_listed Hinv)).
  pose proof (pop_cost s Hsupport Hclean) as Hpopcost.
  rewrite Worklist.step_cost; fold EX EC L S.
  destruct (Heap.pop EC (Worklist.queue s)) as [[[p c] q]|] eqn:Hpop.
  - assert (Hc : In c (System.constraints S)).
    { apply (live_listed s c p Hsupport).
      exact (Heap.pop_priority EC (Analysis.row_laws HL) _ _ _ _ (heap_wf Hs) Hpop). }
    set (base := Worklist.State (Worklist.current s) q
      (FinSet.remove EC c (Worklist.queued s)) (Worklist.delays s)
      (Datatypes.S (Worklist.evaluations s))).
    assert (Hb : queue_supported a base).
    { split; [exact (popped_structural a s p c q Hs Hpop)|].
      intros d Hd; unfold base in Hd; cbn [Worklist.queued] in Hd.
      rewrite FinSet.mem_remove in Hd.
      apply andb_true_iff in Hd as [_ Hd]; exact (queue_listed Hinv d Hd). }
    pose proof (popped_clean a (Analysis.row_laws HL) s p c q Hs Hclean Hpop) as Hclean'.
    pose proof (evaluation_cost (Worklist.current s) c (values_wf Hs) Hgood Hc) as Heval.
    pose proof (updates_cost ix
      (fst (Eval.outputs S c (lookup EX L (Worklist.current s)))) base (valid_index Hinv)
      Hb Hclean' (fun x value Hin => output_unknown a HL c (Worklist.current s) x value Hc Hin))
      as Hupdates.
    pose proof (outputs_budget HB (Worklist.current s) c (values_wf Hs) Hgood Hc) as Houtputs.
    destruct (row_budget HB c Hc) as [Henc Hbits]; fold EC in Henc, Hbits.
    rewrite FinSet.remove_cost; fold (key_bits EC c).
    unfold Budget.step, Budget.row; fold S EX L in Houtputs; nia.
  - unfold Budget.step; nia.
Qed.

(** Initialization pays the primitive enqueue constant for each original row occurrence. *)
Theorem initial_cost :
  (Cost.ticks (Worklist.initial_c a) <=
    N.of_nat (constraint_count a) * Budget.enqueue b (constraint_count a))%N.
Proof.
  rewrite Worklist.initial_cost.
  set (empty := @Worklist.State X C A Map.empty Heap.empty FinSet.empty Map.empty 0).
  apply enqueue_cost.
  - split.
    + constructor; cbn.
      * apply Map.wf_empty.
      * apply Map.wf_empty.
      * apply Heap.wf_empty.
      * apply FinSet.wf_empty.
      * intro c; rewrite FinSet.mem_empty; unfold present; now rewrite Heap.priority_empty.
    + intros c Hbad; cbn [empty Worklist.queued] in Hbad.
      rewrite FinSet.mem_empty in Hbad; discriminate.
  - split; [apply Heap.stale_empty|]; reflexivity.
  - intros c Hc; exact Hc.
Qed.

End PrimitiveCosts.

(** The callback constant includes query, lattice, reader, encoding and heap-width budgets. *)
Definition worklist_k {X C A} (a : Analysis.t X C A) ix (b : Budget.t) :=
  Budget.step b (constraint_count a) (dependency_count a ix).

(** The actual binary driver costs its joining potential plus logarithmic unused-fuel overhead. *)
Theorem worklist_driver_cost {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (HT : Terminates.t a) (HJ : Analysis.joining a) b (HB : cost_model a HT b) fuel :
  let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  (Cost.ticks (iterate (Worklist.step_c a ix) fuel (Worklist.initial a)) <=
    (worklist_k a ix b + 2) *
      (N.of_nat (constraint_count a + bound (Terminates.hgt HT) * dependency_count a ix) + 1) +
    2 * N.pos (Pos.size fuel))%N.
Proof.
  cbn zeta.
  set (ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  assert (HI : sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix).
  { apply index_system_laws, (Analysis.key_laws HL). }
  set (I := fun s => worklist_invariant a ix s /\ good a HT s /\ clean s).
  set (Phi := fun s => N.of_nat (potential a HT ix s)).
  assert (Hstep : forall s, I s ->
    (Cost.ticks (Worklist.step_c a ix s) <= worklist_k a ix b)%N /\
    match Cost.value (Worklist.step_c a ix s) with
    | inl next => I next /\ (Phi next < Phi s)%N
    | inr _ => True
    end).
  { intros s [Hinv [Hgood Hclean]]; split.
    - exact (step_cost a HL HT HJ b HB ix s Hinv (proj2 Hgood) Hclean).
    - destruct (Cost.value (Worklist.step_c a ix s)) as [next|done] eqn:Hnext; [|exact Logic.I].
      destruct (step_credit a HL HT HJ ix s next Hinv Hgood Hnext) as [Hgood' [Hdrop _]].
      split.
      + split; [exact (step_invariant a HL ix HI s next Hinv Hnext)|].
        split; [exact Hgood'|].
        exact (step_clean a HL ix s next (valid_state Hinv) Hclean Hnext).
      + unfold Phi; lia. }
  assert (Hinitial : I (Worklist.initial a)).
  { split; [exact (initial_invariant a HL ix HI)|].
    split; [exact (initial_good a HL HT ix HI)|apply initial_clean, (Analysis.row_laws HL)]. }
  pose proof (iterate_cost (Worklist.step_c a ix) I Phi (worklist_k a ix b) fuel
    (Worklist.initial a) Hstep Hinitial) as Hcost.
  pose proof (initial_potential a HL HT ix) as Hpotential.
  unfold Phi in Hcost; nia.
Qed.

(** Full-run accounting retains actual setup work before the potential-bounded driver. *)
Theorem worklist_cost_callee {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (HT : Terminates.t a) (HJ : Analysis.joining a) b (HB : cost_model a HT b) fuel :
  let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  (Cost.ticks (Worklist.run_c a fuel) <=
    Cost.ticks (index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) +
    N.of_nat (constraint_count a) * Budget.enqueue b (constraint_count a) +
    (worklist_k a ix b + 2) *
      (N.of_nat (constraint_count a + bound (Terminates.hgt HT) * dependency_count a ix) + 1) +
    2 * N.pos (Pos.size fuel))%N.
Proof.
  cbn zeta; rewrite Worklist.run_cost.
  pose proof (worklist_driver_cost a HL HT HJ b HB fuel) as Hdriver.
  cbn zeta in Hdriver.
  pose proof (initial_cost a HL HT b HB) as Hinitial.
  nia.
Qed.

(** Setup budgets include index metadata preparation and every original enqueue occurrence. *)
Definition worklist_setup {X C A} (a : Analysis.t X C A) b preparation :=
  (SystemIndexCost.Budget.preparation preparation (constraint_count a) +
    N.of_nat (constraint_count a) * Budget.enqueue b (constraint_count a))%N.

(** The numeric size contains setup and the potential-weighted primitive callback constant. *)
Definition worklist_size {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) b preparation :=
  let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  (worklist_setup a b preparation + (worklist_k a ix b + 2) *
    (N.of_nat (constraint_count a + bound (Terminates.hgt HT) * dependency_count a ix) + 1))%N.

(** Complete numeric work charges setup, callbacks, traversal and binary fuel overhead. *)
Theorem worklist_cost {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (HT : Terminates.t a) (HJ : Analysis.joining a) b (HB : cost_model a HT b)
    preparation
    (HP : SystemIndexCost.cost_model (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)
      (System.constraints (Analysis.system a)) preparation) fuel :
  (Cost.ticks (Worklist.run_c a fuel) <=
    worklist_size a HT b preparation + 2 * N.pos (Pos.size fuel))%N.
Proof.
  pose proof (worklist_cost_callee a HL HT HJ b HB fuel) as Hrun.
  cbn zeta in Hrun.
  pose proof (SystemIndexCost.index_system_cost (Analysis.key_enc a) (Analysis.key_laws HL)
    (Analysis.system a) (Analysis.static a) preparation HP) as Hindex.
  unfold worklist_size, worklist_setup; fold (constraint_count a) in Hindex; lia.
Qed.

(** The big-O corollary retains all primitive measures and logarithmic supplied-fuel overhead. *)
Theorem worklist_bigO {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    (HT : Terminates.t a) (HJ : Analysis.joining a) b (HB : cost_model a HT b)
    preparation
    (HP : SystemIndexCost.cost_model (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)
      (System.constraints (Analysis.system a)) preparation) :
  bigO (fun fuel => (worklist_size a HT b preparation + N.pos (Pos.size fuel))%N)
    (fun fuel => Cost.ticks (Worklist.run_c a fuel)).
Proof.
  exists 2%N; intro fuel.
  pose proof (worklist_cost a HL HT HJ b HB preparation HP fuel); nia.
Qed.

End WorklistCost.
Import WorklistCost.
