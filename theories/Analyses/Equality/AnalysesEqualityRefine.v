(** * Optimistic congruence refinement

    Refinement intersects an existing partition with its prepared signature classes.
    For example, equal loop parameters keep their optimistic class until their inputs differ.
    Builds on: AnalysesEqualitySignature, AnalysesEqualityClasses and LatticePartitionGroup. *)

From Stdlib Require Import List Bool Arith Lia PArith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseCode BaseUnionFind BaseCertify.
From Galois.Lattice Require Import LatticeCore LatticePartition LatticePartitionGroup.
From Galois.Program Require Import ProgramSsa.
From Galois.Analyses.Equality Require Import AnalysesEqualityProblem AnalysesEqualitySignature
  AnalysesEqualityClasses.
Import List.ListNotations Cost.Notations Numbering NumberingSignature.

Local Open Scope nat_scope.

Module NumberingRefine.

Section Refinement.
Context {N E V K G : Type} (np : problem N E V K G)
  (HV : encoding_laws (Ssa.val_enc (ssa np))).
Let EV := Ssa.val_enc (ssa np).
Let values := Ssa.values (ssa np).
Let part := partition_t EV.

(** Slot labels distinguish missing entries from every allocated signature ID. *)
Definition slot_encoding := codec_enc (option_codec positive_codec).

(** Slot labels inherit injectivity from the public optional-positive codec. *)
Theorem slot_encoding_laws : encoding_laws slot_encoding.
Proof.
  apply codec_laws_injective, option_codec_laws, positive_codec_laws.
Qed.

(** Grouping attaches the internally established forest and Map certificate to its result. *)
Definition grouped_c (pr : prepared V) : Cost.t part :=
  Cost.map (@Some _)
    (Cost.refine
      (partition_group_c EV slot_encoding (slot_c np pr) (checked_values pr))
      (partition_group_wf EV slot_encoding (slot_c np pr) HV (checked_values pr))).

Definition grouped pr := Cost.value (grouped_c pr).

(** Grouped classes equate precisely the listed occurrences with the same cached signature ID. *)
Theorem grouped_spec pr x y :
  partition_equiv EV (grouped pr) x y <->
  x = y \/ In x (checked_values pr) /\ In y (checked_values pr) /\
    slot np pr x = slot np pr y.
Proof.
  unfold grouped, grouped_c; autorewrite with galois_cost.
  change (UnionFind.equiv EV
    (partition_group EV slot_encoding (slot_c np pr) (checked_values pr)) x y <->
    x = y \/ In x (checked_values pr) /\ In y (checked_values pr) /\
      slot np pr x = slot np pr y).
  apply (partition_group_equiv EV slot_encoding (slot_c np pr) HV slot_encoding_laws).
Qed.

(** Group construction always returns a reached partition. *)
Theorem grouped_reached pr : grouped pr <> None.
Proof.
  unfold grouped, grouped_c; autorewrite with galois_cost; discriminate.
Qed.

(** Shape grouping ignores operand classes but retains constructor, operator and arity. *)
Definition shape_prepared_c forms : Cost.t (prepared V) :=
  prepare_with_c np forms values (fun _ => Cost.ret 1%positive).

Definition shape_partition_with_c forms : Cost.t part :=
  let* pr := shape_prepared_c forms in grouped_c pr.

Definition shape_partition_c : Cost.t part :=
  let* forms := prepare_c np in shape_partition_with_c forms.

Definition shape_partition := Cost.value shape_partition_c.

(** One refinement reuses its prepared class/signature table and invokes the public lattice join. *)
Definition refine_prepared_c p pr : Cost.t part :=
  let* signatures := grouped_c pr in partition_join_c EV HV p signatures.

Definition refine_step_with_c forms p : Cost.t part :=
  let* pr := prepare_check_c np forms p in refine_prepared_c p pr.

Definition refine_step_c p : Cost.t part :=
  let* forms := prepare_c np in refine_step_with_c forms p.

Definition refine_step p := Cost.value (refine_step_c p).

(** A reusable step observes the same snapshot and join without repeating static preparation. *)
Definition refine_with forms p := Cost.value (refine_step_with_c forms p).

(** The reusable step exposes its exact public lattice join. *)
Theorem refine_with_equation forms p :
  refine_with forms p = partition_join EV HV p (grouped (prepare_check np forms p)).
Proof.
  unfold refine_with, refine_step_with_c, refine_prepared_c.
  autorewrite with galois_cost; reflexivity.
Qed.

(** Public refinement is the reusable step at its internally prepared static table. *)
Theorem refine_step_with p : refine_step p = refine_with (prepare np) p.
Proof.
  reflexivity.
Qed.

(** Refinement's pure equation exposes its one prepared snapshot and its public join. *)
Theorem refine_step_equation p :
  refine_step p =
  partition_join EV HV p (grouped (prepare_check np (prepare np) p)).
Proof.
  unfold refine_step, refine_step_c, refine_step_with_c, refine_prepared_c.
  autorewrite with galois_cost; reflexivity.
Qed.

(** A refinement keeps exactly the old equalities whose prepared signature slots agree. *)
Theorem refine_step_spec p x y :
  partition_equiv EV (refine_step p) x y <->
  partition_equiv EV p x y /\
  (x = y \/
    In x (domain EV values p) /\ In y (domain EV values p) /\
    slot np (prepare_check np (prepare np) p) x =
      slot np (prepare_check np (prepare np) p) y).
Proof.
  rewrite refine_step_equation, partition_join_spec, grouped_spec.
  rewrite prepare_check_with, prepared_values; reflexivity.
Qed.

(** Refinement is inflationary in the reverse-inclusion partition order. *)
Theorem refine_step_leb p : partition_leb EV p (refine_step p) = true.
Proof.
  rewrite refine_step_equation.
  exact (join_upper_l (partition_laws EV HV) p _).
Qed.

(** A reusable step keeps exactly old equalities and equality of cached signature slots. *)
Theorem refine_with_spec forms p x y :
  partition_equiv EV (refine_with forms p) x y <->
  partition_equiv EV p x y /\
  (x = y \/ In x (domain EV values p) /\ In y (domain EV values p) /\
    slot np (prepare_check np forms p) x = slot np (prepare_check np forms p) y).
Proof.
  rewrite refine_with_equation, partition_join_spec, grouped_spec.
  rewrite prepare_check_with, prepared_values; reflexivity.
Qed.

(** Producer support excludes nontrivial equalities outside the fixed value inventory. *)
Definition supported (p : part) : Prop :=
  p <> None /\
  forall x y, partition_equiv EV p x y ->
    x = y \/ In x values /\ In y values.

(** Shape grouping establishes finite support without caller-supplied invariants. *)
Theorem shape_supported : supported shape_partition.
Proof.
  unfold shape_partition, shape_partition_c, shape_partition_with_c, shape_prepared_c.
  rewrite !Cost.value_bind.
  change (supported (grouped
    (prepare_with np (prepare np) values (fun _ => Cost.ret 1%positive)))).
  split; [apply grouped_reached|].
  intros x y Heq; apply grouped_spec in Heq.
  rewrite prepared_values in Heq; tauto.
Qed.

(** Intersecting equalities preserves the producer's fixed finite support. *)
Theorem refine_supported p : supported p -> supported (refine_step p).
Proof.
  intros [Hreached Hsupport]; split.
  - rewrite refine_step_equation; destruct p as [u|]; [|contradiction].
    destruct (grouped (prepare_check np (prepare np) (Some u))) as [v|] eqn:Hgroup.
    + discriminate.
    + exfalso; exact (grouped_reached _ Hgroup).
  - intros x y Heq; apply refine_step_spec in Heq as [Hold _]; now apply Hsupport.
Qed.

(** Every non-reflexive equality has both endpoints in the checker's finite support domain. *)
Theorem domain_pair p x y :
  p <> None -> partition_equiv EV p x y -> x <> y ->
  In x (domain EV values p) /\ In y (domain EV values p).
Proof.
  destruct p as [u|]; [intros _ Heq Hne|contradiction].
  destruct (partition_support_pair EV HV (proj1_sig u) x y (proj2_sig u) Heq Hne)
    as [Hx Hy].
  unfold domain, domain_c; rewrite Cost.value_bind, value_app_c.
  split; apply in_or_app; now right.
Qed.

(** The represented partition relation is reflexive, including the unreachable case. *)
Theorem partition_refl p x : partition_equiv EV p x x.
Proof.
  apply (proj1 (class_spec EV HV p x x)); reflexivity.
Qed.

(** Every refinement is reached because its signature partition is reached. *)
Theorem refine_with_reached forms p : refine_with forms p <> None.
Proof.
  rewrite refine_with_equation.
  destruct (grouped (prepare_check np forms p)) as [u|] eqn:Hgroup.
  - destruct p; discriminate.
  - exfalso; exact (grouped_reached _ Hgroup).
Qed.

(** Reached partition comparison is reverse inclusion of the actual represented equalities. *)
Theorem partition_order p q :
  p <> None -> q <> None ->
  (partition_leb EV p q = true <->
    forall x y, partition_equiv EV q x y -> partition_equiv EV p x y).
Proof.
  destruct p as [u|], q as [v|]; intros Hp Hq; try contradiction.
  apply (partition_forest_leb_spec EV HV).
Qed.

(** The prepared checker decides signature constancy on the actual candidate classes. *)
Theorem check_with_spec forms p :
  Cost.value (check_with_c np forms p) = true <->
  p <> None /\
  forall x y, In x (domain EV values p) -> In y (domain EV values p) ->
    partition_equiv EV p x y ->
    prepared_key np forms (domain EV values p) (class_c EV p) x =
      prepared_key np forms (domain EV values p) (class_c EV p) y.
Proof.
  rewrite check_with_equation; destruct p as [u|].
  - rewrite prepare_check_with, (check_prepared_spec np HV).
    split.
    + intro Hkeys; split; [discriminate|]; intros x y Hx Hy Heq.
      apply Hkeys; [exact Hx|exact Hy|].
      apply (proj2 (class_spec EV HV (Some u) x y)); exact Heq.
    + intros [_ Hkeys] x y Hx Hy Heq.
      apply Hkeys; [exact Hx|exact Hy|].
      apply (proj1 (class_spec EV HV (Some u) x y)); exact Heq.
  - split; [discriminate|intros [Hnone _]; contradiction].
Qed.

(** A refinement is equivalent to its input exactly when the actual prepared checker accepts. *)
Theorem refine_with_fix_iff_check forms p :
  partition_leb EV (refine_with forms p) p = true <->
    Cost.value (check_with_c np forms p) = true.
Proof.
  split.
  - intro Hfixed; apply check_with_spec.
    assert (Hp : p <> None).
    { destruct p as [u|]; [discriminate|].
      destruct (refine_with forms None) as [v|] eqn:Hnew; [discriminate Hfixed|].
      exfalso; exact (refine_with_reached forms None Hnew). }
    split; [exact Hp|]; intros x y Hx Hy Heq.
    pose proof (partition_leb_sound EV HV _ _ Hfixed x y Heq) as Hnew.
    apply refine_with_spec in Hnew as [_ [Hsame|[_ [_ Hslots]]]].
    + now subst y.
    + rewrite prepare_check_with in Hslots.
      apply (proj1 (slot_spec np HV forms (domain EV values p) (class_c EV p) x y Hx Hy)).
      exact Hslots.
  - intro Hchecked; apply check_with_spec in Hchecked as [Hp Hkeys].
    apply (proj2 (partition_order _ _ (refine_with_reached forms p) Hp)).
    intros x y Heq; apply refine_with_spec; split; [exact Heq|].
    destruct (eqb_dec EV HV x y) as [Hsame|Hne]; [now left|].
    destruct (domain_pair p x y Hp Heq Hne) as [Hx Hy].
    right; split; [exact Hx|split; [exact Hy|]].
    rewrite prepare_check_with.
    apply (proj2 (slot_spec np HV forms (domain EV values p) (class_c EV p) x y Hx Hy)).
    now apply Hkeys.
Qed.

(** Public refinement fixes exactly the arbitrary partitions accepted by the public checker. *)
Theorem refine_step_fix_iff_check p :
  partition_leb EV (refine_step p) p = true <-> check np p = true.
Proof.
  rewrite refine_step_with, check_with_prepared; apply refine_with_fix_iff_check.
Qed.

(** Every rejected reached check exhibits the pair split by its actual refinement. *)
Theorem refine_with_split forms p :
  supported p -> Cost.value (check_with_c np forms p) = false ->
  exists x y, In x values /\ In y values /\ partition_equiv EV p x y /\
    ~ partition_equiv EV (refine_with forms p) x y.
Proof.
  intros [Hp Hsupport] Hbad.
  rewrite check_with_equation in Hbad; destruct p as [u|]; [|contradiction].
  rewrite prepare_check_with in Hbad.
  destruct (check_prepared_bad np HV forms (domain EV values (Some u))
    (class_c EV (Some u)) Hbad) as [x [y [Hx [Hy [Hclass Hkeys]]]]].
  assert (Heq : partition_equiv EV (Some u) x y).
  { apply (proj1 (class_spec EV HV (Some u) x y)); exact Hclass. }
  assert (Hne : x <> y) by (intro Hsame; subst y; apply Hkeys; reflexivity).
  destruct (Hsupport x y Heq) as [Hsame|[Hvx Hvy]]; [contradiction|].
  exists x, y; split; [exact Hvx|split; [exact Hvy|split; [exact Heq|]]].
  intro Hnew; apply refine_with_spec in Hnew as [_ [Hsame|[_ [_ Hslots]]]];
    [contradiction|].
  apply Hkeys; rewrite prepare_check_with in Hslots.
  apply (proj1 (slot_spec np HV forms (domain EV values (Some u))
    (class_c EV (Some u)) x y Hx Hy)); exact Hslots.
Qed.

(** The boolean class relation is used only as a proof measure for the actual runtime partition. *)
Definition equivalent_b p x y := Pos.eqb (class EV p x) (class EV p y).

(** Boolean class comparison reflects the actual partition relation. *)
Theorem equivalent_spec p x y :
  equivalent_b p x y = true <-> partition_equiv EV p x y.
Proof.
  unfold equivalent_b; rewrite Pos.eqb_eq; apply class_spec; exact HV.
Qed.

(** Every represented class relation supplies the laws needed by finite class counting. *)
Theorem equivalent_laws p : NumberingClasses.equivalence (equivalent_b p).
Proof.
  constructor.
  - intro x; unfold equivalent_b; apply Pos.eqb_refl.
  - intros x y; unfold equivalent_b; rewrite !Pos.eqb_eq; congruence.
  - intros x y z; unfold equivalent_b; rewrite !Pos.eqb_eq; congruence.
Qed.

Definition class_count p := NumberingClasses.classes (equivalent_b p) values.

(** The actual rejected refinement strictly increases the class count on the fixed inventory. *)
Theorem refine_class_progress forms p :
  supported p -> Cost.value (check_with_c np forms p) = false ->
  class_count p < class_count (refine_with forms p).
Proof.
  intros Hsupport Hbad; apply NumberingClasses.classes_strict.
  - apply equivalent_laws.
  - apply equivalent_laws.
  - intros x y Hnew; apply equivalent_spec in Hnew; apply equivalent_spec.
    apply refine_with_spec in Hnew; tauto.
  - destruct (refine_with_split forms p Hsupport Hbad)
      as [x [y [Hx [Hy [Hold Hnew]]]]].
    exists x, y; split; [exact Hx|split; [exact Hy|split]].
    + now apply equivalent_spec.
    + destruct (equivalent_b (refine_with forms p) x y) eqn:Htest; [|reflexivity].
      exfalso; apply Hnew; now apply equivalent_spec.
Qed.

(** Class counting is bounded by the original inventory length, even with duplicate occurrences. *)
Theorem class_count_bound p : class_count p <= length values.
Proof.
  apply NumberingClasses.classes_bound.
Qed.

(** The numeric potential is the remaining class capacity of the fixed value inventory. *)
Definition potential p := N.of_nat (length values - class_count p).

(** The potential used for the iteration cost argument decreases on each actual continuing round. *)
Theorem refine_potential_decreases forms p :
  supported p -> Cost.value (check_with_c np forms p) = false ->
  (potential (refine_with forms p) < potential p)%N.
Proof.
  intros Hsupport Hbad; unfold potential.
  pose proof (refine_class_progress forms p Hsupport Hbad) as Hprogress.
  pose proof (class_count_bound (refine_with forms p)) as Hbound.
  lia.
Qed.

(** A non-idempotent actual refinement increases the finite number of classes. *)
Theorem refine_nonfix_progress p :
  supported p -> partition_leb EV (refine_step p) p = false ->
  class_count p < class_count (refine_step p).
Proof.
  intros Hsupport Hnonfix; rewrite refine_step_with.
  apply refine_class_progress; [exact Hsupport|].
  destruct (check np p) eqn:Hcheck.
  - apply refine_step_fix_iff_check in Hcheck; congruence.
  - rewrite <- check_with_prepared; exact Hcheck.
Qed.

(** Reusable refinement preserves support using its actual join relation. *)
Theorem refine_with_supported forms p :
  supported p -> supported (refine_with forms p).
Proof.
  intros [_ Hsupport]; split; [apply refine_with_reached|].
  intros x y Hnew; apply refine_with_spec in Hnew as [Hold _]; now apply Hsupport.
Qed.

(** Runtime state records the candidate and the number of completed signature rounds. *)
Definition state := (part * nat)%type.

(** One runtime round prepares signatures once and either stops or applies that same snapshot.
    A raw unreachable candidate stops with None and is decoded as Rejected. *)
Definition advance_c forms (s : state) : Cost.t (state + state) :=
  let '(p, rounds) := s in
  match p with
  | None => Cost.ret (inr (None, S rounds))
  | Some _ =>
    let* pr := prepare_check_c np forms p in
    let* accepted := check_prepared_c np pr in
    if accepted then Cost.ret (inr (p, S rounds))
    else
      let* next := refine_prepared_c p pr in
      Cost.ret (inl (next, S rounds))
  end.

(** The round equation relates the runtime counter to the same checked refinement operation. *)
Theorem advance_equation forms p rounds :
  p <> None ->
  Cost.value (advance_c forms (p, rounds)) =
    if Cost.value (check_with_c np forms p)
    then inr (p, S rounds)
    else inl (refine_with forms p, S rounds).
Proof.
  destruct p as [u|]; [intros _|contradiction].
  unfold advance_c, refine_with, refine_step_with_c, check_with_c.
  autorewrite with galois_cost.
  fold (prepare_check np forms (Some u)).
  fold (check_prepared np (prepare_check np forms (Some u))).
  destruct (check_prepared np (prepare_check np forms (Some u))); reflexivity.
Qed.

(** An exhausted run has performed exactly its fuel in strict, support-preserving refinements. *)
Theorem exhausted_progress forms n start result :
  runs (advance_c forms) n start (inl result) ->
  supported (fst start) ->
  supported (fst result) /\
    class_count (fst start) + n <= class_count (fst result) /\
    snd result = snd start + n.
Proof.
  intro Hrun; remember (inl result) as outcome eqn:Houtcome.
  induction Hrun as [s|n s r Hstop|n s next outcome Hnext Hrun IH]; intro Hsupport.
  - injection Houtcome as <-; split; [exact Hsupport|split; cbn; lia].
  - discriminate.
  - destruct s as [p rounds].
    change (Cost.value (advance_c forms (p, rounds)) = inl next) in Hnext.
    pose proof (eq_trans (eq_sym (advance_equation forms p rounds (proj1 Hsupport))) Hnext)
      as Htransition.
    clear Hnext; rename Htransition into Hnext.
    destruct (Cost.value (check_with_c np forms p)) eqn:Hcheck; [discriminate|].
    injection Hnext as <-.
    destruct (IH Houtcome (refine_with_supported forms p Hsupport))
      as [Hlast [Hgrowth Hrounds]].
    pose proof (refine_class_progress forms p Hsupport Hcheck) as Hstrict.
    cbn [fst snd] in *; split; [exact Hlast|split; lia].
Qed.

(** A stopped run returns an actually checked candidate and a counter bounded by its fuel. *)
Theorem stopped_checked forms n start result :
  runs (advance_c forms) n start (inr result) ->
  supported (fst start) ->
  supported (fst result) /\
    Cost.value (check_with_c np forms (fst result)) = true /\
    snd result <= snd start + n.
Proof.
  intro Hrun; remember (inr result) as outcome eqn:Houtcome.
  induction Hrun as [s|n s r Hstop|n s next outcome Hnext Hrun IH]; intro Hsupport.
  - discriminate.
  - destruct s as [p rounds].
    change (Cost.value (advance_c forms (p, rounds)) = inr r) in Hstop.
    pose proof (eq_trans (eq_sym (advance_equation forms p rounds (proj1 Hsupport))) Hstop)
      as Htransition.
    clear Hstop; rename Htransition into Hstop.
    destruct (Cost.value (check_with_c np forms p)) eqn:Hcheck; [|discriminate].
    injection Hstop as <-; injection Houtcome as <-.
    split; [exact Hsupport|split; [exact Hcheck|cbn; lia]].
  - destruct s as [p rounds].
    change (Cost.value (advance_c forms (p, rounds)) = inl next) in Hnext.
    pose proof (eq_trans (eq_sym (advance_equation forms p rounds (proj1 Hsupport))) Hnext)
      as Htransition.
    clear Hnext; rename Htransition into Hnext.
    destruct (Cost.value (check_with_c np forms p)) eqn:Hcheck; [discriminate|].
    injection Hnext as <-.
    destruct (IH Houtcome (refine_with_supported forms p Hsupport))
      as [Hlast [Hchecked Hrounds]].
    split; [exact Hlast|split; [exact Hchecked|cbn in *; lia]].
Qed.

(** At most the inventory length of strict refinements precedes an accepting round. *)
Theorem finish_finishes forms initial :
  supported initial ->
  exists final,
    Cost.value (iterate (advance_c forms) (Pos.of_succ_nat (length values)) (initial, 0)) =
      inr final /\
    Cost.value (check_with_c np forms (fst final)) = true /\
    snd final <= S (length values).
Proof.
  intro Hsupport.
  pose proof (iterate_value (advance_c forms)
    (Pos.of_succ_nat (length values)) (initial, 0)) as Hrun.
  destruct (Cost.value (iterate (advance_c forms)
    (Pos.of_succ_nat (length values)) (initial, 0))) as [exhausted|final] eqn:Hresult.
  - destruct (exhausted_progress forms _ _ _ Hrun Hsupport) as [_ [Hgrowth _]].
    rewrite SuccNat2Pos.id_succ in Hgrowth.
    pose proof (class_count_bound (fst exhausted)); cbn [fst] in Hgrowth; lia.
  - exists final; split; [reflexivity|].
    destruct (stopped_checked forms _ _ _ Hrun Hsupport) as [_ [Hchecked Hrounds]].
    rewrite SuccNat2Pos.id_succ in Hrounds; cbn [snd] in Hrounds.
    split; assumption.
Qed.

(** Public outcomes keep exhaustion and malformed raw starts distinct from solved candidates. *)
Inductive outcome : Type :=
  | Solved (candidate : part) (rounds : nat)
  | OutOfFuel (candidate : part) (rounds : nat)
  | Rejected (rounds : nat).

(** The reported round count is the counter maintained by each actual driver callback. *)
Definition rounds_of result :=
  match result with
  | Solved _ rounds => rounds
  | OutOfFuel _ rounds => rounds
  | Rejected rounds => rounds
  end.

(** Solved outcomes contain one final accepting round after their strict refinements. *)
Definition strict_rounds_of result :=
  match result with
  | Solved _ rounds => Nat.pred rounds
  | OutOfFuel _ rounds => rounds
  | Rejected _ => 0
  end.

Definition decode (result : state + state) : outcome :=
  match result with
  | inl (p, rounds) =>
    match p with
    | None => Rejected rounds
    | Some _ => OutOfFuel p rounds
    end
  | inr (p, rounds) =>
    match p with
    | None => Rejected rounds
    | Some _ => Solved p rounds
    end
  end.

(** The raw finite driver exposes its supplied start and fuel without an implicit fallback. *)
Definition finish_c forms initial fuel :=
  Cost.map decode (iterate (advance_c forms) fuel (initial, 0)).

(** Optimistic numbering prepares static syntax and the shape once before its bounded driver. *)
Definition optimistic_c : Cost.t outcome :=
  let* forms := prepare_c np in
  let* initial := shape_partition_with_c forms in
  let* count := length_c values in
  finish_c forms initial (Pos.of_succ_nat count).

(** The raw outcome remains available even when a caller only requests its candidate projection. *)
Definition candidate_of result : part :=
  match result with
  | Solved p _ => p
  | OutOfFuel p _ => p
  | Rejected _ => None
  end.

Definition optimistic : part := candidate_of (Cost.value optimistic_c).

(** The runtime outcome is produced by the same binary driver used in the adequacy proof. *)
Theorem optimistic_equation :
  Cost.value optimistic_c =
    decode (Cost.value (iterate (advance_c (prepare np))
      (Pos.of_succ_nat (length values)) (shape_partition, 0))).
Proof.
  unfold optimistic_c, finish_c; autorewrite with galois_cost.
  rewrite ?value_length_c; reflexivity.
Qed.

(** Optimistic numbering always solves within |V|+1 actual signature rounds. *)
Theorem optimistic_finishes :
  exists p rounds, Cost.value optimistic_c = Solved p rounds /\
    rounds <= S (length values) /\ check np p = true.
Proof.
  destruct (finish_finishes (prepare np) shape_partition shape_supported)
    as [[p rounds] [Hfinish [Hcheck Hrounds]]].
  rewrite <- check_with_prepared in Hcheck.
  change (check np p = true) in Hcheck.
  assert (Hp : p <> None).
  { destruct p; [discriminate|change (false = true) in Hcheck; discriminate]. }
  exists p, rounds; rewrite optimistic_equation, Hfinish; cbn [decode].
  destruct p; [split; [reflexivity|split; assumption]|contradiction].
Qed.

(** The candidate projection of optimistic numbering passes the actual public checker. *)
Theorem optimistic_checked : check np optimistic = true.
Proof.
  destruct optimistic_finishes as [p [rounds [Hresult [_ Hcheck]]]].
  unfold optimistic; rewrite Hresult; exact Hcheck.
Qed.

(** The public producer attaches its checker certificate with the shared certification API. *)
Definition numbering_certified :=
  certify (fun p => check np p = true) (check np) (fun _ accepted => accepted) optimistic.

(** Certification succeeds for the actual optimistic producer output. *)
Theorem numbering_certified_some : exists result, numbering_certified = Some result.
Proof.
  apply (proj2 (certify_some_iff _ _ _ _)); apply optimistic_checked.
Qed.

(** Prepared class keys agree with direct class queries at every key of a reached candidate. *)
Theorem prepared_key_direct p x :
  p <> None ->
  prepared_key np (prepare np) (domain EV values p) (class_c EV p) x =
    signature np (prepare np) (class_c EV p) x.
Proof.
  intro Hp; unfold prepared_key; apply signature_ext.
  intro a; exact (cached_class_total np HV p a Hp).
Qed.

(** A refinement preserves every equality of any checked finer candidate. *)
Theorem refine_preserves_checked p q :
  supported p -> check np q = true -> partition_leb EV p q = true ->
  partition_leb EV (refine_with (prepare np) p) q = true.
Proof.
  intros Hsupport Hcheck Hle.
  assert (Hq : q <> None).
  { destruct q; [discriminate|change (false = true) in Hcheck; discriminate]. }
  apply (proj2 (partition_order _ _ (refine_with_reached (prepare np) p) Hq)).
  intros x y Heq; apply refine_with_spec; split.
  - exact (partition_leb_sound EV HV p q Hle x y Heq).
  - destruct (eqb_dec EV HV x y) as [Hsame|Hne]; [now left|].
    pose proof (partition_leb_sound EV HV p q Hle x y Heq) as Hp.
    destruct (proj2 Hsupport x y Hp) as [Hsame|[Hx Hy]]; [contradiction|].
    assert (Hdx : In x (domain EV values p)) by now apply domain_values.
    assert (Hdy : In y (domain EV values p)) by now apply domain_values.
    right; split; [exact Hdx|split; [exact Hdy|]].
    rewrite prepare_check_with.
    apply (proj2 (slot_spec np HV (prepare np) (domain EV values p)
      (class_c EV p) x y Hdx Hdy)).
    rewrite !prepared_key_direct by exact (proj1 Hsupport).
    apply (signature_monotone np (prepare np) (class_c EV q) (class_c EV p) x y).
    + intros a b Hab; apply (proj2 (class_spec EV HV p a b)).
      apply (partition_leb_sound EV HV p q Hle a b).
      apply (proj1 (class_spec EV HV q a b)); exact Hab.
    + pose proof (check_signatures np HV q x y Hcheck Hx Hy Heq) as Hkeys.
      change (prepared_key np (prepare np) (domain EV values q) (class_c EV q) x =
        prepared_key np (prepare np) (domain EV values q) (class_c EV q) y) in Hkeys.
      rewrite !prepared_key_direct in Hkeys by exact Hq; exact Hkeys.
Qed.

(** Both raw driver outcomes retain every checked candidate initially finer than the start. *)
Theorem runs_preserves_checked q n start result :
  check np q = true ->
  runs (advance_c (prepare np)) n start result ->
  supported (fst start) -> partition_leb EV (fst start) q = true ->
  match result with
  | inl s => partition_leb EV (fst s) q = true
  | inr s => partition_leb EV (fst s) q = true
  end.
Proof.
  intros Hcheck Hrun; induction Hrun as [s|n s r Hstop|n s next result Hnext Hrun IH];
    intros Hsupport Hle.
  - exact Hle.
  - destruct s as [p rounds].
    change (Cost.value (advance_c (prepare np) (p, rounds)) = inr r) in Hstop.
    pose proof (eq_trans
      (eq_sym (advance_equation (prepare np) p rounds (proj1 Hsupport))) Hstop) as Htransition.
    clear Hstop; rename Htransition into Hstop.
    destruct (Cost.value (check_with_c np (prepare np) p)); [|discriminate].
    injection Hstop as <-; exact Hle.
  - destruct s as [p rounds].
    change (Cost.value (advance_c (prepare np) (p, rounds)) = inl next) in Hnext.
    pose proof (eq_trans
      (eq_sym (advance_equation (prepare np) p rounds (proj1 Hsupport))) Hnext) as Htransition.
    clear Hnext; rename Htransition into Hnext.
    destruct (Cost.value (check_with_c np (prepare np) p)); [discriminate|].
    injection Hnext as <-.
    apply IH.
    + now apply refine_with_supported.
    + now apply refine_preserves_checked.
Qed.

(** Decoding keeps the actual runtime candidate in both stopping and exhaustion outcomes. *)
Theorem decode_candidate result :
  candidate_of (decode result) =
    match result with
    | inl s => fst s
    | inr s => fst s
    end.
Proof.
  destruct result as [[p rounds]|[p rounds]]; destruct p; reflexivity.
Qed.

(** Optimistic numbering is the coarsest checked congruence above its shape partition. *)
Theorem optimistic_coarsest q :
  check np q = true -> partition_leb EV shape_partition q = true ->
  partition_leb EV optimistic q = true.
Proof.
  intros Hcheck Hshape; unfold optimistic; rewrite optimistic_equation, decode_candidate.
  pose proof (runs_preserves_checked q _ _ _ Hcheck
    (iterate_value (advance_c (prepare np))
      (Pos.of_succ_nat (length values)) (shape_partition, 0)) shape_supported Hshape) as Hrun.
  destruct (Cost.value (iterate (advance_c (prepare np))
    (Pos.of_succ_nat (length values)) (shape_partition, 0))); exact Hrun.
Qed.

End Refinement.

End NumberingRefine.
