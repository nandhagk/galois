(** * Labelled partition clients

    These clients distinguish label routing, bottom parts and capped joins over integer states.
    For example, a stray skips a bottom part and widens the first live part.
    Builds on: Partition, Env, Interval and ZLang.

    Groups:
    - [CoverageTests] Coverage of parts by labels.
    - [JoinTests] Joins of parts, with and without a label overflow.
    - [WideningTests] Routed widening of parts, and the widening coverage theorem.
    - [BigOTests] The size and work bounds of the timed partition and disjunction. *)

From Stdlib Require Import List NArith ZArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import LatticeSig Simple JoinWidening Disjunction.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval ThresholdsSig
  Thresholds ZLang.
From Galois.States Require Import StateSig DisjunctionSig EnvSig Env Disjunction Partition.
Import List.ListNotations.

(** * Fixtures *)

Module Vars := TrieMap BoolKey.
Module Values := Interval ZLang Thresholds.
Module State := Env BoolKey Vars ZLang Values.

(** A partition cap of two live parts, with its proof that the cap is positive. *)
Module Cap.
  Definition k := 2%nat.
  (** The cap is positive. *)
  Lemma k_pos : (0 < k)%nat.
  Proof.
    unfold k; lia.
  Qed.
End Cap.
Module Parts := Partition BoolKey NatKey ZLang Values State Cap.

(** The state that holds the interval [z, z] for variable false. *)
Definition point (z : Z) : State.t :=
  Reached (Vars.set false (I (Fin z) (Fin z)) Vars.empty).

(** The parts of a partition as pairs of label and the value of variable false. *)
Definition observe (a : Parts.t) :=
  map (fun q => (fst q, State.eval (Leaf false) (snd q))) (proj1_sig a).

(** Two live parts, labelled 1 and 2, holding the points 0 and 10. *)
Definition two_live := Parts.fit [(Some 1%nat, point 0); (Some 2%nat, point 10)].

(** A bottom part labelled 1 followed by a live part labelled 2 holding the point 0. *)
Definition bottom_then_live := Parts.fit [(Some 1%nat, State.bot); (Some 2%nat, point 0)].

Module CoverageTests.

  (** A part under label 1 is covered by the same state under label 2. *)
  Example labels_do_not_restrict_coverage :
    Parts.leb (Parts.inject 1%nat (point 0)) (Parts.inject 2%nat (point 0)) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CoverageTests.

Module JoinTests.

  (** Joining two states under one label keeps one part with their joined values. *)
  Example equal_labels_merge_into_one_part :
    observe (Parts.join (Parts.inject 1%nat (point 0)) (Parts.inject 1%nat (point 5))) =
      [(Some 1%nat, I (Fin 0) (Fin 5))].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** When the parts overflow, the first label stays and the rest merge under no label. *)
  Example overflow_keeps_first_label :
    observe (Parts.join two_live (Parts.inject 3%nat (point 20))) =
      [(Some 1%nat, I (Fin 0) (Fin 0)); (None, I (Fin 10) (Fin 20))].
  Proof.
    vm_compute; reflexivity.
  Qed.

End JoinTests.

Module WideningTests.

  (** A state with a matching label widens the part with that label. *)
  Example matching_label_routes_to_its_part :
    observe (Parts.widen TLeaf two_live (Parts.inject 2%nat (point 20))) =
      [(Some 1%nat, I (Fin 0) (Fin 0)); (Some 2%nat, I (Fin 10) PosInf)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A state with an unknown label skips the bottom parts and widens the first live part. *)
  Example stray_state_skips_bottom_part :
    observe (Parts.widen TLeaf bottom_then_live (Parts.inject 3%nat (point 5))) =
      [(Some 1%nat, IBot); (Some 2%nat, I (Fin 0) PosInf)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A partition with only bottom parts takes the candidate state under its label. *)
  Example all_bottom_keeps_candidate :
    observe (Parts.widen TLeaf (Parts.inject 1%nat State.bot) (Parts.inject 3%nat (point 5))) =
      [(Some 3%nat, I (Fin 5) (Fin 5))].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A routed widening lowers the sum of the ranks of the live parts. *)
  Example routed_update_lowers_rank :
    Nat.ltb (Parts.wrank TLeaf
      (Parts.widen TLeaf bottom_then_live (Parts.inject 3%nat (point 5))))
      (Parts.wrank TLeaf bottom_then_live) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The widening of any two partitions covers its second argument. *)
  Example widening_covers_second_argument :
    forall p a b, Parts.leb b (Parts.widen p a b) = true.
  Proof.
    exact Parts.widen_ub_r.
  Qed.

End WideningTests.

Module BigOTests.

  (** A concrete reachability state supplies the timed partition's two join budgets. *)
  Module TimedValues := IntervalT ZLangT ThresholdsT.

  Module LiveStateT <: STATE_DOMAIN_T BoolKeyT ZLangT TimedValues.
    Include BoolLatT.
    Module Widening := JoinWideningT BoolLatT BoolLatHeight.
    Include Widening.

    Definition gamma (a : t) (_ : BoolKeyT.t -> ZLangT.val) : Prop := a = true.
    Definition assign (_ : BoolKeyT.t) (_ : term ZLangT.op BoolKeyT.t) (a : t) := a.
    Definition havoc (_ : BoolKeyT.t) (a : t) := a.
    Definition assume (_ : ZLangT.guard) (_ : list (term ZLangT.op BoolKeyT.t)) (a : t) := a.
    Definition eval (_ : term ZLangT.op BoolKeyT.t) (_ : t) := TimedValues.top.

    (** The concretization is monotone in the order. *)
    Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
    Proof.
      intros [] [] st; cbn [leb Bool.implb gamma]; congruence.
    Qed.
    (** The bottom value has no concretization. *)
    Lemma gamma_bot : forall st, ~ gamma bot st.
    Proof.
      intros st; discriminate.
    Qed.
    (** The top value describes every state. *)
    Lemma gamma_top : forall st, gamma top st.
    Proof.
      reflexivity.
    Qed.
    (** Assignment is sound. *)
    Lemma assign_sound : forall x e s st c,
      gamma s st -> eval_term ZLangT.eval st e = Some c ->
      gamma (assign x e s) (upd BoolKeyT.eqb st x c).
    Proof.
      intros x e s st c Hs _; exact Hs.
    Qed.
    (** Havoc is sound. *)
    Lemma havoc_sound : forall x s st c,
      gamma s st -> gamma (havoc x s) (upd BoolKeyT.eqb st x c).
    Proof.
      intros x s st c Hs; exact Hs.
    Qed.
    (** Assumption is sound. *)
    Lemma assume_sound : forall g es s st cs,
      gamma s st -> eval_terms ZLangT.eval st es = Some cs -> ZLangT.holds g cs ->
      gamma (assume g es s) st.
    Proof.
      intros g es s st cs Hs _ _; exact Hs.
    Qed.
    (** Evaluation is sound. *)
    Lemma eval_sound : forall e s st c,
      gamma s st -> eval_term ZLangT.eval st e = Some c -> TimedValues.gamma (eval e s) c.
    Proof.
      intros e s st c _ _; apply TimedValues.gamma_top.
    Qed.

    Definition assign_work (_ : BoolKeyT.t) (_ : term ZLangT.op BoolKeyT.t) (_ : t) := 0%nat.
    Definition havoc_work (_ : BoolKeyT.t) (_ : t) := 0%nat.
    Definition assume_work (_ : ZLangT.guard) (_ : list (term ZLangT.op BoolKeyT.t))
      (_ : t) := 0%nat.
    Definition eval_work (_ : term ZLangT.op BoolKeyT.t) (_ : t) := 0%nat.
    TimeFun assign.
    TimeFun havoc.
    TimeFun assume.
    TimeFun eval.
    Definition c_state := 16%N.
    (** The assignment time is within its work measure. *)
    Lemma T_assign_le : forall x e a,
      (T_assign x e a <= c_state * N.of_nat (assign_work x e a + 1))%N.
    Proof.
      intros; unfold c_state, assign_work; time_step.
    Qed.
    (** The havoc time is within its work measure. *)
    Lemma T_havoc_le : forall x a,
      (T_havoc x a <= c_state * N.of_nat (havoc_work x a + 1))%N.
    Proof.
      intros; unfold c_state, havoc_work; time_step.
    Qed.
    (** The assumption time is within its work measure. *)
    Lemma T_assume_le : forall g es a,
      (T_assume g es a <= c_state * N.of_nat (assume_work g es a + 1))%N.
    Proof.
      intros; unfold c_state, assume_work; time_step.
    Qed.
    (** The evaluation time is within its work measure. *)
    Lemma T_eval_le : forall e a,
      (T_eval e a <= c_state * N.of_nat (eval_work e a + 1))%N.
    Proof.
      intros; unfold c_state, eval_work; time_step.
    Qed.
  End LiveStateT.

  Module LiveJoinSize <: JOIN_SIZE LiveStateT.
    (** A join of two live states has a constant size. *)
    Lemma join_size : forall a b,
      (N.of_nat (LiveStateT.size (LiveStateT.join a b)) <=
        LiveStateT.c_lat * N.of_nat (LiveStateT.size a + LiveStateT.size b + 1))%N.
    Proof.
      intros; change (1 <= 3)%N; lia.
    Qed.
  End LiveJoinSize.

  Module LiveJoinUnits <: JOIN_UNITS BoolKeyT ZLangT TimedValues LiveStateT.
    (** A join of two live states has a constant number of widening units. *)
    Lemma join_wunits : forall a b,
      (N.of_nat (LiveStateT.wunits (LiveStateT.join a b)) <= LiveStateT.c_lat *
        N.of_nat (LiveStateT.wunits a + LiveStateT.wunits b + 1))%N.
    Proof.
      intros; change (2 <= 5)%N; lia.
    Qed.
  End LiveJoinUnits.

  Module TimedParts :=
    PartitionT BoolKeyT BoolKeyT ZLangT TimedValues LiveStateT LiveJoinSize LiveJoinUnits Cap.

  (** The concrete timed instance exports the universal joined-size contract. *)
  Example join_size_contract : forall a b,
    (N.of_nat (TimedParts.size (TimedParts.join a b)) <=
      TimedParts.c_lat * N.of_nat (TimedParts.size a + TimedParts.size b + 1))%N.
  Proof.
    exact TimedParts.join_size.
  Qed.

  (** The concrete timed instance exports the widening work contract. *)
  Example widen_work_contract : forall p a b,
    (TimedParts.T_widen p a b <= TimedParts.c_lat * N.of_nat
      ((TimedParts.wunits a + TimedParts.wunits b) * TimedParts.wsize p +
        (TimedParts.size a + TimedParts.size b + TimedParts.wsize p + 1)))%N.
  Proof.
    exact TimedParts.T_widen_le.
  Qed.

  (** Evaluation pays for the concrete component evaluations and actual joins. *)
  Example eval_work_contract : forall e a,
    (TimedParts.T_eval e a <=
      TimedParts.c_state * N.of_nat (TimedParts.eval_work e a + 1))%N.
  Proof.
    exact TimedParts.T_eval_le.
  Qed.

  (** The two-part fixture includes a bottom component and a live component. *)
  Definition timed_parts := TimedParts.fit [(Some false, false); (Some true, true)].

  (** Inclusion satisfies the published linear measure on a full partition. *)
  Example inclusion_within_size_bound :
    (TimedParts.T_leb timed_parts timed_parts <= TimedParts.c_lat *
      (N.of_nat (TimedParts.size timed_parts + TimedParts.size timed_parts) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Widening uses the same size and parameter measure as its big-O field. *)
  Example widen_within_work_bound :
    (TimedParts.T_widen tt TimedParts.bot timed_parts <= TimedParts.c_lat *
      (N.of_nat ((TimedParts.wunits TimedParts.bot + TimedParts.wunits timed_parts) *
        TimedParts.wsize tt +
        (TimedParts.size TimedParts.bot + TimedParts.size timed_parts +
          TimedParts.wsize tt)) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Assignment is bounded by its transfer work on both parts. *)
  Example assign_within_work_bound :
    (TimedParts.T_assign true (Leaf false) timed_parts <= TimedParts.c_state *
      (N.of_nat (TimedParts.assign_work true (Leaf false) timed_parts) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Retagging pays for the new token and all parts that it collapses. *)
  Example retag_within_size_bound :
    (TimedParts.T_retag true timed_parts <= TimedParts.c_partition *
      (N.of_nat (BoolKeyT.bits true + TimedParts.size timed_parts) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  Module TimedShared := DisjunctionT LiveStateT LiveJoinSize Cap.
  Module TimedDisjunction :=
    StateDisjunctionT BoolKeyT ZLangT TimedValues LiveStateT
      LiveJoinSize LiveJoinUnits Cap TimedShared.

  Definition timed_alternatives := TimedShared.clip [false; true].

  (** The widening budget of the disjunction, in the measure of its big-O field. *)
  Definition disjunction_widen_budget : N :=
    (TimedDisjunction.c_lat * (N.of_nat
        ((TimedDisjunction.wunits TimedDisjunction.bot +
          TimedDisjunction.wunits timed_alternatives) * TimedDisjunction.wsize tt +
          (TimedDisjunction.size TimedDisjunction.bot + TimedDisjunction.size timed_alternatives +
            TimedDisjunction.wsize tt)) + 1))%N.

  (** The disjunction widening bound includes the component parameter cost. *)
  Example disjunction_widen_within_work_bound :
    (TimedDisjunction.T_widen tt TimedDisjunction.bot timed_alternatives <=
      disjunction_widen_budget)%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Narrowing satisfies the two-size measure on a full disjunction. *)
  Example disjunction_narrow_within_size_bound :
    (TimedDisjunction.T_narrow timed_alternatives timed_alternatives <=
      TimedDisjunction.c_lat *
        (N.of_nat (TimedDisjunction.size timed_alternatives +
          TimedDisjunction.size timed_alternatives) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Assignment pays for each alternative through the transfer work measure. *)
  Example disjunction_assign_within_work_bound :
    (TimedDisjunction.T_assign true (Leaf false) timed_alternatives <=
      TimedDisjunction.c_state *
        (N.of_nat (TimedDisjunction.assign_work true (Leaf false) timed_alternatives) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Collapse satisfies its measure at the permitted cap-plus-one boundary. *)
  Example collapse_within_size_bound :
    (TimedDisjunction.T_collapse [false; true; false] <= TimedDisjunction.c_disjunction *
      (N.of_nat (fold_right Nat.add 0%nat (map LiveStateT.size [false; true; false]) +
        length [false; true; false]) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.
End BigOTests.
