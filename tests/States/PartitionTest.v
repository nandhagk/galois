(** * Labelled partition clients

    These clients distinguish label routing, bottom parts and capped joins over integer states.
    For example, a stray skips a bottom part and widens the first live part.
    Builds on: Partition, Env, Interval and ZLang. *)

From Stdlib Require Import List NArith ZArith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Key Map.
From Galois.Lattice Require Import LatticeSig Simple JoinWidening.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval ThresholdsSig Thresholds ZLang.
From Galois.States Require Import StateSig DisjunctionSig EnvSig Env Partition.
Import List.ListNotations.

Module Vars := TrieMap BoolKey.
Module Values := Interval ZLang Thresholds.
Module State := Env BoolKey Vars ZLang Values.
Module Cap.
  Definition k := 2%nat.
  Lemma k_pos : (0 < k)%nat.
  Proof.
    unfold k; lia.
  Qed.
End Cap.
Module Parts := Partition BoolKey NatKey ZLang Values State Cap.

Definition point (z : Z) : State.t :=
  Reached (Vars.set false (I (Fin z) (Fin z)) Vars.empty).

Definition observe (a : Parts.t) :=
  map (fun q => (fst q, State.eval (Leaf false) (snd q))) (proj1_sig a).

Definition two_live := Parts.fit [(Some 1%nat, point 0); (Some 2%nat, point 10)].
Definition bottom_then_live := Parts.fit [(Some 1%nat, State.bot); (Some 2%nat, point 0)].

(** Coverage does not depend on labels. *)
Example labels_do_not_restrict_coverage :
  Parts.leb (Parts.inject 1%nat (point 0)) (Parts.inject 2%nat (point 0)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Joining equal labels keeps one part and joins its component states. *)
Example equal_labels_join_values :
  observe (Parts.join (Parts.inject 1%nat (point 0)) (Parts.inject 1%nat (point 5))) =
    [(Some 1%nat, I (Fin 0) (Fin 5))].
Proof.
  vm_compute; reflexivity.
Qed.

(** Overflow keeps the first label and collapses the remaining parts under no label. *)
Example overflow_preserves_prefix :
  observe (Parts.join two_live (Parts.inject 3%nat (point 20))) =
    [(Some 1%nat, I (Fin 0) (Fin 0)); (None, I (Fin 10) (Fin 20))].
Proof.
  vm_compute; reflexivity.
Qed.

(** A matching label routes the fresh state to its own receiver. *)
Example labelled_widening_updates_second_part :
  observe (Parts.widen TLeaf two_live (Parts.inject 2%nat (point 20))) =
    [(Some 1%nat, I (Fin 0) (Fin 0)); (Some 2%nat, I (Fin 10) PosInf)].
Proof.
  vm_compute; reflexivity.
Qed.

(** Stray routing skips parts below bottom. *)
Example stray_widening_skips_bottom :
  observe (Parts.widen TLeaf bottom_then_live (Parts.inject 3%nat (point 5))) =
    [(Some 1%nat, IBot); (Some 2%nat, I (Fin 0) PosInf)].
Proof.
  vm_compute; reflexivity.
Qed.

(** A partition with only bottom parts starts from the candidate. *)
Example all_bottom_widening_keeps_candidate :
  observe (Parts.widen TLeaf (Parts.inject 1%nat State.bot) (Parts.inject 3%nat (point 5))) =
    [(Some 3%nat, I (Fin 5) (Fin 5))].
Proof.
  vm_compute; reflexivity.
Qed.

(** A strict routed update decreases the computed sum of live ranks. *)
Example routed_rank_decreases :
  Nat.ltb (Parts.wrank TLeaf
    (Parts.widen TLeaf bottom_then_live (Parts.inject 3%nat (point 5))))
    (Parts.wrank TLeaf bottom_then_live) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The concrete state instance supplies the universal widening coverage theorem. *)
Example widening_coverage_client : forall p a b, Parts.leb b (Parts.widen p a b) = true.
Proof.
  exact Parts.widen_ub_r.
Qed.

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

  Lemma gamma_mono : forall a b st, leb a b = true -> gamma a st -> gamma b st.
  Proof.
    intros [] [] st; cbn [leb Bool.implb gamma]; congruence.
  Qed.
  Lemma gamma_bot : forall st, ~ gamma bot st.
  Proof.
    intros st; discriminate.
  Qed.
  Lemma gamma_top : forall st, gamma top st.
  Proof.
    reflexivity.
  Qed.
  Lemma assign_sound : forall x e s st c,
    gamma s st -> eval_term ZLangT.eval st e = Some c ->
    gamma (assign x e s) (upd BoolKeyT.eqb st x c).
  Proof.
    intros x e s st c Hs _; exact Hs.
  Qed.
  Lemma havoc_sound : forall x s st c,
    gamma s st -> gamma (havoc x s) (upd BoolKeyT.eqb st x c).
  Proof.
    intros x s st c Hs; exact Hs.
  Qed.
  Lemma assume_sound : forall g es s st cs,
    gamma s st -> eval_terms ZLangT.eval st es = Some cs -> ZLangT.holds g cs ->
    gamma (assume g es s) st.
  Proof.
    intros g es s st cs Hs _ _; exact Hs.
  Qed.
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
  Lemma T_assign_le : forall x e a,
    (T_assign x e a <= c_state * N.of_nat (assign_work x e a + 1))%N.
  Proof.
    intros; unfold c_state, assign_work; time_step.
  Qed.
  Lemma T_havoc_le : forall x a,
    (T_havoc x a <= c_state * N.of_nat (havoc_work x a + 1))%N.
  Proof.
    intros; unfold c_state, havoc_work; time_step.
  Qed.
  Lemma T_assume_le : forall g es a,
    (T_assume g es a <= c_state * N.of_nat (assume_work g es a + 1))%N.
  Proof.
    intros; unfold c_state, assume_work; time_step.
  Qed.
  Lemma T_eval_le : forall e a,
    (T_eval e a <= c_state * N.of_nat (eval_work e a + 1))%N.
  Proof.
    intros; unfold c_state, eval_work; time_step.
  Qed.
End LiveStateT.

Module LiveJoinSize <: JOIN_SIZE LiveStateT.
  Lemma join_size : forall a b,
    (N.of_nat (LiveStateT.size (LiveStateT.join a b)) <=
      LiveStateT.c_lat * N.of_nat (LiveStateT.size a + LiveStateT.size b + 1))%N.
  Proof.
    intros; change (1 <= 3)%N; lia.
  Qed.
End LiveJoinSize.

Module LiveJoinUnits <: JOIN_UNITS BoolKeyT ZLangT TimedValues LiveStateT.
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
Example timed_partition_join_size : forall a b,
  (N.of_nat (TimedParts.size (TimedParts.join a b)) <=
    TimedParts.c_lat * N.of_nat (TimedParts.size a + TimedParts.size b + 1))%N.
Proof.
  exact TimedParts.join_size.
Qed.

(** The concrete timed instance exports the widening work contract. *)
Example timed_partition_widen : forall p a b,
  (TimedParts.T_widen p a b <= TimedParts.c_lat * N.of_nat
    ((TimedParts.wunits a + TimedParts.wunits b) * TimedParts.wsize p +
      (TimedParts.size a + TimedParts.size b + TimedParts.wsize p + 1)))%N.
Proof.
  exact TimedParts.T_widen_le.
Qed.

(** Evaluation pays for the concrete component evaluations and actual joins. *)
Example timed_partition_eval : forall e a,
  (TimedParts.T_eval e a <=
    TimedParts.c_state * N.of_nat (TimedParts.eval_work e a + 1))%N.
Proof.
  exact TimedParts.T_eval_le.
Qed.
