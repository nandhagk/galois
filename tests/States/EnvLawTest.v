(** * Environment semantic clients

    These clients instantiate environment operations and laws over integer intervals.
    For example, two bindings describe different concrete values at their keys.
    Builds on: Env, Interval and ZLang.

    Groups:
    - [InclusionTests] Inclusion of environments, with bottom and unreached states.
    - [WideningTests] Widening of an environment with an unstable binding.
    - [SoundnessTests] The semantic clients of evaluation, assignment and guards.
    - [UpdateTests] Concrete replacements of a key by an update.
    - [BigOTests] Size and work bounds of the timed environment.
    - [EmptyKeyTests] The meaning of environments over a key type without elements. *)

From Stdlib Require Import List Bool NArith ZArith.
From Galois.Base Require Import Key KeySig Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval
  ThresholdsSig Thresholds ZLang.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module BoolMap := TrieMap BoolKey.
Module IntValues := Interval ZLang Thresholds.
Module IntEnv := Env BoolKey BoolMap ZLang IntValues.

(** The reached map that binds true to [2, 2] and false to [1, 1]. *)
Definition two_points_map :=
  BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false (I (Fin 1) (Fin 1)) BoolMap.empty).

(** The reached environment of the map two_points_map. *)
Definition two_points : IntEnv.t := Reached two_points_map.

(** The reached environment that binds true to [1, 4] and false to [0, 3]. *)
Definition two_ranges : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 1) (Fin 4))
    (BoolMap.set false (I (Fin 0) (Fin 3)) BoolMap.empty)).

(** The reached environment that binds true to [2, 2] and false to bottom. *)
Definition bottom_binding : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false IBot BoolMap.empty)).

(** The map that binds true to [3, 3] and false to bottom. *)
Definition bottom_mismatch_map :=
  BoolMap.set true (I (Fin 3) (Fin 3))
    (BoolMap.set false IBot BoolMap.empty).

(** The reached environment that binds true to [2, 2] and false to [3, 3]. *)
Definition raised_point : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false (I (Fin 3) (Fin 3)) BoolMap.empty)).

Module InclusionTests.

  (** An environment is included in itself. *)
  Example equal_environments_are_included : IntEnv.leb two_points two_points = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Point intervals are included in the wider ranges of the other environment. *)
  Example point_environment_is_below_range_environment :
    IntEnv.leb two_points two_ranges = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A range environment is not included in the point environment. *)
  Example range_environment_is_not_below_point_environment :
    IntEnv.leb two_ranges two_points = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A bottom binding on the right rejects a nonbottom left environment. *)
  Example bottom_binding_rejects_nonbottom_left : IntEnv.leb two_points bottom_binding = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A live mismatch makes the fused inclusion traversal fail. *)
  Example live_mismatch_fails_fused_traversal :
    BoolMap.forall2b IntEnv.leb_entry bottom_mismatch_map two_points_map = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A bottom binding on the left makes the fallback inclusion accept. *)
  Example bottom_left_binding_makes_fallback_accept :
    IntEnv.leb (Reached bottom_mismatch_map) two_points = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unreached left environment is included without inspecting the right one. *)
  Example unreached_is_below_any_environment : IntEnv.leb Unreached two_points = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A nonbottom reached environment is not included in an unreached one. *)
  Example nonbottom_is_not_below_unreached : IntEnv.leb two_points Unreached = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A reached bottom environment is included in an unreached state. *)
  Example reached_bottom_is_below_unreached : IntEnv.leb bottom_binding Unreached = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** An unreached state is included in an unreached state. *)
  Example unreached_is_below_unreached : IntEnv.leb Unreached Unreached = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End InclusionTests.

Module WideningTests.

  (** The widening of an environment with itself keeps it exactly. *)
  Example stable_widening_keeps_environment :
    IntEnv.widen TLeaf two_points two_points = two_points.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The widening of two_points with raised_point, which has one unstable binding. *)
  Definition widened := IntEnv.widen TLeaf two_points raised_point.

  (** The unstable binding widens its upper endpoint to plus infinity. *)
  Example unstable_binding_widens_upper_end :
    IntEnv.eval (Leaf false) widened = I (Fin 1) PosInf.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The stable binding keeps its point under the widening. *)
  Example stable_binding_keeps_point :
    IntEnv.eval (Leaf true) widened = I (Fin 2) (Fin 2).
  Proof.
    vm_compute; reflexivity.
  Qed.

End WideningTests.

Module SoundnessTests.

  (** The two-variable point environment is in its own concretization. *)
  Example two_variable_point_is_in_gamma :
    IntEnv.gamma two_points (fun x => if x then 2 else 1).
  Proof. vm_compute. split; [reflexivity | intros []; intuition discriminate]. Qed.

  (** Evaluation of a term is sound on every concrete state in the environment. *)
  Example eval_is_sound_on_concretized_states : forall e s st c,
    IntEnv.gamma s st -> eval_term ZLang.eval st e = Some c ->
    IntValues.gamma (IntEnv.eval e s) c.
  Proof. exact IntEnv.eval_sound. Qed.

  (** Assignment is sound on every concrete state in the environment. *)
  Example assign_is_sound_on_concretized_states : forall x e s st c,
    IntEnv.gamma s st -> eval_term ZLang.eval st e = Some c ->
    IntEnv.gamma (IntEnv.assign x e s) (upd BoolKey.eqb st x c).
  Proof. exact IntEnv.assign_sound. Qed.

  (** A guard is sound on every concrete state that satisfies it. *)
  Example assume_is_sound_on_concretized_states : forall g es s st cs,
    IntEnv.gamma s st -> eval_terms ZLang.eval st es = Some cs -> ZLang.holds g cs ->
    IntEnv.gamma (IntEnv.assume g es s) st.
  Proof. exact IntEnv.assume_sound. Qed.

End SoundnessTests.

Module UpdateTests.

  (** An update reads the new value at the key that it updates. *)
  Example update_reads_new_value :
    upd BoolKey.eqb (fun _ => 1) false 3 false = 3.
  Proof. vm_compute. reflexivity. Qed.

  (** A later update reads its new value at the key that it updates. *)
  Example second_update_reads_new_value :
    upd BoolKey.eqb (fun _ => 1) false 8 false = 8.
  Proof. vm_compute. reflexivity. Qed.

End UpdateTests.

Module BigOTests.

  Module TimedBoolMap := TrieMapT BoolKeyT.
  Module TimedIntValues := IntervalT ZLangT ThresholdsT.
  Module TimedIntEnv := EnvT BoolKeyT TimedBoolMap ZLangT TimedIntValues.

  (** The timed inclusion fixture uses the same two-size measure as the big-O theorem. *)
  Example inclusion_within_size_bound :
    (TimedIntEnv.T_leb two_points two_ranges <= TimedIntEnv.c_lat *
      (N.of_nat (TimedIntEnv.size two_points + TimedIntEnv.size two_ranges) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

  (** Assignment satisfies the transfer measure on a nonempty environment. *)
  Example assign_within_work_bound :
    (TimedIntEnv.T_assign false (Leaf true) two_points <= TimedIntEnv.c_state *
      (N.of_nat (TimedIntEnv.assign_work false (Leaf true) two_points) + 1))%N.
  Proof.
    vm_compute; discriminate.
  Qed.

End BigOTests.

(** Over a key type without elements, the bottom environment has no concretization. *)
Module EmptyKeyTests (K : (KEY with Definition t := Empty_set)).
  Module M := TrieMap K.
  Module E := Env K M ZLang IntValues.

  (** The bottom environment has no concrete state. *)
  Example bottom_concretizes_to_nothing :
    forall st : Empty_set -> Z, ~ E.gamma E.bot st.
  Proof. intros st Hbot. exact Hbot. Qed.

  (** The top environment has every concrete state. *)
  Example top_concretizes_to_every_state :
    forall st : Empty_set -> Z, E.gamma E.top st.
  Proof. intros st. split; [reflexivity | intros []]. Qed.
End EmptyKeyTests.
