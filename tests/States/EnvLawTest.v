(** * Environment semantic clients

    These clients instantiate environment operations and laws over integer intervals.
    For example, two bindings describe different concrete values at their keys.
    Builds on: Env, Interval and ZLang. *)

From Stdlib Require Import List Bool NArith ZArith.
From Galois.Base Require Import Key KeySig Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval
  ThresholdsSig Thresholds ZLang.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module BoolMap := TrieMap BoolKey.
Module IntValues := Interval ZLang Thresholds.
Module IntEnv := Env BoolKey BoolMap ZLang IntValues.
Definition two_points_map :=
  BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false (I (Fin 1) (Fin 1)) BoolMap.empty).

Definition two_points : IntEnv.t := Reached two_points_map.

Definition two_ranges : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 1) (Fin 4))
    (BoolMap.set false (I (Fin 0) (Fin 3)) BoolMap.empty)).

Definition bottom_binding : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false IBot BoolMap.empty)).

Definition bottom_mismatch_map :=
  BoolMap.set true (I (Fin 3) (Fin 3))
    (BoolMap.set false IBot BoolMap.empty).

Definition raised_point : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false (I (Fin 3) (Fin 3)) BoolMap.empty)).

(** Equal nonbottom environments pass the fused inclusion traversal. *)
Example inclusion_equal_environments : IntEnv.leb two_points two_points = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Strict inclusion succeeds only from the point intervals into the wider ranges. *)
Example inclusion_strictly_smaller :
  (IntEnv.leb two_points two_ranges, IntEnv.leb two_ranges two_points) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** A bottom binding on the right rejects a nonbottom left environment. *)
Example inclusion_right_bottom : IntEnv.leb two_points bottom_binding = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** A live mismatch fails the fused test, then the left bottom makes the fallback accept. *)
Example inclusion_left_bottom_only :
  (BoolMap.forall2b IntEnv.leb_entry bottom_mismatch_map two_points_map,
   IntEnv.leb (Reached bottom_mismatch_map) two_points) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** An unreached left environment is included without inspecting the right one. *)
Example inclusion_unreached_left : IntEnv.leb Unreached two_points = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** A nonbottom reached environment is not included in an unreached one. *)
Example inclusion_unreached_right : IntEnv.leb two_points Unreached = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** A reached bottom and an unreached state are both included in an unreached state. *)
Example inclusion_bottom_representations :
  (IntEnv.leb bottom_binding Unreached, IntEnv.leb Unreached Unreached) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** A stable widening returns the original environment exactly. *)
Example widening_stable_environment : IntEnv.widen TLeaf two_points two_points = two_points.
Proof.
  vm_compute; reflexivity.
Qed.

(** One unstable binding widens its upper endpoint and leaves the other point unchanged. *)
Example widening_one_unstable_binding :
  let result := IntEnv.widen TLeaf two_points raised_point in
  (IntEnv.eval (Leaf false) result, IntEnv.eval (Leaf true) result) =
    (I (Fin 1) PosInf, I (Fin 2) (Fin 2)).
Proof.
  vm_compute; reflexivity.
Qed.

Module TimedBoolMap := TrieMapT BoolKeyT.
Module TimedIntValues := IntervalT ZLangT ThresholdsT.
Module TimedIntEnv := EnvT BoolKeyT TimedBoolMap ZLangT TimedIntValues.

(** The timed inclusion fixture uses the same two-size measure as the big-O theorem. *)
Example environment_lattice_bigO_fixture :
  (TimedIntEnv.T_leb two_points two_ranges <= TimedIntEnv.c_lat *
    (N.of_nat (TimedIntEnv.size two_points + TimedIntEnv.size two_ranges) + 1))%N.
Proof.
  vm_compute; discriminate.
Qed.

(** Assignment satisfies the transfer measure on a nonempty environment. *)
Example environment_transfer_bigO_fixture :
  (TimedIntEnv.T_assign false (Leaf true) two_points <= TimedIntEnv.c_state *
    (N.of_nat (TimedIntEnv.assign_work false (Leaf true) two_points) + 1))%N.
Proof.
  vm_compute; discriminate.
Qed.

Example two_variable_control :
  IntEnv.gamma two_points (fun x => if x then 2 else 1).
Proof. vm_compute. split; [reflexivity | intros []; intuition discriminate]. Qed.

Example term_evaluation_sound_client : forall e s st c,
  IntEnv.gamma s st -> eval_term ZLang.eval st e = Some c ->
  IntValues.gamma (IntEnv.eval e s) c.
Proof. exact IntEnv.eval_sound. Qed.

Example assignment_sound_client : forall x e s st c,
  IntEnv.gamma s st -> eval_term ZLang.eval st e = Some c ->
  IntEnv.gamma (IntEnv.assign x e s) (upd BoolKey.eqb st x c).
Proof. exact IntEnv.assign_sound. Qed.

Example guard_sound_client : forall g es s st cs,
  IntEnv.gamma s st -> eval_terms ZLang.eval st es = Some cs -> ZLang.holds g cs ->
  IntEnv.gamma (IntEnv.assume g es s) st.
Proof. exact IntEnv.assume_sound. Qed.

Example havoc_both_concrete_replacements :
  (upd BoolKey.eqb (fun _ => 1) false 3 false,
   upd BoolKey.eqb (fun _ => 1) false 8 false) = (3, 8).
Proof. vm_compute. reflexivity. Qed.

Module EmptyKeyClients (K : (KEY with Definition t := Empty_set)).
  Module M := TrieMap K.
  Module E := Env K M ZLang IntValues.

  Example empty_key_fresh_bottom_has_empty_meaning :
    forall st : Empty_set -> Z, ~ E.gamma E.bot st.
  Proof. intros st Hbot. exact Hbot. Qed.

  Example empty_key_reached_map_has_full_meaning :
    forall st : Empty_set -> Z, E.gamma E.top st.
  Proof. intros st. split; [reflexivity | intros []]. Qed.
End EmptyKeyClients.
