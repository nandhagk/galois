(** * Environment semantic clients

    These clients instantiate environment operations and laws over integer intervals.
    For example, two bindings describe different concrete values at their keys.
    Builds on: Env, Interval and ZLang. *)

From Stdlib Require Import List Bool ZArith.
From Galois.Base Require Import Key KeySig Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval Thresholds ZLang.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module BoolMap := TrieMap BoolKey.
Module IntValues := Interval ZLang Thresholds.
Module IntEnv := Env BoolKey BoolMap ZLang IntValues.
Definition two_points : IntEnv.t :=
  Reached (BoolMap.set true (I (Fin 2) (Fin 2))
    (BoolMap.set false (I (Fin 1) (Fin 1)) BoolMap.empty)).

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
