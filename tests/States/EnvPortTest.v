(** * Environment state observations

    Integer points exercise assignment, refinement and the top-default boundary.
    For example, copying a variable retains its point and havoc gives top.
    Builds on: Env and Const. *)

From Stdlib Require Import List Bool ZArith.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig Const ConstSig.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

Module IntLanguage.
  Definition op := Z.
  Definition guard := Z.
  Definition val := Z.
  Definition eval (z : Z) (_ : list Z) := Some z.
  Definition literal (z : Z) := Some z.
End IntLanguage.
Module IntEq.
  Definition eqb := Z.eqb.
End IntEq.
Module Points := ConstCode IntLanguage IntEq.
Module GuardedPoints.
  Definition t := Points.t.
  Definition leb := Points.leb.
  Definition bot := Points.bot.
  Definition is_bot := Points.is_bot.
  Definition join := Points.join.
  Definition top := Points.top.
  Definition meet := Points.meet.
  Definition wparam := Points.wparam.
  Definition widen := Points.widen.
  Definition narrow := Points.narrow.
  Definition forward (z : Z) (_ : list t) := FVal z.
  Definition backward (_ : Z) (_ : t) (xs : list t) := xs.
  Definition guard (z : Z) (xs : list t) := map (fun a => meet a (FVal z)) xs.
End GuardedPoints.
Module BoolMap := TrieMapCode BoolKeyCode.
Module E := EnvCode BoolKeyCode BoolMap IntLanguage GuardedPoints.

Definition stored (xs : list (bool * Points.t)) : E.t :=
  Reached (fold_left (fun m p => BoolMap.set (fst p) (snd p) m) xs BoolMap.empty).
Definition get x (s : E.t) := match s with Unreached => FBot | Reached m => E.read m x end.

Example constant_assignment : get false (E.assign false (Node 7 []) E.top) = FVal 7.
Proof. vm_compute. reflexivity. Qed.
Example copy_assignment :
  get true (E.assign true (Leaf false) (stored [(false, FVal 7)])) = FVal 7.
Proof. vm_compute. reflexivity. Qed.
Example distinct_variable_frame :
  get true (E.assign false (Node 9 []) (stored [(true, FVal 2)])) = FVal 2.
Proof. vm_compute. reflexivity. Qed.
Example havoc_replaces_binding :
  get false (E.havoc false (stored [(false, FVal 7)])) = FTop.
Proof. vm_compute. reflexivity. Qed.
Example impossible_assume :
  get false (E.assume 1 [Leaf false] (stored [(false, FVal 0)])) = FBot.
Proof. vm_compute. reflexivity. Qed.
Example two_term_refinement :
  let s := E.assume 4 [Leaf false; Leaf true] E.top in
  (get false s, get true s) = (FVal 4, FVal 4).
Proof. vm_compute. reflexivity. Qed.
Example nested_term_materialization :
  let s := E.assume 7 [Node 7 [Leaf false]; Leaf true] (stored [(false, FVal 3)]) in
  (get false s, get true s) = (FVal 3, FVal 7).
Proof. vm_compute. reflexivity. Qed.
Example duplicate_leaf_meets_threaded_values :
  get false (E.assume 4 [Leaf false; Leaf false] E.top) = FVal 4.
Proof. vm_compute. reflexivity. Qed.
Example different_key_join :
  let s := E.join (stored [(false, FVal 1)]) (stored [(true, FVal 2)]) in
  (get false s, get true s) = (FTop, FTop).
Proof. vm_compute. reflexivity. Qed.
Example absent_and_empty_mean_top : (get false E.top, get true E.top) = (FTop, FTop).
Proof. vm_compute. reflexivity. Qed.
Example fresh_bottom_is_distinct : (E.leb E.bot E.top, E.leb E.top E.bot) = (true, false).
Proof. vm_compute. reflexivity. Qed.
Example fresh_bottom_survives_transfers :
  (E.assign false (Node 1 []) E.bot, E.havoc false E.bot, E.assume 1 [Leaf false] E.bot) =
    (E.bot, E.bot, E.bot).
Proof. vm_compute. reflexivity. Qed.
Example empty_guard_keeps_old_binding :
  get true (E.assume 8 [] (stored [(true, FVal 2)])) = FVal 2.
Proof. vm_compute. reflexivity. Qed.
Example three_widening_iterations :
  let s1 := E.widen tt E.bot (stored [(false, FVal 1)]) in
  let s2 := E.widen tt s1 (stored [(false, FVal 2)]) in
  let s3 := E.widen tt s2 E.top in
  (get false s1, get false s2, get false s3) = (FVal 1, FTop, FTop).
Proof. vm_compute. reflexivity. Qed.

Module TraceLanguage.
  Definition op := unit.
  Definition guard := list (list nat).
  Definition val := unit.
  Definition eval (_ : op) (_ : list val) := Some tt.
  Definition literal (_ : op) : option Z := None.
End TraceLanguage.
Module TraceValues.
  Definition t := list nat.
  Definition leb (_ _ : t) := true.
  Definition bot : t := [].
  Definition is_bot (_ : t) := false.
  Definition join (a _ : t) := a.
  Definition top : t := [].
  Definition meet := @app nat.
  Definition wparam := unit.
  Definition widen (_ : unit) (a _ : t) := a.
  Definition narrow (a _ : t) := a.
  Definition forward (_ : unit) (_ : list t) : t := [].
  Definition backward (_ : unit) (_ : t) (_ : list t) := [[1%nat]; [2%nat]].
  Definition guard (targets : list t) (_ : list t) := targets.
End TraceValues.
Module TraceEnv := EnvCode BoolKeyCode BoolMap TraceLanguage TraceValues.
Definition trace_input : TraceEnv.t :=
  Reached (BoolMap.set true [8%nat] (BoolMap.set false [9%nat] BoolMap.empty)).
Definition trace_get x (s : TraceEnv.t) :=
  match s with Unreached => [] | Reached m => TraceEnv.read m x end.

Example term_order_survives_materialization :
  trace_get false (TraceEnv.assume [[1%nat]; [2%nat]] [Leaf false; Leaf false] trace_input) =
    [9%nat; 1%nat; 2%nat].
Proof. vm_compute. reflexivity. Qed.
Example reversing_guard_targets_is_observable :
  trace_get false (TraceEnv.assume [[2%nat]; [1%nat]] [Leaf false; Leaf false] trace_input) =
    [9%nat; 2%nat; 1%nat].
Proof. vm_compute. reflexivity. Qed.
Example generic_node_order_survives_materialization :
  trace_get false (TraceEnv.assume [[]] [Node tt [Leaf false; Leaf false]] trace_input) =
    [9%nat; 1%nat; 2%nat].
Proof. vm_compute. reflexivity. Qed.
Example materialization_does_not_recompute_old_bindings :
  trace_get true (TraceEnv.assume [[1%nat]; [2%nat]] [Leaf false; Leaf false] trace_input) =
    [8%nat].
Proof. vm_compute. reflexivity. Qed.
