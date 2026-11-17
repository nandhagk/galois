(** * Environment state observations

    Integer points exercise assignment, refinement and the top-default boundary.
    For example, copying a variable retains its point and havoc gives top.
    Builds on: Env and Const.

    Groups:
    - [AssignTests] Assignment and havoc of one variable.
    - [AssumeTests] Guards that refine the stored values.
    - [TraceTests] Operand order of traces through a guard.
    - [JoinTests] Joins and the top and bottom environments.
    - [WideningTests] Widening over three iterations, and narrowing.
    - [BoundaryTests] The order on a value domain whose top is not the greatest element.
    - [PointTests] Meets and tops of the point domain. *)

From Stdlib Require Import List Bool ZArith.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig Const ConstSig.
From Galois.States Require Import Env EnvSig.
Import List.ListNotations.
Local Open Scope Z_scope.

(** * Fixtures *)

Module IntLanguage.
  Definition op := Z.
  Definition guard := Z.
  Definition val := Z.
  Definition eval (z : Z) (_ : list Z) := Some z.
  Definition literal (z : Z) := Some z.
End IntLanguage.

(** Integer points are equal when their numbers are equal. *)
Module IntEq.
  Definition eqb := Z.eqb.
End IntEq.
Module Points := ConstCode IntLanguage IntEq.

(** A point domain whose forward step gives the constant z and whose guard meets
    each target with z. *)
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

(** The reached environment that binds each listed variable to its point. *)
Definition stored (xs : list (bool * Points.t)) : E.t :=
  Reached (fold_left (fun m p => BoolMap.set (fst p) (snd p) m) xs BoolMap.empty).

(** The value of variable x in an environment, or bottom when unreached. *)
Definition get x (s : E.t) := match s with Unreached => FBot | Reached m => E.read m x end.

Module AssignTests.

  (** Assigning a constant gives the variable that constant. *)
  Example constant_sets_variable : get false (E.assign false (Node 7 []) E.top) = FVal 7.
  Proof. vm_compute. reflexivity. Qed.

  (** Copying a variable gives the target the point of its source. *)
  Example copy_takes_source_value :
    get true (E.assign true (Leaf false) (stored [(false, FVal 7)])) = FVal 7.
  Proof. vm_compute. reflexivity. Qed.

  (** Assigning one variable leaves the point of another variable unchanged. *)
  Example assignment_leaves_other_variables :
    get true (E.assign false (Node 9 []) (stored [(true, FVal 2)])) = FVal 2.
  Proof. vm_compute. reflexivity. Qed.

  (** Havoc replaces the stored point of a variable with top. *)
  Example havoc_forgets_value :
    get false (E.havoc false (stored [(false, FVal 7)])) = FTop.
  Proof. vm_compute. reflexivity. Qed.

End AssignTests.

Module AssumeTests.

  (** A guard that contradicts the stored point gives the bottom value. *)
  Example contradictory_guard_gives_bottom :
    get false (E.assume 1 [Leaf false] (stored [(false, FVal 0)])) = FBot.
  Proof. vm_compute. reflexivity. Qed.

  (** The state after a guard with two leaves, each refined to 4. *)
  Definition two_leaf_state := E.assume 4 [Leaf false; Leaf true] E.top.

  (** The first leaf of a two-leaf guard is refined to 4. *)
  Example two_term_guard_refines_first_leaf : get false two_leaf_state = FVal 4.
  Proof. vm_compute. reflexivity. Qed.

  (** The second leaf of a two-leaf guard is refined to 4. *)
  Example two_term_guard_refines_second_leaf : get true two_leaf_state = FVal 4.
  Proof. vm_compute. reflexivity. Qed.

  (** The state after a guard whose nested term keeps the stored leaf and materializes
      the other one. *)
  Definition nested_leaf_state :=
    E.assume 7 [Node 7 [Leaf false]; Leaf true] (stored [(false, FVal 3)]).

  (** A stored leaf under a nested term keeps its stored point. *)
  Example nested_term_keeps_bound_leaf : get false nested_leaf_state = FVal 3.
  Proof. vm_compute. reflexivity. Qed.

  (** A free leaf under a nested term takes the value of the guard. *)
  Example nested_term_materializes_free_leaf : get true nested_leaf_state = FVal 7.
  Proof. vm_compute. reflexivity. Qed.

  (** A leaf that occurs twice meets its values from both occurrences. *)
  Example duplicate_leaf_meets_values :
    get false (E.assume 4 [Leaf false; Leaf false] E.top) = FVal 4.
  Proof. vm_compute. reflexivity. Qed.

  (** An empty guard keeps the stored point of each variable. *)
  Example empty_guard_keeps_binding :
    get true (E.assume 8 [] (stored [(true, FVal 2)])) = FVal 2.
  Proof. vm_compute. reflexivity. Qed.

End AssumeTests.

Module TraceTests.

  (** A trace language whose guard carries lists of targets. *)
  Module TraceLanguage.
    Definition op := unit.
    Definition guard := list (list nat).
    Definition val := unit.
    Definition eval (_ : op) (_ : list val) := Some tt.
    Definition literal (_ : op) : option Z := None.
  End TraceLanguage.

  (** A trace domain whose values are lists of naturals and whose guard returns its
      targets. *)
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

  (** The environment that binds variable true to [8] and variable false to [9]. *)
  Definition trace_input : TraceEnv.t :=
    Reached (BoolMap.set true [8%nat] (BoolMap.set false [9%nat] BoolMap.empty)).

  (** The trace bound to variable x, or the empty trace when unreached. *)
  Definition trace_get x (s : TraceEnv.t) :=
    match s with Unreached => [] | Reached m => TraceEnv.read m x end.

  (** Guard targets that are listed in order keep their order in the trace. *)
  Example forward_targets_keep_operand_order :
    trace_get false (TraceEnv.assume [[1%nat]; [2%nat]] [Leaf false; Leaf false] trace_input) =
      [9%nat; 1%nat; 2%nat].
  Proof. vm_compute. reflexivity. Qed.

  (** Reversed guard targets appear in the trace in their reversed order. *)
  Example reversed_targets_are_observed :
    trace_get false (TraceEnv.assume [[2%nat]; [1%nat]] [Leaf false; Leaf false] trace_input) =
      [9%nat; 2%nat; 1%nat].
  Proof. vm_compute. reflexivity. Qed.

  (** The operands of a node keep their order in the trace. *)
  Example node_operands_keep_order :
    trace_get false (TraceEnv.assume [[]] [Node tt [Leaf false; Leaf false]] trace_input) =
      [9%nat; 1%nat; 2%nat].
  Proof. vm_compute. reflexivity. Qed.

  (** Materializing a guard leaves the traces of the other variables unchanged. *)
  Example old_bindings_are_not_recomputed :
    trace_get true (TraceEnv.assume [[1%nat]; [2%nat]] [Leaf false; Leaf false] trace_input) =
      [8%nat].
  Proof. vm_compute. reflexivity. Qed.

End TraceTests.

Module JoinTests.

  (** The join of two environments with different keys, as the environment of variable
      false. *)
  Definition joined := E.join (stored [(false, FVal 1)]) (stored [(true, FVal 2)]).

  (** A key that only the first environment binds reads as top after the join. *)
  Example join_of_disjoint_keys_loses_first_key : get false joined = FTop.
  Proof. vm_compute. reflexivity. Qed.

  (** A key that only the second environment binds reads as top after the join. *)
  Example join_of_disjoint_keys_loses_second_key : get true joined = FTop.
  Proof. vm_compute. reflexivity. Qed.

  (** An unbound variable of the top environment reads as top. *)
  Example top_reads_top_for_false : get false E.top = FTop.
  Proof. vm_compute. reflexivity. Qed.

  (** An unbound variable of the top environment reads as top, for the other key. *)
  Example top_reads_top_for_true : get true E.top = FTop.
  Proof. vm_compute. reflexivity. Qed.

  (** The fresh bottom environment is below the top environment. *)
  Example bottom_is_below_top : E.leb E.bot E.top = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The top environment is not below the fresh bottom environment. *)
  Example top_is_not_below_bottom : E.leb E.top E.bot = false.
  Proof. vm_compute. reflexivity. Qed.

  (** Assigning a variable in the fresh bottom environment keeps it bottom. *)
  Example bottom_survives_assignment : E.assign false (Node 1 []) E.bot = E.bot.
  Proof. vm_compute. reflexivity. Qed.

  (** Havoc of the fresh bottom environment keeps it bottom. *)
  Example bottom_survives_havoc : E.havoc false E.bot = E.bot.
  Proof. vm_compute. reflexivity. Qed.

  (** A guard on the fresh bottom environment keeps it bottom. *)
  Example bottom_survives_assumption : E.assume 1 [Leaf false] E.bot = E.bot.
  Proof. vm_compute. reflexivity. Qed.

End JoinTests.

Module WideningTests.

  (** The environment after the first widening from bottom. *)
  Definition widened_once := E.widen tt E.bot (stored [(false, FVal 1)]).

  (** The environment after a second widening that raises the point to 2. *)
  Definition widened_twice := E.widen tt widened_once (stored [(false, FVal 2)]).

  (** The environment after a third widening, against top. *)
  Definition widened_thrice := E.widen tt widened_twice E.top.

  (** The first widening from bottom keeps the point of the new environment. *)
  Example first_widening_keeps_point : get false widened_once = FVal 1.
  Proof. vm_compute. reflexivity. Qed.

  (** A second widening with a different point gives top. *)
  Example second_widening_reaches_top : get false widened_twice = FTop.
  Proof. vm_compute. reflexivity. Qed.

  (** A widening against top keeps top. *)
  Example third_widening_stays_top : get false widened_thrice = FTop.
  Proof. vm_compute. reflexivity. Qed.

End WideningTests.

Module NarrowTests.

  (** Narrowing keeps a candidate recognized through its stored bottom. *)
  Example narrowing_keeps_candidate_with_stored_bottom :
    E.narrow (stored [(false, FVal 5); (true, FVal 0)])
      (stored [(false, FBot); (true, FTop)]) = stored [(false, FBot); (true, FTop)].
  Proof. vm_compute. reflexivity. Qed.

End NarrowTests.

Module BoundaryTests.

  (** A fact of a value domain whose top is a point that is not the greatest element. *)
  Inductive fact := Bot | Point | Upper.

  (** A value domain in which Upper is above Bot but not below the top Point. *)
  Module TopBoundary.
    Definition t := fact.
    Definition leb a b :=
      match a, b with Bot, _ => true | _, Upper => true | Point, Point => true | _, _ => false end.
    Definition bot := Bot.
    Definition is_bot a := match a with Bot => true | _ => false end.
    Definition join a b :=
      match a, b with Bot, _ => b | _, Bot => a | Point, Point => Point | _, _ => Upper end.
    Definition top := Point.
    Definition meet (a _ : t) := a.
    Definition wparam := unit.
    Definition widen (_ : unit) := join.
    Definition narrow (a _ : t) := a.
    Definition forward (_ : unit) (_ : list t) := Point.
    Definition backward (_ : unit) (_ : t) (xs : list t) := xs.
    Definition guard (_ : unit) (xs : list t) := xs.
  End TopBoundary.

  (** A language with one operator, no literals and a unit value. *)
  Module UnitLanguage.
    Definition op := unit.
    Definition guard := unit.
    Definition val := unit.
    Definition eval (_ : op) (_ : list val) := Some tt.
    Definition literal (_ : op) : option Z := None.
  End UnitLanguage.
  Module BadEnv := EnvCode BoolKeyCode BoolMap UnitLanguage TopBoundary.

  (** The environment that binds variable false to Upper. *)
  Definition upper := Reached (BoolMap.set false Upper BoolMap.empty).

  (** The environment that binds variable false to Point. *)
  Definition point := Reached (BoolMap.set false Point BoolMap.empty).

  (** Upper is not below the top point, so the order does not make top greatest. *)
  Example upper_is_not_below_point : TopBoundary.leb Upper TopBoundary.top = false.
  Proof. vm_compute. reflexivity. Qed.

  (** The upper environment is below the top environment. *)
  Example upper_environment_is_below_top : BadEnv.leb upper BadEnv.top = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The top environment is below the point environment. *)
  Example top_environment_is_below_point : BadEnv.leb BadEnv.top point = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The upper environment is not below the point environment, so the order is not
      transitive. *)
  Example upper_environment_is_not_below_point : BadEnv.leb upper point = false.
  Proof. vm_compute. reflexivity. Qed.

End BoundaryTests.

Module PointTests.

  (** The concrete values that a point abstracts: none for bottom, the number for a
      point and every number for top. *)
  Definition point_gamma (a : Points.t) (z : Z) : Prop :=
    match a with FBot => False | FVal x => z = x | FTop => True end.

  (** The meet of two points keeps the values that both represent. *)
  Example meet_retains_common_values : forall a b c,
    point_gamma a c -> point_gamma b c -> point_gamma (Points.meet a b) c.
  Proof.
    intros [|x|] [|y|] c; cbn [point_gamma Points.meet];
      intros Ha Hb; try contradiction; try exact I; try assumption.
    subst x y. now rewrite Z.eqb_refl.
  Qed.

  (** Every point is below the top point. *)
  Example top_is_above_every_point : forall a, Points.leb a Points.top = true.
  Proof. intros [|x|]; reflexivity. Qed.

End PointTests.
