(** * Priority worklist computation

    The engine evaluates a popped row once and applies its primary and side outputs in order.
    For example, a changed self-read queues the popped row again before the next probe.
    Builds on: FixpointEval, FixpointIndex, FixpointSolver and BaseHeapCost. *)

From Stdlib Require Import List Bool NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseHeapCost.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointIndex
  FixpointAnalysis FixpointSolver.
Import List.ListNotations Cost.Notations.

Module Worklist.

(** Delay entries count changes still allowed before widening, with absent entries at delay. *)
Record state (X C A : Type) := State {
  current : assignment X A;
  queue : Heap.t C;
  queued : FinSet.t C;
  delays : Map.t X nat;
  evaluations : nat
}.

Arguments State {X C A}.
Arguments current {X C A}.
Arguments queue {X C A}.
Arguments queued {X C A}.
Arguments delays {X C A}.
Arguments evaluations {X C A}.

(** An enqueue skips every already queued key before invoking target and priority callbacks. *)
Definition enqueue_one_c {X C A} (a : Analysis.t X C A) c (s : state X C A) :=
  let* present := FinSet.mem_c (Analysis.row_enc a) c (queued s) in
  if present then Cost.ret s
  else
    Cost.step ;;
    let* x := System.target_c (Analysis.system a) c in
    Cost.step ;;
    let* p := Policy.order_c (Analysis.policy a) x in
    let* q := Heap.push_c (Analysis.row_enc a) p c (queue s) in
    let* keys := FinSet.add_c (Analysis.row_enc a) c (queued s) in
    Cost.ret (State (current s) q keys (delays s) (evaluations s)).

Definition enqueue_one {X C A} (a : Analysis.t X C A) c s :=
  Cost.value (enqueue_one_c a c s).

Fixpoint enqueue_c {X C A} (a : Analysis.t X C A) cs (s : state X C A) :=
  match cs with
  | [] => Cost.ret s
  | c :: rest =>
    Cost.step ;;
    let* next := enqueue_one_c a c s in enqueue_c a rest next
  end.

Definition enqueue {X C A} (a : Analysis.t X C A) cs s :=
  Cost.value (enqueue_c a cs s).

(** A delayed widening invokes its policy callback only when the shared rule requests a raise. *)
Definition operation_c {X C A} (a : Analysis.t X C A) x remaining old value :=
  Cost.step ;;
  let* selected := Policy.widen_at_c (Analysis.policy a) x in
  Cost.step ;;
  if selected then
    match remaining with
    | O => widen_c (Analysis.lat a) old value
    | S _ => join_c (Analysis.lat a) old value
    end
  else join_c (Analysis.lat a) old value.

(** Every actual change decrements its delay and traverses the complete prepared reader list. *)
Definition update_c {X C A} (a : Analysis.t X C A) (ix : sys_index X C)
    (s : state X C A) (xa : X * A) :=
  let '(x, value) := xa in
  let* remaining := Map.find_or_c (Analysis.key_enc a)
    (Policy.delay (Analysis.policy a)) x (delays s) in
  let* result := Update.rule_c (Analysis.key_enc a) (Analysis.lat a)
    (operation_c a x remaining) (current s) x value in
  if snd result then
    let* counters := Map.set_c (Analysis.key_enc a) x (Nat.pred remaining) (delays s) in
    let* readers := readers_of_c (Analysis.key_enc a) ix x in
    enqueue_c a readers
      (State (fst result) (queue s) (queued s) counters (evaluations s))
  else Cost.ret s.

Definition update {X C A} (a : Analysis.t X C A) ix s xa :=
  Cost.value (update_c a ix s xa).

Fixpoint updates_c {X C A} (a : Analysis.t X C A) ix outs (s : state X C A) :=
  match outs with
  | [] => Cost.ret s
  | xa :: rest =>
    Cost.step ;;
    let* next := update_c a ix s xa in updates_c a ix rest next
  end.

Definition updates {X C A} (a : Analysis.t X C A) ix outs s :=
  Cost.value (updates_c a ix outs s).

(** A successful pop clears membership before evaluating and applying the frozen output list. *)
Definition step_c {X C A} (a : Analysis.t X C A) ix (s : state X C A)
    : Cost.t (state X C A + assignment X A) :=
  let* popped := Heap.pop_c (Analysis.row_enc a) (queue s) in
  match popped with
  | None => Cost.ret (inr (current s))
  | Some (_, c, q) =>
    let* keys := FinSet.remove_c (Analysis.row_enc a) c (queued s) in
    let* outputs := Eval.outputs_c (Analysis.system a)
      (lookup_c (Analysis.key_enc a) (Analysis.lat a) (current s)) c in
    let* next := updates_c a ix (fst outputs)
      (State (current s) q keys (delays s) (S (evaluations s))) in
    Cost.ret (inl next)
  end.

Definition step {X C A} (a : Analysis.t X C A) ix s :=
  Cost.value (step_c a ix s).

(** Initialization charges each original constraint occurrence, including skipped duplicates. *)
Definition initial_c {X C A} (a : Analysis.t X C A) :=
  let* values := Map.empty_c in
  let* q := Heap.empty_c in
  let* keys := FinSet.empty_c in
  let* counters := Map.empty_c in
  enqueue_c a (System.constraints (Analysis.system a)) (State values q keys counters 0).

Definition initial {X C A} (a : Analysis.t X C A) := Cost.value (initial_c a).

(** Preparation and initialization are part of the same charged run as the binary driver. *)
Definition run_c {X C A} (a : Analysis.t X C A) fuel
    : Cost.t (Outcome.t X A (assignment X A)) :=
  let* ix := index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  let* start := initial_c a in
  let* result := iterate (step_c a ix) fuel start in
  Cost.ret
    (match result with
     | inl pending => Outcome.OutOfFuel (current pending)
     | inr done => Outcome.Solved done
     end).

Definition run {X C A} (a : Analysis.t X C A) fuel := Cost.value (run_c a fuel).

(** The solver record stores computation alone. *)
Definition solver {X C A} : Solver.t X C A := Solver.Make run_c.

(** Enqueue exposes the single membership test and the absent-key push. *)
Theorem enqueue_one_equation {X C A} (a : Analysis.t X C A) c s :
  enqueue_one a c s =
    if FinSet.mem (Analysis.row_enc a) c (queued s) then s
    else State (current s)
      (Heap.push (Analysis.row_enc a)
        (Policy.order (Analysis.policy a) (System.target (Analysis.system a) c)) c (queue s))
      (FinSet.add (Analysis.row_enc a) c (queued s)) (delays s) (evaluations s).
Proof.
  unfold enqueue_one, enqueue_one_c; autorewrite with galois_cost.
  fold (FinSet.mem (Analysis.row_enc a) c (queued s)).
  destruct (FinSet.mem (Analysis.row_enc a) c (queued s));
    autorewrite with galois_cost; reflexivity.
Qed.

(** List enqueue follows source occurrence order. *)
Theorem enqueue_equation {X C A} (a : Analysis.t X C A) cs s :
  enqueue a cs s =
    match cs with
    | [] => s
    | c :: rest => enqueue a rest (enqueue_one a c s)
    end.
Proof.
  destruct cs; reflexivity.
Qed.

(** The operation value selects widening precisely after the delay reaches zero. *)
Theorem operation_equation {X C A} (a : Analysis.t X C A) x remaining old value :
  Cost.value (operation_c a x remaining old value) =
    if Policy.widen_at (Analysis.policy a) x then
      match remaining with
      | O => widen (Analysis.lat a) old value
      | S _ => join (Analysis.lat a) old value
      end
    else join (Analysis.lat a) old value.
Proof.
  unfold operation_c; autorewrite with galois_cost.
  fold (Policy.widen_at (Analysis.policy a) x).
  destruct (Policy.widen_at (Analysis.policy a) x), remaining; reflexivity.
Qed.

(** Update exposes the shared rule and its exact change branch. *)
Theorem update_equation {X C A} (a : Analysis.t X C A) ix s x value :
  update a ix s (x, value) =
    let remaining := Map.find_or (Analysis.key_enc a)
      (Policy.delay (Analysis.policy a)) x (delays s) in
    let result := Update.rule (Analysis.key_enc a) (Analysis.lat a)
      (operation_c a x remaining) (current s) x value in
    if snd result then
      enqueue a (readers_of (Analysis.key_enc a) ix x)
        (State (fst result) (queue s) (queued s)
          (Map.set (Analysis.key_enc a) x (Nat.pred remaining) (delays s)) (evaluations s))
    else s.
Proof.
  unfold update, update_c; autorewrite with galois_cost.
  fold (Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a)) x (delays s)).
  fold (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    (operation_c a x
      (Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a)) x (delays s)))
    (current s) x value).
  destruct (snd (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    (operation_c a x
      (Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a)) x (delays s)))
    (current s) x value)); autorewrite with galois_cost; reflexivity.
Qed.

(** Outputs are applied in order without deduplicating side occurrences. *)
Theorem updates_equation {X C A} (a : Analysis.t X C A) ix outs s :
  updates a ix outs s =
    match outs with
    | [] => s
    | xa :: rest => updates a ix rest (update a ix s xa)
    end.
Proof.
  destruct outs; reflexivity.
Qed.

(** The step equation freezes evaluation against the assignment before any output update. *)
Theorem step_equation {X C A} (a : Analysis.t X C A) ix s :
  step a ix s =
    match Heap.pop (Analysis.row_enc a) (queue s) with
    | None => inr (current s)
    | Some (_, c, q) =>
      inl (updates a ix
        (fst (Eval.outputs (Analysis.system a) c
          (lookup (Analysis.key_enc a) (Analysis.lat a) (current s))))
        (State (current s) q (FinSet.remove (Analysis.row_enc a) c (queued s))
          (delays s) (S (evaluations s))))
    end.
Proof.
  unfold step, step_c; rewrite Cost.value_bind.
  fold (Heap.pop (Analysis.row_enc a) (queue s)).
  destruct (Heap.pop _ _) as [[[p c] q]|]; autorewrite with galois_cost; [|reflexivity].
  rewrite (Eval.outputs_c_spec _ _ _ (lookup _ _ (current s))) by reflexivity.
  reflexivity.
Qed.

(** Initial state starts at bottom with an empty heap, membership set and delay table. *)
Theorem initial_equation {X C A} (a : Analysis.t X C A) :
  initial a = enqueue a (System.constraints (Analysis.system a))
    (State Map.empty Heap.empty FinSet.empty Map.empty 0).
Proof.
  reflexivity.
Qed.

(** The run equation uses the public binary-driver value and retains exhausted assignments. *)
Theorem run_equation {X C A} (a : Analysis.t X C A) fuel :
  run a fuel =
    match Cost.value (iterate
      (step_c a (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)))
      fuel (initial a)) with
    | inl pending => Outcome.OutOfFuel (current pending)
    | inr done => Outcome.Solved done
    end.
Proof.
  reflexivity.
Qed.

(** Enqueue retains membership, target, priority, heap and membership-write charges. *)
Theorem enqueue_one_cost {X C A} (a : Analysis.t X C A) c s :
  Cost.ticks (enqueue_one_c a c s) =
    (Cost.ticks (FinSet.mem_c (Analysis.row_enc a) c (queued s)) +
      if FinSet.mem (Analysis.row_enc a) c (queued s) then 0
      else 2 + Cost.ticks (System.target_c (Analysis.system a) c) +
        Cost.ticks (Policy.order_c (Analysis.policy a) (System.target (Analysis.system a) c)) +
        Cost.ticks (Heap.push_c (Analysis.row_enc a)
          (Policy.order (Analysis.policy a) (System.target (Analysis.system a) c)) c (queue s)) +
        Cost.ticks (FinSet.add_c (Analysis.row_enc a) c (queued s)))%N.
Proof.
  unfold enqueue_one_c; autorewrite with galois_cost.
  fold (FinSet.mem (Analysis.row_enc a) c (queued s)).
  destruct (FinSet.mem (Analysis.row_enc a) c (queued s));
    autorewrite with galois_cost.
  - lia.
  - fold (System.target (Analysis.system a) c).
    fold (Policy.order (Analysis.policy a) (System.target (Analysis.system a) c)).
    lia.
Qed.

(** The enqueue fold pays for every input occurrence, including duplicate skips. *)
Theorem enqueue_cost {X C A} (a : Analysis.t X C A) cs s :
  Cost.ticks (enqueue_c a cs s) =
    match cs with
    | [] => 0%N
    | c :: rest =>
      (1 + Cost.ticks (enqueue_one_c a c s) +
        Cost.ticks (enqueue_c a rest (enqueue_one a c s)))%N
    end.
Proof.
  destruct cs; [reflexivity|].
  cbn [enqueue_c]; autorewrite with galois_cost.
  fold (enqueue_one a c s); lia.
Qed.

(** The selected operator pays the policy callback invocation and the chosen lattice callback. *)
Theorem operation_cost {X C A} (a : Analysis.t X C A) x n old value :
  Cost.ticks (operation_c a x n old value) =
    (2 + Cost.ticks (Policy.widen_at_c (Analysis.policy a) x) +
      if Policy.widen_at (Analysis.policy a) x then
        match n with
        | O => Cost.ticks (widen_c (Analysis.lat a) old value)
        | S _ => Cost.ticks (join_c (Analysis.lat a) old value)
        end
      else Cost.ticks (join_c (Analysis.lat a) old value))%N.
Proof.
  unfold operation_c; autorewrite with galois_cost.
  fold (Policy.widen_at (Analysis.policy a) x).
  destruct (Policy.widen_at (Analysis.policy a) x), n; lia.
Qed.

(** Update charges its delay lookup, shared rule and all reached propagation work. *)
Theorem update_cost {X C A} (a : Analysis.t X C A) ix s x value :
  Cost.ticks (update_c a ix s (x, value)) =
    let n := Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a)) x (delays s) in
    let result := Update.rule (Analysis.key_enc a) (Analysis.lat a)
      (operation_c a x n) (current s) x value in
    (Cost.ticks (Map.find_or_c (Analysis.key_enc a)
       (Policy.delay (Analysis.policy a)) x (delays s)) +
     Cost.ticks (Update.rule_c (Analysis.key_enc a) (Analysis.lat a)
       (operation_c a x n) (current s) x value) +
     if snd result then
       Cost.ticks (Map.set_c (Analysis.key_enc a) x (Nat.pred n) (delays s)) +
       Cost.ticks (readers_of_c (Analysis.key_enc a) ix x) +
       Cost.ticks (enqueue_c a (readers_of (Analysis.key_enc a) ix x)
         (State (fst result) (queue s) (queued s)
           (Map.set (Analysis.key_enc a) x (Nat.pred n) (delays s)) (evaluations s)))
     else 0)%N.
Proof.
  cbn zeta; unfold update_c; autorewrite with galois_cost.
  fold (Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a)) x (delays s)).
  fold (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    (operation_c a x (Map.find_or (Analysis.key_enc a)
      (Policy.delay (Analysis.policy a)) x (delays s))) (current s) x value).
  destruct (snd (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    (operation_c a x (Map.find_or (Analysis.key_enc a)
      (Policy.delay (Analysis.policy a)) x (delays s))) (current s) x value));
    autorewrite with galois_cost.
  - fold (Map.set (Analysis.key_enc a) x
      (Nat.pred (Map.find_or (Analysis.key_enc a) (Policy.delay (Analysis.policy a))
        x (delays s))) (delays s)).
    fold (readers_of (Analysis.key_enc a) ix x); lia.
  - lia.
Qed.

(** Output application pays for each primary or side occurrence before its recursive tail. *)
Theorem updates_cost {X C A} (a : Analysis.t X C A) ix outs s :
  Cost.ticks (updates_c a ix outs s) =
    match outs with
    | [] => 0%N
    | xa :: rest =>
      (1 + Cost.ticks (update_c a ix s xa) +
        Cost.ticks (updates_c a ix rest (update a ix s xa)))%N
    end.
Proof.
  destruct outs as [|xa rest]; [reflexivity|].
  cbn [updates_c]; autorewrite with galois_cost.
  fold (update a ix s xa); lia.
Qed.

(** Callback cost includes the actual heap pop and the reached evaluator and output fold. *)
Theorem step_cost {X C A} (a : Analysis.t X C A) ix s :
  Cost.ticks (step_c a ix s) =
    (Cost.ticks (Heap.pop_c (Analysis.row_enc a) (queue s)) +
      match Heap.pop (Analysis.row_enc a) (queue s) with
      | None => 0
      | Some (_, c, q) =>
        Cost.ticks (FinSet.remove_c (Analysis.row_enc a) c (queued s)) +
        Cost.ticks (Eval.outputs_c (Analysis.system a)
          (lookup_c (Analysis.key_enc a) (Analysis.lat a) (current s)) c) +
        Cost.ticks (updates_c a ix
          (fst (Eval.outputs (Analysis.system a) c
            (lookup (Analysis.key_enc a) (Analysis.lat a) (current s))))
          (State (current s) q (FinSet.remove (Analysis.row_enc a) c (queued s))
            (delays s) (S (evaluations s))))
      end)%N.
Proof.
  unfold step_c; rewrite Cost.ticks_bind.
  fold (Heap.pop (Analysis.row_enc a) (queue s)).
  destruct (Heap.pop _ _) as [[[p c] q]|]; autorewrite with galois_cost; [|lia].
  rewrite (Eval.outputs_c_spec _ _ _ (lookup _ _ (current s))) by reflexivity.
  fold (FinSet.remove (Analysis.row_enc a) c (queued s)).
  lia.
Qed.

(** The complete run adds actual preparation, initialization and binary-driver charges. *)
Theorem run_cost {X C A} (a : Analysis.t X C A) fuel :
  Cost.ticks (run_c a fuel) =
    (Cost.ticks (index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) +
     Cost.ticks (initial_c a) +
     Cost.ticks (iterate
       (step_c a (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)))
       fuel (initial a)))%N.
Proof.
  unfold run_c; autorewrite with galois_cost.
  fold (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)).
  fold (initial a).
  destruct (Cost.value (iterate
    (step_c a (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)))
    fuel (initial a))); autorewrite with galois_cost; lia.
Qed.

(** Empty constructors are free and initialization charges the complete original enqueue list. *)
Theorem initial_cost {X C A} (a : Analysis.t X C A) :
  Cost.ticks (initial_c a) =
    Cost.ticks (enqueue_c a (System.constraints (Analysis.system a))
      (State Map.empty Heap.empty FinSet.empty Map.empty 0)).
Proof.
  reflexivity.
Qed.

Arguments step_c {X C A} a ix s : simpl never.
Arguments step {X C A} a ix s : simpl never.
Arguments run_c {X C A} a fuel : simpl never.
Arguments run {X C A} a fuel : simpl never.
Arguments solver {X C A} : simpl never.

End Worklist.
Import Worklist.
