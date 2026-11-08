(** * Unprioritized joining transitions

    Each transition evaluates one pending row and requeues readers of changed outputs.
    For example, a side update can put the current row back on the pending list.
    Builds on: FixpointEval, FixpointIndex and FixpointTotalQueue. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointIndex FixpointAnalysis
  FixpointTotalQueue.
Import List.ListNotations Cost.Notations.

Module TotalKernel.

(** Continuation equality exposes states without reducing their computational contents. *)
Theorem continuing_eq {B D} (s t : B) : @inl B D s = inl t -> s = t.
Proof.
  congruence.
Qed.

(** An engine state keeps its computational assignment and its pending-row cache. *)
Record state (X C A : Type) := State {
  current : assignment X A;
  queue : TotalQueue.t C
}.

Arguments State {X C A}.
Arguments current {X C A}.
Arguments queue {X C A}.

(** An output invokes the shared rule and requeues readers only when the rule reports change. *)
Definition update_c {X C A} (a : Analysis.t X C A) (ix : sys_index X C)
    (s : state X C A) (xa : X * A) :=
  let* changed := Update.rule_c (Analysis.key_enc a) (Analysis.lat a)
    (join_c (Analysis.lat a)) (current s) (fst xa) (snd xa) in
  if snd changed then
    let* readers := readers_of_c (Analysis.key_enc a) ix (fst xa) in
    let* todo := TotalQueue.push_many_c (Analysis.row_enc a) readers (queue s) in
    Cost.ret (State (fst changed) todo)
  else Cost.ret (State (fst changed) (queue s)).

Definition update {X C A} (a : Analysis.t X C A) ix s xa :=
  Cost.value (update_c a ix s xa).

(** Ordered output application keeps evaluator inputs frozen throughout one constraint step. *)
Definition updates_c {X C A} (a : Analysis.t X C A) ix outs (s : state X C A) :=
  fold_left_c (update_c a ix) outs s.

Definition updates {X C A} (a : Analysis.t X C A) ix outs s :=
  Cost.value (updates_c a ix outs s).

(** The empty queue stops, and every nonempty queue performs one constraint evaluation. *)
Definition step_c {X C A} (a : Analysis.t X C A) ix (s : state X C A)
    : Cost.t (state X C A + assignment X A) :=
  let* popped := TotalQueue.pop_c (Analysis.row_enc a) (queue s) in
  match popped with
  | None => Cost.ret (inr (current s))
  | Some (c, rest) =>
    let* r := Eval.outputs_c (Analysis.system a)
      (lookup_c (Analysis.key_enc a) (Analysis.lat a) (current s)) c in
    Cost.map inl (updates_c a ix (fst r) (State (current s) rest))
  end.

Definition step {X C A} (a : Analysis.t X C A) ix s := Cost.value (step_c a ix s).

(** Initial insertion deduplicates row membership and charges each original occurrence. *)
Definition initial_c {X C A} (a : Analysis.t X C A) :=
  let* q := TotalQueue.push_many_c (Analysis.row_enc a)
    (System.constraints (Analysis.system a)) TotalQueue.empty in
  Cost.ret (@State X C A Map.empty q).

Definition initial {X C A} (a : Analysis.t X C A) := Cost.value (initial_c a).

(** Read incidence counts retain duplicate metadata and duplicate constraint occurrences. *)
Definition read_keys_c {X C A} (a : Analysis.t X C A) :=
  fold_right_c (fun c xs =>
    Cost.step ;;
    let* reads := System.deps_c (Analysis.static a) c in
    app_c reads xs) [] (System.constraints (Analysis.system a)).

Definition read_keys {X C A} (a : Analysis.t X C A) := Cost.value (read_keys_c a).

(** Unary numeric conversion charges one cell per successor and returns positive fuel. *)
Fixpoint positive_c (n : nat) : Cost.t positive :=
  match n with
  | O => Cost.ret 1%positive
  | S k => Cost.step ;; Cost.map Pos.succ (positive_c k)
  end.

(** Numeric preparation charges row counting, read construction, incidence counting and conversion. *)
Definition fuel_c {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) :=
  let* cs := length_c (System.constraints (Analysis.system a)) in
  let* reads := read_keys_c a in
  let* ds := length_c reads in
  let n := (cs + bound (Terminates.hgt HT) * ds)%nat in
  positive_c n.

Definition fuel {X C A} (a : Analysis.t X C A) HT := Cost.value (fuel_c a HT).

(** The prepared engine returns an explicit exhaustion observation at arbitrary caller fuel. *)
Definition loop_c {X C A} (a : Analysis.t X C A) ix f :=
  let* start := initial_c a in iterate (step_c a ix) f start.

(** The total entry prepares one index and computes its own numeric fuel. *)
Definition run_c {X C A} (a : Analysis.t X C A) HT :=
  let* ix := index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  let* f := fuel_c a HT in
  let* result := loop_c a ix f in
  Cost.ret (match result with inl s => current s | inr m => m end).

Definition run {X C A} (a : Analysis.t X C A) HT := Cost.value (run_c a HT).

(** The update equation uses the shared rule's public result and indexed reader list. *)
Theorem update_equation {X C A} (a : Analysis.t X C A) ix s xa :
  update a ix s xa =
    let r := Update.rule (Analysis.key_enc a) (Analysis.lat a)
      (join_c (Analysis.lat a)) (current s) (fst xa) (snd xa) in
    State (fst r) (if snd r then TotalQueue.push_many (Analysis.row_enc a)
      (readers_of (Analysis.key_enc a) ix (fst xa)) (queue s) else queue s).
Proof.
  unfold update, update_c; rewrite Cost.value_bind.
  fold (Update.rule (Analysis.key_enc a) (Analysis.lat a)
    (join_c (Analysis.lat a)) (current s) (fst xa) (snd xa)).
  destruct (snd (Update.rule _ _ _ _ _ _)); autorewrite with galois_cost; reflexivity.
Qed.

(** The update fold exposes its ordered shared-rule calls. *)
Theorem updates_equation {X C A} (a : Analysis.t X C A) ix outs s :
  updates a ix outs s =
    match outs with
    | [] => s
    | xa :: rest => updates a ix rest (update a ix s xa)
    end.
Proof.
  destruct outs; unfold updates, updates_c; rewrite !value_fold_left_c; reflexivity.
Qed.

(** One step exposes its queue pop, evaluator observation and frozen output fold. *)
Theorem step_equation {X C A} (a : Analysis.t X C A) ix s :
  step a ix s =
    match TotalQueue.pop (Analysis.row_enc a) (queue s) with
    | None => inr (current s)
    | Some (c, rest) =>
      inl (updates a ix
        (fst (Eval.outputs (Analysis.system a) c
          (lookup (Analysis.key_enc a) (Analysis.lat a) (current s))))
        (State (current s) rest))
    end.
Proof.
  unfold step, step_c; rewrite Cost.value_bind.
  fold (TotalQueue.pop (Analysis.row_enc a) (queue s)).
  destruct (TotalQueue.pop _ _) as [[c rest]|]; autorewrite with galois_cost;
    [|reflexivity].
  rewrite (Eval.outputs_c_spec (Analysis.system a) c
    (lookup_c (Analysis.key_enc a) (Analysis.lat a) (current s))
    (lookup (Analysis.key_enc a) (Analysis.lat a) (current s))) by reflexivity.
  reflexivity.
Qed.

(** Initial computation starts at bottom and queues all listed constraints. *)
Theorem initial_equation {X C A} (a : Analysis.t X C A) :
  initial a = State Map.empty (TotalQueue.push_many (Analysis.row_enc a)
    (System.constraints (Analysis.system a)) TotalQueue.empty).
Proof.
  reflexivity.
Qed.

(** Read preparation returns every declared read occurrence in source order. *)
Theorem read_keys_equation {X C A} (a : Analysis.t X C A) :
  read_keys a = flat_map (deps (Analysis.static a)) (System.constraints (Analysis.system a)).
Proof.
  unfold read_keys, read_keys_c; rewrite value_fold_right_c.
  induction (System.constraints (Analysis.system a)) as [|c cs IH].
  - reflexivity.
  - cbn [fold_right flat_map]; autorewrite with galois_cost; rewrite IH; reflexivity.
Qed.

(** The total projection exposes its single prepared loop and both explicit loop outcomes. *)
Theorem run_equation {X C A} (a : Analysis.t X C A) HT :
  run a HT =
    match Cost.value (loop_c a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))
      (fuel a HT)) with
    | inl s => current s
    | inr m => m
    end.
Proof.
  unfold run, run_c; rewrite !Cost.value_bind, Cost.value_ret; reflexivity.
Qed.

End TotalKernel.
Import TotalKernel.
