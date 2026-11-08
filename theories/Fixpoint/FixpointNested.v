(** * Nested traversal codes

    A traversal separates component bodies from the code that follows them.
    For example, [Component h (Visit x End) End] visits h before its body x.
    The observation engine is dropped because eviction changes memory use alone.
    Builds on: FixpointAnalysis, FixpointCycles, FixpointIndex, FixpointEval and CostLoop. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis FixpointCycles FixpointIndex
  FixpointEval FixpointSolver.
Import List.ListNotations Cost.Notations.

Module Nested.

(** A component visits its head and stabilizes its body before continuing with its rest. *)
Inductive code (X : Type) : Type :=
  | End
  | Visit (x : X) (rest : code X)
  | Component (h : X) (body rest : code X).

Arguments End {X}.
Arguments Visit {X}.
Arguments Component {X}.

Fixpoint vertices {X} (p : code X) : list X :=
  match p with
  | End => []
  | Visit x rest => x :: vertices rest
  | Component h body rest => h :: vertices body ++ vertices rest
  end.

Fixpoint heads {X} (p : code X) : list X :=
  match p with
  | End => []
  | Visit _ rest => heads rest
  | Component h body rest => h :: heads body ++ heads rest
  end.

Fixpoint depth {X} (p : code X) : nat :=
  match p with
  | End => 0
  | Visit _ rest => depth rest
  | Component _ body rest => Nat.max (S (depth body)) (depth rest)
  end.

(** Validity covers primary targets and cuts every static cycle at a component head. *)
Definition code_ok {X C A} (a : Analysis.t X C A) (p : code X) : Prop :=
  (forall c, In c (System.constraints (Analysis.system a)) ->
    In (System.target (Analysis.system a) c) (vertices p)) /\
  cuts_every_cycle (Analysis.static a) (fun x =>
    existsb (fun h => eqb (Analysis.key_enc a) x h) (heads p)).

(** The scheduled size counts actual contributor occurrences, including side-target buckets. *)
Fixpoint scheduled {X C} (EX : encoding X) (ix : sys_index X C) (p : code X) : nat :=
  match p with
  | End => 0
  | Visit x rest => length (contributors_of EX ix x) + scheduled EX ix rest
  | Component h body rest =>
    length (contributors_of EX ix h) + scheduled EX ix body + scheduled EX ix rest
  end.

Fixpoint vertices_c {X} (p : code X) : Cost.t (list X) :=
  Cost.step ;;
  match p with
  | End => Cost.ret []
  | Visit x rest =>
    let* xs := vertices_c rest in Cost.ret (x :: xs)
  | Component h body rest =>
    let* xs := vertices_c body in
    let* ys := vertices_c rest in
    let* zs := app_c xs ys in Cost.ret (h :: zs)
  end.

Fixpoint heads_c {X} (p : code X) : Cost.t (list X) :=
  Cost.step ;;
  match p with
  | End => Cost.ret []
  | Visit _ rest => heads_c rest
  | Component h body rest =>
    let* xs := heads_c body in
    let* ys := heads_c rest in
    let* zs := app_c xs ys in Cost.ret (h :: zs)
  end.

(** Unary policy input conversion charges every constructor it traverses. *)
Fixpoint delay_c (n : nat) : Cost.t N :=
  match n with
  | O => Cost.ret 0%N
  | S n =>
    Cost.step ;;
    let* k := delay_c n in Cost.ret (N.succ k)
  end.

Fixpoint cover_c {X C A} (a : Analysis.t X C A) (vs : FinSet.t X) (cs : list C)
    : Cost.t bool :=
  match cs with
  | [] => Cost.ret true
  | c :: rest =>
    Cost.step ;;
    let* x := System.target_c (Analysis.system a) c in
    let* covered := FinSet.mem_c (Analysis.key_enc a) x vs in
    if covered then cover_c a vs rest else Cost.ret false
  end.

Module Frame.

(** A saved epoch represents a changed flag for every suspended component in constant work. *)
Record t (X : Type) := Make {
  head : X;
  body : code X;
  rest : code X;
  epoch : N
}.

Arguments Make {X}.
Arguments head {X}.
Arguments body {X}.
Arguments rest {X}.
Arguments epoch {X}.

Definition pass {X} (f : t X) := Visit (head f) (body f).

End Frame.
Import Frame.

Module State.

(** Epoch inequality marks all active frames after any changed evaluation. *)
Record t (X C A : Type) := Make {
  values : assignment X A;
  counters : Map.t X N;
  pointer : code X;
  ready : list C;
  frames : list (Frame.t X);
  epoch : N;
  outer : N;
  evals : N
}.

Arguments Make {X C A}.
Arguments values {X C A}.
Arguments counters {X C A}.
Arguments pointer {X C A}.
Arguments ready {X C A}.
Arguments frames {X C A}.
Arguments epoch {X C A}.
Arguments outer {X C A}.
Arguments evals {X C A}.

End State.
Import State.

Definition start {X C A} (p : code X) : State.t X C A :=
  State.Make Map.empty Map.empty p [] [] 0 0 0.

(** The operator widens only at component heads selected by the policy after its delay. *)
Definition op_c {X C A} (a : Analysis.t X C A) (hs : FinSet.t X) (delay : N)
    (x : X) (count : N) (old value : A) : Cost.t A :=
  let* head := FinSet.mem_c (Analysis.key_enc a) x hs in
  Cost.step ;;
  let* selected := Policy.widen_at_c (Analysis.policy a) x in
  if head && selected && N.leb delay count
  then Cost.step ;; widen_c (Analysis.lat a) old value
  else Cost.step ;; join_c (Analysis.lat a) old value.

(** Output updates retain ordered repeated side outputs and count changes per unknown. *)
Fixpoint updates_c {X C A} (a : Analysis.t X C A) (hs : FinSet.t X) (delay : N)
    (outs : list (X * A)) (m : assignment X A) (counts : Map.t X N)
    : Cost.t (assignment X A * Map.t X N * bool) :=
  match outs with
  | [] => Cost.ret (m, counts, false)
  | (x, value) :: rest =>
    Cost.step ;;
    let* count := Map.find_or_c (Analysis.key_enc a) 0%N x counts in
    let* first := Update.rule_c (Analysis.key_enc a) (Analysis.lat a)
      (op_c a hs delay x count) m x value in
    let* counts' :=
      if snd first then Map.set_c (Analysis.key_enc a) x (N.succ count) counts
      else Cost.ret counts in
    let* next := updates_c a hs delay rest (fst first) counts' in
    Cost.ret (fst (fst next), snd (fst next), snd first || snd next)
  end.

Definition updates {X C A} (a : Analysis.t X C A) hs delay outs m counts :=
  Cost.value (updates_c a hs delay outs m counts).

(** Each transition evaluates one row or advances one traversal constructor. *)
Definition step_c {X C A} (a : Analysis.t X C A) (root : code X)
    (ix : sys_index X C) (hs : FinSet.t X) (delay : N) (s : State.t X C A)
    : Cost.t (State.t X C A + assignment X A) :=
  match State.ready s with
  | c :: rest =>
    let* out := Eval.outputs_c (Analysis.system a)
      (lookup_c (Analysis.key_enc a) (Analysis.lat a) (State.values s)) c in
    let* next := updates_c a hs delay (fst out) (State.values s) (State.counters s) in
    Cost.ret (inl (State.Make (fst (fst next)) (snd (fst next))
      (State.pointer s) rest (State.frames s)
      (if snd next then N.succ (State.epoch s) else State.epoch s)
      (State.outer s) (N.succ (State.evals s))))
  | [] =>
    match State.pointer s with
    | Visit x rest =>
      let* cs := contributors_of_c (Analysis.key_enc a) ix x in
      Cost.ret (inl (State.Make (State.values s) (State.counters s) rest cs
        (State.frames s) (State.epoch s) (State.outer s) (State.evals s)))
    | Component h body rest =>
      Cost.ret (inl (State.Make (State.values s) (State.counters s) (Visit h body) []
        (Frame.Make h body rest (State.epoch s) :: State.frames s)
        (State.epoch s) (State.outer s) (State.evals s)))
    | End =>
      match State.frames s with
      | f :: rest =>
        if N.eqb (Frame.epoch f) (State.epoch s) then
          Cost.ret (inl (State.Make (State.values s) (State.counters s) (Frame.rest f) []
            rest (State.epoch s) (State.outer s) (State.evals s)))
        else
          Cost.ret (inl (State.Make (State.values s) (State.counters s) (Frame.pass f) []
            (Frame.Make (Frame.head f) (Frame.body f) (Frame.rest f) (State.epoch s) :: rest)
            (State.epoch s) (State.outer s) (State.evals s)))
      | [] =>
        if N.eqb (State.outer s) (State.epoch s) then Cost.ret (inr (State.values s))
        else Cost.ret (inl (State.Make (State.values s) (State.counters s) root [] []
          (State.epoch s) (State.epoch s) (State.evals s)))
      end
    end
  end.

Definition step {X C A} (a : Analysis.t X C A) root ix hs delay s :=
  Cost.value (step_c a root ix hs delay s).

(** Preparation guards coverage so Solver.laws can quantify over arbitrary analyses. *)
Definition run_c {X C A} (a : Analysis.t X C A) (root : code X) fuel
    : Cost.t (Outcome.t X A (assignment X A)) :=
  let* vs := vertices_c root in
  let* vertex_set := FinSet.of_list_c (Analysis.key_enc a) vs in
  let* covered := cover_c a vertex_set (System.constraints (Analysis.system a)) in
  if covered then
    let* hh := heads_c root in
    let* hs := FinSet.of_list_c (Analysis.key_enc a) hh in
    let* delay := delay_c (Policy.delay (Analysis.policy a)) in
    let* ix := index_system_c (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
    let* result := iterate (step_c a root ix hs delay) fuel (start root) in
    Cost.ret (match result with
    | inl s => Outcome.OutOfFuel (State.values s)
    | inr m => Outcome.Solved m
    end)
  else Cost.ret (Outcome.Rejected Reason.Bad_wto).

Definition run {X C A} (a : Analysis.t X C A) root fuel := Cost.value (run_c a root fuel).

Definition solver {X C A} (root : code X) : Solver.t X C A :=
  Solver.Make (fun a fuel => run_c a root fuel).

(** Costed vertex traversal returns the full multiplicity-preserving inventory. *)
Theorem vertices_equation {X} (p : code X) : Cost.value (vertices_c p) = vertices p.
Proof.
  induction p; cbn [vertices_c vertices]; autorewrite with galois_cost;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

(** Costed head traversal returns the component-head inventory in traversal order. *)
Theorem heads_equation {X} (p : code X) : Cost.value (heads_c p) = heads p.
Proof.
  induction p; cbn [heads_c heads]; autorewrite with galois_cost;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

(** Unary delay conversion computes the binary value without discarding traversal charges. *)
Theorem delay_equation n : Cost.value (delay_c n) = N.of_nat n.
Proof.
  induction n; cbn [delay_c]; autorewrite with galois_cost.
  - reflexivity.
  - rewrite IHn, Nat2N.inj_succ; reflexivity.
Qed.

(** The run uses the public iterator and returns its unchecked exhausted assignment. *)
Theorem run_equation {X C A} (a : Analysis.t X C A) root fuel :
  run a root fuel =
    if Cost.value (cover_c a (FinSet.of_list (Analysis.key_enc a) (vertices root))
      (System.constraints (Analysis.system a))) then
      match Cost.value (iterate
        (step_c a root
          (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))
          (FinSet.of_list (Analysis.key_enc a) (heads root))
          (N.of_nat (Policy.delay (Analysis.policy a)))) fuel (start root)) with
      | inl s => Outcome.OutOfFuel (State.values s)
      | inr m => Outcome.Solved m
      end
    else Outcome.Rejected Reason.Bad_wto.
Proof.
  unfold run, run_c; autorewrite with galois_cost; rewrite vertices_equation.
  fold (FinSet.of_list (Analysis.key_enc a) (vertices root)).
  destruct (Cost.value (cover_c a
    (FinSet.of_list (Analysis.key_enc a) (vertices root))
    (System.constraints (Analysis.system a)))); [|reflexivity].
  autorewrite with galois_cost; rewrite heads_equation, delay_equation.
  reflexivity.
Qed.

End Nested.
Import Nested.
