(** * Parent walking through the binary driver

    The driver records a reversed path and stops at a root or the requested prefix length.
    For example, a one-link budget records one compression update even in a malformed cycle.
    Builds on: CostLoop, BaseMap and BaseEncoding. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap.
Import List.ListNotations Cost.Notations.

Module UnionFindLoop.

Local Open Scope nat_scope.

(** The path is in compression order, from the last visited parent back to the initial query. *)
Definition state K := (nat * K * list K)%type.

(** One step looks up at most one parent and records at most one compression frame. *)
Definition step_c {K} (E : encoding K) (parents : Map.t K K) (s : state K)
    : Cost.t (state K + (K * list K)) :=
  let '(remaining, current, path) := s in
  match remaining with
  | 0 => Cost.ret (inr (current, path))
  | S rest =>
    let* parent := Map.get_c E current parents in
    match parent with
    | None => Cost.ret (inr (current, path))
    | Some next => Cost.ret (inl (rest, next, current :: path))
    end
  end.

(** The step's value follows the public parent-map lookup equation. *)
Theorem step_equation {K} (E : encoding K) parents remaining current path :
  Cost.value (step_c E parents (remaining, current, path)) =
  match remaining with
  | 0 => inr (current, path)
  | S rest =>
    match Map.get E current parents with
    | None => inr (current, path)
    | Some next => inl (rest, next, current :: path)
    end
  end.
Proof.
  destruct remaining as [|rest]; [reflexivity|].
  unfold step_c. rewrite Cost.value_bind. fold (Map.get E current parents).
  destruct (Map.get E current parents); reflexivity.
Qed.

(** Bounded path specifications include exhausted prefixes on arbitrary raw maps. *)
Inductive path_spec {K} (E : encoding K) (parents : Map.t K K) :
    nat -> K -> K -> list K -> Prop :=
  | Path_zero x : path_spec E parents 0 x x []
  | Path_root rest x : Map.get E x parents = None ->
      path_spec E parents (S rest) x x []
  | Path_next rest x y root path :
      Map.get E x parents = Some y ->
      path_spec E parents rest y root path ->
      path_spec E parents (S rest) x root (path ++ [x]).

(** A fixed bounded query has one root-prefix endpoint and one compression path. *)
Theorem path_unique {K} (E : encoding K) parents fuel x r ps :
  path_spec E parents fuel x r ps ->
  forall r' ps', path_spec E parents fuel x r' ps' -> r = r' /\ ps = ps'.
Proof.
  intro Hpath.
  induction Hpath as [x|rest x Hnone|rest x y root path Hparent Htail IH];
    intros r' ps' Hother;
    inversion Hother as [x0|rest0 x0 Hnone'|rest0 x0 y0 root0 path0 Hparent' Htail'];
    subst; try (split; reflexivity);
    try congruence.
  assert (Hequal : y = y0) by congruence. subst y0.
  destruct (IH _ _ Htail') as [Hr Hps]. subst. split; reflexivity.
Qed.

Local Lemma runs_path {K} (E : encoding K) parents budget :
  forall remaining current path result,
  remaining < budget ->
  runs (step_c E parents) budget (remaining, current, path) result ->
  exists root frames,
    result = inr (root, frames ++ path) /\
    path_spec E parents remaining current root frames.
Proof.
  induction budget as [|budget IH]; intros remaining current path result Hbudget Hrun.
  - lia.
  - inversion Hrun as [|n s r Hstop|n s next final Hnext Htail]; subst.
    + rewrite step_equation in Hstop. destruct remaining as [|rest].
      * inversion Hstop; subst r. exists current, []. split; [reflexivity|constructor].
      * destruct (Map.get E current parents) as [next|] eqn:Hparent; [discriminate|].
        inversion Hstop; subst r. exists current, []. split; [reflexivity|constructor; assumption].
    + rewrite step_equation in Hnext. destruct remaining as [|rest]; [discriminate|].
      destruct (Map.get E current parents) as [parent|] eqn:Hparent; [|discriminate].
      inversion Hnext; subst next.
      destruct (IH rest parent (current :: path) result ltac:(lia) Htail)
        as [root [frames [Hresult Hspec]]].
      exists root, (frames ++ [current]). split.
      * rewrite Hresult, <- app_assoc. reflexivity.
      * eapply Path_next; eassumption.
Qed.

(** Sufficient binary fuel is built by charging each natural prefix constructor once. *)
Fixpoint sufficient_fuel_c (fuel : nat) : Cost.t positive :=
  match fuel with
  | 0 => Cost.ret xH
  | S rest =>
    Cost.step ;;
    let* smaller := sufficient_fuel_c rest in Cost.ret (xO smaller)
  end.

Definition sufficient_fuel fuel := Cost.value (sufficient_fuel_c fuel).

(** Each charged prefix constructor contributes one binary zero digit. *)
Theorem sufficient_fuel_equation fuel :
  sufficient_fuel fuel =
    match fuel with 0 => xH | S rest => xO (sufficient_fuel rest) end.
Proof.
  destruct fuel; reflexivity.
Qed.

(** Fuel construction charges its complete natural traversal. *)
Theorem sufficient_fuel_cost fuel :
  Cost.ticks (sufficient_fuel_c fuel) = N.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; [reflexivity|].
  cbn [sufficient_fuel_c]. autorewrite with galois_cost.
  rewrite IH, Nat2N.inj_succ. lia.
Qed.

(** The constructed fuel's width includes its leading one digit. *)
Theorem sufficient_fuel_width fuel :
  N.pos (Pos.size (sufficient_fuel fuel)) = N.of_nat (S fuel).
Proof.
  induction fuel as [|fuel IH]; rewrite sufficient_fuel_equation; [reflexivity|].
  cbn [Pos.size].
  change (N.succ (N.pos (Pos.size (sufficient_fuel fuel))) = N.of_nat (S (S fuel))).
  rewrite IH, !Nat2N.inj_succ. reflexivity.
Qed.

(** The constructed power of two can inspect the entire prefix and its stopping state. *)
Theorem sufficient_fuel_capacity fuel :
  fuel < Pos.to_nat (sufficient_fuel fuel).
Proof.
  induction fuel as [|fuel IH]; rewrite sufficient_fuel_equation; [cbn; lia|].
  rewrite Pos2Nat.inj_xO. lia.
Qed.

(** The actual driver returns a root and the compression-order path for the requested prefix. *)
Definition walk_c {K} (E : encoding K) parents fuel (x : K) : Cost.t (K * list K) :=
  let* binary := sufficient_fuel_c fuel in
  let* result := iterate (step_c E parents) binary (fuel, x, []) in
  Cost.ret
    (match result with
    | inl (_, current, path) => (current, path)
    | inr result => result
    end).

(** The extra stopping step makes exhaustion impossible even for malformed parent maps. *)
Theorem walk_correct {K} (E : encoding K) parents fuel (x : K) :
  let '(root, path) := Cost.value (walk_c E parents fuel x) in
  path_spec E parents fuel x root path.
Proof.
  pose proof (iterate_value (step_c E parents) (sufficient_fuel fuel) (fuel, x, [])) as Hrun.
  destruct (runs_path E parents (Pos.to_nat (sufficient_fuel fuel)) fuel x [] _
    (sufficient_fuel_capacity fuel) Hrun)
    as [root [frames [Hresult Hspec]]].
  unfold walk_c. rewrite !Cost.value_bind. fold (sufficient_fuel fuel).
  rewrite Hresult. cbn. rewrite app_nil_r. exact Hspec.
Qed.

(** Recorded compression frames never exceed the queried parent-link budget. *)
Theorem path_length {K} (E : encoding K) parents fuel x root path :
  path_spec E parents fuel x root path -> length path <= fuel.
Proof.
  intro Hpath. induction Hpath; cbn [length]; try lia.
  rewrite length_app. cbn. lia.
Qed.

(** An allowed query visits only allowed keys when the parent relation is closed on them. *)
Theorem path_allowed {K} (E : encoding K) parents (allowed : K -> Prop) :
  (forall a b, allowed a -> Map.get E a parents = Some b -> allowed b) ->
  forall fuel x root path, path_spec E parents fuel x root path ->
  allowed x -> allowed root /\ Forall allowed path.
Proof.
  intros Hclosed fuel x root path Hpath.
  induction Hpath as [x|rest x Hnone|rest x y root path Hparent Htail IH]; intro Hx.
  - split; [exact Hx|constructor].
  - split; [exact Hx|constructor].
  - destruct (IH (Hclosed x y Hx Hparent)) as [Hr Hps].
    split; [exact Hr|]. apply Forall_app. split; [exact Hps|].
    constructor; [exact Hx|constructor].
Qed.

(** The step charges exactly one reached lookup, including on arbitrary raw maps. *)
Theorem step_cost {K} (E : encoding K) parents remaining (x : K) path :
  Cost.ticks (step_c E parents (remaining, x, path)) =
    match remaining with 0 => 0%N | S _ => Cost.ticks (Map.get_c E x parents) end.
Proof.
  destruct remaining as [|rest]; [reflexivity|].
  unfold step_c. rewrite Cost.ticks_bind. fold (Map.get E x parents).
  destruct (Map.get E x parents); rewrite Cost.ticks_ret; lia.
Qed.

(** A callee budget on the closed visited domain bounds the actual binary walk. *)
Theorem walk_cost {K} (E : encoding K) parents fuel (x : K) (allowed : K -> Prop) g :
  allowed x ->
  (forall a b, allowed a -> Map.get E a parents = Some b -> allowed b) ->
  (forall a, allowed a -> (Cost.ticks (Map.get_c E a parents) <= g)%N) ->
  (Cost.ticks (walk_c E parents fuel x) <=
    Cost.ticks (sufficient_fuel_c fuel) + (g + 2) * (N.of_nat fuel + 1) +
    2 * N.pos (Pos.size (sufficient_fuel fuel)))%N.
Proof.
  intros Hx Hclosed Hcallee.
  pose proof (iterate_cost (step_c E parents)
    (fun s => let '(remaining, current, _) := s in allowed current)
    (fun s => let '(remaining, _, _) := s in N.of_nat remaining) g
    (sufficient_fuel fuel) (fuel, x, [])) as Hcost.
  assert (Hstep : forall s : state K,
    (let '(_, current, _) := s in allowed current) ->
    (Cost.ticks (step_c E parents s) <= g)%N /\
    match Cost.value (step_c E parents s) with
    | inl s' =>
      (let '(_, current, _) := s' in allowed current) /\
      (let '(remaining', _, _) := s' in
        remaining' < let '(remaining, _, _) := s in remaining)
    | inr _ => True
    end).
  { intros [[remaining current] path] Hcurrent.
    rewrite step_cost, step_equation. destruct remaining as [|rest].
    - split; [lia|exact I].
    - split; [apply Hcallee; exact Hcurrent|].
      destruct (Map.get E current parents) as [next|] eqn:Hparent; [|exact I].
      split; [eapply Hclosed; eassumption|lia]. }
  assert (Hbound : (Cost.ticks
      (iterate (step_c E parents) (sufficient_fuel fuel) (fuel, x, [])) <=
    (g + 2) * (N.of_nat fuel + 1) +
    2 * N.pos (Pos.size (sufficient_fuel fuel)))%N).
  { apply Hcost; [|exact Hx]. intros [[remaining current] path] Hcurrent.
    destruct (Hstep (remaining, current, path) Hcurrent) as [Hticks Hnext].
    split; [exact Hticks|]. destruct (Cost.value (step_c E parents _)) as [s'|r].
    - destruct s' as [[remaining' current'] path']. cbn in *.
      destruct Hnext as [Hcurrent' Hdecrease]. split; [exact Hcurrent'|lia].
    - exact I. }
  unfold walk_c. rewrite Cost.ticks_bind. fold (sufficient_fuel fuel).
  rewrite Cost.ticks_bind.
  destruct (Cost.value (iterate _ _ _)); rewrite Cost.ticks_ret; lia.
Qed.

End UnionFindLoop.
