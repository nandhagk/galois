(** * Fold and bind tactic clients

    These proofs exercise the shared suite against symbolic callbacks and containers.
    For example, folding a nonnegative increment cannot reduce an accumulator.
    Builds on: BaseTacticsInv and CostList. *)

From Stdlib Require Import List NArith Lia PeanoNat Sorting.Sorted.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseCode BaseMap BaseSet BaseKeyTactics
  BaseTactics BaseTacticsInv.
Import List.ListNotations Cost.Notations.

Open Scope nat_scope.

(** Costed addition preserves a lower bound on the initial accumulator. *)
Lemma cost_fold_sum_lower (xs : list nat) n :
  n <= Cost.value (fold_left_c (fun a x => Cost.ret (a + x)) xs n).
Proof.
  rewrite value_fold_left_c.
  fold_invariant (fun a => n <= a).
  - lia.
  - intros acc x Hin Hacc. rewrite Cost.value_ret. lia.
Qed.

(** A costed fold of monotone callbacks preserves an arbitrary lower bound. *)
Lemma cost_fold_monotone (f : nat -> nat -> Cost.t nat) xs n bound :
  bound <= n ->
  (forall a x, In x xs -> a <= Cost.value (f a x)) ->
  bound <= Cost.value (fold_left_c f xs n).
Proof.
  intros Hinit Hstep. rewrite value_fold_left_c.
  fold_invariant (fun a => bound <= a).
  - exact Hinit.
  - intros acc x Hin Hacc. specialize (Hstep acc x Hin). lia.
Qed.

Example fold_empty n : n <= fold_left Nat.add [] n.
Proof.
  fold_invariant (fun a => n <= a).
  - lia.
  - intros acc x Hin. inversion Hin.
Qed.

Example fold_sorted xs :
  StronglySorted le (fold_left (fun acc (_ : nat) => 0 :: acc) xs []).
Proof.
  fold_invariant (fun acc => StronglySorted le acc).
  - constructor.
  - intros acc x Hin Hsorted. constructor.
    + exact Hsorted.
    + apply Forall_forall. intros y Hy. lia.
Qed.

Example fold_right_bound xs n : n <= fold_right Nat.add n xs.
Proof.
  apply (fold_right_invariant Nat.add xs n (fun a => n <= a)).
  - lia.
  - intros x acc Hin Hacc. lia.
Qed.

Example fold_precondition xs :
  Forall (fun x => x <= 4) xs ->
  fold_left Nat.max xs 0 <= 4.
Proof.
  intro Hall.
  apply (fold_invariant_gen Nat.max xs 0 (fun a => a <= 4) (fun x => x <= 4)).
  - exact Hall.
  - lia.
  - intros acc x Hx Hacc. apply Nat.max_lub; assumption.
Qed.

(** A non-fold conclusion is rejected rather than silently accepted. *)
Example fold_reject : True.
Proof.
  Fail fold_invariant (fun n : nat => n = n).
  exact I.
Qed.

Definition lookup_then (m : Cost.t (option nat)) (f : nat -> Cost.t (option nat)) :=
  let* o := m in
  match o with
  | Some x => f x
  | None => Cost.ret None
  end.

(** A successful lookup and callback expose the successful lookup result. *)
Lemma lookup_then_success m f y :
  Cost.value (lookup_then m f) = Some y ->
  exists x, Cost.value m = Some x /\ Cost.value (f x) = Some y.
Proof.
  unfold lookup_then. intro H. inv_bind. eauto.
Qed.

(** The successful path retains the exact charges of both arbitrary callees. *)
Lemma lookup_then_ticks m f y :
  Cost.value (lookup_then m f) = Some y ->
  exists x, Cost.value m = Some x /\
    Cost.ticks (lookup_then m f) = (Cost.ticks m + Cost.ticks (f x))%N.
Proof.
  unfold lookup_then. intro H. inv_bind. eauto.
Qed.

Example lookup_then_budget m f y budget :
  Cost.value (lookup_then m f) = Some y ->
  (forall x, Cost.value m = Some x ->
    (Cost.ticks m + Cost.ticks (f x) <= budget)%N) ->
  (Cost.ticks (lookup_then m f) <= budget)%N.
Proof.
  unfold lookup_then. intros H Hbudget. inv_bind. eauto.
Qed.

Example bind_one_step (m : Cost.t (option nat)) y :
  Cost.value (let* x := m in Cost.ret x) = Some y ->
  Cost.value m = Some y.
Proof.
  intro H. inv_bind. reflexivity.
Qed.

Example bind_none (f : nat -> Cost.t (option nat)) y :
  Cost.value (let* x := Cost.ret None in
    match x with Some n => f n | None => Cost.ret None end) = Some y -> False.
Proof.
  intro H. inv_bind.
Qed.

Example bind_chain (m : Cost.t (option nat)) (f g : nat -> Cost.t (option nat)) y :
  Cost.value (let* o := m in
    match o with
    | None => Cost.ret None
    | Some x =>
      let* p := f x in
      match p with None => Cost.ret None | Some z => g z end
    end) = Some y ->
  exists x z, Cost.value m = Some x /\ Cost.value (f x) = Some z /\
    Cost.value (g z) = Some y.
Proof.
  intro H. inv_bind. eauto.
Qed.

Example bind_self_reference (m : Cost.t (option nat)) (g : option nat -> nat) :
  Cost.value (let* x := Cost.ret tt in m) = Some (g (Cost.value m)) ->
  exists y, Cost.value m = Some y.
Proof.
  intro H. inv_bind. eauto.
Qed.

Example lookup_fixture_success :
  (Cost.value (lookup_then (Cost.mk (Some 2) 5) (fun n => Cost.mk (Some (S n)) 7)),
   Cost.ticks (lookup_then (Cost.mk (Some 2) 5) (fun n => Cost.mk (Some (S n)) 7))) =
  (Some 3, 12%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example lookup_fixture_none :
  (Cost.value (lookup_then (Cost.mk None 5) (fun n => Cost.mk (Some (S n)) 7)),
   Cost.ticks (lookup_then (Cost.mk None 5) (fun n => Cost.mk (Some (S n)) 7))) =
  (None, 5%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** A hypothesis without a value-of-bind observation is out of contract. *)
Example bind_reject : True.
Proof.
  Fail inv_bind.
  exact I.
Qed.

Section Suite.
Context {K V : Type} (E : encoding K) (HE : encoding_laws E).
Variables (k j : K) (v : V) (m : Map.t K V) (s t : FinSet.t K).
Hypotheses (Hm : Map.wf E m) (Hs : FinSet.wf E s) (Ht : FinSet.wf E t).

Example suite_key : eqb E k j = true -> j = k.
Proof.
  case_key; intros; congruence.
Qed.

Example suite_map : k <> j -> Map.get E k (Map.set E j v m) = Map.get E k m.
Proof.
  intro Hneq. simpl_map.
Qed.

Example suite_set : FinSet.mem E k (FinSet.union s FinSet.empty) = FinSet.mem E k s.
Proof.
  simpl_set. apply Bool.orb_false_r.
Qed.

Example suite_solver :
  FinSet.mem E k (FinSet.inter s t) = true -> FinSet.mem E k (FinSet.union s t) = true.
Proof.
  set_solver.
Qed.
End Suite.

Example suite_option (o : option nat) :
  (match o with Some x => Some (S x) | None => None end) = Some 2 ->
  o = Some 1.
Proof.
  intro H. inv_option. reflexivity.
Qed.

Example suite_roundtrip {A B} (CA : codec A) (CB : codec B)
    (HA : codec_laws CA) (HB : codec_laws CB) :
  forall x, sum_of_code CA CB (Cost.value (sum_to_code_c CA CB x)) = Some x.
Proof.
  solve_roundtrip.
Qed.
