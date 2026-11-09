(** * Hierarchy work measures

    Additive vertex weights count each source and every outgoing occurrence at that source.
    For example, a rejected target still contributes through its source's adjacency length.
    Builds on: GraphPrepared, GraphHierSpec and scoped Search support. *)

From Stdlib Require Import List PArith NArith Arith Lia Permutation.
From Galois.Base Require Import BaseEncoding.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchInvariant
  GraphSearchScopedCost GraphHierSpec.
Import List.ListNotations.
Local Open Scope N_scope.

Module HierWork.

Definition sum {A} (weight : A -> N) xs :=
  fold_right (fun x rest => weight x + rest) 0 xs.

(** Additive work distributes over list concatenation. *)
Theorem sum_app {A} (weight : A -> N) first last :
  sum weight (first ++ last) = sum weight first + sum weight last.
Proof.
  unfold sum. induction first as [|x rest IH]; cbn [fold_right app]; [lia|].
  rewrite IH. lia.
Qed.

(** Permuting source occurrences does not change their additive work. *)
Theorem sum_permutation {A} (weight : A -> N) first last :
  Permutation first last -> sum weight first = sum weight last.
Proof.
  unfold sum. intro Hperm. induction Hperm; cbn [fold_right]; lia.
Qed.

(** Flattening partitions preserves the sum of their per-block work. *)
Theorem sum_concat {A} (weight : A -> N) cs :
  sum weight (concat cs) = sum (sum weight) cs.
Proof.
  induction cs as [|c rest IH]; [reflexivity|].
  cbn [concat]. rewrite sum_app, IH. reflexivity.
Qed.

(** Uniform occurrence work is its constant times the number of occurrences. *)
Theorem sum_constant {A} k (xs : list A) :
  sum (fun _ => k) xs = N.of_nat (length xs) * k.
Proof.
  unfold sum. induction xs as [|x rest IH]; cbn [fold_right length];
    rewrite ?Nat2N.inj_succ; nia.
Qed.

(** Scaling each source weight scales its complete additive work. *)
Theorem sum_scale {A} k (weight : A -> N) xs :
  sum (fun x => k * weight x) xs = k * sum weight xs.
Proof.
  unfold sum. induction xs as [|x rest IH]; cbn [fold_right]; nia.
Qed.

(** Right scaling each source weight scales its complete additive work. *)
Theorem sum_scale_r {A} k (weight : A -> N) xs :
  sum (fun x => weight x * k) xs = sum weight xs * k.
Proof.
  unfold sum. induction xs as [|x rest IH]; cbn [fold_right]; nia.
Qed.

(** Adding pointwise budgets adds their total work. *)
Theorem sum_add {A} (first last : A -> N) xs :
  sum (fun x => first x + last x) xs = sum first xs + sum last xs.
Proof.
  unfold sum. induction xs as [|x rest IH]; cbn [fold_right]; lia.
Qed.

(** Pointwise source budgets bound their complete additive work. *)
Theorem sum_mono {A} (first last : A -> N) xs :
  (forall x, In x xs -> first x <= last x) -> sum first xs <= sum last xs.
Proof.
  unfold sum. induction xs as [|x rest IH]; intro Hbound; cbn [fold_right]; [lia|].
  pose proof (Hbound x (or_introl eq_refl)).
  specialize (IH ltac:(intros y Hy; apply Hbound; now right)). lia.
Qed.

(** Duplicate-free support inclusion bounds any nonnegative additive source work. *)
Theorem sum_incl {A} (weight : A -> N) first last :
  NoDup first -> incl first last -> sum weight first <= sum weight last.
Proof.
  intro Hnodup. revert last.
  induction Hnodup as [|x rest Hfresh Hnodup IH]; intros last Hincl.
  - unfold sum. cbn [fold_right]. lia.
  - destruct (in_split x last (Hincl x (or_introl eq_refl))) as [prefix [suffix Hlast]].
    assert (Hsub : incl rest (prefix ++ suffix)).
    { intros y Hy. specialize (Hincl y (or_intror Hy)).
      rewrite Hlast, in_app_iff in Hincl. rewrite in_app_iff. cbn [In] in Hincl.
      destruct Hincl as [Hin|[Heq|Hin]]; auto.
      subst y. contradiction. }
    specialize (IH _ Hsub).
    rewrite Hlast, sum_app.
    change (weight x + sum weight rest <= sum weight prefix + (weight x + sum weight suffix)).
    rewrite sum_app in IH. lia.
Qed.

(** Every occurrence contributes its own weight to total work. *)
Theorem member_le {A} (weight : A -> N) xs x :
  In x xs -> weight x <= sum weight xs.
Proof.
  intro Hin. apply in_split in Hin. destruct Hin as [first [last ->]].
  rewrite sum_app. cbn [sum fold_right]. lia.
Qed.

Definition outgoing {V E} (p : Prepared.t V E) vs :=
  sum (fun v => N.of_nat (length (Prepared.succ_edges p v))) vs.

(** Unit source-plus-adjacency weights sum to the source count plus all outgoing occurrences. *)
Theorem source_work {V E} (p : Prepared.t V E) vs :
  sum (fun v => 1 + N.of_nat (length (Prepared.succ_edges p v))) vs =
    N.of_nat (length vs) + outgoing p vs.
Proof.
  induction vs as [|v rest IH]; [reflexivity|].
  change (1 + N.of_nat (length (Prepared.succ_edges p v)) +
    sum (fun v => 1 + N.of_nat (length (Prepared.succ_edges p v))) rest =
    N.of_nat (S (length rest)) +
      (N.of_nat (length (Prepared.succ_edges p v)) + outgoing p rest)).
  rewrite Nat2N.inj_succ, IH. lia.
Qed.

(** Source-plus-adjacency work has a common scalar multiplier. *)
Theorem source_work_scale {V E} (p : Prepared.t V E) w vs :
  sum (fun v => (1 + N.of_nat (length (Prepared.succ_edges p v))) * w) vs =
    (N.of_nat (length vs) + outgoing p vs) * w.
Proof.
  rewrite sum_scale_r, source_work. reflexivity.
Qed.

(** Component source-plus-adjacency work adds to that of the flattened member occurrences. *)
Theorem source_partition {V E} (p : Prepared.t V E) cs :
  sum (fun c => N.of_nat (length c) + outgoing p c) cs =
    N.of_nat (length (concat cs)) + outgoing p (concat cs).
Proof.
  induction cs as [|c rest IH]; [reflexivity|].
  change (N.of_nat (length c) + outgoing p c +
    sum (fun c => N.of_nat (length c) + outgoing p c) rest =
    N.of_nat (length (c ++ concat rest)) + outgoing p (c ++ concat rest)).
  unfold outgoing at 3. rewrite sum_app.
  fold (outgoing p c) (outgoing p (concat rest)).
  rewrite length_app, Nat2N.inj_add, IH. lia.
Qed.

Definition fuel_width {V E} (p : Prepared.t V E) := N.pos (Pos.size (Prepared.fuel p)).

(** Per-source work retains global key width and actual global prepared-fuel width. *)
Definition weight {V E} (p : Prepared.t V E) w v :=
  (1 + N.of_nat (length (Prepared.succ_edges p v))) * (1 + w) + fuel_width p.

Definition mass {V E} (p : Prepared.t V E) w vs := sum (weight p w) vs.

(** Component mass is source-plus-outgoing work and one actual fuel-width term per source. *)
Theorem mass_equation {V E} (p : Prepared.t V E) w vs :
  mass p w vs =
    (N.of_nat (length vs) + outgoing p vs) * (1 + w) +
      N.of_nat (length vs) * fuel_width p.
Proof.
  induction vs as [|v rest IH].
  - reflexivity.
  - change (weight p w v + mass p w rest =
      (N.of_nat (S (length rest)) +
        (N.of_nat (length (Prepared.succ_edges p v)) + outgoing p rest)) * (1 + w) +
        N.of_nat (S (length rest)) * fuel_width p).
    rewrite IH, Nat2N.inj_succ. unfold weight. nia.
Qed.

Fixpoint depth_tree (t : Hier.tree) : nat :=
  match t with
  | Hier.Vertex _ => O
  | Hier.Component _ body => S (depth body)
  end
with depth (f : Hier.forest) : nat :=
  match f with
  | Hier.Nil => O
  | Hier.Cons t rest => Nat.max (depth_tree t) (depth rest)
  end.

(** A component's member work is strictly positive. *)
Theorem mass_nonempty {V E} (p : Prepared.t V E) w v rest :
  1 + w <= mass p w (v :: rest).
Proof.
  cbn [mass sum fold_right]. unfold weight. nia.
Qed.

(** A header-deleted body and its SCC partition have the same admitted valid source support. *)
Theorem scoped_support {V E} (p : Prepared.t V E) scope vs :
  Prepared.ready p -> NoDup vs ->
  (forall v, In v vs <-> Prepared.valid_id p v /\ Scope.admits scope v = true) ->
    Permutation vs (ScopedSearchCost.vertices p scope).
Proof.
  intros Hready Hnodup Hmembers.
  apply NoDup_Permutation; [exact Hnodup|now apply ScopedSearchCost.vertices_nodup|].
  intro v. rewrite ScopedSearchCost.vertices_spec. apply Hmembers.
Qed.

(** Scoped source and outgoing counts are exactly the additive work of their admitted support. *)
Theorem scoped_mass {V E} (p : Prepared.t V E) scope w :
  mass p w (ScopedSearchCost.vertices p scope) =
    (N.of_nat (ScopedSearchCost.node_count p scope) +
      N.of_nat (ScopedSearchCost.edge_count p scope)) * (1 + w) +
      N.of_nat (ScopedSearchCost.node_count p scope) * fuel_width p.
Proof.
  assert (Hout : outgoing p (ScopedSearchCost.vertices p scope) =
    N.of_nat (ScopedSearchCost.edge_count p scope)).
  { unfold outgoing, sum, ScopedSearchCost.edge_count.
    induction (ScopedSearchCost.vertices p scope) as [|v rest IH]; cbn [fold_right].
    - reflexivity.
    - rewrite Nat2N.inj_add, IH. reflexivity. }
  rewrite mass_equation, Hout. reflexivity.
Qed.

End HierWork.
