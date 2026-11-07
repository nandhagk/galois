(** * Stable group-by indexes

    Buckets accumulate by cons and reverse once after indexing.
    For example, grouping [a; b; a] retains the input order within a's bucket.
    Builds on: BaseMap, BaseEncoding and BaseEq. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module Index.

(** An index maps each key to a bucket of values. *)
Definition t K V := Map.t K (list V).

(** Index well-formedness is the bucket map invariant. *)
Definition wf {K V} (E : encoding K) (idx : t K V) := Map.wf E idx.

(** Bucket lookup charges its underlying map lookup. *)
Definition find_c {K V} (E : encoding K) k (idx : t K V) := Map.find_or_c E [] k idx.

(** An absent bucket is observed as an empty list. *)
Definition find {K V} (E : encoding K) k (idx : t K V) := Cost.value (find_c E k idx).

(** Reversal consumes one charged cell at each tail-recursive step. *)
Fixpoint reverse_acc_c {A} (xs acc : list A) : Cost.t (list A) :=
  match xs with
  | [] => Cost.ret acc
  | x :: rest => Cost.step ;; reverse_acc_c rest (x :: acc)
  end.

(** A bucket is reversed once after all constant-time cons updates. *)
Definition reverse_c {A} (xs : list A) := reverse_acc_c xs [].

Local Lemma reverse_acc_value {A} (xs acc : list A) :
  Cost.value (reverse_acc_c xs acc) = rev xs ++ acc.
Proof.
  revert acc. induction xs as [|x rest IH]; intro acc; [reflexivity|].
  cbn [reverse_acc_c rev]. autorewrite with galois_cost.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

(** The bucket reversal traverses each accumulated element once. *)
Theorem reverse_value {A} (xs : list A) : Cost.value (reverse_c xs) = rev xs.
Proof.
  unfold reverse_c. rewrite reverse_acc_value, app_nil_r. reflexivity.
Qed.

(** Collection charges its input traversal, key callback and bucket map updates. *)
Fixpoint collect_c {K V} (E : encoding K) (key_c : V -> Cost.t K)
    (xs : list V) (idx : t K V) : Cost.t (t K V) :=
  match xs with
  | [] => Cost.ret idx
  | x :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* k := key_c x in
    let* idx' := Map.update_c E k
      (fun old => Cost.ret (Some (x ::
        match old with
        | None => []
        | Some ys => ys
        end))) idx in
    collect_c E key_c rest idx'
  end.

(** Grouping composes reverse-order collection with one costed reversal per bucket. *)
Definition group_by_c {K V} (E : encoding K) (key_c : V -> Cost.t K) (xs : list V) :=
  let* idx := collect_c E key_c xs Map.empty in
  Map.map_c reverse_c idx.

(** The pure grouping wrapper assigns one primitive tick to each key callback. *)
Definition group_by {K V} (E : encoding K) (key : V -> K) (xs : list V) :=
  Cost.value (group_by_c E (Cost.lift (fun _ => 1%N) key) xs).

(** Bucket lookup returns the stored list or the empty list. *)
Theorem find_equation {K V} (E : encoding K) k (idx : t K V) :
  find E k idx =
  match Map.get E k idx with
  | Some xs => xs
  | None => []
  end.
Proof.
  apply Map.find_or_equation.
Qed.

Local Lemma collect_value {K V} (E : encoding K) (key : V -> K) xs (idx : t K V) :
  Cost.value (collect_c E (Cost.lift (fun _ => 1%N) key) xs idx) =
  match xs with
  | [] => idx
  | x :: rest =>
    Cost.value (collect_c E (Cost.lift (fun _ => 1%N) key) rest
      (Map.update E (key x)
        (fun old => Some (x ::
          match old with
          | None => []
          | Some ys => ys
          end)) idx))
  end.
Proof.
  destruct xs as [|x rest]; [reflexivity|].
  cbn [collect_c]. autorewrite with galois_cost. now rewrite Map.update_c_value.
Qed.

Local Lemma wf_collect {K V} (E : encoding K) (key : V -> K) xs (idx : t K V) :
  wf E idx -> wf E (Cost.value (collect_c E (Cost.lift (fun _ => 1%N) key) xs idx)).
Proof.
  revert idx. induction xs as [|x rest IH]; intros idx Hidx; rewrite collect_value.
  - exact Hidx.
  - apply IH, Map.wf_update, Hidx.
Qed.

Local Lemma find_collect {K V} (E : encoding K) (key : V -> K) k xs (idx : t K V) :
  wf E idx ->
  find E k (Cost.value (collect_c E (Cost.lift (fun _ => 1%N) key) xs idx)) =
    rev (filter (fun a => eqb E (key a) k) xs) ++ find E k idx.
Proof.
  revert idx. induction xs as [|x rest IH]; intros idx Hidx; rewrite collect_value.
  - reflexivity.
  - rewrite IH by now apply Map.wf_update.
    rewrite (find_equation E k (Map.update E (key x) _ idx)).
    rewrite Map.get_update by exact Hidx.
    rewrite (eqb_sym E k (key x)). cbn [filter].
    destruct (eqb E (key x) k) eqn:Hkey.
    + rewrite eqb_equation in Hkey. apply Pos.eqb_eq in Hkey.
      cbn [rev]. rewrite <- app_assoc, find_equation, !Map.get_equation, Hkey.
      reflexivity.
    + reflexivity.
Qed.

(** Grouping builds a well-formed index. *)
Theorem wf_group_by {K V} (E : encoding K) (key : V -> K) xs :
  wf E (group_by E key xs).
Proof.
  unfold group_by, group_by_c. rewrite Cost.value_bind, Map.map_c_value.
  apply Map.wf_map, wf_collect, Map.wf_empty.
Qed.

(** Grouping retains precisely the matching inputs in their original order. *)
Theorem find_group_by {K V} (E : encoding K) (key : V -> K) k xs :
  find E k (group_by E key xs) = filter (fun a => eqb E (key a) k) xs.
Proof.
  unfold group_by, group_by_c. rewrite Cost.value_bind, Map.map_c_value.
  rewrite find_equation, Map.get_map.
  assert (Hfind : find E k
    (Cost.value (collect_c E (Cost.lift (fun _ => 1%N) key) xs Map.empty)) =
    rev (filter (fun a => eqb E (key a) k) xs)).
  { rewrite find_collect by apply Map.wf_empty.
    rewrite find_equation, Map.get_empty, app_nil_r. reflexivity. }
  rewrite find_equation in Hfind.
  destruct (Map.get E k
    (Cost.value (collect_c E (Cost.lift (fun _ => 1%N) key) xs Map.empty))) as [ys|].
  - cbn [option_map]. rewrite reverse_value, Hfind, rev_involutive. reflexivity.
  - cbn [option_map]. apply (f_equal (@rev V)) in Hfind.
    rewrite rev_involutive in Hfind. exact Hfind.
Qed.

Local Lemma collect_value_ext {K V} (E : encoding K) (f g : V -> Cost.t K) xs idx :
  (forall x, Cost.value (f x) = Cost.value (g x)) ->
  Cost.value (collect_c E f xs idx) = Cost.value (collect_c E g xs idx).
Proof.
  intro Hfg. revert idx. induction xs as [|x rest IH]; intro idx; [reflexivity|].
  cbn [collect_c]. autorewrite with galois_cost. rewrite Hfg. apply IH.
Qed.

(** Grouping retains arbitrary key-callback costs without changing the stable buckets. *)
Theorem group_by_c_value {K V} (E : encoding K) (key_c : V -> Cost.t K) xs :
  Cost.value (group_by_c E key_c xs) = group_by E (fun a => Cost.value (key_c a)) xs.
Proof.
  unfold group_by, group_by_c. autorewrite with galois_cost.
  rewrite (collect_value_ext E key_c
    (Cost.lift (fun _ => 1%N) (fun a => Cost.value (key_c a))) xs Map.empty)
    by reflexivity.
  reflexivity.
Qed.

Arguments find_c {K V} E k idx : simpl never.
Arguments find {K V} E k idx : simpl never.
Arguments group_by_c {K V} E key_c xs : simpl never.
Arguments group_by {K V} E key xs : simpl never.
Arguments reverse_acc_c {A} xs acc : simpl never.
Arguments reverse_c {A} xs : simpl never.
Arguments collect_c {K V} E key_c xs idx : simpl never.

End Index.
