(** * Memo tables with a reference meaning

    Cached values are related to a reference function by a separate predicate.
    For example, looking up an absent key computes and records its reference result.
    Builds on: BaseMap, BaseEncoding and BaseEq. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module Memo.

(** A memo table is an ordinary canonical map. *)
Definition t K V := Map.t K V.

(** Empty cache construction has the map's empty cost. *)
Definition empty_c {K V} : Cost.t (t K V) := Map.empty_c.

(** Empty caches contain no reference results yet. *)
Definition empty {K V} : t K V := Cost.value empty_c.

(** Valid caches contain only reference results, independently of their representation invariant. *)
Definition valid {K V} (E : encoding K) (f : K -> V) (m : t K V) :=
  forall k v, Map.get E k m = Some v -> v = f k.

(** Cache lookup charges the reference callback only on a miss and retains its full charge. *)
Definition get_or_c {K V} (E : encoding K) (f_c : K -> Cost.t V) k (m : t K V) :=
  let* old := Map.get_c E k m in
  match old with
  | Some v => Cost.ret (v, m)
  | None =>
    Cost.step ;;
    let* v := f_c k in
    let* m' := Map.set_c E k v m in Cost.ret (v, m')
  end.
(** The pure wrapper treats the reference function as a one-tick primitive callback. *)
Definition get_or {K V} (E : encoding K) (f : K -> V) k (m : t K V) :=
  Cost.value (get_or_c E (Cost.lift (fun _ => 1%N) f) k m).

(** A miss stores its computed result and a hit leaves the table untouched. *)
Theorem get_or_equation {K V} (E : encoding K) (f : K -> V) k (m : t K V) :
  get_or E f k m =
  match Map.get E k m with
  | Some v => (v, m)
  | None => (f k, Map.set E k (f k) m)
  end.
Proof.
  unfold get_or, get_or_c. autorewrite with galois_cost.
  fold (Map.get E k m). destruct (Map.get E k m); reflexivity.
Qed.

(** An empty table is valid for every reference function. *)
Theorem valid_empty {K V} (E : encoding K) (f : K -> V) : valid E f (@empty K V).
Proof.
  intros k v H. rewrite Map.get_empty in H. discriminate.
Qed.

(** Cache lookup agrees with the reference and retains the cache's semantic validity. *)
Theorem get_or_agrees {K V} (E : encoding K) (HE : encoding_laws E) (f : K -> V) k m :
  Map.wf E m -> valid E f m ->
  fst (get_or E f k m) = f k /\ valid E f (snd (get_or E f k m)).
Proof.
  intros Hwf Hvalid. rewrite get_or_equation.
  destruct (Map.get E k m) as [v|] eqn:Hget; cbn [fst snd].
  - split; [now apply (Hvalid k v)|exact Hvalid].
  - split; [reflexivity|]. intros a v Hvalue.
    rewrite Map.get_set in Hvalue by exact Hwf.
    destruct (eqb_spec E HE a k) as [Heq|Hne].
    + subst a. now injection Hvalue.
    + exact (Hvalid a v Hvalue).
Qed.

(** Cache lookup retains the representation invariant. *)
Theorem wf_get_or {K V} (E : encoding K) (f : K -> V) k (m : t K V) :
  Map.wf E m -> Map.wf E (snd (get_or E f k m)).
Proof.
  intro H. rewrite get_or_equation. destruct (Map.get E k m); cbn [snd].
  - exact H.
  - now apply Map.wf_set.
Qed.

(** Memoized mapping charges each input cell and threads the costed callback through misses. *)
Fixpoint map_memo_c {K V} (E : encoding K) (f_c : K -> Cost.t V)
    (xs : list K) (m : t K V) : Cost.t (list V * t K V) :=
  match xs with
  | [] => Cost.ret ([], m)
  | k :: rest =>
    Cost.step ;;
    let* vm := get_or_c E f_c k m in
    let* tail := map_memo_c E f_c rest (snd vm) in
    Cost.ret (fst vm :: fst tail, snd tail)
  end.
(** Pure memoized mapping returns the results and the final table. *)
Definition map_memo {K V} (E : encoding K) (f : K -> V) xs (m : t K V) :=
  Cost.value (map_memo_c E (Cost.lift (fun _ => 1%N) f) xs m).

(** Memoized mapping threads one cache through the entire input. *)
Theorem map_memo_equation {K V} (E : encoding K) (f : K -> V) xs (m : t K V) :
  map_memo E f xs m =
  match xs with
  | [] => ([], m)
  | k :: rest =>
    let vm := get_or E f k m in
    let tail := map_memo E f rest (snd vm) in (fst vm :: fst tail, snd tail)
  end.
Proof.
  destruct xs; reflexivity.
Qed.

(** Memoized mapping returns the reference list and a valid well-formed cache. *)
Theorem map_memo_agrees {K V} (E : encoding K) (HE : encoding_laws E) (f : K -> V) xs m :
  Map.wf E m -> valid E f m ->
  fst (map_memo E f xs m) = List.map f xs /\
  valid E f (snd (map_memo E f xs m)) /\ Map.wf E (snd (map_memo E f xs m)).
Proof.
  revert m. induction xs as [|k rest IH]; intros m Hwf Hvalid;
    rewrite map_memo_equation; cbn [fst snd List.map].
  - auto.
  - pose proof (get_or_agrees E HE f k m Hwf Hvalid) as [Hv Hcache].
    pose proof (wf_get_or E f k m Hwf) as Hrepr.
    destruct (IH _ Hrepr Hcache) as [Hlist [Hvalid' Hwf']].
    rewrite Hv, Hlist. auto.
Qed.

Arguments empty_c {K V} : simpl never.
Arguments empty {K V} : simpl never.
Arguments get_or_c {K V} E f_c k m : simpl never.
Arguments get_or {K V} E f k m : simpl never.
Arguments map_memo_c {K V} E f_c xs m : simpl never.
Arguments map_memo {K V} E f xs m : simpl never.

End Memo.
