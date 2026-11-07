(** * Canonical maps over encoded keys

    Sorted binding lists provide a reference implementation of the map interface.
    For example, codes two, one and three enumerate in that order.
    Builds on: BaseEncoding, BaseEq and CostMonad. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq.
Import List.ListNotations Cost.Notations.

Create Rewrite HintDb galois_map.

Module Map.

(** Comparison follows trie traversal, with zero branches before the root before one branches. *)
Fixpoint code_compare_c (p q : positive) : Cost.t comparison :=
  Cost.step ;;
  match p, q with
  | xO p, xO q => code_compare_c p q
  | xI p, xI q => code_compare_c p q
  | xH, xH => Cost.ret Eq
  | xO _, _ => Cost.ret Lt
  | _, xI _ => Cost.ret Lt
  | _, _ => Cost.ret Gt
  end.

Definition code_compare p q := Cost.value (code_compare_c p q).

(** Comparison exposes the recursive digit order. *)
Theorem code_compare_equation p q :
  code_compare p q =
  match p, q with
  | xO p, xO q => code_compare p q
  | xI p, xI q => code_compare p q
  | xH, xH => Eq
  | xO _, _ => Lt
  | _, xI _ => Lt
  | _, _ => Gt
  end.
Proof.
  destruct p, q; reflexivity.
Qed.

(** Codes compare equal exactly when they are equal. *)
Theorem code_compare_eq p q : code_compare p q = Eq <-> p = q.
Proof.
  revert q. induction p; intros q; destruct q; rewrite code_compare_equation;
    try rewrite IHp; split; intros H; try discriminate; congruence.
Qed.

(** Reversing the arguments reverses the comparison. *)
Theorem code_compare_antisym p q :
  code_compare p q = CompOpp (code_compare q p).
Proof.
  revert q. induction p; intros q; destruct q;
    cbn [code_compare code_compare_c]; autorewrite with galois_cost;
    try reflexivity; apply IHp.
Qed.

(** Strict code order is transitive. *)
Theorem code_compare_trans p q r :
  code_compare p q = Lt -> code_compare q r = Lt -> code_compare p r = Lt.
Proof.
  revert q r. induction p; intros q r; destruct q, r;
    cbn [code_compare code_compare_c]; autorewrite with galois_cost;
    intros Hpq Hqr; try discriminate;
    try reflexivity; eapply IHp; eassumption.
Qed.

Local Lemma compare_refl p : code_compare p p = Eq.
Proof.
  apply code_compare_eq. reflexivity.
Qed.

Local Lemma compare_flip p q :
  code_compare p q = Gt <-> code_compare q p = Lt.
Proof.
  rewrite (code_compare_antisym p q).
  destruct (code_compare q p); cbn; split; congruence.
Qed.

(** A map stores code, key and value separately from its invariant. *)
Definition t (K V : Type) := list (positive * (K * V)).

(** Well-formed maps have consistent stored codes and strictly ordered bindings. *)
Definition wf {K V} (E : encoding K) (m : t K V) : Prop :=
  Forall (fun e => fst e = encode E (fst (snd e))) m /\
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) m.

Definition empty {K V} : t K V := [].
Definition empty_c {K V} : Cost.t (t K V) := Cost.ret empty.

(** Code lookup visits list cells and charges every digit comparison. *)
Fixpoint get_code_c {K V} (p : positive) (m : t K V) : Cost.t (option V) :=
  match m with
  | [] => Cost.ret None
  | (q, (_, v)) :: rest =>
    Cost.step ;;
    let* same := positive_eqb_c p q in
    if same then Cost.ret (Some v) else get_code_c p rest
  end.

Definition get_code {K V} p (m : t K V) := Cost.value (get_code_c p m).

(** Key lookup calls the encoding once before code lookup. *)
Definition get_c {K V} (E : encoding K) k (m : t K V) :=
  Cost.step ;;
  let* p := encode_c E k in get_code_c p m.

Definition get {K V} (E : encoding K) k (m : t K V) := Cost.value (get_c E k m).

(** Code lookup stops at the first matching cell. *)
Local Lemma get_code_equation {K V} p (m : t K V) :
  get_code p m =
  match m with
  | [] => None
  | (q, (_, v)) :: rest => if Pos.eqb p q then Some v else get_code p rest
  end.
Proof.
  destruct m as [|[q [k v]] rest]; unfold get_code; cbn [get_code_c];
    autorewrite with galois_cost; try reflexivity.
  rewrite positive_eqb_equation. destruct (Pos.eqb p q); reflexivity.
Qed.

(** Key lookup observes precisely the encoded position. *)
Theorem get_equation {K V} (E : encoding K) k (m : t K V) :
  get E k m = get_code (encode E k) m.
Proof.
  reflexivity.
Qed.

(** Sorted insertion replaces an existing code or inserts at its ordered position. *)
Fixpoint set_code_c {K V} (p : positive) k (v : V) (m : t K V) : Cost.t (t K V) :=
  match m with
  | [] => Cost.ret [(p, (k, v))]
  | (q, kv) :: rest =>
    Cost.step ;;
    let* order := code_compare_c p q in
    match order with
    | Eq => Cost.ret ((p, (k, v)) :: rest)
    | Lt => Cost.ret ((p, (k, v)) :: m)
    | Gt => Cost.map (cons (q, kv)) (set_code_c p k v rest)
    end
  end.

Definition set_code {K V} p k (v : V) (m : t K V) :=
  Cost.value (set_code_c p k v m).

Definition set_c {K V} (E : encoding K) k (v : V) (m : t K V) :=
  Cost.step ;;
  let* p := encode_c E k in set_code_c p k v m.

Definition set {K V} (E : encoding K) k (v : V) (m : t K V) :=
  Cost.value (set_c E k v m).

(** Setting inserts the encoded binding in code order. *)
Theorem set_equation {K V} (E : encoding K) k (v : V) m :
  set E k v m = set_code (encode E k) k v m.
Proof.
  reflexivity.
Qed.

(** Code insertion exposes its three order cases. *)
Local Lemma set_code_equation {K V} p (k : K) (v : V) m :
  set_code p k v m =
  match m with
  | [] => [(p, (k, v))]
  | (q, kv) :: rest =>
    match code_compare p q with
    | Eq => (p, (k, v)) :: rest
    | Lt => (p, (k, v)) :: m
    | Gt => (q, kv) :: set_code p k v rest
    end
  end.
Proof.
  destruct m as [|[q kv] rest]; [reflexivity|].
  unfold set_code at 1. cbn [set_code_c]. autorewrite with galois_cost.
  fold (code_compare p q).
  destruct (code_compare p q); reflexivity.
Qed.

(** Removal scans all cells, deleting the matching code. *)
Fixpoint remove_code_c {K V} p (m : t K V) : Cost.t (t K V) :=
  match m with
  | [] => Cost.ret []
  | (q, kv) :: rest =>
    Cost.step ;;
    let* same := positive_eqb_c p q in
    let* tail := remove_code_c p rest in
    Cost.ret (if same then tail else (q, kv) :: tail)
  end.

Definition remove_code {K V} p (m : t K V) := Cost.value (remove_code_c p m).
Definition remove_c {K V} (E : encoding K) k (m : t K V) :=
  Cost.step ;;
  let* p := encode_c E k in remove_code_c p m.
Definition remove {K V} (E : encoding K) k (m : t K V) :=
  Cost.value (remove_c E k m).

(** Code removal filters precisely the matching positions. *)
Local Lemma remove_code_equation {K V} p (m : t K V) :
  remove_code p m = filter (fun e => negb (Pos.eqb p (fst e))) m.
Proof.
  induction m as [|[q [k v]] rest IH]; [reflexivity|].
  unfold remove_code in *. cbn [remove_code_c filter fst].
  autorewrite with galois_cost. rewrite positive_eqb_equation, IH.
  destruct (Pos.eqb p q); reflexivity.
Qed.

(** Removal uses the encoded code. *)
Theorem remove_equation {K V} (E : encoding K) k (m : t K V) :
  remove E k m = remove_code (encode E k) m.
Proof.
  reflexivity.
Qed.

Definition update_c {K V} (E : encoding K) k (f_c : option V -> Cost.t (option V))
    (m : t K V) :=
  let* old := get_c E k m in
  Cost.step ;;
  let* new := f_c old in
  match new with
  | None => remove_c E k m
  | Some v => set_c E k v m
  end.

Definition update {K V} (E : encoding K) k (f : option V -> option V) (m : t K V) :=
  Cost.value (update_c E k (Cost.lift (fun _ => 1%N) f) m).

(** Update applies its callback to the old optional value. *)
Theorem update_equation {K V} (E : encoding K) k f (m : t K V) :
  update E k f m =
  match f (get E k m) with
  | None => remove E k m
  | Some v => set E k v m
  end.
Proof.
  unfold update, update_c. autorewrite with galois_cost.
  fold (get E k m). destruct (f (get E k m)); reflexivity.
Qed.

Definition mem_c {K V} (E : encoding K) k (m : t K V) :=
  Cost.map (fun o => match o with Some _ => true | None => false end) (get_c E k m).
Definition mem {K V} (E : encoding K) k (m : t K V) := Cost.value (mem_c E k m).
Definition find_or_c {K V} (E : encoding K) (d : V) k (m : t K V) :=
  Cost.map (fun o => match o with Some v => v | None => d end) (get_c E k m).
Definition find_or {K V} (E : encoding K) (d : V) k (m : t K V) :=
  Cost.value (find_or_c E d k m).

(** Empty maps have no value. *)
Theorem get_empty {K V} (E : encoding K) k : get E k (@empty K V) = None.
Proof.
  reflexivity.
Qed.

Local Lemma get_code_absent {K V} p (m : t K V) :
  Forall (fun e => fst e <> p) m -> get_code p m = None.
Proof.
  induction m as [|[q [k v]] rest IH]; intro H; rewrite get_code_equation;
    [reflexivity|].
  inversion H as [|? ? Hq Hr]; subst. cbn in Hq.
  assert (Hpq : Pos.eqb p q = false) by (apply Pos.eqb_neq; congruence).
  rewrite Hpq. now apply IH.
Qed.

Local Lemma sorted_absent {K V} p q (m : t K V) :
  code_compare p q = Lt ->
  Forall (fun e => code_compare q (fst e) = Lt) m ->
  get_code p m = None.
Proof.
  intros Hpq Hall. apply get_code_absent.
  rewrite Forall_forall in Hall |- *. intros [r kv] Hin Heq. cbn in Heq. subst r.
  specialize (Hall _ Hin). cbn in Hall.
  pose proof (code_compare_trans _ _ _ Hpq Hall) as Hpp.
  rewrite compare_refl in Hpp. discriminate.
Qed.

Local Lemma get_set_code {K V} p q (k : K) (v : V) m :
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) m ->
  get_code p (set_code q k v m) =
    if Pos.eqb p q then Some v else get_code p m.
Proof.
  induction m as [|[r [a w]] rest IH]; intro Hsort; rewrite set_code_equation.
  - rewrite !get_code_equation. destruct (Pos.eqb p q); reflexivity.
  - inversion Hsort as [|? ? Hrest Hafter]; subst.
    cbn [fst] in Hafter. destruct (code_compare q r) eqn:Hqr.
    + apply code_compare_eq in Hqr. subst r.
      rewrite get_code_equation, (get_code_equation p ((q, (a, w)) :: rest)).
      destruct (Pos.eqb p q); reflexivity.
    + rewrite get_code_equation. destruct (Pos.eqb p q); reflexivity.
    + rewrite get_code_equation, IH by exact Hrest.
      rewrite (get_code_equation p ((r, (a, w)) :: rest)).
      destruct (Pos.eqb p q) eqn:Hpq, (Pos.eqb p r) eqn:Hpr; try reflexivity.
      apply Pos.eqb_eq in Hpq. apply Pos.eqb_eq in Hpr. subst q r.
      rewrite compare_refl in Hqr. discriminate.
Qed.

(** Setting a key makes its new value readable. *)
Theorem get_set_same {K V} (E : encoding K) k (v : V) m :
  wf E m -> get E k (set E k v m) = Some v.
Proof.
  intros [_ Hsort]. rewrite get_equation, set_equation, get_set_code by exact Hsort.
  now rewrite Pos.eqb_refl.
Qed.

(** Setting a distinct key leaves the queried value unchanged. *)
Theorem get_set_other {K V} (E : encoding K) (HE : encoding_laws E) k a (v : V) m :
  wf E m -> k <> a -> get E k (set E a v m) = get E k m.
Proof.
  intros [_ Hsort] Hne. rewrite !get_equation, set_equation, get_set_code by exact Hsort.
  assert (Hneq : Pos.eqb (encode E k) (encode E a) = false).
  { apply Pos.eqb_neq. intro H. apply Hne. exact (encode_injective HE _ _ H). }
  now rewrite Hneq.
Qed.

(** Lookup after setting is a reflected key test. *)
Theorem get_set {K V} (E : encoding K) k a (v : V) m :
  wf E m -> get E k (set E a v m) = if eqb E k a then Some v else get E k m.
Proof.
  intros [_ Hsort]. rewrite eqb_equation, !get_equation, set_equation.
  now apply get_set_code.
Qed.

Local Lemma get_remove_code {K V} p q (m : t K V) :
  get_code p (remove_code q m) =
    if Pos.eqb p q then None else get_code p m.
Proof.
  rewrite remove_code_equation. induction m as [|[r [a v]] rest IH].
  - rewrite get_code_equation. destruct (Pos.eqb p q); reflexivity.
  - cbn [filter fst]. destruct (Pos.eqb q r) eqn:Hqr; cbn [negb].
    + apply Pos.eqb_eq in Hqr. subst r.
      rewrite IH, (get_code_equation p ((q, (a, v)) :: rest)).
      destruct (Pos.eqb p q); reflexivity.
    + rewrite get_code_equation, IH, (get_code_equation p ((r, (a, v)) :: rest)).
      destruct (Pos.eqb p q) eqn:Hpq, (Pos.eqb p r) eqn:Hpr; try reflexivity.
      apply Pos.eqb_eq in Hpq. apply Pos.eqb_eq in Hpr. subst q r.
      rewrite Pos.eqb_refl in Hqr. discriminate.
Qed.

(** Removal clears its own key. *)
Theorem get_remove_same {K V} (E : encoding K) k (m : t K V) :
  get E k (remove E k m) = None.
Proof.
  rewrite get_equation, remove_equation, get_remove_code, Pos.eqb_refl. reflexivity.
Qed.

(** Removing another key leaves the queried value unchanged. *)
Theorem get_remove_other {K V} (E : encoding K) (HE : encoding_laws E) k a (m : t K V) :
  k <> a -> get E k (remove E a m) = get E k m.
Proof.
  intro Hne. rewrite !get_equation, remove_equation, get_remove_code.
  assert (Hneq : Pos.eqb (encode E k) (encode E a) = false).
  { apply Pos.eqb_neq. intro H. apply Hne. exact (encode_injective HE _ _ H). }
  now rewrite Hneq.
Qed.

(** Lookup after removal is a reflected key test. *)
Theorem get_remove {K V} (E : encoding K) k a (m : t K V) :
  get E k (remove E a m) = if eqb E k a then None else get E k m.
Proof.
  rewrite eqb_equation, !get_equation, remove_equation. apply get_remove_code.
Qed.

(** Empty maps satisfy both representation invariants. *)
Theorem wf_empty {K V} (E : encoding K) : wf E (@empty K V).
Proof.
  split; constructor.
Qed.

Local Lemma set_members {K V} p (k : K) (v : V) m e :
  In e (set_code p k v m) -> e = (p, (k, v)) \/ In e m.
Proof.
  induction m as [|[q kv] rest IH]; rewrite set_code_equation.
  - cbn. intuition congruence.
  - destruct (code_compare p q); cbn; intuition.
Qed.

Local Lemma set_sorted {K V} p (k : K) (v : V) m :
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) m ->
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt)
    (set_code p k v m).
Proof.
  induction m as [|[q kv] rest IH]; intro Hsort; rewrite set_code_equation.
  - constructor; constructor.
  - inversion Hsort as [|? ? Hrest Hafter]; subst.
    destruct (code_compare p q) eqn:Hpq.
    + apply code_compare_eq in Hpq. subst p. constructor; assumption.
    + constructor; [exact Hsort|]. constructor; [exact Hpq|].
      rewrite Forall_forall in Hafter |- *. intros e Hin.
      eapply code_compare_trans; [exact Hpq|exact (Hafter e Hin)].
    + constructor; [now apply IH|].
      rewrite Forall_forall in Hafter |- *. intros e Hin.
      apply set_members in Hin as [->|Hin]; [cbn; now apply compare_flip|].
      exact (Hafter e Hin).
Qed.

(** Setting maintains code consistency and strict ordering. *)
Theorem wf_set {K V} (E : encoding K) k (v : V) m :
  wf E m -> wf E (set E k v m).
Proof.
  intros [Hcodes Hsort]. rewrite set_equation. split; [|now apply set_sorted].
  rewrite Forall_forall in Hcodes |- *. intros e Hin.
  apply set_members in Hin as [->|Hin]; [reflexivity|exact (Hcodes e Hin)].
Qed.

Local Lemma sorted_filter {A} (R : A -> A -> Prop) f xs :
  StronglySorted R xs -> StronglySorted R (filter f xs).
Proof.
  induction xs as [|x xs IH]; intro Hsort; [constructor|].
  inversion Hsort as [|? ? Htail Hafter]; subst. cbn [filter].
  destruct (f x); [constructor|]; try (now apply IH).
  rewrite Forall_forall in Hafter |- *. intros y Hin.
  apply filter_In in Hin as [Hin _]. now apply Hafter.
Qed.

(** Removal keeps the invariants by taking a subsequence. *)
Theorem wf_remove {K V} (E : encoding K) k (m : t K V) :
  wf E m -> wf E (remove E k m).
Proof.
  intros [Hcodes Hsort]. rewrite remove_equation, remove_code_equation.
  split; [|now apply sorted_filter].
  rewrite Forall_forall in Hcodes |- *. intros e Hin.
  apply filter_In in Hin as [Hin _]. now apply Hcodes.
Qed.

(** Update maintains well-formedness for every callback result. *)
Theorem wf_update {K V} (E : encoding K) k f (m : t K V) :
  wf E m -> wf E (update E k f m).
Proof.
  intro H. rewrite update_equation. destruct (f (get E k m)).
  - now apply wf_set.
  - now apply wf_remove.
Qed.

(** Lookup after update exposes the callback only at its selected key. *)
Theorem get_update {K V} (E : encoding K) k a f (m : t K V) :
  wf E m ->
  get E k (update E a f m) = if eqb E k a then f (get E a m) else get E k m.
Proof.
  intro Hwf. rewrite update_equation. destruct (f (get E a m)) eqn:Hf.
  - rewrite get_set by exact Hwf. reflexivity.
  - rewrite get_remove. reflexivity.
Qed.

(** Trie implementations discharge these independent code-operation bounds. *)
Record cost_laws : Prop := Cost_laws {
  get_code_cost : forall K V p (m : t K V),
    (Cost.ticks (get_code_c p m) <= N.pos (Pos.size p))%N;
  set_code_cost : forall K V p k (v : V) (m : t K V),
    (Cost.ticks (set_code_c p k v m) <= N.pos (Pos.size p))%N;
  remove_code_cost : forall K V p (m : t K V),
    (Cost.ticks (remove_code_c p m) <= N.pos (Pos.size p))%N
}.

Fixpoint map_c {K V W} (f_c : V -> Cost.t W) (m : t K V) : Cost.t (t K W) :=
  match m with
  | [] => Cost.ret []
  | (p, (k, v)) :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* w := f_c v in
    let* tail := map_c f_c rest in
    Cost.ret ((p, (k, w)) :: tail)
  end.

Definition map {K V W} (f : V -> W) (m : t K V) :=
  Cost.value (map_c (Cost.lift (fun _ => 1%N) f) m).

(** Mapping retains positions and keys. *)
Local Lemma map_equation {K V W} (f : V -> W) (m : t K V) :
  map f m = List.map (fun e => (fst e, (fst (snd e), f (snd (snd e))))) m.
Proof.
  induction m as [|[p [k v]] rest IH]; unfold map in *; cbn [map_c List.map];
    autorewrite with galois_cost; now rewrite ?IH.
Qed.

Local Lemma get_code_map {K V W} (f : V -> W) p (m : t K V) :
  get_code p (map f m) = option_map f (get_code p m).
Proof.
  rewrite map_equation. induction m as [|[q [k v]] rest IH].
  - reflexivity.
  - cbn [List.map fst snd].
    rewrite get_code_equation, (get_code_equation p ((q, (k, v)) :: rest)).
    destruct (Pos.eqb p q); [reflexivity|exact IH].
Qed.

(** Mapping applies its function to every present value. *)
Theorem get_map {K V W} (E : encoding K) (f : V -> W) k (m : t K V) :
  get E k (map f m) = option_map f (get E k m).
Proof.
  rewrite !get_equation. apply get_code_map.
Qed.

Local Lemma sorted_map {A B} (R : A -> A -> Prop) (S : B -> B -> Prop) f xs :
  (forall x y, R x y -> S (f x) (f y)) ->
  StronglySorted R xs -> StronglySorted S (List.map f xs).
Proof.
  intros Hf Hsort. induction Hsort as [|x xs Hsort IH Hafter]; cbn; constructor.
  - exact IH.
  - rewrite Forall_forall in Hafter |- *. intros y Hin.
    apply in_map_iff in Hin as [a [<- Hin]]. now apply Hf, Hafter.
Qed.

(** Value mapping maintains both invariants. *)
Theorem wf_map {K V W} (E : encoding K) (f : V -> W) (m : t K V) :
  wf E m -> wf E (map f m).
Proof.
  intros [Hcodes Hsort]. rewrite map_equation. split.
  - rewrite Forall_forall in Hcodes |- *. intros e Hin.
    apply in_map_iff in Hin as [[p [k v]] [<- Hin]]. exact (Hcodes _ Hin).
  - eapply sorted_map; [|exact Hsort]. intros [p [k v]] [q [a w]] H. exact H.
Qed.

Fixpoint elements_c {K V} (m : t K V) : Cost.t (list (K * V)) :=
  match m with
  | [] => Cost.ret []
  | (_, kv) :: rest =>
    Cost.step ;; Cost.map (cons kv) (elements_c rest)
  end.

Definition elements {K V} (m : t K V) := Cost.value (elements_c m).

(** Enumeration drops codes without changing traversal order. *)
Local Lemma elements_equation {K V} (m : t K V) : elements m = List.map snd m.
Proof.
  induction m as [|[p kv] rest IH]; unfold elements in *; cbn [elements_c List.map];
    autorewrite with galois_cost; now rewrite ?IH.
Qed.

Fixpoint size_c {K V} (m : t K V) : Cost.t nat :=
  match m with
  | [] => Cost.ret 0
  | _ :: rest => Cost.step ;; Cost.map S (size_c rest)
  end.
Definition size {K V} (m : t K V) := Cost.value (size_c m).
Definition is_empty_c {K V} (m : t K V) :=
  Cost.ret (match m with [] => true | _ :: _ => false end).
Definition is_empty {K V} (m : t K V) := Cost.value (is_empty_c m).

Fixpoint fold_c {K V B} (f_c : B -> K -> V -> Cost.t B) (m : t K V) (b : B) :=
  match m with
  | [] => Cost.ret b
  | (_, (k, v)) :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* b' := f_c b k v in fold_c f_c rest b'
  end.
Definition fold {K V B} (f : B -> K -> V -> B) (m : t K V) b :=
  Cost.value (fold_c (fun b k v => Cost.lift (fun _ => 1%N) (f b k) v) m b).

(** Size equals the length of enumeration. *)
Theorem size_elements {K V} (m : t K V) : size m = length (elements m).
Proof.
  rewrite elements_equation, length_map.
  induction m as [|e rest IH]; unfold size in *; cbn [size_c length];
    autorewrite with galois_cost; now rewrite ?IH.
Qed.

(** Folding processes the public enumeration from left to right. *)
Theorem fold_elements {K V B} (f : B -> K -> V -> B) (m : t K V) b :
  fold f m b = fold_left (fun b kv => f b (fst kv) (snd kv)) (elements m) b.
Proof.
  rewrite elements_equation. revert b.
  induction m as [|[p [k v]] rest IH]; intro b; unfold fold in *;
    cbn [fold_c List.map fold_left fst snd]; autorewrite with galois_cost;
    [reflexivity|apply IH].
Qed.

Local Lemma get_code_in {K V} p (m : t K V) v :
  get_code p m = Some v -> exists k, In (p, (k, v)) m.
Proof.
  induction m as [|[q [k w]] rest IH]; rewrite get_code_equation; [discriminate|].
  destruct (Pos.eqb p q) eqn:Hpq.
  - apply Pos.eqb_eq in Hpq. intro H. injection H as ->. subst q. exists k. now left.
  - intro H. destruct (IH H) as [a Hin]. exists a. now right.
Qed.

Local Lemma in_get_code {K V} p k (v : V) (m : t K V) :
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) m ->
  In (p, (k, v)) m -> get_code p m = Some v.
Proof.
  induction m as [|[q [a w]] rest IH]; intros Hsort Hin; [contradiction|].
  inversion Hsort as [|? ? Htail Hafter]; subst.
  destruct Hin as [Heq|Hin].
  - injection Heq as -> -> ->. rewrite get_code_equation, Pos.eqb_refl. reflexivity.
  - rewrite get_code_equation. destruct (Pos.eqb p q) eqn:Hpq.
    + apply Pos.eqb_eq in Hpq. subst p.
      rewrite Forall_forall in Hafter. specialize (Hafter _ Hin).
      cbn in Hafter. rewrite compare_refl in Hafter. discriminate.
    + now apply IH.
Qed.

(** Public bindings are exactly the successful key lookups. *)
Theorem elements_spec {K V} (E : encoding K) (HE : encoding_laws E) k v (m : t K V) :
  wf E m -> (In (k, v) (elements m) <-> get E k m = Some v).
Proof.
  intros [Hcodes Hsort]. rewrite elements_equation, get_equation. split.
  - intro Hin. apply in_map_iff in Hin as [[p [a w]] [Heq Hin]].
    cbn in Heq. injection Heq as -> ->.
    rewrite Forall_forall in Hcodes. specialize (Hcodes _ Hin). cbn in Hcodes.
    subst p. eapply in_get_code; eassumption.
  - intro Hget. destruct (get_code_in _ _ _ Hget) as [a Hin].
    rewrite Forall_forall in Hcodes. specialize (Hcodes _ Hin). cbn in Hcodes.
    apply (encode_injective HE) in Hcodes. subst a.
    apply in_map_iff. exists (encode E k, (k, v)). split; [reflexivity|exact Hin].
Qed.

(** Enumeration has the canonical strict trie order on encoded keys. *)
Theorem elements_sorted {K V} (E : encoding K) (m : t K V) :
  wf E m ->
  StronglySorted (fun a b => code_compare (encode E (fst a)) (encode E (fst b)) = Lt)
    (elements m).
Proof.
  intros [Hcodes Hsort]. rewrite elements_equation.
  induction Hsort as [|[p [k v]] rest Hsort IH Hafter];
    cbn [List.map fst snd]; [constructor|].
  inversion Hcodes as [|? ? Hp Hrest]; subst.
  constructor; [now apply IH|].
  rewrite Forall_forall in Hrest, Hafter |- *. intros [a w] Hin.
  apply in_map_iff in Hin as [[q [b u]] [Heq Hin]].
  cbn in Heq. injection Heq as -> ->.
  specialize (Hafter _ Hin). specialize (Hrest _ Hin).
  cbn [fst snd] in Hp, Hafter, Hrest.
  cbn [fst snd].
  now rewrite <- Hp, <- Hrest.
Qed.

Local Lemma raw_ext {K V} (m n : t K V) :
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) m ->
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) n ->
  (forall e, In e m <-> In e n) -> m = n.
Proof.
  revert n. induction m as [|[p kv] rest IH]; intros [|[q av] tail] Hm Hn Heq.
  - reflexivity.
  - exfalso. specialize (Heq (q, av)). cbn in Heq. tauto.
  - exfalso. specialize (Heq (p, kv)). cbn in Heq. tauto.
  - inversion Hm as [|? ? Hrest Hp]; subst.
    inversion Hn as [|? ? Htail Hq]; subst.
    assert (Hpin : In (p, kv) ((q, av) :: tail)) by (apply Heq; now left).
    assert (Hqin : In (q, av) ((p, kv) :: rest)) by (apply Heq; now left).
    destruct Hpin as [Hhead|Hpin]; [injection Hhead as -> ->|].
    + f_equal. apply IH; try assumption. intro e. specialize (Heq e).
      cbn [In] in Heq. destruct (Pos.eq_dec p (fst e)) as [Hcode|Hcode].
      *
        split; intro Hin; exfalso;
          first [rewrite Forall_forall in Hp; specialize (Hp _ Hin)
                |rewrite Forall_forall in Hq; specialize (Hq _ Hin)];
          cbn [fst] in *; rewrite <- Hcode, compare_refl in *; discriminate.
      * assert (Hne : (p, kv) <> e).
        { intro H. subst e. apply Hcode. reflexivity. }
        tauto.
    + destruct Hqin as [Hhead|Hqin].
      * injection Hhead as -> ->. rewrite Forall_forall in Hq.
        specialize (Hq _ Hpin). cbn in Hq. rewrite compare_refl in Hq. discriminate.
      * rewrite Forall_forall in Hp, Hq.
        specialize (Hp _ Hqin). specialize (Hq _ Hpin). cbn in Hp, Hq.
        pose proof (code_compare_trans _ _ _ Hp Hq) as Hpp.
        rewrite compare_refl in Hpp. discriminate.
Qed.

(** Well-formed maps with identical lookups are equal as computational values. *)
Theorem ext {K V} (E : encoding K) (HE : encoding_laws E) (m n : t K V) :
  wf E m -> wf E n -> (forall k, get E k m = get E k n) -> m = n.
Proof.
  intros [Hm Hms] [Hn Hns] Hget. apply raw_ext; try assumption.
  intros [p [k v]]. split; intro Hin.
  - pose proof Hm as Hcodes. rewrite Forall_forall in Hcodes.
    specialize (Hcodes _ Hin). cbn in Hcodes. subst p.
    assert (Hlookup : get E k n = Some v).
    { rewrite <- Hget, get_equation. eapply in_get_code; eassumption. }
    rewrite get_equation in Hlookup.
    destruct (get_code_in _ _ _ Hlookup) as [a Ha].
    rewrite Forall_forall in Hn. specialize (Hn _ Ha). cbn in Hn.
    apply (encode_injective HE) in Hn. now subst a.
  - pose proof Hn as Hcodes. rewrite Forall_forall in Hcodes.
    specialize (Hcodes _ Hin). cbn in Hcodes. subst p.
    assert (Hlookup : get E k m = Some v).
    { rewrite Hget, get_equation. eapply in_get_code; eassumption. }
    rewrite get_equation in Hlookup.
    destruct (get_code_in _ _ _ Hlookup) as [a Ha].
    rewrite Forall_forall in Hm. specialize (Hm _ Ha). cbn in Hm.
    apply (encode_injective HE) in Hm. now subst a.
Qed.

Fixpoint filter_map_c {K V W} (f_c : V -> Cost.t (option W)) (m : t K V)
    : Cost.t (t K W) :=
  match m with
  | [] => Cost.ret []
  | (p, (k, v)) :: rest =>
    Cost.step ;;
    Cost.step ;;
    let* w := f_c v in
    let* tail := filter_map_c f_c rest in
    Cost.ret (match w with None => tail | Some x => (p, (k, x)) :: tail end)
  end.

Definition filter_map {K V W} (f : V -> option W) (m : t K V) :=
  Cost.value (filter_map_c (Cost.lift (fun _ => 1%N) f) m).

(** Filtering values keeps precisely the bindings whose callback succeeds. *)
Local Lemma filter_map_equation {K V W} (f : V -> option W) (m : t K V) :
  filter_map f m =
  match m with
  | [] => []
  | (p, (k, v)) :: rest =>
    match f v with
    | None => filter_map f rest
    | Some w => (p, (k, w)) :: filter_map f rest
    end
  end.
Proof.
  destruct m as [|[p [k v]] rest]; [reflexivity|].
  unfold filter_map. cbn [filter_map_c]. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma filter_map_members {K V W} (f : V -> option W) (m : t K V) p k w :
  In (p, (k, w)) (filter_map f m) -> exists v, In (p, (k, v)) m /\ f v = Some w.
Proof.
  induction m as [|[q [a v]] rest IH]; rewrite filter_map_equation; [contradiction|].
  destruct (f v) as [u|] eqn:Hf.
  - intros [Hhead|Hin].
    + injection Hhead as -> -> ->. exists v. split; [now left|exact Hf].
    + destruct (IH Hin) as [x [Hx Hfx]]. exists x. split; [now right|exact Hfx].
  - intro Hin. destruct (IH Hin) as [x [Hx Hfx]]. exists x. split; [now right|exact Hfx].
Qed.

(** Filtering mapped values maintains code consistency and order. *)
Theorem wf_filter_map {K V W} (E : encoding K) (f : V -> option W) (m : t K V) :
  wf E m -> wf E (filter_map f m).
Proof.
  intros [Hcodes Hsort]. split.
  - rewrite Forall_forall in Hcodes |- *. intros [p [k w]] Hin.
    apply filter_map_members in Hin as [v [Hin _]]. exact (Hcodes _ Hin).
  - clear Hcodes. induction Hsort as [|[p [k v]] rest Hsort IH Hafter];
      rewrite filter_map_equation; [constructor|].
    destruct (f v) as [w|]; [constructor|]; try exact IH.
    rewrite Forall_forall in Hafter |- *. intros [q [a x]] Hin.
    apply filter_map_members in Hin as [u [Hin _]]. exact (Hafter _ Hin).
Qed.

Local Lemma get_code_filter_map {K V W} (f : V -> option W) p (m : t K V) :
  StronglySorted (fun a b => code_compare (fst a) (fst b) = Lt) m ->
  get_code p (filter_map f m) =
    match get_code p m with None => None | Some v => f v end.
Proof.
  induction m as [|[q [k v]] rest IH]; intro Hsort;
    rewrite filter_map_equation; [reflexivity|].
  inversion Hsort as [|? ? Hrest Hafter]; subst.
  rewrite (get_code_equation p ((q, (k, v)) :: rest)).
  destruct (Pos.eqb p q) eqn:Hpq.
  - apply Pos.eqb_eq in Hpq. subst p. destruct (f v) as [w|] eqn:Hf.
    + rewrite get_code_equation, Pos.eqb_refl. reflexivity.
    + rewrite IH by exact Hrest.
      assert (Hnone : get_code q rest = None).
      { apply get_code_absent. rewrite Forall_forall in Hafter |- *.
        intros [r av] Hin Heq. cbn in Heq. subst r.
        specialize (Hafter _ Hin). cbn in Hafter.
        rewrite compare_refl in Hafter. discriminate. }
      now rewrite Hnone.
  - destruct (f v) as [w|]; [rewrite get_code_equation, Hpq|]; now apply IH.
Qed.

(** Combining recursively updates a sorted right-only result at every left code.
    This reference favors a small proof over the later trie's shared traversal. *)
Fixpoint combine_c {K V W U} (f_c : option V -> option W -> Cost.t (option U))
    (m : t K V) (n : t K W) : Cost.t (t K U) :=
  match m with
  | [] => filter_map_c (fun w => f_c None (Some w)) n
  | (p, (k, v)) :: rest =>
    Cost.step ;;
    let* acc := combine_c f_c rest n in
    let* rv := get_code_c p n in
    Cost.step ;;
    let* new := f_c (Some v) rv in
    match new with
    | None => remove_code_c p acc
    | Some u => set_code_c p k u acc
    end
  end.

Definition combine {K V W U} (f : option V -> option W -> option U)
    (m : t K V) (n : t K W) :=
  Cost.value (combine_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) m n).

(** The reference combination processes left bindings after the right-only base. *)
Local Lemma combine_equation {K V W U} (f : option V -> option W -> option U)
    (m : t K V) (n : t K W) :
  combine f m n =
  match m with
  | [] => filter_map (fun w => f None (Some w)) n
  | (p, (k, v)) :: rest =>
    match f (Some v) (get_code p n) with
    | None => remove_code p (combine f rest n)
    | Some u => set_code p k u (combine f rest n)
    end
  end.
Proof.
  destruct m as [|[p [k v]] rest]; [reflexivity|].
  unfold combine at 1. cbn [combine_c]. autorewrite with galois_cost.
  fold (get_code p n).
  destruct (f (Some v) (get_code p n)); reflexivity.
Qed.

(** Combination keeps the invariant for arbitrary callback results. *)
Theorem wf_combine {K V W U} (E : encoding K) (f : option V -> option W -> option U)
    (m : t K V) (n : t K W) :
  wf E m -> wf E n -> wf E (combine f m n).
Proof.
  induction m as [|[p [k v]] rest IH]; intros Hm Hn; rewrite combine_equation.
  - now apply wf_filter_map.
  - destruct Hm as [Hcodes Hsort].
    inversion Hcodes as [|? ? Hp Hrest]; subst.
    inversion Hsort as [|? ? Htail Hafter]; subst.
    specialize (IH (conj Hrest Htail) Hn). cbn in Hp. subst p.
    destruct (f (Some v) (get_code (encode E k) n)).
    + rewrite <- set_equation. now apply wf_set.
    + rewrite <- remove_equation. now apply wf_remove.
Qed.

Local Lemma get_combine_code {K V W U} (E : encoding K)
    (f : option V -> option W -> option U) p (m : t K V) (n : t K W) :
  wf E m -> wf E n -> f None None = None ->
  get_code p (combine f m n) = f (get_code p m) (get_code p n).
Proof.
  induction m as [|[q [k v]] rest IH]; intros Hm Hn Hnone; rewrite combine_equation.
  - rewrite get_code_filter_map by exact (proj2 Hn).
    change (match get_code p n with
      | Some v => f None (Some v)
      | None => None
      end = f None (get_code p n)).
    destruct (get_code p n); [reflexivity|symmetry; exact Hnone].
  - destruct Hm as [Hcodes Hsort].
    inversion Hcodes as [|? ? Hq Hrest]; subst.
    inversion Hsort as [|? ? Htail Hafter]; subst.
    pose proof (wf_combine E f rest n (conj Hrest Htail) Hn) as Hacc.
    specialize (IH (conj Hrest Htail) Hn Hnone).
    destruct (f (Some v) (get_code q n)) as [u|] eqn:Hf.
    + rewrite get_set_code by exact (proj2 Hacc).
      rewrite (get_code_equation p ((q, (k, v)) :: rest)).
      destruct (Pos.eqb p q) eqn:Hpq; [apply Pos.eqb_eq in Hpq; subst p|].
      * symmetry. exact Hf.
      * exact IH.
    + rewrite get_remove_code, (get_code_equation p ((q, (k, v)) :: rest)).
      destruct (Pos.eqb p q) eqn:Hpq; [apply Pos.eqb_eq in Hpq; subst p|].
      * symmetry. exact Hf.
      * exact IH.
Qed.

(** Combination computes each optional value independently and cannot invent absent keys. *)
Theorem get_combine {K V W U} (E : encoding K)
    (f : option V -> option W -> option U) k (m : t K V) (n : t K W) :
  wf E m -> wf E n -> f None None = None ->
  get E k (combine f m n) = f (get E k m) (get E k n).
Proof.
  rewrite !get_equation. apply get_combine_code.
Qed.

Local Lemma filter_map_value_ext {K V W} (f g : V -> Cost.t (option W)) (m : t K V) :
  (forall v, Cost.value (f v) = Cost.value (g v)) ->
  Cost.value (filter_map_c f m) = Cost.value (filter_map_c g m).
Proof.
  intro Hfg. induction m as [|[p [k v]] rest IH]; [reflexivity|].
  cbn [filter_map_c]. autorewrite with galois_cost. now rewrite Hfg, IH.
Qed.

Local Lemma combine_value_ext {K V W U}
    (f g : option V -> option W -> Cost.t (option U)) (m : t K V) (n : t K W) :
  (forall a b, Cost.value (f a b) = Cost.value (g a b)) ->
  Cost.value (combine_c f m n) = Cost.value (combine_c g m n).
Proof.
  intro Hfg. induction m as [|[p [k v]] rest IH].
  - cbn [combine_c]. apply filter_map_value_ext. intro w. apply Hfg.
  - cbn [combine_c]. autorewrite with galois_cost. rewrite IH, Hfg. reflexivity.
Qed.

Definition union_opt {V} (f : V -> V -> V) (a b : option V) :=
  match a, b with
  | Some v, Some w => Some (f v w)
  | Some v, None => Some v
  | None, Some w => Some w
  | None, None => None
  end.
Definition inter_opt {V W U} (f : V -> W -> U) (a : option V) (b : option W) :=
  match a, b with Some v, Some w => Some (f v w) | _, _ => None end.
Definition diff_opt {V W} (a : option V) (b : option W) :=
  match b with None => a | Some _ => None end.

Definition union_with_c {K V} (f_c : V -> V -> Cost.t V) (m n : t K V) :=
  combine_c (fun a b =>
    match a, b with
    | Some v, Some w => Cost.map (@Some V) (f_c v w)
    | Some v, None => Cost.ret (Some v)
    | None, Some w => Cost.ret (Some w)
    | None, None => Cost.ret None
    end) m n.
Definition union_with {K V} (f : V -> V -> V) (m n : t K V) :=
  Cost.value (union_with_c (fun v w => Cost.lift (fun _ => 1%N) (f v) w) m n).
Definition inter_with_c {K V W U} (f_c : V -> W -> Cost.t U) (m : t K V) (n : t K W) :=
  combine_c (fun a b =>
    match a, b with
    | Some v, Some w => Cost.map (@Some U) (f_c v w)
    | _, _ => Cost.ret None
    end) m n.
Definition inter_with {K V W U} (f : V -> W -> U) (m : t K V) (n : t K W) :=
  Cost.value (inter_with_c (fun v w => Cost.lift (fun _ => 1%N) (f v) w) m n).
Definition diff_c {K V W} (m : t K V) (n : t K W) :=
  combine_c (fun a b => Cost.ret (diff_opt a b)) m n.
Definition diff {K V W} (m : t K V) (n : t K W) := Cost.value (diff_c m n).

(** Union specializes optional combination to retaining one-sided values. *)
Theorem union_with_equation {K V} f (m n : t K V) :
  union_with f m n = combine (union_opt f) m n.
Proof.
  unfold union_with, union_with_c, combine. apply combine_value_ext.
  intros [v|] [w|]; reflexivity.
Qed.

(** Intersection specializes optional combination to shared values. *)
Theorem inter_with_equation {K V W U} (f : V -> W -> U) (m : t K V) (n : t K W) :
  inter_with f m n = combine (inter_opt f) m n.
Proof.
  unfold inter_with, inter_with_c, combine. apply combine_value_ext.
  intros [v|] [w|]; reflexivity.
Qed.

(** Union keeps one-sided bindings and combines shared bindings. *)
Theorem get_union_with {K V} (E : encoding K) f k (m n : t K V) :
  wf E m -> wf E n ->
  get E k (union_with f m n) = union_opt f (get E k m) (get E k n).
Proof.
  intros Hm Hn. rewrite union_with_equation. now apply get_combine.
Qed.

(** Intersection keeps only shared bindings. *)
Theorem get_inter_with {K V W U} (E : encoding K) (f : V -> W -> U) k m n :
  wf E m -> wf E n ->
  get E k (inter_with f m n) = inter_opt f (get E k m) (get E k n).
Proof.
  intros Hm Hn. rewrite inter_with_equation. now apply get_combine.
Qed.

Local Lemma diff_combine {K V W} (m : t K V) (n : t K W) :
  diff m n = combine diff_opt m n.
Proof.
  unfold diff, diff_c, combine. apply combine_value_ext. reflexivity.
Qed.

(** Difference drops every binding whose code is present on the right. *)
Theorem get_diff {K V W} (E : encoding K) k (m : t K V) (n : t K W) :
  wf E m -> wf E n -> get E k (diff m n) = diff_opt (get E k m) (get E k n).
Proof.
  intros Hm Hn. rewrite diff_combine. now apply get_combine.
Qed.

(** Union maintains map well-formedness. *)
Theorem wf_union_with {K V} (E : encoding K) f (m n : t K V) :
  wf E m -> wf E n -> wf E (union_with f m n).
Proof.
  rewrite union_with_equation. apply wf_combine.
Qed.

(** Intersection maintains map well-formedness. *)
Theorem wf_inter_with {K V W U} (E : encoding K) (f : V -> W -> U) m n :
  wf E m -> wf E n -> wf E (inter_with f m n).
Proof.
  rewrite inter_with_equation. apply wf_combine.
Qed.

(** Difference maintains map well-formedness. *)
Theorem wf_diff {K V W} (E : encoding K) (m : t K V) (n : t K W) :
  wf E m -> wf E n -> wf E (diff m n).
Proof.
  rewrite diff_combine. apply wf_combine.
Qed.

Local Fixpoint of_list_from_c {K V} (E : encoding K) (xs : list (K * V)) (m : t K V) :=
  match xs with
  | [] => Cost.ret m
  | (k, v) :: rest =>
    Cost.step ;;
    let* acc := set_c E k v m in of_list_from_c E rest acc
  end.
Definition of_list_c {K V} (E : encoding K) (xs : list (K * V)) :=
  of_list_from_c E xs (@empty K V).
Definition of_list {K V} (E : encoding K) (xs : list (K * V)) :=
  Cost.value (of_list_c E xs).

Local Lemma of_list_from_equation {K V} (E : encoding K) xs (m : t K V) :
  Cost.value (of_list_from_c E xs m) =
  fold_left (fun acc kv => set E (fst kv) (snd kv) acc) xs m.
Proof.
  revert m. induction xs as [|[k v] rest IH]; intro m; [reflexivity|].
  cbn [of_list_from_c fold_left fst snd]. autorewrite with galois_cost. apply IH.
Qed.

(** List construction is a left-to-right sequence of replacements. *)
Theorem of_list_equation {K V} (E : encoding K) (xs : list (K * V)) :
  of_list E xs = fold_left (fun acc kv => set E (fst kv) (snd kv) acc) xs empty.
Proof.
  apply of_list_from_equation.
Qed.

Local Lemma wf_of_list_from {K V} (E : encoding K) xs (m : t K V) :
  wf E m -> wf E (Cost.value (of_list_from_c E xs m)).
Proof.
  revert m. induction xs as [|[k v] rest IH]; intros m Hm; [exact Hm|].
  cbn [of_list_from_c]. autorewrite with galois_cost. apply IH, wf_set, Hm.
Qed.

(** List construction always produces a well-formed map. *)
Theorem wf_of_list {K V} (E : encoding K) (xs : list (K * V)) : wf E (of_list E xs).
Proof.
  apply wf_of_list_from, wf_empty.
Qed.

Local Lemma get_of_list_from {K V} (E : encoding K) k xs (m : t K V) :
  wf E m ->
  get E k (Cost.value (of_list_from_c E xs m)) =
  fold_left (fun old kv => if eqb E k (fst kv) then Some (snd kv) else old)
    xs (get E k m).
Proof.
  revert m. induction xs as [|[a v] rest IH]; intros m Hm; [reflexivity|].
  cbn [of_list_from_c fold_left fst snd]. autorewrite with galois_cost.
  fold (set E a v m).
  rewrite IH by now apply wf_set. rewrite get_set by exact Hm. reflexivity.
Qed.

(** Looking up a constructed map returns the last matching input value. *)
Theorem of_list_get {K V} (E : encoding K) k (xs : list (K * V)) :
  get E k (of_list E xs) =
  fold_left (fun old kv => if eqb E k (fst kv) then Some (snd kv) else old) xs None.
Proof.
  unfold of_list, of_list_c. rewrite get_of_list_from by apply wf_empty.
  rewrite get_empty. reflexivity.
Qed.

Fixpoint forall2_c {K V W} (r_c : V -> option W -> Cost.t bool)
    (m : t K V) (n : t K W) : Cost.t bool :=
  match m with
  | [] => Cost.ret true
  | (p, (_, v)) :: rest =>
    Cost.step ;;
    let* w := get_code_c p n in
    Cost.step ;;
    let* yes := r_c v w in
    if yes then forall2_c r_c rest n else Cost.ret false
  end.
Definition forall2 {K V W} (r : V -> option W -> bool) (m : t K V) (n : t K W) :=
  Cost.value (forall2_c (fun v w => Cost.lift (fun _ => 1%N) (r v) w) m n).
Definition beq_c {K V} (f_c : V -> V -> Cost.t bool) (m n : t K V) :=
  let test := fun a b => match b with None => Cost.ret false | Some b => f_c a b end in
  let* yes := forall2_c test m n in
  if yes then forall2_c test n m else Cost.ret false.
Definition beq {K V} (f : V -> V -> bool) (m n : t K V) :=
  Cost.value (beq_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) m n).

(** Comparison stops on the first rejected binding. *)
Local Lemma forall2_equation {K V W} r (m : t K V) (n : t K W) :
  forall2 r m n =
  match m with
  | [] => true
  | (p, (_, v)) :: rest => r v (get_code p n) && forall2 r rest n
  end.
Proof.
  destruct m as [|[p [k v]] rest]; [reflexivity|].
  unfold forall2. cbn [forall2_c]. autorewrite with galois_cost.
  fold (get_code p n). destruct (r v (get_code p n)); reflexivity.
Qed.

Local Lemma forall2_entries {K V W} r (m : t K V) (n : t K W) :
  forall2 r m n = true <->
  forall p k v, In (p, (k, v)) m -> r v (get_code p n) = true.
Proof.
  induction m as [|[p [k v]] rest IH]; rewrite forall2_equation.
  - cbn. intuition.
  - rewrite andb_true_iff, IH. split.
    + intros [Hhead Htail] q a w [Heq|Hin].
      * injection Heq as -> -> ->. exact Hhead.
      * exact (Htail q a w Hin).
    + intro H. split.
      * apply (H p k v). now left.
      * intros q a w Hin. apply (H q a w). now right.
Qed.

(** Comparison accepts exactly when every left binding satisfies the supplied relation. *)
Theorem forall2_spec {K V W} (E : encoding K) (HE : encoding_laws E)
    r (m : t K V) (n : t K W) :
  wf E m ->
  (forall2 r m n = true <->
    forall k v, get E k m = Some v -> r v (get E k n) = true).
Proof.
  intros [Hcodes Hsort]. rewrite forall2_entries. split.
  - intros H k v Hget. rewrite get_equation in Hget.
    destruct (get_code_in _ _ _ Hget) as [a Hin].
    rewrite get_equation. exact (H _ _ _ Hin).
  - intros H p k v Hin. rewrite Forall_forall in Hcodes.
    specialize (Hcodes _ Hin). cbn [fst snd] in Hcodes. subst p.
    rewrite <- get_equation. apply H.
    rewrite get_equation. eapply in_get_code; eassumption.
Qed.

(** Membership succeeds exactly when lookup succeeds. *)
Theorem mem_spec {K V} (E : encoding K) k (m : t K V) :
  mem E k m = true <-> exists v, get E k m = Some v.
Proof.
  unfold mem, mem_c. rewrite Cost.value_map. fold (get E k m).
  destruct (get E k m); split; intros H; try discriminate; eauto.
  destruct H as [v H]. discriminate.
Qed.

(** The empty map has false membership. *)
Theorem mem_empty {K V} (E : encoding K) k : mem E k (@empty K V) = false.
Proof.
  reflexivity.
Qed.

(** Emptiness is equivalent to absence at every key in a well-formed map. *)
Theorem is_empty_spec {K V} (E : encoding K) (m : t K V) :
  wf E m -> (is_empty m = true <-> forall k, get E k m = None).
Proof.
  intro Hwf. destruct m as [|[p [k v]] rest].
  - split; [intros _ a; apply get_empty|reflexivity].
  - split; [discriminate|]. intro H.
    assert (Hin : In (p, (k, v)) ((p, (k, v)) :: rest)) by now left.
    destruct Hwf as [Hcodes Hsort]. inversion Hcodes as [|? ? Hp Htail]; subst.
    cbn [fst snd] in Hp. specialize (H k). rewrite get_equation, <- Hp in H.
    rewrite (in_get_code _ _ _ _ Hsort Hin) in H. discriminate.
Qed.

(** Setting increases the size exactly when its code was absent. *)
Theorem size_set {K V} (E : encoding K) k (v : V) m :
  wf E m ->
  size (set E k v m) =
  match get E k m with None => S (size m) | Some _ => size m end.
Proof.
  intros [_ Hsort]. rewrite !size_elements, !elements_equation, !length_map.
  rewrite set_equation, get_equation.
  remember (encode E k) as p. clear Heqp.
  induction m as [|[q [a w]] rest IH]; rewrite set_code_equation, get_code_equation.
  - cbn [length]. reflexivity.
  - inversion Hsort as [|? ? Htail Hafter]; subst.
    destruct (code_compare p q) eqn:Hpq.
    + apply code_compare_eq in Hpq. subst p. rewrite Pos.eqb_refl. reflexivity.
    + assert (Hne : Pos.eqb p q = false).
      { apply Pos.eqb_neq. intro H. subst p. rewrite compare_refl in Hpq. discriminate. }
      rewrite Hne, (sorted_absent p q rest Hpq Hafter). reflexivity.
    + assert (Hne : Pos.eqb p q = false).
      { apply Pos.eqb_neq. intro H. subst p. rewrite compare_refl in Hpq. discriminate. }
      rewrite Hne. cbn [length]. rewrite IH by exact Htail.
      destruct (get_code p rest); reflexivity.
Qed.

Local Lemma filter_all {A} f (xs : list A) :
  (forall x, In x xs -> f x = true) -> filter f xs = xs.
Proof.
  induction xs as [|x xs IH]; intro H; [reflexivity|].
  cbn [filter]. rewrite H by now left. f_equal.
  apply IH. intros a Hin. apply H. now right.
Qed.

(** Removing a present binding reduces the size by one. *)
Theorem size_remove {K V} (E : encoding K) k (v : V) m :
  wf E m -> get E k m = Some v -> size m = S (size (remove E k m)).
Proof.
  intros [_ Hsort]. rewrite !size_elements, !elements_equation, !length_map.
  rewrite remove_equation, remove_code_equation, get_equation.
  remember (encode E k) as p. clear Heqp.
  induction m as [|[q [a w]] rest IH]; rewrite get_code_equation; [discriminate|].
  inversion Hsort as [|? ? Htail Hafter]; subst.
  cbn [filter fst]. destruct (Pos.eqb p q) eqn:Hpq; cbn [negb length].
  - intros _. apply Pos.eqb_eq in Hpq. subst p.
    assert (Hfilter : filter (fun e => negb (Pos.eqb q (fst e))) rest = rest).
    { apply filter_all. intros [r kv] Hin.
      rewrite Forall_forall in Hafter. specialize (Hafter _ Hin). cbn [fst] in Hafter.
      assert (Hne : Pos.eqb q r = false).
      { apply Pos.eqb_neq. intro H. subst r. rewrite compare_refl in Hafter. discriminate. }
      cbn [fst]. now rewrite Hne. }
    now rewrite Hfilter.
  - intro Hget. rewrite (IH Htail Hget). reflexivity.
Qed.

(** Costed update has the same result as its pure callback projection. *)
Theorem update_c_value {K V} (E : encoding K) k f_c (m : t K V) :
  Cost.value (update_c E k f_c m) = update E k (fun o => Cost.value (f_c o)) m.
Proof.
  rewrite update_equation. unfold update_c. autorewrite with galois_cost.
  fold (get E k m). destruct (Cost.value (f_c (get E k m))); reflexivity.
Qed.

(** Costed mapping has the same result as mapping callback values. *)
Theorem map_c_value {K V W} (f_c : V -> Cost.t W) (m : t K V) :
  Cost.value (map_c f_c m) = map (fun v => Cost.value (f_c v)) m.
Proof.
  rewrite map_equation. induction m as [|[p [k v]] rest IH]; [reflexivity|].
  cbn [map_c List.map fst snd]. autorewrite with galois_cost. now rewrite IH.
Qed.

(** Default lookup exposes its only two possible outcomes. *)
Theorem find_or_equation {K V} (E : encoding K) (d : V) k (m : t K V) :
  find_or E d k m = match get E k m with Some v => v | None => d end.
Proof.
  reflexivity.
Qed.

#[export] Hint Rewrite @get_empty @get_set @get_remove @get_update @get_map
  @get_combine @get_union_with @get_inter_with @get_diff @of_list_get
  @mem_empty using solve [auto using wf_empty, wf_set, wf_remove, wf_update,
    wf_map, wf_combine, wf_union_with, wf_inter_with, wf_diff, wf_of_list] : galois_map.

Arguments code_compare_c p q : simpl never.
Arguments code_compare p q : simpl never.
Arguments empty {K V} : simpl never.
Arguments empty_c {K V} : simpl never.
Arguments get_code_c {K V} p m : simpl never.
Arguments get_code {K V} p m : simpl never.
Arguments get_c {K V} E k m : simpl never.
Arguments get {K V} E k m : simpl never.
Arguments set_code_c {K V} p k v m : simpl never.
Arguments set_code {K V} p k v m : simpl never.
Arguments set_c {K V} E k v m : simpl never.
Arguments set {K V} E k v m : simpl never.
Arguments remove_code_c {K V} p m : simpl never.
Arguments remove_code {K V} p m : simpl never.
Arguments remove_c {K V} E k m : simpl never.
Arguments remove {K V} E k m : simpl never.
Arguments update_c {K V} E k f_c m : simpl never.
Arguments update {K V} E k f m : simpl never.
Arguments mem_c {K V} E k m : simpl never.
Arguments mem {K V} E k m : simpl never.
Arguments find_or_c {K V} E d k m : simpl never.
Arguments find_or {K V} E d k m : simpl never.
Arguments map_c {K V W} f_c m : simpl never.
Arguments map {K V W} f m : simpl never.
Arguments elements_c {K V} m : simpl never.
Arguments elements {K V} m : simpl never.
Arguments size_c {K V} m : simpl never.
Arguments size {K V} m : simpl never.
Arguments is_empty_c {K V} m : simpl never.
Arguments is_empty {K V} m : simpl never.
Arguments fold_c {K V B} f_c m b : simpl never.
Arguments fold {K V B} f m b : simpl never.
Arguments filter_map_c {K V W} f_c m : simpl never.
Arguments filter_map {K V W} f m : simpl never.
Arguments combine_c {K V W U} f_c m n : simpl never.
Arguments combine {K V W U} f m n : simpl never.
Arguments union_with_c {K V} f_c m n : simpl never.
Arguments union_with {K V} f m n : simpl never.
Arguments inter_with_c {K V W U} f_c m n : simpl never.
Arguments inter_with {K V W U} f m n : simpl never.
Arguments diff_c {K V W} m n : simpl never.
Arguments diff {K V W} m n : simpl never.
Arguments of_list_c {K V} E xs : simpl never.
Arguments of_list {K V} E xs : simpl never.
Arguments forall2_c {K V W} r_c m n : simpl never.
Arguments forall2 {K V W} r m n : simpl never.
Arguments beq_c {K V} f_c m n : simpl never.
Arguments beq {K V} f m n : simpl never.

End Map.
