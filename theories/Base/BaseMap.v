(** * Canonical maps over encoded keys

    Maps store each key beside its value in a canonical costed trie.
    For example, codes two, one and three enumerate in that order.
    Builds on: BaseEncoding, BaseEq, BaseTrie and BaseTrieMerge. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseTrie BaseTrieMerge.
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

(** Code comparison inspects at most the number of digits in its left operand. *)
Theorem code_compare_cost p q :
  (Cost.ticks (code_compare_c p q) <= N.pos (Pos.size p))%N.
Proof.
  revert q. induction p as [p IH|p IH|]; intros q; destruct q;
    cbn [code_compare_c]; autorewrite with galois_cost.
  all: try (change (1 + Cost.ticks (code_compare_c p q) <=
    N.succ (N.pos (Pos.size p)))%N; pose proof (IH q) as Htail; lia).
  all: try (change (1 + 0 <= N.succ (N.pos (Pos.size p)))%N; lia).
  all: reflexivity.
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

(** A map stores each key and value at its encoded trie position. *)
Definition t (K V : Type) := Trie.t (K * V).

(** Well-formed maps store every key at its own encoded position. *)
Definition wf {K V} (E : encoding K) (m : t K V) : Prop :=
  forall p k v, Trie.get p m = Some (k, v) -> encode E k = p.

Definition empty {K V} : t K V := Trie.empty.
(** Empty construction returns the backend's constant empty trie without traversal. *)
Definition empty_c {K V} : Cost.t (t K V) := Cost.ret Trie.empty.

(** Code lookup discards the stored key and retains the complete path charge. *)
Definition get_code_c {K V} p (m : t K V) :=
  Cost.map (option_map snd) (Trie.get_c p m).
Definition get_code {K V} p (m : t K V) := Cost.value (get_code_c p m).

Local Lemma get_code_trie {K V} p (m : t K V) :
  get_code p m = option_map snd (Trie.get p m).
Proof.
  reflexivity.
Qed.

(** Key lookup pays encoding-call overhead, the encoding and the trie descent. *)
Definition get_c {K V} (E : encoding K) k (m : t K V) :=
  Cost.step ;; let* p := encode_c E k in get_code_c p m.
Definition get {K V} (E : encoding K) k (m : t K V) := Cost.value (get_c E k m).

(** Key lookup observes precisely the encoded position. *)
Theorem get_equation {K V} (E : encoding K) k (m : t K V) :
  get E k m = get_code (encode E k) m.
Proof.
  reflexivity.
Qed.

Definition set_code_c {K V} p k (v : V) (m : t K V) := Trie.set_c p (k, v) m.
Definition set_code {K V} p k (v : V) (m : t K V) :=
  Cost.value (set_code_c p k v m).
Definition set_c {K V} (E : encoding K) k (v : V) (m : t K V) :=
  Cost.step ;; let* p := encode_c E k in set_code_c p k v m.
Definition set {K V} (E : encoding K) k (v : V) (m : t K V) :=
  Cost.value (set_c E k v m).

(** Setting inserts the encoded binding at its canonical position. *)
Theorem set_equation {K V} (E : encoding K) k (v : V) m :
  set E k v m = set_code (encode E k) k v m.
Proof.
  reflexivity.
Qed.

Definition remove_code_c {K V} p (m : t K V) := Trie.remove_c p m.
Definition remove_code {K V} p (m : t K V) := Cost.value (remove_code_c p m).
Definition remove_c {K V} (E : encoding K) k (m : t K V) :=
  Cost.step ;; let* p := encode_c E k in remove_code_c p m.
Definition remove {K V} (E : encoding K) k (m : t K V) :=
  Cost.value (remove_c E k m).

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
  change (option_map snd (Trie.get (encode E k) (Trie.empty : t K V)) = None).
  now rewrite Trie.get_empty.
Qed.

(** Updating an encoded position has its exact query effect on arbitrary stored labels. *)
Theorem get_set_raw {K V} (E : encoding K) k a (v : V) m :
  get E k (set E a v m) = if eqb E k a then Some v else get E k m.
Proof.
  rewrite eqb_equation.
  change (option_map snd (Trie.get (encode E k)
    (Trie.set (encode E a) (a, v) m)) =
    if Pos.eqb (encode E k) (encode E a) then Some v
    else option_map snd (Trie.get (encode E k) m)).
  destruct (Pos.eqb_spec (encode E k) (encode E a)) as [Heq|Hne].
  - rewrite Heq, Trie.get_set_same. reflexivity.
  - rewrite Trie.get_set_other by congruence. reflexivity.
Qed.

(** Setting a key makes its new value readable. *)
Theorem get_set_same {K V} (E : encoding K) k (v : V) m :
  wf E m -> get E k (set E k v m) = Some v.
Proof.
  intro Hwf. change (option_map snd (Trie.get (encode E k)
    (Trie.set (encode E k) (k, v) m)) = Some v).
  now rewrite Trie.get_set_same.
Qed.

(** Setting a distinct key leaves the queried value unchanged. *)
Theorem get_set_other {K V} (E : encoding K) (HE : encoding_laws E) k a (v : V) m :
  wf E m -> k <> a -> get E k (set E a v m) = get E k m.
Proof.
  intros Hwf Hne. change (option_map snd (Trie.get (encode E k)
    (Trie.set (encode E a) (a, v) m)) = option_map snd (Trie.get (encode E k) m)).
  rewrite Trie.get_set_other; [reflexivity|].
  intro Hcode. apply Hne. symmetry. exact (encode_injective HE _ _ Hcode).
Qed.

(** Lookup after setting is a reflected encoded-key test. *)
Theorem get_set {K V} (E : encoding K) k a (v : V) m :
  wf E m -> get E k (set E a v m) = if eqb E k a then Some v else get E k m.
Proof.
  intro Hwf. rewrite eqb_equation.
  destruct (Pos.eqb (encode E k) (encode E a)) eqn:Hcode.
  - apply Pos.eqb_eq in Hcode.
    change (option_map snd (Trie.get (encode E k)
      (Trie.set (encode E a) (a, v) m)) = Some v).
    rewrite Hcode, Trie.get_set_same. reflexivity.
  - change (option_map snd (Trie.get (encode E k)
      (Trie.set (encode E a) (a, v) m)) = option_map snd (Trie.get (encode E k) m)).
    rewrite Trie.get_set_other; [reflexivity|].
    apply Pos.eqb_neq in Hcode. congruence.
Qed.

(** Removal clears its own key. *)
Theorem get_remove_same {K V} (E : encoding K) k (m : t K V) :
  get E k (remove E k m) = None.
Proof.
  change (option_map snd (Trie.get (encode E k) (Trie.remove (encode E k) m)) = None).
  now rewrite Trie.get_remove_same.
Qed.

(** Removing another key leaves the queried value unchanged. *)
Theorem get_remove_other {K V} (E : encoding K) (HE : encoding_laws E) k a (m : t K V) :
  k <> a -> get E k (remove E a m) = get E k m.
Proof.
  intro Hne. change (option_map snd (Trie.get (encode E k) (Trie.remove (encode E a) m)) =
    option_map snd (Trie.get (encode E k) m)).
  rewrite Trie.get_remove_other; [reflexivity|].
  intro Hcode. apply Hne. symmetry. exact (encode_injective HE _ _ Hcode).
Qed.

(** Lookup after removal is a reflected encoded-key test. *)
Theorem get_remove {K V} (E : encoding K) k a (m : t K V) :
  get E k (remove E a m) = if eqb E k a then None else get E k m.
Proof.
  rewrite eqb_equation.
  destruct (Pos.eqb (encode E k) (encode E a)) eqn:Hcode.
  - apply Pos.eqb_eq in Hcode.
    change (option_map snd (Trie.get (encode E k) (Trie.remove (encode E a) m)) = None).
    rewrite Hcode, Trie.get_remove_same. reflexivity.
  - change (option_map snd (Trie.get (encode E k) (Trie.remove (encode E a) m)) =
      option_map snd (Trie.get (encode E k) m)).
    rewrite Trie.get_remove_other; [reflexivity|].
    apply Pos.eqb_neq in Hcode. congruence.
Qed.

(** Empty maps satisfy the stored-position invariant. *)
Theorem wf_empty {K V} (E : encoding K) : wf E (@empty K V).
Proof.
  intros p k v Hget. unfold empty in Hget. rewrite Trie.get_empty in Hget. discriminate.
Qed.

(** Setting maintains code consistency. *)
Theorem wf_set {K V} (E : encoding K) k (v : V) m :
  wf E m -> wf E (set E k v m).
Proof.
  intros Hwf p a w. change (Trie.get p (Trie.set (encode E k) (k, v) m) =
    Some (a, w) -> encode E a = p).
  destruct (Pos.eq_dec (encode E k) p) as [Hcode|Hne].
  - rewrite <- Hcode, Trie.get_set_same.
    intro Hpair. injection Hpair as <- <-. reflexivity.
  - rewrite Trie.get_set_other by exact Hne. apply Hwf.
Qed.

(** Removal maintains code consistency. *)
Theorem wf_remove {K V} (E : encoding K) k (m : t K V) :
  wf E m -> wf E (remove E k m).
Proof.
  intros Hwf p a v. change (Trie.get p (Trie.remove (encode E k) m) =
    Some (a, v) -> encode E a = p).
  destruct (Pos.eq_dec (encode E k) p) as [Hcode|Hne].
  - rewrite <- Hcode, Trie.get_remove_same. discriminate.
  - rewrite Trie.get_remove_other by exact Hne. apply Hwf.
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

(** Code operations have the independent key-width bounds consumed by other containers. *)
Record cost_laws : Prop := Cost_laws {
  get_code_cost : forall K V p (m : t K V),
    (Cost.ticks (get_code_c p m) <= N.pos (Pos.size p))%N;
  set_code_cost : forall K V p k (v : V) (m : t K V),
    (Cost.ticks (set_code_c p k v m) <= N.pos (Pos.size p))%N;
  remove_code_cost : forall K V p (m : t K V),
    (Cost.ticks (remove_code_c p m) <= N.pos (Pos.size p))%N
}.

(** The canonical trie backend discharges every existing Map cost-law field. *)
Theorem cost_laws_hold : cost_laws.
Proof.
  constructor; intros.
  - unfold get_code_c. rewrite Cost.ticks_map, Trie.get_cost. reflexivity.
  - unfold set_code_c. rewrite Trie.set_cost. reflexivity.
  - unfold remove_code_c. rewrite Trie.remove_cost. reflexivity.
Qed.

(** Key lookup retains the encoder charge and one invocation-overhead tick. *)
Theorem get_cost {K V} (E : encoding K) k (m : t K V) :
  Cost.ticks (get_c E k m) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold get_c, get_code_c. autorewrite with galois_cost.
  rewrite Trie.get_cost. fold (encode E k). lia.
Qed.

(** Key insertion retains the encoder charge and one invocation-overhead tick. *)
Theorem set_cost {K V} (E : encoding K) k (v : V) (m : t K V) :
  Cost.ticks (set_c E k v m) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold set_c, set_code_c. autorewrite with galois_cost.
  rewrite Trie.set_cost. fold (encode E k). lia.
Qed.

(** Key removal retains the encoder charge and one invocation-overhead tick. *)
Theorem remove_cost {K V} (E : encoding K) k (m : t K V) :
  Cost.ticks (remove_c E k m) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold remove_c, remove_code_c. autorewrite with galois_cost.
  rewrite Trie.remove_cost. fold (encode E k). lia.
Qed.

Definition map_c {K V W} (f_c : V -> Cost.t W) (m : t K V) :=
  TrieMerge.map_c (fun kv => Cost.map (fun w => (fst kv, w)) (f_c (snd kv))) m.
Definition map {K V W} (f : V -> W) (m : t K V) :=
  Cost.value (map_c (Cost.lift (fun _ => 1%N) f) m).

(** Mapping applies its function to every present value. *)
Theorem get_map {K V W} (E : encoding K) (f : V -> W) k (m : t K V) :
  get E k (map f m) = option_map f (get E k m).
Proof.
  rewrite !get_equation, !get_code_trie.
  unfold map, map_c.
  rewrite TrieMerge.get_map. destruct (Trie.get (encode E k) m) as [[a v]|]; reflexivity.
Qed.

(** Value mapping retains every stored key. *)
Theorem wf_map {K V W} (E : encoding K) (f : V -> W) (m : t K V) :
  wf E m -> wf E (map f m).
Proof.
  intros Hwf p a w. unfold map, map_c. rewrite TrieMerge.get_map.
  destruct (Trie.get p m) as [[k v]|] eqn:Hget; cbn; intro Hpair; try discriminate.
  injection Hpair as <- <-. now apply (Hwf p k v).
Qed.

(** Enumeration avoids constructing trie codes because stored pairs already contain keys. *)
Definition elements_c {K V} (m : t K V) :=
  let* rev := TrieMerge.fold_values_c (fun acc kv => Cost.ret (kv :: acc)) m [] in rev_c rev.
Definition elements {K V} (m : t K V) := Cost.value (elements_c m).
Definition size_c {K V} (m : t K V) := TrieMerge.size_c m.
Definition size {K V} (m : t K V) := Cost.value (size_c m).
Definition is_empty_c {K V} (m : t K V) := Cost.ret (Trie.is_empty m).
Definition is_empty {K V} (m : t K V) := Cost.value (is_empty_c m).
Definition fold_c {K V B} (f_c : B -> K -> V -> Cost.t B) (m : t K V) (b : B) :=
  TrieMerge.fold_values_c (fun acc kv => f_c acc (fst kv) (snd kv)) m b.
Definition fold {K V B} (f : B -> K -> V -> B) (m : t K V) b :=
  Cost.value (fold_c (fun b k v => Cost.lift (fun _ => 1%N) (f b k) v) m b).

Local Lemma elements_equation {K V} (m : t K V) :
  elements m = List.map snd (TrieMerge.elements m).
Proof.
  unfold elements, elements_c. rewrite Cost.value_bind, value_rev_c.
  rewrite TrieMerge.fold_values_entries, TrieMerge.elements_entries.
  generalize (TrieMerge.entries m). intro xs.
  assert (H : forall acc, fold_left (fun acc pv => snd pv :: acc) xs acc =
    List.rev (List.map snd xs) ++ acc).
  { induction xs as [|x xs IH]; intro acc; cbn [fold_left List.map rev].
    - reflexivity.
    - rewrite IH, <- app_assoc. reflexivity. }
  rewrite H, app_nil_r, rev_involutive. reflexivity.
Qed.

(** Size equals the length of enumeration. *)
Theorem size_elements {K V} (m : t K V) : size m = length (elements m).
Proof.
  rewrite elements_equation, length_map. apply TrieMerge.size_elements.
Qed.

(** Folding processes the public enumeration from left to right. *)
Theorem fold_elements {K V B} (f : B -> K -> V -> B) (m : t K V) b :
  fold f m b = fold_left (fun b kv => f b (fst kv) (snd kv)) (elements m) b.
Proof.
  unfold fold, fold_c. rewrite TrieMerge.fold_values_entries, elements_equation.
  rewrite TrieMerge.elements_entries.
  generalize (TrieMerge.entries m). intro xs. revert b.
  induction xs as [|x xs IH]; intro b; cbn [List.map fold_left]; auto.
Qed.

Local Lemma get_pair {K V} (E : encoding K) (HE : encoding_laws E) (m : t K V) k v :
  wf E m -> get E k m = Some v -> Trie.get (encode E k) m = Some (k, v).
Proof.
  intros Hwf. rewrite get_equation, get_code_trie.
  destruct (Trie.get (encode E k) m) as [[a w]|] eqn:Hget; cbn; intro H; try discriminate.
  injection H as <-. assert (a = k).
  { apply (encode_injective HE). exact (Hwf _ _ _ Hget). }
  now subst a.
Qed.

(** Public bindings are exactly the successful key lookups. *)
Theorem elements_spec {K V} (E : encoding K) (HE : encoding_laws E) k v (m : t K V) :
  wf E m -> (In (k, v) (elements m) <-> get E k m = Some v).
Proof.
  intro Hwf. rewrite elements_equation. split.
  - intro Hin. apply in_map_iff in Hin as [[p [a w]] [Heq Hin]].
    cbn in Heq. injection Heq as Hkey Hvalue. subst a w.
    apply TrieMerge.elements_spec in Hin.
    change (option_map snd (Trie.get (encode E k) m) = Some v).
    rewrite (Hwf _ _ _ Hin), Hin. reflexivity.
  - intro Hget. apply in_map_iff. exists (encode E k, (k, v)).
    split; [reflexivity|]. apply TrieMerge.elements_spec. now apply (get_pair E HE).
Qed.

Local Lemma code_lt p q : TrieMerge.key_lt p q <-> code_compare p q = Lt.
Proof.
  revert q. induction p; intro q; destruct q; rewrite code_compare_equation;
    cbn [TrieMerge.key_lt]; try apply IHp; intuition discriminate.
Qed.

(** Enumeration has the canonical strict trie order on encoded keys. *)
Theorem elements_sorted {K V} (E : encoding K) (m : t K V) :
  wf E m ->
  StronglySorted (fun a b => code_compare (encode E (fst a)) (encode E (fst b)) = Lt)
    (elements m).
Proof.
  intro Hwf. rewrite elements_equation.
  pose proof (TrieMerge.elements_sorted m) as Hsort.
  assert (Hcodes : forall p k v, In (p, (k, v)) (TrieMerge.elements m) -> encode E k = p).
  { intros p k v Hin. apply (Hwf p k v). now apply TrieMerge.elements_spec. }
  remember (TrieMerge.elements m) as xs. clear Heqxs.
  induction Hsort as [|[p [k v]] xs Hsort IH Hafter]; cbn [List.map snd].
  - constructor.
  - constructor.
    + apply IH. intros q a w Hin. exact (Hcodes q a w (or_intror Hin)).
    + apply Forall_forall. intros [a w] Hin.
      apply in_map_iff in Hin as [[q [b u]] [Heq Hin]].
      cbn in Heq. injection Heq as Hkey Hvalue. subst b u.
      cbn [fst].
      rewrite (Hcodes p k v (or_introl eq_refl)), (Hcodes q a w (or_intror Hin)).
      apply code_lt. rewrite Forall_forall in Hafter. exact (Hafter _ Hin).
Qed.

(** Well-formed maps with identical lookups are equal as computational values. *)
Theorem ext {K V} (E : encoding K) (HE : encoding_laws E) (m n : t K V) :
  wf E m -> wf E n -> (forall k, get E k m = get E k n) -> m = n.
Proof.
  intros Hm Hn Heq. apply Trie.extensionality. intro p.
  destruct (Trie.get p m) as [[k v]|] eqn:Hleft;
    destruct (Trie.get p n) as [[a w]|] eqn:Hright; try reflexivity.
  - pose proof (Hm _ _ _ Hleft) as Hcode.
    pose proof (Hn _ _ _ Hright) as Hcode'.
    assert (k = a) by (apply (encode_injective HE); congruence).
    subst a. specialize (Heq k).
    change (option_map snd (Trie.get (encode E k) m) =
      option_map snd (Trie.get (encode E k) n)) in Heq.
    rewrite Hcode, Hleft, Hright in Heq. cbn in Heq. congruence.
  - specialize (Heq k).
    change (option_map snd (Trie.get (encode E k) m) =
      option_map snd (Trie.get (encode E k) n)) in Heq.
    rewrite (Hm _ _ _ Hleft), Hleft, Hright in Heq. discriminate.
  - specialize (Heq a).
    change (option_map snd (Trie.get (encode E a) m) =
      option_map snd (Trie.get (encode E a) n)) in Heq.
    rewrite (Hn _ _ _ Hright), Hleft, Hright in Heq. discriminate.
Qed.

Definition filter_map_c {K V W} (f_c : V -> Cost.t (option W)) (m : t K V) :=
  TrieMerge.filter_map_c
    (fun kv => Cost.map (option_map (fun w => (fst kv, w))) (f_c (snd kv))) m.
Definition filter_map {K V W} (f : V -> option W) (m : t K V) :=
  Cost.value (filter_map_c (Cost.lift (fun _ => 1%N) f) m).

(** Cost composition observes the native filter without introducing a second traversal. *)
Theorem filter_map_backend {K V W} (f_c : V -> Cost.t (option W)) (m : t K V) :
  filter_map_c f_c m = TrieMerge.filter_map_c
    (fun kv => Cost.map (option_map (fun w => (fst kv, w))) (f_c (snd kv))) m.
Proof.
  reflexivity.
Qed.

(** Filtering mapped values maintains code consistency. *)
Theorem wf_filter_map {K V W} (E : encoding K) (f : V -> option W) (m : t K V) :
  wf E m -> wf E (filter_map f m).
Proof.
  intros Hwf p a w. unfold filter_map, filter_map_c. rewrite TrieMerge.get_filter.
  destruct (Trie.get p m) as [[k v]|] eqn:Hget; [|discriminate].
  cbn. destruct (f v) as [u|]; cbn; intro Hpair; try discriminate.
  injection Hpair as <- <-. now apply (Hwf p k v).
Qed.

(** Costed filtering reads the callback result at each present source binding. *)
Theorem get_filter_map_c {K V W} (E : encoding K) (f_c : V -> Cost.t (option W)) k
    (m : t K V) :
  get E k (Cost.value (filter_map_c f_c m)) =
    match get E k m with Some v => Cost.value (f_c v) | None => None end.
Proof.
  unfold filter_map_c.
  change (option_map snd
    (Trie.get (encode E k) (Cost.value (TrieMerge.filter_map_c
      (fun kv => Cost.map (option_map (fun w => (fst kv, w))) (f_c (snd kv))) m))) =
    match option_map snd (Trie.get (encode E k) m) with
    | Some v => Cost.value (f_c v)
    | None => None
    end).
  rewrite TrieMerge.get_filter.
  destruct (Trie.get (encode E k) m) as [[stored v]|]; [|reflexivity].
  autorewrite with galois_cost; cbn [option_map fst snd].
  destruct (Cost.value (f_c v)); reflexivity.
Qed.

(** Pure mapped filtering has exactly the optional callback's lookup behaviour. *)
Theorem get_filter_map {K V W} (E : encoding K) (f : V -> option W) k (m : t K V) :
  get E k (filter_map f m) =
    match get E k m with Some v => f v | None => None end.
Proof.
  apply get_filter_map_c.
Qed.

(** Costed filtering depends only on callback values and preserves the native traversal. *)
Theorem filter_map_c_value {K V W} (f_c : V -> Cost.t (option W)) (m : t K V) :
  Cost.value (filter_map_c f_c m) = filter_map (fun v => Cost.value (f_c v)) m.
Proof.
  unfold filter_map, filter_map_c; apply Trie.extensionality; intro p.
  rewrite !TrieMerge.get_filter.
  destruct (Trie.get p m) as [[k v]|]; autorewrite with galois_cost; reflexivity.
Qed.

(** Arbitrary costed filter callbacks preserve the source map's representation invariant. *)
Theorem wf_filter_map_c {K V W} (E : encoding K) (f_c : V -> Cost.t (option W)) (m : t K V) :
  wf E m -> wf E (Cost.value (filter_map_c f_c m)).
Proof.
  rewrite filter_map_c_value; apply wf_filter_map.
Qed.

(** Pair combination selects the first available stored key and cannot invent a key. *)
Definition combine_pair_c {K V W U} (f : option V -> option W -> Cost.t (option U))
    (a : option (K * V)) (b : option (K * W)) :=
  match a, b with
  | Some (k, v), _ =>
    Cost.map (option_map (fun u => (k, u))) (f (Some v) (option_map snd b))
  | None, Some (k, w) =>
    Cost.map (option_map (fun u => (k, u))) (f None (Some w))
  | None, None => Cost.ret None
  end.

Definition combine_c {K V W U} (f_c : option V -> option W -> Cost.t (option U))
    (m : t K V) (n : t K W) := TrieMerge.combine_c (combine_pair_c f_c) m n.
Definition combine {K V W U} (f : option V -> option W -> option U)
    (m : t K V) (n : t K W) :=
  Cost.value (combine_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) m n).

Local Lemma drop_pair {K U} (k : K) (o : option U) :
  option_map snd (option_map (fun u => (k, u)) o) = o.
Proof.
  destruct o; reflexivity.
Qed.

(** Combination computes each optional value independently and cannot invent absent keys. *)
Theorem get_combine {K V W U} (E : encoding K)
    (f : option V -> option W -> option U) k (m : t K V) (n : t K W) :
  wf E m -> wf E n -> f None None = None ->
  get E k (combine f m n) = f (get E k m) (get E k n).
Proof.
  intros Hm Hn Hnone. rewrite !get_equation, !get_code_trie.
  unfold combine, combine_c.
  rewrite TrieMerge.get_combine by reflexivity.
  destruct (Trie.get (encode E k) m) as [[a v]|];
    destruct (Trie.get (encode E k) n) as [[b w]|]; cbn [combine_pair_c];
    autorewrite with galois_cost; cbn [option_map snd]; rewrite ?drop_pair; congruence.
Qed.

(** Combination selects only a key that already has the selected position. *)
Theorem wf_combine {K V W U} (E : encoding K) (f : option V -> option W -> option U)
    (m : t K V) (n : t K W) :
  wf E m -> wf E n -> wf E (combine f m n).
Proof.
  intros Hm Hn p a u. unfold combine, combine_c.
  rewrite TrieMerge.get_combine by reflexivity.
  destruct (Trie.get p m) as [[k v]|] eqn:Hl;
    destruct (Trie.get p n) as [[b w]|] eqn:Hr; cbn [combine_pair_c];
    autorewrite with galois_cost; try discriminate;
    destruct (f _ _); cbn; intro Hpair; try discriminate;
    injection Hpair as <- <-; eauto.
Qed.

(** Costed combination depends only on the values returned by its callback. *)
Theorem combine_c_value {K V W U}
    (f_c : option V -> option W -> Cost.t (option U)) (m : t K V) (n : t K W) :
  Cost.value (combine_c f_c m n) = combine (fun a b => Cost.value (f_c a b)) m n.
Proof.
  apply Trie.extensionality. intro p. unfold combine, combine_c.
  rewrite !TrieMerge.get_combine by reflexivity.
  destruct (Trie.get p m) as [[a v]|], (Trie.get p n) as [[b w]|]; reflexivity.
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
  TrieMerge.union_with_c
    (fun a b => Cost.map (fun v => (fst a, v)) (f_c (snd a) (snd b))) m n.
Definition union_with {K V} (f : V -> V -> V) (m n : t K V) :=
  Cost.value (union_with_c (fun v w => Cost.lift (fun _ => 1%N) (f v) w) m n).
Definition inter_with_c {K V W U} (f_c : V -> W -> Cost.t U) (m : t K V) (n : t K W) :=
  TrieMerge.inter_with_c
    (fun a b => Cost.map (fun v => (fst a, v)) (f_c (snd a) (snd b))) m n.
Definition inter_with {K V W U} (f : V -> W -> U) (m : t K V) (n : t K W) :=
  Cost.value (inter_with_c (fun v w => Cost.lift (fun _ => 1%N) (f v) w) m n).
Definition diff_c {K V W} (m : t K V) (n : t K W) := TrieMerge.diff_c m n.
Definition diff {K V W} (m : t K V) (n : t K W) := Cost.value (diff_c m n).

(** Difference exposes its backend computation for independently owned cost proofs. *)
Theorem diff_backend {K V W} (m : t K V) (n : t K W) :
  diff_c m n = TrieMerge.diff_c m n.
Proof.
  reflexivity.
Qed.

(** Union exposes the stored-key-preserving collision callback and its complete charge. *)
Theorem union_with_backend {K V} (f : V -> V -> Cost.t V) (m n : t K V) :
  union_with_c f m n =
    TrieMerge.union_with_c
      (fun a b => Cost.map (fun v => (fst a, v)) (f (snd a) (snd b))) m n.
Proof.
  reflexivity.
Qed.

(** Union specializes optional combination to retaining one-sided values. *)
Theorem union_with_equation {K V} f (m n : t K V) :
  union_with f m n = combine (union_opt f) m n.
Proof.
  apply Trie.extensionality. intro p. unfold union_with, union_with_c, combine, combine_c.
  rewrite TrieMerge.union_get, TrieMerge.get_combine by reflexivity.
  destruct (Trie.get p m) as [[a v]|], (Trie.get p n) as [[b w]|]; reflexivity.
Qed.

(** Intersection specializes optional combination to shared values. *)
Theorem inter_with_equation {K V W U} (f : V -> W -> U) (m : t K V) (n : t K W) :
  inter_with f m n = combine (inter_opt f) m n.
Proof.
  apply Trie.extensionality. intro p. unfold inter_with, inter_with_c, combine, combine_c.
  rewrite TrieMerge.inter_get, TrieMerge.get_combine by reflexivity.
  destruct (Trie.get p m) as [[a v]|], (Trie.get p n) as [[b w]|]; reflexivity.
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
  apply Trie.extensionality. intro p. unfold diff, diff_c, combine, combine_c.
  fold (TrieMerge.diff m n).
  rewrite TrieMerge.diff_get, TrieMerge.get_combine by reflexivity.
  destruct (Trie.get p m) as [[a v]|], (Trie.get p n) as [[b w]|]; reflexivity.
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
  let* initial := @empty_c K V in of_list_from_c E xs initial.
Definition of_list {K V} (E : encoding K) (xs : list (K * V)) :=
  Cost.value (of_list_c E xs).

Local Lemma of_list_from_equation {K V} (E : encoding K) xs (m : t K V) :
  Cost.value (of_list_from_c E xs m) =
  fold_left (fun acc kv => set E (fst kv) (snd kv) acc) xs m.
Proof.
  revert m. induction xs as [|[k v] rest IH]; intro m; [reflexivity|].
  cbn [of_list_from_c fold_left fst snd]. autorewrite with galois_cost. apply IH.
Qed.

Local Lemma of_list_from_cost {K V} (E : encoding K) xs (m : t K V) :
  Cost.ticks (of_list_from_c E xs m) =
    Cost.ticks (fold_left_c
      (fun acc kv => set_c E (fst kv) (snd kv) acc) xs m).
Proof.
  revert m. induction xs as [|[k v] rest IH]; intro m.
  - cbn [of_list_from_c]. rewrite Cost.ticks_ret, ticks_fold_left_c_nil. reflexivity.
  - cbn [of_list_from_c]. autorewrite with galois_cost.
    cbn [fst snd]. rewrite IH. lia.
Qed.

(** List construction retains initialization and each accumulator-threaded insertion charge. *)
Theorem of_list_cost_equation {K V} (E : encoding K) (xs : list (K * V)) :
  Cost.ticks (of_list_c E xs) =
    (Cost.ticks (@empty_c K V) +
      Cost.ticks (fold_left_c
        (fun acc kv => set_c E (fst kv) (snd kv) acc) xs empty))%N.
Proof.
  unfold of_list_c. rewrite Cost.ticks_bind, of_list_from_cost. reflexivity.
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
  unfold of_list, of_list_c. rewrite Cost.value_bind.
  change (get E k (Cost.value (of_list_from_c E xs empty)) =
    fold_left (fun old kv => if eqb E k (fst kv) then Some (snd kv) else old) xs None).
  rewrite get_of_list_from by apply wf_empty.
  rewrite get_empty. reflexivity.
Qed.

Definition forall2_c {K V W} (r_c : V -> option W -> Cost.t bool)
    (m : t K V) (n : t K W) :=
  TrieMerge.forall2_c (fun a b => r_c (snd a) (option_map snd b)) m n.
Definition forall2 {K V W} (r : V -> option W -> bool) (m : t K V) (n : t K W) :=
  Cost.value (forall2_c (fun v w => Cost.lift (fun _ => 1%N) (r v) w) m n).
Definition beq_c {K V} (f_c : V -> V -> Cost.t bool) (m n : t K V) :=
  let test := fun a b => match b with None => Cost.ret false | Some b => f_c a b end in
  let* yes := forall2_c test m n in
  if yes then forall2_c test n m else Cost.ret false.
Definition beq {K V} (f : V -> V -> bool) (m n : t K V) :=
  Cost.value (beq_c (fun a b => Cost.lift (fun _ => 1%N) (f a) b) m n).

(** Costed comparison depends only on the values returned by its callback. *)
Theorem forall2_c_value {K V W} (r_c : V -> option W -> Cost.t bool)
    (m : t K V) (n : t K W) :
  Cost.value (forall2_c r_c m n) = forall2 (fun v w => Cost.value (r_c v w)) m n.
Proof.
  apply eq_true_iff_eq. unfold forall2, forall2_c.
  rewrite !TrieMerge.forall2_spec. reflexivity.
Qed.

(** Comparison accepts exactly when every left binding satisfies the supplied relation. *)
Theorem forall2_spec {K V W} (E : encoding K) (HE : encoding_laws E)
    r (m : t K V) (n : t K W) :
  wf E m ->
  (forall2 r m n = true <->
    forall k v, get E k m = Some v -> r v (get E k n) = true).
Proof.
  intro Hwf. unfold forall2, forall2_c. rewrite TrieMerge.forall2_spec. split.
  - intros H k v Hget. pose proof (get_pair E HE m k v Hwf Hget) as Hpair.
    exact (H _ _ Hpair).
  - intros H p [k v] Hget. cbn [snd].
    pose proof (Hwf _ _ _ Hget) as Hcode. rewrite <- Hcode.
    apply H. change (option_map snd (Trie.get (encode E k) m) = Some v).
    now rewrite Hcode, Hget.
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
  unfold mem, mem_c. rewrite Cost.value_map. change (match get E k (@empty K V) with
    Some _ => true | None => false end = false). now rewrite get_empty.
Qed.

(** Emptiness is equivalent to absence at every key in a well-formed map. *)
Theorem is_empty_spec {K V} (E : encoding K) (m : t K V) :
  wf E m -> (is_empty m = true <-> forall k, get E k m = None).
Proof.
  intro Hwf. unfold is_empty, is_empty_c.
  rewrite Cost.value_ret, Trie.is_empty_spec. split.
  - intros -> k. apply get_empty.
  - intro Hnone. apply Trie.extensionality. intro p.
    rewrite Trie.get_empty. destruct (Trie.get p m) as [[k v]|] eqn:Hget; [|reflexivity].
    specialize (Hnone k).
    change (option_map snd (Trie.get (encode E k) m) = None) in Hnone.
    rewrite (Hwf _ _ _ Hget), Hget in Hnone. discriminate.
Qed.

(** Setting increases the size exactly when its code was absent. *)
Theorem size_set {K V} (E : encoding K) k (v : V) m :
  wf E m ->
  size (set E k v m) =
  match get E k m with None => S (size m) | Some _ => size m end.
Proof.
  intro Hwf. change (TrieMerge.size (Trie.set (encode E k) (k, v) m) =
    match option_map snd (Trie.get (encode E k) m) with
    | None => S (TrieMerge.size m) | Some _ => TrieMerge.size m end).
  rewrite TrieMerge.size_set. destruct (Trie.get (encode E k) m); reflexivity.
Qed.

(** Removing a present binding reduces the size by one. *)
Theorem size_remove {K V} (E : encoding K) k (v : V) m :
  wf E m -> get E k m = Some v -> size m = S (size (remove E k m)).
Proof.
  intros Hwf Hget.
  change (option_map snd (Trie.get (encode E k) m) = Some v) in Hget.
  destruct (Trie.get (encode E k) m) as [[a w]|] eqn:Hpair; [|discriminate].
  cbn in Hget. injection Hget as Hvalue. subst w.
  exact (TrieMerge.size_remove (encode E k) (a, v) m Hpair).
Qed.

(** The loose backend-neutral size bound includes an allowance for empty maps. *)
Definition size_cost_k : N := 2.

(** The backend-neutral size-bound constant is positive. *)
Theorem size_cost_k_positive : (0 < size_cost_k)%N.
Proof.
  reflexivity.
Qed.

(** Lookup satisfies the public loose size-and-width bound, including empty maps. *)
Theorem get_size_cost {K V} (E : encoding K) k (m : t K V) :
  (Cost.ticks (get_c E k m) <= Cost.ticks (encode_c E k) +
    size_cost_k * (1 + N.of_nat (size m)) * (1 + key_bits E k))%N.
Proof.
  rewrite get_cost. fold (key_bits E k). unfold size_cost_k. nia.
Qed.

(** Insertion satisfies the public loose size-and-width bound, including empty maps. *)
Theorem set_size_cost {K V} (E : encoding K) k (v : V) (m : t K V) :
  (Cost.ticks (set_c E k v m) <= Cost.ticks (encode_c E k) +
    size_cost_k * (1 + N.of_nat (size m)) * (1 + key_bits E k))%N.
Proof.
  rewrite set_cost. fold (key_bits E k). unfold size_cost_k. nia.
Qed.

(** Default lookup has exactly the charge of its underlying lookup. *)
Theorem find_or_cost {K V} (E : encoding K) (d : V) k (m : t K V) :
  Cost.ticks (find_or_c E d k m) = Cost.ticks (get_c E k m).
Proof.
  apply Cost.ticks_map.
Qed.

(** Membership pays exactly the lookup's encoder and queried-code width charges. *)
Theorem mem_cost {K V} (E : encoding K) k (m : t K V) :
  Cost.ticks (mem_c E k m) =
    (1 + Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)))%N.
Proof.
  unfold mem_c. rewrite Cost.ticks_map. apply get_cost.
Qed.

(** Canonical enumeration never repeats a stored key in a well-formed map. *)
Theorem elements_nodup {K V} (E : encoding K) (m : t K V) :
  wf E m -> NoDup (List.map fst (elements m)).
Proof.
  intro Hwf. pose proof (elements_sorted E m Hwf) as Hsort.
  induction Hsort as [|[k v] xs Hsort IH Hafter]; cbn [List.map fst].
  - constructor.
  - constructor; [|exact IH]. intro Hin.
    apply in_map_iff in Hin as [[a w] [Heq Hin]]. cbn [fst] in Heq. subst a.
    rewrite Forall_forall in Hafter. specialize (Hafter (k, w) Hin).
    cbn [fst] in Hafter.
    rewrite (proj2 (code_compare_eq _ _) eq_refl) in Hafter. discriminate.
Qed.

(** Costed update retains lookup, callback invocation and the selected write's full charge. *)
Theorem update_cost {K V} (E : encoding K) k (f_c : option V -> Cost.t (option V))
    (m : t K V) :
  Cost.ticks (update_c E k f_c m) =
    (Cost.ticks (get_c E k m) + 1 + Cost.ticks (f_c (get E k m)) +
      match Cost.value (f_c (get E k m)) with
      | Some v => Cost.ticks (set_c E k v m)
      | None => Cost.ticks (remove_c E k m)
      end)%N.
Proof.
  unfold update_c. autorewrite with galois_cost. fold (get E k m).
  destruct (Cost.value (f_c (get E k m))); lia.
Qed.

(** Map mapping delegates its stored pairs to the backend's public costed mapping operation. *)
Theorem map_backend {K V W} (f_c : V -> Cost.t W) (m : t K V) :
  map_c f_c m =
    TrieMerge.map_c (fun kv => Cost.map (fun w => (fst kv, w)) (f_c (snd kv))) m.
Proof.
  reflexivity.
Qed.

(** Counting map bindings delegates to the backend's public code-free size operation. *)
Theorem size_backend {K V} (m : t K V) :
  size_c m = TrieMerge.size_c m.
Proof.
  reflexivity.
Qed.

(** Public map enumeration drops only the code component of backend enumeration. *)
Theorem elements_backend {K V} (m : t K V) :
  elements m = List.map snd (TrieMerge.elements m).
Proof.
  apply elements_equation.
Qed.

(** A successful backend binding in a well-formed map is stored at its original key's code. *)
Theorem stored_code {K V} (E : encoding K) (m : t K V) p k v :
  wf E m -> Trie.get p m = Some (k, v) -> encode E k = p.
Proof.
  intros Hwf Hget. exact (Hwf p k v Hget).
Qed.

(** A stored binding in a well-formed map is visible through its original key. *)
Theorem stored_get {K V} (E : encoding K) (m : t K V) p k v :
  wf E m -> Trie.get p m = Some (k, v) -> get E k m = Some v.
Proof.
  intros Hwf Hget. rewrite get_equation, get_code_trie, (stored_code E m p k v Hwf Hget).
  now rewrite Hget.
Qed.

(** A finite support list bounds the cardinality of a well-formed map. *)
Theorem size_support_bound {K V} (E : encoding K) (HE : encoding_laws E)
    (U : list K) (m : t K V) :
  wf E m -> (forall k v, get E k m = Some v -> In k U) ->
  (size m <= length U)%nat.
Proof.
  intros Hwf Hsupport. rewrite size_elements, <- (length_map fst).
  apply NoDup_incl_length; [now apply (elements_nodup E)|].
  intros k Hin. apply in_map_iff in Hin as [[a v] [Heq Hin]]. cbn in Heq. subst a.
  apply (Hsupport k v). now apply (elements_spec E HE).
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
  apply Trie.extensionality. intro p. unfold map, map_c. rewrite !TrieMerge.get_map.
  destruct (Trie.get p m) as [[k v]|]; reflexivity.
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
