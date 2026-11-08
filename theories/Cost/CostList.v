(** * Costed list traversal

    Traversals charge one tick per visited element and retain all callback costs.
    For example, mapping a two-tick callback over three elements costs nine ticks.
    Builds on: CostMonad and Stdlib lists. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
Import List.ListNotations Cost.Notations.

Open Scope N_scope.

(** A left fold charges each callback and one traversal tick. *)
Fixpoint fold_left_c {A B} (f : B -> A -> Cost.t B) (l : list A) (b : B)
    : Cost.t B :=
  match l with
  | [] => Cost.ret b
  | x :: xs =>
    Cost.step ;;
    let* b' := f b x in
    fold_left_c f xs b'
  end.

(** A right fold visits the tail before charging the callback at the head. *)
Fixpoint fold_right_c {A B} (f : A -> B -> Cost.t B) (b : B) (l : list A)
    : Cost.t B :=
  match l with
  | [] => Cost.ret b
  | x :: xs =>
    Cost.step ;;
    let* b' := fold_right_c f b xs in
    f x b'
  end.

(** A left fold agrees with the ordinary fold of callback values. *)
Theorem value_fold_left_c {A B} (f : B -> A -> Cost.t B) l b :
  Cost.value (fold_left_c f l b) = fold_left (fun b x => Cost.value (f b x)) l b.
Proof.
  revert b. induction l as [|x xs IH]; intro b; cbn [fold_left_c fold_left].
  - reflexivity.
  - autorewrite with galois_cost. apply IH.
Qed.

(** A left fold charges precisely the head callback and the reached tail fold. *)
Theorem ticks_fold_left_c_cons {A B} (f : B -> A -> Cost.t B) x xs b :
  Cost.ticks (fold_left_c f (x :: xs) b) =
  1 + Cost.ticks (f b x) + Cost.ticks (fold_left_c f xs (Cost.value (f b x))).
Proof.
  cbn [fold_left_c]. autorewrite with galois_cost. lia.
Qed.

(** An empty left fold is free. *)
Theorem ticks_fold_left_c_nil {A B} (f : B -> A -> Cost.t B) b :
  Cost.ticks (fold_left_c f [] b) = 0.
Proof.
  reflexivity.
Qed.

(** A right fold agrees with the ordinary fold of callback values. *)
Theorem value_fold_right_c {A B} (f : A -> B -> Cost.t B) b l :
  Cost.value (fold_right_c f b l) = fold_right (fun x b => Cost.value (f x b)) b l.
Proof.
  induction l as [|x xs IH]; cbn [fold_right_c fold_right].
  - reflexivity.
  - autorewrite with galois_cost. rewrite IH. reflexivity.
Qed.

(** A right fold charges its tail and the callback on the tail result. *)
Theorem ticks_fold_right_c_cons {A B} (f : A -> B -> Cost.t B) b x xs :
  Cost.ticks (fold_right_c f b (x :: xs)) =
  1 + Cost.ticks (fold_right_c f b xs) +
    Cost.ticks (f x (Cost.value (fold_right_c f b xs))).
Proof.
  cbn [fold_right_c]. autorewrite with galois_cost. lia.
Qed.

(** An empty right fold is free. *)
Theorem ticks_fold_right_c_nil {A B} (f : A -> B -> Cost.t B) b :
  Cost.ticks (fold_right_c f b []) = 0.
Proof.
  reflexivity.
Qed.

(** Left-fold credits telescope across invariant-preserving callback calls. *)
Theorem ticks_fold_left_c_potential {A B} (f : B -> A -> Cost.t B)
    (I : B -> Prop) (Phi : B -> N) k l b :
  (forall b x, I b -> In x l ->
    I (Cost.value (f b x)) /\ Cost.ticks (f b x) + Phi (Cost.value (f b x)) <= k + Phi b) ->
  I b ->
  Cost.ticks (fold_left_c f l b) + Phi (Cost.value (fold_left_c f l b)) <=
    N.of_nat (length l) * (k + 1) + Phi b.
Proof.
  revert b. induction l as [|x xs IH]; intros b Hstep Hb.
  - cbn [fold_left_c length]. autorewrite with galois_cost. nia.
  - destruct (Hstep b x Hb (or_introl eq_refl)) as [Hb' Hcredit].
    specialize (IH (Cost.value (f b x))).
    assert (Htail : forall b x, I b -> In x xs ->
      I (Cost.value (f b x)) /\
      Cost.ticks (f b x) + Phi (Cost.value (f b x)) <= k + Phi b).
    { intros b' y HI Hin. apply Hstep; [exact HI | right; exact Hin]. }
    specialize (IH Htail Hb').
    rewrite ticks_fold_left_c_cons.
    change (1 + Cost.ticks (f b x) +
      Cost.ticks (fold_left_c f xs (Cost.value (f b x))) +
      Phi (Cost.value (fold_left_c f xs (Cost.value (f b x)))) <=
      N.of_nat (S (length xs)) * (k + 1) + Phi b).
    rewrite Nat2N.inj_succ. nia.
Qed.

(** Right-fold credits telescope from the initial accumulator to the final result. *)
Theorem ticks_fold_right_c_potential {A B} (f : A -> B -> Cost.t B)
    (I : B -> Prop) (Phi : B -> N) k l b :
  (forall x b, In x l -> I b ->
    I (Cost.value (f x b)) /\ Cost.ticks (f x b) + Phi (Cost.value (f x b)) <= k + Phi b) ->
  I b ->
  I (Cost.value (fold_right_c f b l)) /\
  Cost.ticks (fold_right_c f b l) + Phi (Cost.value (fold_right_c f b l)) <=
    N.of_nat (length l) * (k + 1) + Phi b.
Proof.
  induction l as [|x xs IH]; intros Hstep Hb.
  - cbn [fold_right_c length]. autorewrite with galois_cost. split; [exact Hb | nia].
  - assert (Htail : forall x b, In x xs -> I b ->
      I (Cost.value (f x b)) /\
      Cost.ticks (f x b) + Phi (Cost.value (f x b)) <= k + Phi b).
    { intros y b' Hin HI. apply Hstep; [right; exact Hin | exact HI]. }
    destruct (IH Htail Hb) as [HI Hcredit].
    destruct (Hstep x _ (or_introl eq_refl) HI) as [HI' Hcredit'].
    cbn [fold_right_c]. autorewrite with galois_cost.
    split; [exact HI' |].
    cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** A uniform callback bound gives a linear left-fold bound. *)
Theorem ticks_fold_left_c_le {A B} (f : B -> A -> Cost.t B) k l b :
  (forall b x, Cost.ticks (f b x) <= k) ->
  Cost.ticks (fold_left_c f l b) <= N.of_nat (length l) * (k + 1).
Proof.
  intro Hbound.
  pose proof (ticks_fold_left_c_potential f (fun _ => True) (fun _ => 0) k l b)
    as Hpotential.
  assert (Hstep : forall b x, True -> In x l ->
    True /\ Cost.ticks (f b x) + 0 <= k + 0).
  { intros b' x _ _. split; [exact I | specialize (Hbound b' x); lia]. }
  specialize (Hpotential Hstep I). lia.
Qed.

(** A uniform callback bound gives a linear right-fold bound. *)
Theorem ticks_fold_right_c_le {A B} (f : A -> B -> Cost.t B) k b l :
  (forall x b, Cost.ticks (f x b) <= k) ->
  Cost.ticks (fold_right_c f b l) <= N.of_nat (length l) * (k + 1).
Proof.
  intro Hbound.
  pose proof (ticks_fold_right_c_potential f (fun _ => True) (fun _ => 0) k l b)
    as Hpotential.
  assert (Hstep : forall x b, In x l -> True ->
    True /\ Cost.ticks (f x b) + 0 <= k + 0).
  { intros x b' _ _. split; [exact I | specialize (Hbound x b'); lia]. }
  destruct (Hpotential Hstep I) as [_ Hcost]. lia.
Qed.

(** Counting charges one tick per element. *)
Definition length_c {A} (l : list A) : Cost.t nat :=
  fold_right_c (fun _ n => Cost.ret (S n)) O l.

(** Appending copies and charges the first list alone. *)
Definition app_c {A} (l r : list A) : Cost.t (list A) :=
  fold_right_c (fun x xs => Cost.ret (x :: xs)) r l.

(** Reversal uses a single charged left traversal. *)
Definition rev_c {A} (l : list A) : Cost.t (list A) :=
  fold_left_c (fun xs x => Cost.ret (x :: xs)) l [].

(** Mapping charges each visited element and its callback. *)
Definition map_c {A B} (f : A -> Cost.t B) (l : list A) : Cost.t (list B) :=
  fold_right_c (fun x xs => Cost.map (fun y => y :: xs) (f x)) [] l.

(** Filtering retains elements whose charged predicate returns true. *)
Definition filter_c {A} (f : A -> Cost.t bool) (l : list A) : Cost.t (list A) :=
  fold_right_c (fun x xs =>
    Cost.map (fun keep : bool => if keep then x :: xs else xs) (f x)) [] l.

(** Filter-map discards absent callback results and keeps the order of present results. *)
Definition filter_map_c {A B} (f : A -> Cost.t (option B)) (l : list A) : Cost.t (list B) :=
  fold_right_c (fun x xs =>
    Cost.map (fun y => match y with Some b => b :: xs | None => xs end) (f x)) [] l.

(** The uncosted filter-map specification keeps present results in input order. *)
Definition filter_map {A B} (f : A -> option B) (l : list A) : list B :=
  fold_right (fun x xs => match f x with Some b => b :: xs | None => xs end) [] l.

(** Filter-map membership is witnessed by an input whose callback returns that output. *)
Theorem filter_map_spec {A B} (f : A -> option B) xs y :
  In y (filter_map f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  induction xs as [|x xs IH]; cbn [filter_map fold_right]; [firstorder|].
  destruct (f x) as [z|] eqn:Hfx; cbn [In]; rewrite IH.
  - split.
    + intros [Heq|[a [Ha Hfa]]].
      * subst y; exists x; auto.
      * exists a; auto.
    + intros [a [[Heq|Ha] Hfa]].
      * subst a; rewrite Hfx in Hfa; inversion Hfa; auto.
      * right; exists a; auto.
  - split.
    + intros [a [Ha Hfa]]; exists a; auto.
    + intros [a [[Heq|Ha] Hfa]].
      * subst a; rewrite Hfx in Hfa; discriminate.
      * exists a; auto.
Qed.

(** The counter returns the ordinary list length. *)
Theorem value_length_c {A} (l : list A) : Cost.value (length_c l) = length l.
Proof.
  unfold length_c. rewrite value_fold_right_c.
  change (fold_right (fun (_ : A) n => S n) O l = length l).
  induction l as [|x xs IH]; cbn; congruence.
Qed.

(** Append returns ordinary list concatenation. *)
Theorem value_app_c {A} (l r : list A) : Cost.value (app_c l r) = l ++ r.
Proof.
  unfold app_c. rewrite value_fold_right_c.
  change (fold_right (fun x xs => x :: xs) r l = l ++ r).
  induction l as [|x xs IH]; cbn; congruence.
Qed.

(** Reverse returns the ordinary reversed list. *)
Theorem value_rev_c {A} (l : list A) : Cost.value (rev_c l) = rev l.
Proof.
  unfold rev_c. rewrite value_fold_left_c.
  change (fold_left (fun xs x => x :: xs) l [] = rev l).
  assert (Hacc : forall l r : list A,
    fold_left (fun xs x => x :: xs) l r = rev l ++ r).
  { intro xs. induction xs as [|x xs IH]; intro r; cbn [fold_left rev].
    - reflexivity.
    - rewrite IH, <- app_assoc. reflexivity. }
  rewrite Hacc, app_nil_r. reflexivity.
Qed.

(** Mapping returns the list of callback values. *)
Theorem value_map_c {A B} (f : A -> Cost.t B) l :
  Cost.value (map_c f l) = List.map (fun x => Cost.value (f x)) l.
Proof.
  unfold map_c. rewrite value_fold_right_c.
  induction l as [|x xs IH]; cbn [fold_right List.map].
  - reflexivity.
  - rewrite Cost.value_map, IH. reflexivity.
Qed.

(** Filtering returns the ordinary filter of predicate values. *)
Theorem value_filter_c {A} (f : A -> Cost.t bool) l :
  Cost.value (filter_c f l) = filter (fun x => Cost.value (f x)) l.
Proof.
  unfold filter_c. rewrite value_fold_right_c.
  induction l as [|x xs IH]; cbn [fold_right filter].
  - reflexivity.
  - rewrite Cost.value_map, IH. reflexivity.
Qed.

(** Filter-map returns the pure filter-map of callback values. *)
Theorem value_filter_map_c {A B} (f : A -> Cost.t (option B)) l :
  Cost.value (filter_map_c f l) = filter_map (fun x => Cost.value (f x)) l.
Proof.
  unfold filter_map_c, filter_map. rewrite value_fold_right_c.
  induction l as [|x xs IH]; cbn [fold_right].
  - reflexivity.
  - rewrite Cost.value_map, IH. reflexivity.
Qed.

(** Right-fold cost is the sum of callback costs when they ignore the accumulator. *)
Theorem ticks_fold_right_c_sum {A B} (f : A -> B -> Cost.t B) (w : A -> N) b l :
  (forall x b, Cost.ticks (f x b) = w x) ->
  Cost.ticks (fold_right_c f b l) = fold_right (fun x n => 1 + w x + n) 0 l.
Proof.
  intro Hcost. induction l as [|x xs IH].
  - reflexivity.
  - rewrite ticks_fold_right_c_cons, Hcost, IH. cbn [fold_right]. lia.
Qed.

(** Counting charges the length, including zero on the empty list. *)
Theorem ticks_length_c {A} (l : list A) : Cost.ticks (length_c l) = N.of_nat (length l).
Proof.
  unfold length_c. rewrite (ticks_fold_right_c_sum _ (fun _ => 0)); [|reflexivity].
  induction l as [|x xs IH]; cbn [fold_right length]; [reflexivity |].
  rewrite Nat2N.inj_succ. nia.
Qed.

(** Append charges the length of the first list. *)
Theorem ticks_app_c {A} (l r : list A) : Cost.ticks (app_c l r) = N.of_nat (length l).
Proof.
  unfold app_c. rewrite (ticks_fold_right_c_sum _ (fun _ => 0)); [|reflexivity].
  induction l as [|x xs IH]; cbn [fold_right length]; [reflexivity |].
  rewrite Nat2N.inj_succ. nia.
Qed.

(** Reversal charges the input length. *)
Theorem ticks_rev_c {A} (l : list A) : Cost.ticks (rev_c l) = N.of_nat (length l).
Proof.
  unfold rev_c.
  assert (Hacc : forall l r : list A,
    Cost.ticks (fold_left_c (fun xs x => Cost.ret (x :: xs)) l r) = N.of_nat (length l)).
  { intro xs. induction xs as [|x xs IH]; intro r; [reflexivity |].
    rewrite ticks_fold_left_c_cons, IH, Cost.ticks_ret.
    cbn [length]. rewrite Nat2N.inj_succ. nia. }
  apply Hacc.
Qed.

(** Mapping charges one traversal tick and the callback cost per element. *)
Theorem ticks_map_c {A B} (f : A -> Cost.t B) l :
  Cost.ticks (map_c f l) =
    fold_right (fun x n => 1 + Cost.ticks (f x) + n) 0 l.
Proof.
  unfold map_c. apply ticks_fold_right_c_sum. intros x b. apply Cost.ticks_map.
Qed.

(** Filtering charges every predicate call, including rejected elements. *)
Theorem ticks_filter_c {A} (f : A -> Cost.t bool) l :
  Cost.ticks (filter_c f l) =
    fold_right (fun x n => 1 + Cost.ticks (f x) + n) 0 l.
Proof.
  unfold filter_c. apply ticks_fold_right_c_sum. intros x b. apply Cost.ticks_map.
Qed.

(** Filter-map charges every callback, including absent results. *)
Theorem ticks_filter_map_c {A B} (f : A -> Cost.t (option B)) l :
  Cost.ticks (filter_map_c f l) =
    fold_right (fun x n => 1 + Cost.ticks (f x) + n) 0 l.
Proof.
  unfold filter_map_c. apply ticks_fold_right_c_sum. intros x b. apply Cost.ticks_map.
Qed.

#[export] Hint Rewrite
  @value_fold_left_c @value_fold_right_c
  @ticks_fold_left_c_nil @ticks_fold_left_c_cons
  @ticks_fold_right_c_nil @ticks_fold_right_c_cons
  @value_length_c @value_app_c @value_rev_c @value_map_c @value_filter_c @value_filter_map_c
  @ticks_length_c @ticks_app_c @ticks_rev_c @ticks_map_c @ticks_filter_c @ticks_filter_map_c
  : galois_cost.

(** A uniform pointwise charge bounds the sum of traversal and callback costs. *)
Theorem traversal_sum_le {A} (f : A -> N) k (l : list A) :
  (forall x, f x <= k) ->
  fold_right (fun x n => 1 + f x + n) 0 l <= N.of_nat (length l) * (k + 1).
Proof.
  intro Hbound. induction l as [|x xs IH]; cbn [fold_right length].
  - nia.
  - rewrite Nat2N.inj_succ. specialize (Hbound x). nia.
Qed.

(** Counting has a unit uniform bound. *)
Theorem ticks_length_c_le {A} (l : list A) :
  Cost.ticks (length_c l) <= N.of_nat (length l).
Proof.
  rewrite ticks_length_c. lia.
Qed.

(** Append has a unit uniform bound on its first list. *)
Theorem ticks_app_c_le {A} (l r : list A) :
  Cost.ticks (app_c l r) <= N.of_nat (length l).
Proof.
  rewrite ticks_app_c. lia.
Qed.

(** Reversal has a unit uniform bound. *)
Theorem ticks_rev_c_le {A} (l : list A) :
  Cost.ticks (rev_c l) <= N.of_nat (length l).
Proof.
  rewrite ticks_rev_c. lia.
Qed.

(** Mapping has a linear bound when every callback has a uniform bound. *)
Theorem ticks_map_c_le {A B} (f : A -> Cost.t B) k l :
  (forall x, Cost.ticks (f x) <= k) ->
  Cost.ticks (map_c f l) <= N.of_nat (length l) * (k + 1).
Proof.
  rewrite ticks_map_c. apply traversal_sum_le.
Qed.

(** Filtering has a linear bound even when every element is rejected. *)
Theorem ticks_filter_c_le {A} (f : A -> Cost.t bool) k l :
  (forall x, Cost.ticks (f x) <= k) ->
  Cost.ticks (filter_c f l) <= N.of_nat (length l) * (k + 1).
Proof.
  rewrite ticks_filter_c. apply traversal_sum_le.
Qed.

(** Filter-map has a linear bound even when every result is absent. *)
Theorem ticks_filter_map_c_le {A B} (f : A -> Cost.t (option B)) k l :
  (forall x, Cost.ticks (f x) <= k) ->
  Cost.ticks (filter_map_c f l) <= N.of_nat (length l) * (k + 1).
Proof.
  rewrite ticks_filter_map_c. apply traversal_sum_le.
Qed.

(** Counting telescopes any invariant accumulator potential. *)
Theorem ticks_length_c_potential {A} (I : nat -> Prop) (Phi : nat -> N) k (l : list A) :
  I O -> (forall n, I n -> I (S n) /\ Phi (S n) <= k + Phi n) ->
  Cost.ticks (length_c l) + Phi (Cost.value (length_c l)) <=
    N.of_nat (length l) * (k + 1) + Phi O.
Proof.
  intros HI Hstep. unfold length_c.
  exact (proj2 (ticks_fold_right_c_potential (fun (_ : A) n => Cost.ret (S n)) I Phi k l O
    (fun _ n _ Hn => Hstep n Hn) HI)).
Qed.

(** Append telescopes credits on the list being constructed. *)
Theorem ticks_app_c_potential {A} (I : list A -> Prop) (Phi : list A -> N) k l r :
  I r -> (forall x xs, In x l -> I xs -> I (x :: xs) /\ Phi (x :: xs) <= k + Phi xs) ->
  Cost.ticks (app_c l r) + Phi (Cost.value (app_c l r)) <=
    N.of_nat (length l) * (k + 1) + Phi r.
Proof.
  intros HI Hstep. unfold app_c.
  exact (proj2 (ticks_fold_right_c_potential (fun x xs => Cost.ret (x :: xs))
    I Phi k l r Hstep HI)).
Qed.

(** Reverse telescopes credits on its growing accumulator. *)
Theorem ticks_rev_c_potential {A} (I : list A -> Prop) (Phi : list A -> N) k l :
  I [] -> (forall xs x, I xs -> In x l ->
    I (x :: xs) /\ Phi (x :: xs) <= k + Phi xs) ->
  Cost.ticks (rev_c l) + Phi (Cost.value (rev_c l)) <=
    N.of_nat (length l) * (k + 1) + Phi [].
Proof.
  intros HI Hstep. unfold rev_c. apply (ticks_fold_left_c_potential _ I Phi k l []); [|exact HI].
  intros xs x Hxs Hin. specialize (Hstep xs x Hxs Hin). cbn. tauto.
Qed.

(** Mapping telescopes credits on the output accumulator and charges every callback. *)
Theorem ticks_map_c_potential {A B} (f : A -> Cost.t B)
    (I : list B -> Prop) (Phi : list B -> N) k l :
  I [] -> (forall x xs, In x l -> I xs ->
    I (Cost.value (f x) :: xs) /\
    Cost.ticks (f x) + Phi (Cost.value (f x) :: xs) <= k + Phi xs) ->
  Cost.ticks (map_c f l) + Phi (Cost.value (map_c f l)) <=
    N.of_nat (length l) * (k + 1) + Phi [].
Proof.
  intros HI Hstep. unfold map_c.
  exact (proj2 (ticks_fold_right_c_potential
    (fun x xs => Cost.map (fun y => y :: xs) (f x)) I Phi k l [] Hstep HI)).
Qed.

(** Filtering telescopes credits on the retained output list. *)
Theorem ticks_filter_c_potential {A} (f : A -> Cost.t bool)
    (I : list A -> Prop) (Phi : list A -> N) k l :
  I [] -> (forall x xs, In x l -> I xs ->
    let ys := if Cost.value (f x) then x :: xs else xs in
    I ys /\ Cost.ticks (f x) + Phi ys <= k + Phi xs) ->
  Cost.ticks (filter_c f l) + Phi (Cost.value (filter_c f l)) <=
    N.of_nat (length l) * (k + 1) + Phi [].
Proof.
  intros HI Hstep. unfold filter_c.
  exact (proj2 (ticks_fold_right_c_potential
    (fun x xs => Cost.map (fun keep : bool => if keep then x :: xs else xs) (f x))
    I Phi k l [] Hstep HI)).
Qed.

(** Filter-map telescopes credits on the present callback results. *)
Theorem ticks_filter_map_c_potential {A B} (f : A -> Cost.t (option B))
    (I : list B -> Prop) (Phi : list B -> N) k l :
  I [] -> (forall x xs, In x l -> I xs ->
    let ys := match Cost.value (f x) with Some b => b :: xs | None => xs end in
    I ys /\ Cost.ticks (f x) + Phi ys <= k + Phi xs) ->
  Cost.ticks (filter_map_c f l) + Phi (Cost.value (filter_map_c f l)) <=
    N.of_nat (length l) * (k + 1) + Phi [].
Proof.
  intros HI Hstep. unfold filter_map_c.
  exact (proj2 (ticks_fold_right_c_potential
    (fun x xs => Cost.map
      (fun y => match y with Some b => b :: xs | None => xs end) (f x))
    I Phi k l [] Hstep HI)).
Qed.

(** Find stops at the first successful charged predicate. *)
Fixpoint find_c {A} (f : A -> Cost.t bool) (l : list A) : Cost.t (option A) :=
  match l with
  | [] => Cost.ret None
  | x :: xs =>
    Cost.step ;;
    let* found := f x in
    if found then Cost.ret (Some x) else find_c f xs
  end.

(** Universal testing stops at the first false callback. *)
Definition forallb_c {A} (f : A -> Cost.t bool) (l : list A) : Cost.t bool :=
  Cost.map (fun result => match result with None => true | Some _ => false end)
    (find_c (fun x => Cost.map negb (f x)) l).

(** Existential testing stops at the first true callback. *)
Definition existsb_c {A} (f : A -> Cost.t bool) (l : list A) : Cost.t bool :=
  Cost.map (fun result => match result with None => false | Some _ => true end) (find_c f l).

(** Find agrees with first-match list search. *)
Theorem value_find_c {A} (f : A -> Cost.t bool) l :
  Cost.value (find_c f l) = find (fun x => Cost.value (f x)) l.
Proof.
  induction l as [|x xs IH]; cbn [find_c find].
  - reflexivity.
  - autorewrite with galois_cost.
    destruct (Cost.value (f x)); [reflexivity | exact IH].
Qed.

(** Universal testing agrees with the ordinary short-circuit test. *)
Theorem value_forallb_c {A} (f : A -> Cost.t bool) l :
  Cost.value (forallb_c f l) = forallb (fun x => Cost.value (f x)) l.
Proof.
  unfold forallb_c. rewrite Cost.value_map, value_find_c.
  induction l as [|x xs IH]; cbn [find forallb].
  - reflexivity.
  - rewrite Cost.value_map. destruct (Cost.value (f x)); cbn; assumption || reflexivity.
Qed.

(** Existential testing agrees with the ordinary short-circuit test. *)
Theorem value_existsb_c {A} (f : A -> Cost.t bool) l :
  Cost.value (existsb_c f l) = existsb (fun x => Cost.value (f x)) l.
Proof.
  unfold existsb_c. rewrite Cost.value_map, value_find_c.
  induction l as [|x xs IH]; cbn [find existsb].
  - reflexivity.
  - destruct (Cost.value (f x)); cbn; assumption || reflexivity.
Qed.

(** Empty search does not call its predicate. *)
Theorem ticks_find_c_nil {A} (f : A -> Cost.t bool) : Cost.ticks (find_c f []) = 0.
Proof.
  reflexivity.
Qed.

(** Search charges no unvisited suffix after its first successful predicate. *)
Theorem ticks_find_c_cons {A} (f : A -> Cost.t bool) x xs :
  Cost.ticks (find_c f (x :: xs)) =
    1 + Cost.ticks (f x) +
      if Cost.value (f x) then 0 else Cost.ticks (find_c f xs).
Proof.
  cbn [find_c]. autorewrite with galois_cost.
  destruct (Cost.value (f x)); autorewrite with galois_cost; lia.
Qed.

(** Empty universal testing is free. *)
Theorem ticks_forallb_c_nil {A} (f : A -> Cost.t bool) :
  Cost.ticks (forallb_c f []) = 0.
Proof.
  reflexivity.
Qed.

(** Universal testing charges the suffix only when the head test succeeds. *)
Theorem ticks_forallb_c_cons {A} (f : A -> Cost.t bool) x xs :
  Cost.ticks (forallb_c f (x :: xs)) =
    1 + Cost.ticks (f x) +
      if Cost.value (f x) then Cost.ticks (forallb_c f xs) else 0.
Proof.
  unfold forallb_c. rewrite !Cost.ticks_map, ticks_find_c_cons.
  autorewrite with galois_cost. destruct (Cost.value (f x)); reflexivity.
Qed.

(** Empty existential testing is free. *)
Theorem ticks_existsb_c_nil {A} (f : A -> Cost.t bool) :
  Cost.ticks (existsb_c f []) = 0.
Proof.
  reflexivity.
Qed.

(** Existential testing charges the suffix only when the head test fails. *)
Theorem ticks_existsb_c_cons {A} (f : A -> Cost.t bool) x xs :
  Cost.ticks (existsb_c f (x :: xs)) =
    1 + Cost.ticks (f x) +
      if Cost.value (f x) then 0 else Cost.ticks (existsb_c f xs).
Proof.
  unfold existsb_c. rewrite !Cost.ticks_map, ticks_find_c_cons. reflexivity.
Qed.

(** Find has a linear uniform bound even when it exhausts the list. *)
Theorem ticks_find_c_le {A} (f : A -> Cost.t bool) k l :
  (forall x, Cost.ticks (f x) <= k) ->
  Cost.ticks (find_c f l) <= N.of_nat (length l) * (k + 1).
Proof.
  intro Hbound. induction l as [|x xs IH].
  - rewrite ticks_find_c_nil. nia.
  - rewrite ticks_find_c_cons. cbn [length]. rewrite Nat2N.inj_succ.
    specialize (Hbound x). destruct (Cost.value (f x)); nia.
Qed.

(** Universal testing inherits the bound of its short-circuit search. *)
Theorem ticks_forallb_c_le {A} (f : A -> Cost.t bool) k l :
  (forall x, Cost.ticks (f x) <= k) ->
  Cost.ticks (forallb_c f l) <= N.of_nat (length l) * (k + 1).
Proof.
  intro Hbound. unfold forallb_c. rewrite Cost.ticks_map.
  apply ticks_find_c_le. intro x. rewrite Cost.ticks_map. apply Hbound.
Qed.

(** Existential testing inherits the bound of its short-circuit search. *)
Theorem ticks_existsb_c_le {A} (f : A -> Cost.t bool) k l :
  (forall x, Cost.ticks (f x) <= k) ->
  Cost.ticks (existsb_c f l) <= N.of_nat (length l) * (k + 1).
Proof.
  intro Hbound. unfold existsb_c. rewrite Cost.ticks_map. apply ticks_find_c_le, Hbound.
Qed.

(** The search remainder is the unvisited suffix after success, or empty on exhaustion. *)
Fixpoint find_remainder {A} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if f x then xs else find_remainder f xs
  end.

(** Search telescopes suffix credits and refunds the unvisited suffix potential. *)
Theorem ticks_find_c_potential {A} (f : A -> Cost.t bool)
    (I : list A -> Prop) (Phi : list A -> N) k l :
  (forall x xs, I (x :: xs) ->
    I xs /\ Cost.ticks (f x) + Phi xs <= k + Phi (x :: xs)) ->
  I l ->
  Cost.ticks (find_c f l) + Phi (find_remainder (fun x => Cost.value (f x)) l) <=
    N.of_nat (length l) * (k + 1) + Phi l.
Proof.
  intros Hstep. induction l as [|x xs IH]; intro HI.
  - cbn [find_remainder length]. rewrite ticks_find_c_nil. nia.
  - destruct (Hstep x xs HI) as [HI' Hcredit]. specialize (IH HI').
    rewrite ticks_find_c_cons. cbn [find_remainder length]. rewrite Nat2N.inj_succ.
    destruct (Cost.value (f x)); nia.
Qed.

(** Universal testing refunds the suffix left after the first false callback. *)
Theorem ticks_forallb_c_potential {A} (f : A -> Cost.t bool)
    (I : list A -> Prop) (Phi : list A -> N) k l :
  (forall x xs, I (x :: xs) ->
    I xs /\ Cost.ticks (f x) + Phi xs <= k + Phi (x :: xs)) ->
  I l ->
  Cost.ticks (forallb_c f l) +
    Phi (find_remainder (fun x => negb (Cost.value (f x))) l) <=
    N.of_nat (length l) * (k + 1) + Phi l.
Proof.
  intros Hstep HI. unfold forallb_c. rewrite Cost.ticks_map.
  apply (ticks_find_c_potential (fun x => Cost.map negb (f x)) I Phi k); [|exact HI].
  intros x xs Hxs. rewrite Cost.ticks_map. apply Hstep, Hxs.
Qed.

(** Existential testing refunds the suffix left after the first true callback. *)
Theorem ticks_existsb_c_potential {A} (f : A -> Cost.t bool)
    (I : list A -> Prop) (Phi : list A -> N) k l :
  (forall x xs, I (x :: xs) ->
    I xs /\ Cost.ticks (f x) + Phi xs <= k + Phi (x :: xs)) ->
  I l ->
  Cost.ticks (existsb_c f l) + Phi (find_remainder (fun x => Cost.value (f x)) l) <=
    N.of_nat (length l) * (k + 1) + Phi l.
Proof.
  intros Hstep HI. unfold existsb_c. rewrite Cost.ticks_map.
  apply (ticks_find_c_potential _ I Phi k); assumption.
Qed.

#[export] Hint Rewrite
  @value_find_c @value_forallb_c @value_existsb_c
  @ticks_find_c_nil @ticks_find_c_cons @ticks_forallb_c_nil @ticks_forallb_c_cons
  @ticks_existsb_c_nil @ticks_existsb_c_cons : galois_cost.
