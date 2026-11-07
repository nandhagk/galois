(** * Value composition

    Products intersect meanings and disjunctions retain existential alternatives.
    For example, an identity reducer gives the ordinary pair product.
    Builds on: DomainsValue, DomainsTactics and LatticeKit. *)

From Stdlib Require Import List Bool Arith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeKit.
From Galois.Domains Require Import DomainsValue DomainsTactics.
Import List.ListNotations Cost.Notations.

(** Product meaning interprets both components at the same concrete value. *)
Definition product_gamma {A B C} (GA : concretisation A C) (GB : concretisation B C) :=
  slots2_gamma GA GB (@fst A B) (@snd A B).

Local Lemma pair_slots {A B} (LA : lattice A) (LB : lattice B) :
  slots2 (ValueAbs.pair_lattice LA LB) LA LB (@fst A B) (@snd A B).
Proof.
  constructor.
  - intros [a b] [c d]. change ((leb LA a c && leb LB b d) = true <->
      leb LA a c = true /\ leb LB b d = true).
    apply andb_true_iff.
  - split; reflexivity.
  - intros [a b] [c d]. split; reflexivity.
  - intros [a b] [c d]. split; reflexivity.
  - intros [a b] [c d]. split; reflexivity.
Qed.

Local Lemma product_arguments {A B C} (GA : concretisation A C) (GB : concretisation B C)
    xs cs :
  Forall2 (gamma (product_gamma GA GB)) xs cs ->
  Forall2 (gamma GA) (map fst xs) cs /\ Forall2 (gamma GB) (map snd xs) cs.
Proof.
  intro H. induction H as [|[a b] c xs cs [Ha Hb] Hxs [IHl IHr]];
    cbn; split; constructor; assumption.
Qed.

Local Lemma zip_sound {A B C} (GA : concretisation A C) (GB : concretisation B C)
    (red : A * B -> Cost.t (A * B)) :
  (forall p c, gamma (product_gamma GA GB) p c ->
    gamma (product_gamma GA GB) (Cost.value (red p)) c) ->
  forall xs ys cs, Forall2 (gamma GA) xs cs -> Forall2 (gamma GB) ys cs ->
  Forall2 (gamma (product_gamma GA GB)) (Cost.value (ValueAbs.zip_reduce_c red xs ys)) cs.
Proof.
  intros Hr xs ys cs Hx. revert ys.
  induction Hx as [|x c xs cs Hx Hxs IH]; intros ys Hyrel.
  - inversion Hyrel. constructor.
  - inversion Hyrel as [|y c' ys' cs' Hy Hys]; subst.
    cbn [ValueAbs.zip_reduce_c]. autorewrite with galois_cost. constructor.
    + apply Hr. split; assumption.
    + now apply IH.
Qed.

Local Lemma zip_length {A B} (red : A * B -> Cost.t (A * B)) xs ys :
  length (Cost.value (ValueAbs.zip_reduce_c red xs ys)) = Nat.min (length xs) (length ys).
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn [ValueAbs.zip_reduce_c];
    autorewrite with galois_cost; cbn; auto.
Qed.

(** A meaning-preserving reducer makes the componentwise product a lawful value dictionary. *)
Theorem product_laws {A B C K G} (D : ValueAbs.t A K G) (E : ValueAbs.t B K G)
    (M : ValueSem.t C K G) GA GB red :
  value_laws D M GA -> value_laws E M GB ->
  (forall p c, gamma (product_gamma GA GB) p c ->
    gamma (product_gamma GA GB) (Cost.value (red p)) c) ->
  value_laws (ValueAbs.product D E red) M (product_gamma GA GB).
Proof.
  intros HD HE Hr. constructor.
  - exact (slots2_laws (pair_slots _ _) (lat_ok HD) (lat_ok HE)).
  - exact (slots2_gamma_laws (pair_slots _ _) GA GB (gamma_ok HD) (gamma_ok HE)).
  - intros c [Ha Hb]. exact (bot_empty HD c Ha).
  - intro c. change (gamma GA (ValueAbs.top D) c /\ gamma GB (ValueAbs.top E) c).
    split; gamma_solver.
  - intros k xs cs c Hxs He. destruct (product_arguments GA GB xs cs Hxs) as [Hl Hr'].
    cbn [ValueAbs.op ValueAbs.product]. autorewrite with galois_cost.
    autorewrite with galois_cost.
    apply Hr. split.
    + cbn [fst snd]. autorewrite with galois_cost.
      exact (op_sound HD k (map fst xs) cs c Hl He).
    + cbn [fst snd]. autorewrite with galois_cost.
      exact (op_sound HE k (map snd xs) cs c Hr' He).
  - intros k a xs cs c Hxs He [Ha Hb].
    destruct (product_arguments GA GB xs cs Hxs) as [Hl Hr'].
    cbn [ValueAbs.back ValueAbs.product]. autorewrite with galois_cost.
    autorewrite with galois_cost.
    apply zip_sound; [exact Hr| |].
    + autorewrite with galois_cost.
      exact (back_sound HD k (fst a) (map fst xs) cs c Hl He Ha).
    + autorewrite with galois_cost.
      exact (back_sound HE k (snd a) (map snd xs) cs c Hr' He Hb).
  - intros g xs cs Hxs Hg. destruct (product_arguments GA GB xs cs Hxs) as [Hl Hr'].
    cbn [ValueAbs.guard ValueAbs.product]. autorewrite with galois_cost.
    autorewrite with galois_cost.
    apply zip_sound; [exact Hr| |].
    + autorewrite with galois_cost.
      exact (guard_sound HD g (map fst xs) cs Hl Hg).
    + autorewrite with galois_cost.
      exact (guard_sound HE g (map snd xs) cs Hr' Hg).
  - intros k a xs. unfold ValueAbs.back, ValueAbs.product.
    cbn [ValueAbs.back_c]. autorewrite with galois_cost.
    autorewrite with galois_cost.
    rewrite zip_length.
    change (Nat.min (length (ValueAbs.back D k (fst a) (map fst xs)))
      (length (ValueAbs.back E k (snd a) (map snd xs))) = length xs).
    rewrite (back_length HD), (back_length HE), !length_map, Nat.min_id.
    reflexivity.
  - intros g xs. unfold ValueAbs.guard, ValueAbs.product.
    cbn [ValueAbs.guard_c]. autorewrite with galois_cost.
    autorewrite with galois_cost.
    rewrite zip_length.
    change (Nat.min (length (ValueAbs.guard D g (map fst xs)))
      (length (ValueAbs.guard E g (map snd xs))) = length xs).
    rewrite (guard_length HD), (guard_length HE), !length_map, Nat.min_id.
    reflexivity.
Qed.

(** Operator and guard agreement transports all value laws through a vocabulary renaming. *)
Theorem rename_laws {A C K G K' G'} (D : ValueAbs.t A K G)
    (M : ValueSem.t C K G) (N : ValueSem.t C K' G') gam fk fg :
  value_laws D M gam ->
  (forall k cs, ValueSem.eval N k cs = ValueSem.eval M (fk k) cs) ->
  (forall g cs, ValueSem.holds N g cs -> ValueSem.holds M (fg g) cs) ->
  value_laws (ValueAbs.rename fk fg D) N gam.
Proof.
  intros H He Hg. constructor.
  - exact (lat_ok H).
  - exact (gamma_ok H).
  - exact (bot_empty H).
  - exact (top_full H).
  - intros k xs cs c Hxs Hc. apply (op_sound H (fk k) xs cs c Hxs).
    now rewrite <- He.
  - intros k a xs cs c Hxs Hc Ha. apply (back_sound H (fk k) a xs cs c Hxs); auto.
    now rewrite <- He.
  - intros g xs cs Hxs Hholds. apply (guard_sound H (fg g) xs cs Hxs), Hg, Hholds.
  - intros. apply (back_length H).
  - intros. apply (guard_length H).
Qed.

(** Disjunctive meaning requires at least one alternative describing the concrete value. *)
Definition disjunctive_gamma {A C} (G : concretisation A C) : concretisation (list A) C :=
  {| gamma := fun xs c => exists a, In a xs /\ gamma G a c |}.

Local Lemma choices_sound {A C} (G : concretisation A C) xs cs :
  Forall2 (gamma (disjunctive_gamma G)) xs cs ->
  exists row, In row (Cost.value (ValueAbs.choices_c xs)) /\ Forall2 (gamma G) row cs.
Proof.
  intro H. induction H as [|alts c xs cs [a [Ha Hc]] Hxs [row [Hin Hr]]].
  - exists []. split; [now left|constructor].
  - exists (a :: row). split; [|constructor; assumption].
    change (In (a :: row)
      (Cost.value (fold_right_c (fun x rest =>
        let* rows := map_c (fun tail => Cost.ret (x :: tail))
          (Cost.value (ValueAbs.choices_c xs)) in app_c rows rest) [] alts))).
    assert (Hflat : forall alts rest, In a alts -> In (a :: row)
      (Cost.value (fold_right_c (fun x rest =>
        let* rows := map_c (fun tail => Cost.ret (x :: tail))
          (Cost.value (ValueAbs.choices_c xs)) in app_c rows rest) rest alts))).
    { intros ys. induction ys as [|y ys IH]; intros rest Hy; [contradiction|].
      cbn [fold_right_c]. autorewrite with galois_cost.
      apply in_app_iff. destruct Hy as [<-|Hy].
      - left. change (In (y :: row) (map (cons y) (Cost.value (ValueAbs.choices_c xs)))).
        now apply in_map.
      - right. pose proof (IH rest Hy) as Htail.
        autorewrite with galois_cost in Htail. exact Htail. }
    apply Hflat, Ha.
Qed.

Local Lemma join_all_sound {A C} (L : lattice A) (G : concretisation A C) :
  lattice_laws L -> concretisation_laws L G -> forall xs c,
  gamma (disjunctive_gamma G) xs c -> gamma G (Cost.value (ValueAbs.join_all_c L xs)) c.
Proof.
  intros HL HG xs c [a [Ha Hc]]. unfold ValueAbs.join_all_c.
  rewrite value_fold_right_c.
  change (gamma G (fold_right (join L) (bot L) xs) c).
  induction xs as [|x xs IH]; [contradiction|].
  destruct Ha as [<-|Ha]; cbn [fold_right].
  - exact (gamma_join_l L G x _ c HL HG Hc).
  - exact (gamma_join_r L G x _ c HL HG (IH Ha)).
Qed.

Local Lemma disj_arguments {A C} (L : lattice A) (G : concretisation A C) :
  lattice_laws L -> concretisation_laws L G -> forall xs cs,
  Forall2 (gamma (disjunctive_gamma G)) xs cs ->
  Forall2 (gamma G) (map (fun xs => Cost.value (ValueAbs.join_all_c L xs)) xs) cs.
Proof.
  intros HL HG xs cs H. induction H; cbn; constructor; auto.
  eapply join_all_sound; eauto.
Qed.

Local Lemma singleton_arguments {A C} (G : concretisation A C) xs cs :
  Forall2 (gamma G) xs cs ->
  Forall2 (gamma (disjunctive_gamma G)) (map (fun a => [a]) xs) cs.
Proof.
  intro H. induction H as [|a c xs cs Hc Hxs IH]; cbn; constructor; auto.
  exists a. split; [now left|exact Hc].
Qed.

(** Weak disjunctive lattice laws and meaning-preserving compaction suffice for value soundness. *)
Theorem disjunctive_laws {A C K G} (D : ValueAbs.t A K G) (M : ValueSem.t C K G)
    gam k (L : lattice (list A)) compact :
  value_laws D M gam -> lattice_laws L ->
  concretisation_laws L (disjunctive_gamma gam) -> bot L = [] ->
  (forall xs c, gamma (disjunctive_gamma gam) xs c ->
    gamma (disjunctive_gamma gam) (Cost.value (compact k xs)) c) ->
  value_laws (ValueAbs.disjunctive k L compact D) M (disjunctive_gamma gam).
Proof.
  intros H HL HG Hbot Hcompact. constructor.
  - exact HL.
  - exact HG.
  - intros c [a [Ha Hc]]. change (In a (bot L)) in Ha.
    rewrite Hbot in Ha. exact Ha.
  - intro c. exists (ValueAbs.top D). split; [now left|apply (top_full H)].
  - intros o xs cs c Hxs He. unfold ValueAbs.op, ValueAbs.disjunctive.
    cbn [ValueAbs.op_c].
    autorewrite with galois_cost. apply Hcompact.
    destruct (choices_sound gam xs cs Hxs) as [row [Hin Hr]].
    exists (ValueAbs.op D o row). split.
    + autorewrite with galois_cost. apply in_map. exact Hin.
    + exact (op_sound H o row cs c Hr He).
  - intros o a xs cs c Hxs He Ha. unfold ValueAbs.back.
    unfold ValueAbs.disjunctive. cbn [ValueAbs.back_c].
    autorewrite with galois_cost. apply singleton_arguments.
    apply (back_sound H o _ _ cs c).
    + exact (disj_arguments _ _ (lat_ok H) (gamma_ok H) xs cs Hxs).
    + exact He.
    + exact (join_all_sound _ _ (lat_ok H) (gamma_ok H) a c Ha).
  - intros g xs cs Hxs Hg. unfold ValueAbs.guard.
    unfold ValueAbs.disjunctive. cbn [ValueAbs.guard_c].
    autorewrite with galois_cost. apply singleton_arguments.
    apply (guard_sound H g _ cs); [|exact Hg].
    exact (disj_arguments _ _ (lat_ok H) (gamma_ok H) xs cs Hxs).
  - intros o a xs. unfold ValueAbs.back, ValueAbs.disjunctive.
    cbn [ValueAbs.back_c].
    autorewrite with galois_cost.
    rewrite length_map.
    change (length (ValueAbs.back D o (Cost.value (ValueAbs.join_all_c (ValueAbs.lat D) a))
      (map (fun xs => Cost.value (ValueAbs.join_all_c (ValueAbs.lat D) xs)) xs)) = length xs).
    rewrite (back_length H), length_map. reflexivity.
  - intros g xs. unfold ValueAbs.guard, ValueAbs.disjunctive.
    cbn [ValueAbs.guard_c].
    autorewrite with galois_cost.
    rewrite length_map.
    change (length (ValueAbs.guard D g
      (map (fun xs => Cost.value (ValueAbs.join_all_c (ValueAbs.lat D) xs)) xs)) = length xs).
    rewrite (guard_length H), length_map. reflexivity.
Qed.

(** Bounded compaction bounds forward alternatives and permits the legacy zero-cap singleton. *)
Theorem disjunctive_forward_bound {A K G} (D : ValueAbs.t A K G)
    k (L : lattice (list A)) compact :
  (forall ys, length (Cost.value (compact k ys)) <= Nat.max 1 k) ->
  forall o xs, length (ValueAbs.op (ValueAbs.disjunctive k L compact D) o xs) <= Nat.max 1 k.
Proof.
  intros H o xs. unfold ValueAbs.op, ValueAbs.disjunctive.
  cbn [ValueAbs.op_c]. autorewrite with galois_cost. apply H.
Qed.
