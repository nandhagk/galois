(** * Reference memo scan reasoning

    A scan records one class for each signature and reports a pair when classes disagree.
    For example, observations [(k,c);(k,d)] report a collision when [c <> d].
    Builds on: BaseMap and BaseEncoding. *)

From Stdlib Require Import List PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph.
Import List.ListNotations.

Module EggIndex.

Definition enc := positive_encoding.

Definition step (acc : Map.t positive positive * option (positive * positive))
    (entry : positive * positive) :=
  let '(table, collision) := acc in
  let '(key, c) := entry in
  match Map.get enc key table with
  | None => (Map.set enc key c table, collision)
  | Some d =>
    (table, match collision with
      | Some cd => Some cd
      | None => if Pos.eqb c d then None else Some (c, d)
      end)
  end.

(** Scan evidence connects every table binding and collision to observations already visited. *)
Record invariant (seen : list (positive * positive))
    (table : Map.t positive positive) (collision : option (positive * positive)) : Prop := Inv {
  table_wf : Map.wf enc table;
  table_sound : forall key c, Map.get enc key table = Some c -> In (key, c) seen;
  table_complete : forall key c, In (key, c) seen -> exists d, Map.get enc key table = Some d;
  no_collision : collision = None ->
    forall key c, In (key, c) seen -> Map.get enc key table = Some c;
  collision_sound : forall c d, collision = Some (c, d) ->
    c <> d /\ exists key, In (key, c) seen /\ In (key, d) seen
}.

Local Lemma initial : invariant [] Map.empty None.
Proof.
  constructor.
  - apply Map.wf_empty.
  - intros key c Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros key c Hin; contradiction.
  - intros _ key c Hin; contradiction.
  - intros c d Heq; discriminate.
Qed.

Local Lemma insert_lookup (table : Map.t positive positive) (key c k : positive) :
  Map.wf enc table -> Map.get enc k (Map.set enc key c table) =
    if Pos.eq_dec k key then Some c else Map.get enc k table.
Proof.
  intro Hwf; destruct (Pos.eq_dec k key) as [->|Hne].
  - apply Map.get_set_same; exact Hwf.
  - apply Map.get_set_other; [exact positive_encoding_laws|exact Hwf|exact Hne].
Qed.

Local Lemma step_preserves seen table collision key c :
  invariant seen table collision ->
  invariant ((key, c) :: seen) (fst (step (table, collision) (key, c)))
    (snd (step (table, collision) (key, c))).
Proof.
  intros Hinv; unfold step.
  destruct (Map.get enc key table) as [d|] eqn:Hhit.
  - cbn [fst snd]; constructor.
    + exact (table_wf _ _ _ Hinv).
    + intros k v Hget; right; exact (table_sound _ _ _ Hinv k v Hget).
    + intros k v [Heq|Hin].
      * injection Heq as <- <-; eauto.
      * exact (table_complete _ _ _ Hinv k v Hin).
    + destruct collision as [[x y]|]; [discriminate|].
      destruct (Pos.eqb c d) eqn:Hsame; [|discriminate].
      apply Pos.eqb_eq in Hsame; subst d; intros _ k v [Heq|Hin].
      * injection Heq as <- <-; exact Hhit.
      * exact (no_collision _ _ _ Hinv eq_refl k v Hin).
    + intros x y Heq; destruct collision as [[x' y']|] eqn:Hcollision.
      * injection Heq as Hx Hy; subst x' y'.
        destruct (collision_sound _ _ _ Hinv x y eq_refl) as [Hne [k [Hx Hy]]].
        split; [exact Hne|exists k; split; right; assumption].
      * destruct (Pos.eqb c d) eqn:Hsame; [discriminate|].
        injection Heq as <- <-; split; [now apply Pos.eqb_neq|].
        exists key; split; [left; reflexivity|right; exact (table_sound _ _ _ Hinv _ _ Hhit)].
  - cbn [fst snd]; constructor.
    + apply Map.wf_set; exact (table_wf _ _ _ Hinv).
    + intros k v Hget; rewrite insert_lookup in Hget by exact (table_wf _ _ _ Hinv).
      destruct (Pos.eq_dec k key) as [->|Hne].
      * injection Hget as <-; left; reflexivity.
      * right; exact (table_sound _ _ _ Hinv k v Hget).
    + intros k v Hin; rewrite insert_lookup by exact (table_wf _ _ _ Hinv).
      destruct (Pos.eq_dec k key) as [->|Hne]; [eauto|].
      destruct Hin as [Heq|Hin]; [injection Heq as Hkey Hvalue; congruence|].
      exact (table_complete _ _ _ Hinv k v Hin).
    + intros Hnone k v Hin; rewrite insert_lookup by exact (table_wf _ _ _ Hinv).
      destruct Hin as [Heq|Hin].
      * injection Heq as <- <-; destruct (Pos.eq_dec key key); congruence.
      * pose proof (no_collision _ _ _ Hinv Hnone k v Hin) as Hget.
        destruct (Pos.eq_dec k key) as [->|Hne]; [congruence|exact Hget].
    + intros x y Hcollision.
      destruct (collision_sound _ _ _ Hinv x y Hcollision) as [Hne [k [Hx Hy]]].
      split; [exact Hne|exists k; split; right; assumption].
Qed.

Local Lemma fold_preserves entries seen table collision :
  invariant seen table collision ->
  invariant (rev entries ++ seen)
    (fst (fold_left step entries (table, collision)))
    (snd (fold_left step entries (table, collision))).
Proof.
  revert seen table collision; induction entries as [|[key c] entries IH];
    intros seen table collision Hinv.
  - exact Hinv.
  - cbn [fold_left rev].
    specialize (IH ((key, c) :: seen) _ _ (step_preserves _ _ _ _ _ Hinv)).
    destruct (step (table, collision) (key, c)) as [table' collision'].
    cbn [fst snd] in IH; rewrite <- app_assoc; exact IH.
Qed.

(** A completed scan has a sound complete index and either agreement or a witnessed collision. *)
Theorem scan_correct entries :
  invariant (rev entries)
    (fst (fold_left step entries (Map.empty, None)))
    (snd (fold_left step entries (Map.empty, None))).
Proof.
  pose proof (fold_preserves entries [] Map.empty None initial) as H.
  now rewrite app_nil_r in H.
Qed.

Definition observe {K Sort V} (a : EggAlg.t K Sort V) g
    (entry : Egraph.id * Egraph.enode K Sort V) :=
  (Egraph.node_code a (Egraph.canonical a g (snd entry)), Egraph.find a g (fst entry)).

Local Lemma graph_step_equation {K Sort V} (a : EggAlg.t K Sort V) g acc entry :
  Cost.value (Egraph.scan_step_c a g acc entry) = step acc (observe a g entry).
Proof.
  destruct acc as [table collision], entry as [c n].
  unfold Egraph.scan_step_c; rewrite !Cost.value_bind.
  fold (Egraph.canonical a g n) (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.find a g c).
  fold (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n)) table).
  unfold step, observe; cbn [fst snd].
  destruct (Map.get _ _ _) as [other|]; [|reflexivity].
  rewrite Cost.value_bind, Cost.value_ret, positive_eqb_equation.
  reflexivity.
Qed.

(** The graph's charged scan is the value of the observation-index fold. *)
Theorem graph_scan_equation {K Sort V} (a : EggAlg.t K Sort V) g :
  Egraph.scan a g = fold_left step
    (map (observe a g) (Map.elements (Egraph.nodes g))) (Map.empty, None).
Proof.
  unfold Egraph.scan, Egraph.scan_c; rewrite !Cost.value_bind.
  change (Cost.value (fold_left_c (Egraph.scan_step_c a g)
    (Map.elements (Egraph.nodes g)) (Map.empty, None)) =
    fold_left step (map (observe a g) (Map.elements (Egraph.nodes g))) (Map.empty, None)).
  rewrite value_fold_left_c.
  change (fold_left (fun acc entry => Cost.value (Egraph.scan_step_c a g acc entry))
    (Map.elements (Egraph.nodes g)) (@Map.empty positive positive, None) =
    fold_left step (map (observe a g) (Map.elements (Egraph.nodes g)))
      (@Map.empty positive positive, None)).
  assert (Hfold : forall entries acc,
    fold_left (fun acc entry => Cost.value (Egraph.scan_step_c a g acc entry)) entries acc =
    fold_left step (map (observe a g) entries) acc).
  { induction entries as [|entry entries IH]; intro acc; cbn.
    - reflexivity.
    - rewrite graph_step_equation; apply IH. }
  apply Hfold.
Qed.

(** Charged graph scans inherit the observation fold's complete collision evidence. *)
Theorem graph_scan_correct {K Sort V} (a : EggAlg.t K Sort V) g :
  invariant (rev (map (observe a g) (Map.elements (Egraph.nodes g))))
    (fst (Egraph.scan a g)) (snd (Egraph.scan a g)).
Proof.
  rewrite graph_scan_equation; apply scan_correct.
Qed.

(** Pair enumeration is a proof-side universe for a finite partition's missing equalities. *)
Definition pairs {A} (xs : list A) := flat_map (fun x => map (fun y => (x, y)) xs) xs.

(** Ordered pair enumeration has the square of its input length. *)
Theorem pairs_length {A} (xs : list A) :
  length (pairs xs) = (length xs * length xs)%nat.
Proof.
  unfold pairs.
  assert (Hlength : forall ys : list A,
    length (flat_map (fun x => map (fun y => (x, y)) xs) ys) =
      (length ys * length xs)%nat).
  { induction ys as [|x ys IH]; cbn [flat_map length].
    - reflexivity.
    - rewrite length_app, length_map, IH; cbn [length]; lia. }
  apply Hlength.
Qed.

(** An ordered pair occurs exactly when both endpoints occur in the universe. *)
Theorem pairs_in {A} (xs : list A) x y :
  In (x, y) (pairs xs) <-> In x xs /\ In y xs.
Proof.
  unfold pairs; rewrite in_flat_map; split.
  - intros [z [Hz Hin]]; apply in_map_iff in Hin as [w [Heq Hw]].
    injection Heq as <- <-; auto.
  - intros [Hx Hy]; exists x; split; [exact Hx|apply in_map; exact Hy].
Qed.

(** A monotone boolean filter strictly shrinks when it drops one formerly retained witness. *)
Theorem filter_decreases {A} (old new : A -> bool) xs :
  (forall x, In x xs -> new x = true -> old x = true) ->
  (exists x, In x xs /\ old x = true /\ new x = false) ->
  (length (filter new xs) < length (filter old xs))%nat.
Proof.
  induction xs as [|x xs IH]; intros Hmono [w [Hin [Hold Hnew]]]; [contradiction|].
  assert (Htail : forall y, In y xs -> new y = true -> old y = true).
  { intros y Hy; apply Hmono; right; exact Hy. }
  assert (Hle : (length (filter new xs) <= length (filter old xs))%nat).
  { clear IH Hin Hold Hnew w Hmono; revert Htail.
    induction xs as [|y ys IH]; intro Htail; [reflexivity|].
    specialize (IH (fun z Hz => Htail z (or_intror Hz))).
    cbn [filter].
    destruct (new y) eqn:Hny, (old y) eqn:Hoy; cbn [length].
    - lia.
    - pose proof (Htail y (or_introl eq_refl) Hny); congruence.
    - lia.
    - exact IH. }
  cbn [filter]; destruct Hin as [Heq|Hin].
  - subst w; rewrite Hold, Hnew; cbn [length]; lia.
  - specialize (IH Htail (ex_intro _ w (conj Hin (conj Hold Hnew)))).
    destruct (new x) eqn:Hnx, (old x) eqn:Hox; cbn [length] in *; try lia.
    pose proof (Hmono x (or_introl eq_refl) Hnx); congruence.
Qed.

(** Missing pairs count a finite partition's ordered pairs with different representatives. *)
Definition missing (rep : positive -> positive) ids :=
  length (filter (fun xy => negb (Pos.eqb (rep (fst xy)) (rep (snd xy)))) (pairs ids)).

(** Missing pairs never exceed the square of the identifier-universe length. *)
Theorem missing_bound rep ids : (missing rep ids <= length ids * length ids)%nat.
Proof.
  unfold missing; rewrite <- pairs_length.
  generalize (pairs ids) as xs; induction xs as [|xy xs IH]; cbn [filter length].
  - reflexivity.
  - destruct (negb (Pos.eqb (rep (fst xy)) (rep (snd xy)))); cbn [length]; lia.
Qed.

(** Merging one distinct pair strictly reduces the missing-pair measure. *)
Theorem missing_decreases old new ids x y :
  In x ids -> In y ids -> old x <> old y -> new x = new y ->
  (forall c d, old c = old d -> new c = new d) ->
  (missing new ids < missing old ids)%nat.
Proof.
  intros Hx Hy Hne Heq Hmono; unfold missing; apply filter_decreases.
  - intros [c d] Hin Hnew; cbn [fst snd] in *.
    apply Bool.negb_true_iff in Hnew; apply Pos.eqb_neq in Hnew.
    apply Bool.negb_true_iff, Pos.eqb_neq; intro Hsame; apply Hnew, Hmono, Hsame.
  - exists (x, y); split; [apply pairs_in; auto|]; cbn [fst snd].
    split.
    + apply Bool.negb_true_iff, Pos.eqb_neq; exact Hne.
    + rewrite Heq, Pos.eqb_refl; reflexivity.
Qed.

Local Lemma run_progress {S R} (step : S -> Cost.t (S + R)) (I : S -> Prop)
    (Q : R -> Prop) (measure : S -> nat)
    (Hstep : forall s, I s ->
      match Cost.value (step s) with
      | inl h => I h /\ (measure h < measure s)%nat
      | inr r => Q r
      end) n s result :
  runs step n s result -> I s ->
  match result with
  | inl h => I h /\ (measure h + n <= measure s)%nat
  | inr r => Q r
  end.
Proof.
  intros Hrun; induction Hrun as [s|n s r Hstop|n s h result Hnext Hrun IH]; intro HI.
  - split; [exact HI|lia].
  - specialize (Hstep s HI); rewrite Hstop in Hstep; exact Hstep.
  - pose proof (Hstep s HI) as Hprogress; rewrite Hnext in Hprogress.
    destruct Hprogress as [Hh Hlt]; specialize (IH Hh).
    destruct result as [h'|r]; [destruct IH as [HI' Hbound]; split; [exact HI'|lia]|exact IH].
Qed.

(** A decreasing natural measure strictly below the fuel rules out exhausted loop results. *)
Theorem iterate_stops {S R} (step : S -> Cost.t (S + R)) (I : S -> Prop)
    (Q : R -> Prop) (measure : S -> nat) fuel s :
  (forall s, I s ->
    match Cost.value (step s) with
    | inl h => I h /\ (measure h < measure s)%nat
    | inr r => Q r
    end) ->
  I s -> (measure s < Pos.to_nat fuel)%nat ->
  exists r, Cost.value (iterate step fuel s) = inr r /\ Q r.
Proof.
  intros Hstep HI Hfuel.
  pose proof (run_progress step I Q measure Hstep _ _ _ (iterate_value step fuel s) HI) as Hrun.
  destruct (Cost.value (iterate step fuel s)) as [h|r] eqn:Hresult.
  - destruct Hrun as [Hh Hbound]; lia.
  - eauto.
Qed.

(** A terminal first callback is the result of any positive-fuel driver call. *)
Theorem iterate_immediate {S R} (step : S -> Cost.t (S + R)) fuel s r :
  Cost.value (step s) = inr r -> Cost.value (iterate step fuel s) = inr r.
Proof.
  intro Hstop; pose proof (iterate_value step fuel s) as Hrun.
  inversion Hrun as [s'|n s' r' Hfirst|n s' h result Hnext Hrest]; subst.
  - pose proof (Pos2Nat.is_pos fuel); lia.
  - congruence.
  - congruence.
Qed.

End EggIndex.
