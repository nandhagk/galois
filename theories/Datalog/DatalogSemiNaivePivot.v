(** * Exact occurrence-pivot firing

    A cached job reads its selected occurrence from the frontier and all others from current.
    For example, one newly enabled premise supplies the matching job even in a nonlinear rule.
    Builds on: DatalogSemiNaiveReady and public Join firing exactness. *)

From Stdlib Require Import List Bool PeanoNat Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeSet.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogRelation DatalogFire
  DatalogJoin DatalogJoinProof DatalogSolve DatalogSemiNaive DatalogSemiNaiveSyntax
  DatalogSemiNaiveIndex DatalogSemiNaiveReady.
Import List.ListNotations SemiNaive SemiNaiveSyntax SemiNaiveIndex SemiNaiveReady.
Local Open Scope nat_scope.

Module SemiNaivePivot.

(** Body satisfaction fixes the positive and negative tuple observations at one environment. *)
Definition body_holds {P} (r : rule P) (env : P -> relation) sigma :=
  (forall a, In (LPos a) (body r) -> member (map (inst sigma) (args a)) (env (pred a)) = true) /\
  (forall a, In (LNeg a) (body r) -> member (map (inst sigma) (args a)) (env (pred a)) = false).

(** Tagged firing is source valuation satisfaction at the exact selected occurrence positions. *)
Theorem variant_exact {P} (prog : program P) (r : rule P) pivot
    (env : P * bool -> Cost.t relation) (plan : Join.plan_state (P * bool)) :
  safe_rule r ->
  JoinProof.ready [] (positive_atoms (body (tag_rule r pivot))) env plan ->
  forall row, member row (Join.fire (tag_rule r pivot) env plan) = true <->
  exists sigma, row = map (inst sigma) (args (head r)) /\
    (forall i a, In (i, a) (occurrences 0 (body r)) ->
      member (map (inst sigma) (args a)) (Cost.value (env (pred a, Nat.eqb i pivot))) = true) /\
    (forall a, In (LNeg a) (body r) ->
      member (map (inst sigma) (args a)) (Cost.value (env (pred a, false))) = false).
Proof.
  intros Hsafe Hplan row.
  rewrite (JoinProof.join_fire_exact (tag_program prog) _ env plan Hplan
    (tagged_safe r pivot Hsafe) row).
  rewrite tag_rule_equation; cbn [head body args]; split.
  - intros [sigma [Hrow [Hpos Hneg]]]; exists sigma; split; [exact Hrow | split].
    + intros i a Ha; apply (Hpos (Atom (pred a, Nat.eqb i pivot) (args a))).
      apply tagged_positive; exists i, a; auto.
    + intros a Ha; apply (Hneg (Atom (pred a, false) (args a))).
      apply tagged_negative; exists a; auto.
  - intros [sigma [Hrow [Hpos Hneg]]]; exists sigma; split; [exact Hrow | split].
    + intros a Ha; apply tagged_positive in Ha as [i [source [Hsource ->]]].
      apply Hpos, Hsource.
    + intros a Ha; apply tagged_negative in Ha as [source [Hsource ->]].
      apply Hneg, Hsource.
Qed.

Section Pivots.
Context {P : Type} (prog : program P) (HE : encoding_laws (penc prog))
  (st : stratification P) (lower : P -> Cost.t relation) (k : nat).
Local Abbreviation E := (ground_encoding prog).
Local Abbreviation GE := (ground_encoding_laws prog HE).
Local Abbreviation env s := (current prog st k lower (accumulated_index s)).
Local Abbreviation tenv s :=
  (tagged_c prog st k lower (accumulated_index s) (frontier_index s)).

Lemma job_exists s r i :
  ready prog st lower k s -> In r (rules prog) -> level st (pred (head r)) = k ->
  In i (pivots st k r) ->
  exists j, In j (jobs s) /\ source_rule j = r /\ pivot j = i.
Proof.
  intros Hready Hr Hl Hi.
  assert (Hin : In (r, i) (snd (classify st k (rules prog)))) by
    (apply classify_jobs; auto).
  rewrite <- (job_specs _ _ _ _ _ Hready) in Hin.
  apply in_map_iff in Hin as [j [Heq Hj]].
  injection Heq as Hsource Hpivot; exists j; auto.
Qed.

Lemma pivot_level r i a :
  In i (pivots st k r) -> In (i, a) (occurrences 0 (body r)) -> level st (pred a) = k.
Proof.
  intros Hi Ha; apply (pivots_from_spec st k 0 (body r) i) in Hi as [source [Hsource Hl]].
  pose proof (occurrence_unique 0 (body r) i a source Ha Hsource) as ->; exact Hl.
Qed.

Lemma tagged_positive_current s j i a row :
  ready prog st lower k s -> In j (jobs s) ->
  In (i, a) (occurrences 0 (body (source_rule j))) ->
  member row (Cost.value (tenv s (pred a, Nat.eqb i (pivot j)))) = true ->
  member row (env s (pred a)) = true.
Proof.
  intros Hready Hj Ha Hmem.
  change (member row
    (tagged prog st k lower (accumulated_index s) (frontier_index s)
      (pred a, Nat.eqb i (pivot j))) = true) in Hmem.
  rewrite tagged_equation in Hmem; destruct (Nat.eqb i (pivot j)) eqn:Hi; [|exact Hmem].
  apply Nat.eqb_eq in Hi; subst i.
  pose proof (pivot_level _ _ a (proj2 (proj2
    (job_member prog st lower k s j Hready Hj))) Ha) as Hl.
  rewrite current_equation, Hl, Nat.eqb_refl.
  rewrite (accumulated_exact _ _ _ _ _ Hready).
  apply (frontier_subset _ _ _ _ _ Hready).
  rewrite <- (frontier_exact _ _ _ _ _ Hready); exact Hmem.
Qed.

(** A satisfied body with a selected frontier premise is emitted by an actual cached pivot job. *)
Theorem candidates_cover s r sigma i a :
  ready prog st lower k s -> In r (rules prog) -> level st (pred (head r)) = k ->
  safe_rule r -> In (i, a) (occurrences 0 (body r)) -> level st (pred a) = k ->
  body_holds r (env s) sigma ->
  FinSet.mem E (ground sigma a) (frontier s) = true ->
  FinSet.mem E (ground sigma (head r)) (candidates prog st lower k s) = true.
Proof.
  intros Hready Hr Hl Hsafe Ha Halevel [Hpos Hneg] Hfront.
  assert (Hi : In i (pivots st k r)).
  { apply (pivots_from_spec st k 0 (body r) i); exists a; auto. }
  destruct (job_exists s r i Hready Hr Hl Hi) as [j [Hj [Hsource Hpivot]]].
  destruct (job_layout _ _ _ _ _ Hready j Hj) as [Htag Hplan].
  rewrite Hsource, Hpivot in Htag; rewrite Htag in Hplan.
  rewrite candidates_equation; apply (mem_of_list E GE), in_flat_map.
  exists j; split; [exact Hj |].
  apply in_map_iff; exists (map (inst sigma) (args (head r))); split.
  - rewrite Hsource; reflexivity.
  - apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws);
      [exact (proj2_sig (Join.fire (tagged_rule j) (tenv s) (plan j))) |].
    change (member (map (inst sigma) (args (head r)))
      (Join.fire (tagged_rule j) (tenv s) (plan j)) = true).
    rewrite Htag; apply (proj2 (variant_exact prog r i (tenv s) (plan j) Hsafe Hplan _)).
    exists sigma; split; [reflexivity | split].
    + intros position source Hocc.
      change (member (map (inst sigma) (args source))
        (tagged prog st k lower (accumulated_index s) (frontier_index s)
          (pred source, Nat.eqb position i)) = true).
      rewrite tagged_equation; destruct (Nat.eqb position i) eqn:Hsame.
      * apply Nat.eqb_eq in Hsame; subst position.
        pose proof (occurrence_unique 0 (body r) i source a Hocc Ha) as ->.
        rewrite (frontier_exact _ _ _ _ _ Hready); exact Hfront.
      * apply Hpos, (proj1 (occurrences_spec 0 (body r) source)); exists position; exact Hocc.
    + intros source Hnegative; exact (Hneg source Hnegative).
Qed.

(** Actual candidate membership supplies a source rule and a body valuation in the current rows. *)
Theorem candidates_satisfy s :
  ready prog st lower k s ->
  (forall r, In r (rules prog) -> safe_rule r) ->
  forall f, FinSet.mem E f (candidates prog st lower k s) = true ->
  exists r sigma, In r (rules prog) /\ level st (pred (head r)) = k /\
    f = ground sigma (head r) /\ body_holds r (env s) sigma.
Proof.
  intros Hready Hsafe f Hf; rewrite candidates_equation in Hf.
  apply (mem_of_list E GE) in Hf; apply in_flat_map in Hf as [j [Hj Hrow]].
  apply in_map_iff in Hrow as [row [<- Hrow]].
  apply (FinSet.elements_spec tuple_encoding tuple_encoding_laws) in Hrow;
    [|exact (proj2_sig (Join.fire (tagged_rule j) (tenv s) (plan j)))].
  destruct (job_member prog st lower k s j Hready Hj) as [Hr [Hl Hi]].
  destruct (job_layout _ _ _ _ _ Hready j Hj) as [Htag Hplan].
  change (member row (Join.fire (tagged_rule j) (tenv s) (plan j)) = true) in Hrow.
  rewrite Htag in Hrow, Hplan.
  apply (proj1 (variant_exact prog _ _ (tenv s) (plan j) (Hsafe _ Hr) Hplan row)) in Hrow
    as [sigma [Hrow [Hpos Hneg]]].
  exists (source_rule j), sigma; split; [exact Hr | split; [exact Hl | split]].
  - unfold ground; rewrite Hrow; reflexivity.
  - split; [|exact Hneg]; intros a Ha.
    destruct (proj2 (occurrences_spec 0 (body (source_rule j)) a) Ha) as [i Hocc].
    exact (tagged_positive_current s j i a _ Hready Hj Hocc (Hpos i a Hocc)).
Qed.

End Pivots.

End SemiNaivePivot.
Import SemiNaivePivot.
