(** * Finite read-incidence credits

    Queue length and unused height credits bound every continuation transition.
    For example, a changed unknown pays for one enqueue attempt per indexed reader occurrence.
    Builds on: FixpointTotalInvariant and the public index occurrence theorem. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointIndex FixpointAnalysis
  FixpointTotalQueue FixpointTotalKernel FixpointTotalInvariant.
Import List.ListNotations.

Module TotalPotential.

Fixpoint sum {B} (f : B -> nat) (xs : list B) : nat :=
  match xs with
  | [] => O
  | x :: rest => (f x + sum f rest)%nat
  end.

Local Lemma sum_le {B} f g (xs : list B) :
  (forall x, In x xs -> f x <= g x)%nat -> (sum f xs <= sum g xs)%nat.
Proof.
  intro Hle; induction xs as [|x xs IH]; cbn [sum]; [lia|].
  specialize (IH (fun y Hy => Hle y (or_intror Hy))).
  specialize (Hle x (or_introl eq_refl)); lia.
Qed.

Local Lemma sum_constant {B} (xs : list B) n : sum (fun _ => n) xs = (length xs * n)%nat.
Proof.
  induction xs as [|x xs IH]; cbn [sum length]; lia.
Qed.

Local Lemma sum_app {B} f (xs ys : list B) :
  sum f (xs ++ ys) = (sum f xs + sum f ys)%nat.
Proof.
  induction xs as [|x xs IH]; cbn [sum app]; lia.
Qed.

Definition count {X} (EX : encoding X) x xs :=
  sum (fun y => if eqb EX y x then 1%nat else O) xs.

Local Lemma count_positive {X} EX (HE : encoding_laws EX) x (xs : list X) :
  In x xs -> (1 <= count EX x xs)%nat.
Proof.
  induction xs as [|y xs IH]; intro Hin; [contradiction|].
  cbn [count sum] in *; destruct Hin as [<-|Hin].
  - rewrite eqb_refl; lia.
  - specialize (IH Hin); unfold count in IH; destruct (eqb EX y x); lia.
Qed.

Local Lemma reader_incidence_bound {X C A} EX (HE : encoding_laws EX)
    (S : System.t X C A) SS x :
  (length (readers_of EX (index_system EX S SS) x) <=
    count EX x (flat_map (deps SS) (System.constraints S)))%nat.
Proof.
  rewrite readers_occurrences by exact HE.
  induction (System.constraints S) as [|c cs IH]; cbn [filter flat_map length count sum].
  - lia.
  - unfold count in *; rewrite sum_app.
    destruct (existsb (eqb EX x) (deps SS c)) eqn:Hseen; cbn [length].
    + apply existsb_exists in Hseen as [y [Hy Hsame]].
      apply (eqb_true_iff EX HE) in Hsame; subst y.
      pose proof (count_positive EX HE x (deps SS c) Hy); unfold count in *; lia.
    + lia.
Qed.

Section Potential.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a).

Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let SS := Analysis.static a.
Let ix := index_system EX S SS.
Let HI := index_system_laws EX (Analysis.key_laws HL) S SS.
Let R := Terminates.hgt HT.

(** Duplicate-preserving declared reads form the finite domain of the height potential. *)
Definition credit (m : assignment X A) : nat :=
  sum (fun x => (bound R - rank R (lookup EX L m x))%nat) (TotalKernel.read_keys a).

(** Pending rows add one credit each to the unused read-incidence height. *)
Definition potential (s : TotalKernel.state X C A) : nat :=
  (length (TotalQueue.pending (TotalKernel.queue s)) + credit (TotalKernel.current s))%nat.

Local Lemma credit_bound m :
  (credit m <= length (TotalKernel.read_keys a) * bound R)%nat.
Proof.
  unfold credit; rewrite <- sum_constant; apply sum_le; intros; lia.
Qed.

Local Lemma rule_credit m x b :
  TotalInvariant.good a HT m -> Terminates.inv HT b ->
  snd (Update.rule EX L (join_c L) m x b) = true ->
  (credit (fst (Update.rule EX L (join_c L) m x b)) +
    count EX x (TotalKernel.read_keys a) <= credit m)%nat.
Proof.
  intros [Hwf Hinv] Hb Hchange.
  assert (Hfalse : leb L b (lookup EX L m x) = false).
  { pose proof (proj1 (Update.rule_spec EX L (join_c L) m x b Hwf)) as Hflag.
    rewrite Hchange in Hflag; destruct (leb L b (lookup EX L m x)); cbn in Hflag;
      congruence. }
  assert (Hstrict : leb L (join L (lookup EX L m x) b) (lookup EX L m x) = false).
  { destruct (leb L (join L (lookup EX L m x) b) (lookup EX L m x)) eqn:Htest;
      [|reflexivity].
    pose proof (leb_trans (Analysis.lattice_law HL) _ _ _
      (join_upper_r (Analysis.lattice_law HL) _ _) Htest) as Hbad.
    fold L in Hbad; rewrite Hfalse in Hbad; discriminate. }
  pose proof (join_rank_grows R (lookup EX L m x) b (Hinv x) Hb Hstrict) as Hgrow.
  pose proof (rank_bounded R (join L (lookup EX L m x) b)
    (Terminates.inv_join HT _ _ (Hinv x) Hb)) as Hbound.
  change (rank R (lookup EX L m x) < rank R (join L (lookup EX L m x) b))%nat in Hgrow.
  unfold credit, count.
  assert (Hpoint : forall y,
    (bound R - rank R (lookup EX L (fst (Update.rule EX L (join_c L) m x b)) y) +
      (if eqb EX y x then 1%nat else O) <= bound R - rank R (lookup EX L m y))%nat).
  { intro y; rewrite (proj2 (Update.rule_spec EX L (join_c L) m x b Hwf)), Hfalse.
    destruct (eqb EX y x) eqn:Hsame; [|lia].
    apply (eqb_true_iff EX (Analysis.key_laws HL)) in Hsame; subst y.
    rewrite <- join_equation; lia. }
  induction (TotalKernel.read_keys a) as [|y ys IH]; cbn [sum]; [lia|].
  specialize (Hpoint y); lia.
Qed.

(** Every output's reader insertions are paid for by that unknown's height decrease. *)
Theorem update_potential s x b :
  TotalInvariant.good a HT (TotalKernel.current s) ->
  Terminates.inv HT b ->
  (potential (TotalKernel.update a ix s (x, b)) <= potential s)%nat.
Proof.
  intros Hg Hb; rewrite TotalKernel.update_equation; cbn [fst snd].
  fold EX EC L.
  set (r := Update.rule EX L (join_c L) (TotalKernel.current s) x b).
  destruct (snd r) eqn:Hchange.
  - pose proof (TotalQueue.push_many_length EC (readers_of EX ix x)
      (TotalKernel.queue s)) as Hqueue.
    pose proof (rule_credit _ x b Hg Hb Hchange) as Hcredit.
    pose proof (reader_incidence_bound EX (Analysis.key_laws HL) S SS x) as Hreaders.
    assert (Hreaders' : (length (readers_of EX ix x) <=
      count EX x (TotalKernel.read_keys a))%nat).
    { rewrite TotalKernel.read_keys_equation; exact Hreaders. }
    unfold potential; cbn [TotalKernel.current TotalKernel.queue]; unfold r.
    change (length (TotalQueue.pending
      (TotalQueue.push_many EC (readers_of EX ix x) (TotalKernel.queue s))) +
      credit (fst (Update.rule EX L (join_c L) (TotalKernel.current s) x b)) <=
      length (TotalQueue.pending (TotalKernel.queue s)) +
        credit (TotalKernel.current s))%nat.
    lia.
  - pose proof (Update.rule_unchanged EX L (join_c L)
      (TotalKernel.current s) x b Hchange) as Hsame.
    unfold potential; cbn [TotalKernel.current TotalKernel.queue]; unfold r.
    rewrite Hsame; lia.
Qed.

(** Ordered outputs cannot increase the combined pending-row and incidence potential. *)
Theorem updates_potential outs s :
  TotalInvariant.good a HT (TotalKernel.current s) ->
  TotalQueue.wf EC (TotalKernel.queue s) ->
  incl (TotalQueue.pending (TotalKernel.queue s)) (System.constraints S) ->
  (forall x b, In (x, b) outs -> Terminates.inv HT b) ->
  (potential (TotalKernel.updates a ix outs s) <= potential s)%nat.
Proof.
  revert s; induction outs as [|[x b] outs IH]; intros s Hg Hq Hlisted Houts;
    rewrite TotalKernel.updates_equation; [lia|].
  destruct (TotalInvariant.update_good a HL HT ix HI s x b Hg Hq Hlisted
    (Houts x b (or_introl eq_refl))) as [Hg' [Hq' [Hlisted' Hle]]].
  specialize (IH _ Hg' Hq' Hlisted' (fun y d Hd => Houts y d (or_intror Hd))).
  pose proof (update_potential s x b Hg (Houts x b (or_introl eq_refl))); lia.
Qed.

(** Every continuation removes one pending occurrence before paid reader reinsertions. *)
Theorem step_decreases s t :
  TotalInvariant.invariant a HT s ->
  TotalKernel.step a ix s = inl t -> (potential t < potential s)%nat.
Proof.
  intros [Hg [Hq [Hlisted Hvalid]]] Hstep.
  rewrite TotalKernel.step_equation in Hstep.
  fold EX EC L S SS in Hstep.
  destruct (TotalQueue.pop EC (TotalKernel.queue s)) as [[c rest]|] eqn:Hpop;
    [|discriminate].
  apply TotalKernel.continuing_eq in Hstep; subst t.
  destruct (TotalQueue.pop_spec EC (Analysis.row_laws HL) _ _ c Hq Hpop) as [Hr Hqueue].
  assert (Hc : In c (System.constraints S)).
  { apply Hlisted; rewrite Hqueue; now left. }
  assert (Hrest : incl (TotalQueue.pending rest) (System.constraints S)).
  { intros d Hd; apply Hlisted; rewrite Hqueue; now right. }
  pose proof (updates_potential
    (fst (Eval.outputs S c (lookup EX L (TotalKernel.current s))))
    (TotalKernel.State (TotalKernel.current s) rest) Hg Hr Hrest
    (fun x b Hb => Terminates.inv_closed HT _ (proj2 Hg) c Hc (x, b) Hb)) as Hpotential.
  unfold potential in *; cbn [TotalKernel.current TotalKernel.queue] in *.
  rewrite Hqueue; cbn [length]; lia.
Qed.

(** The initial potential is bounded by rows plus height times declared read occurrences. *)
Theorem initial_bound :
  (potential (TotalKernel.initial a) <=
    length (System.constraints S) + bound R * length (TotalKernel.read_keys a))%nat.
Proof.
  rewrite TotalKernel.initial_equation; unfold potential.
  cbn [TotalKernel.current TotalKernel.queue].
  pose proof (TotalQueue.push_many_length EC (System.constraints S) TotalQueue.empty).
  pose proof (credit_bound (@Map.empty X A)).
  cbn [TotalQueue.empty TotalQueue.pending length] in *.
  change (length (TotalQueue.pending
    (TotalQueue.push_many EC (System.constraints S) TotalQueue.empty)) +
    credit (@Map.empty X A) <=
    length (System.constraints S) + bound R * length (TotalKernel.read_keys a))%nat.
  lia.
Qed.

End Potential.

End TotalPotential.
Import TotalPotential.
