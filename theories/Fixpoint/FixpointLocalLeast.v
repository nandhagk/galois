(** * Agreement of local and global least solutions

    A declared-closed restriction has the same least values as the global system in its region.
    For example, an unrelated constraint cannot change the least value of a cyclic root.
    Builds on: FixpointLocalProof, FixpointTotal and query determinacy. *)

From Stdlib Require Import List Bool Arith Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointIndex FixpointAnalysis FixpointSolver FixpointTotal FixpointLocal FixpointLocalProof.
Import List.ListNotations.

Module LocalLeast.

(** Restriction retains all dictionary and summary laws of the original analysis. *)
Theorem restriction_laws {X C A} (a : Analysis.t X C A) cs :
  Analysis.laws a -> Analysis.laws (Local.restrict a cs).
Proof.
  intro HL; constructor.
  - exact (Analysis.key_laws HL).
  - exact (Analysis.row_laws HL).
  - exact (Analysis.lattice_law HL).
  - constructor.
    + exact (System.reads_within (Analysis.static_law HL)).
    + exact (System.sides_within (Analysis.static_law HL)).
Qed.

Local Lemma selected_member {X C A} (a : Analysis.t X C A) r c :
  In c (Local.rows a r) <->
    In c (System.constraints (Analysis.system a)) /\
    FinSet.mem (Analysis.row_enc a) c (Local.selected r) = true.
Proof.
  unfold Local.rows, Local.rows_c; rewrite value_filter_c, filter_In; reflexivity.
Qed.

Local Lemma solved_eq {X A R} (s t : R) :
  @Outcome.Solved X A R s = Outcome.Solved t -> s = t.
Proof.
  congruence.
Qed.

(** Successful local solving returns the assignment of its actual discovered restriction. *)
Theorem local_run_result {X C A} (a : Analysis.t X C A) HT roots fuel result :
  Local.run a HT roots fuel = Outcome.Solved result ->
  exists r,
    Cost.value (Local.discover_indexed_c a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel) =
      inr r /\
    result = Local.Result (Local.unknowns r)
      (Total.run (Local.restrict a (Local.rows a r))
        (Local.restriction_termination a HT (Local.rows a r) (Local.rows_incl a r))).
Proof.
  rewrite Local.run_equation, Local.run_indexed_equation.
  destruct (Cost.value (Local.discover_indexed_c a
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel))
    as [state|r] eqn:Hdiscovered; [discriminate|].
  intro Hresult; apply solved_eq in Hresult; exists r; split; [reflexivity|symmetry; exact Hresult].
Qed.

Section Agreement.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  (HT : Terminates.t a) (HJ : lub_laws (Analysis.lat a))
  (HM : monotone_system (Analysis.lat a) (Analysis.system a))
  (r : Local.region X C) (roots : list X).

Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let L := Analysis.lat a.
Let S := Analysis.system a.
Let SS := Analysis.static a.
Let ix := index_system EX S SS.
Let E := Local.unknowns r.
Let local_a := Local.restrict a (Local.rows a r).
Let local_HT := Local.restriction_termination a HT (Local.rows a r) (Local.rows_incl a r).
Let small := lookup EX L (Total.run local_a local_HT).
Let global := lookup EX L (Total.run a HT).

Hypothesis Hclosed : LocalProof.closed a ix roots r.

Local Lemma small_post : post_solution L (Analysis.system local_a) small.
Proof.
  exact (Total.total_post local_a (restriction_laws a _ HL) local_HT).
Qed.

Local Lemma global_least : least_solution L S global.
Proof.
  exact (Total.total_least a HL HT HJ HM).
Qed.

Local Lemma restricted_monotone : monotone_system L (Analysis.system local_a).
Proof.
  intros c Hc; apply HM, (Local.rows_incl a r), Hc.
Qed.

Local Lemma global_restricted : post_solution L (Analysis.system local_a) global.
Proof.
  intros c Hc; exact (proj1 global_least c (Local.rows_incl a r c Hc)).
Qed.

Local Lemma small_below : fun_leb L small global.
Proof.
  pose proof (Total.total_least local_a (restriction_laws a _ HL) local_HT HJ
    restricted_monotone) as Hleast.
  exact (proj2 Hleast global global_restricted).
Qed.

Definition patched x := if FinSet.mem EX x E then small x else global x.

Local Lemma selected_agreement c :
  In c (Local.rows a r) ->
  Query.eval (System.rhs S c) small = Query.eval (System.rhs S c) patched /\
  Query.reads (System.rhs S c) small = Query.reads (System.rhs S c) patched /\
  Query.sides (System.rhs S c) small = Query.sides (System.rhs S c) patched.
Proof.
  intro Hc; apply Query.query_determined.
  intros x Hread; unfold patched.
  destruct Hclosed as [_ [_ Houtputs]].
  assert (Hx : FinSet.mem EX x E = true).
  { apply (Houtputs c (proj2 (proj1 (selected_member a r c) Hc)) x).
    right; apply in_or_app; right.
    exact (System.reads_within (Analysis.static_law HL) c small x Hread). }
  rewrite Hx; reflexivity.
Qed.

Local Lemma touching_selected c x :
  In c (System.constraints S) -> FinSet.mem EX x E = true ->
  System.target S c = x \/ In x (side_targets SS c) ->
  In c (Local.rows a r).
Proof.
  intros Hc Hx Hout; apply selected_member; split; [exact Hc|].
  destruct Hclosed as [_ [Hcontributors _]].
  apply (Hcontributors x c Hx).
  apply (contributors_agree (index_system_laws EX (Analysis.key_laws HL) S SS)); now split.
Qed.

Local Lemma patched_post : post_solution L S patched.
Proof.
  intros c Hc; split.
  - destruct (FinSet.mem EX (System.target S c) E) eqn:Htarget.
    + assert (Hselected : In c (Local.rows a r)).
      { apply (touching_selected c (System.target S c) Hc Htarget); now left. }
      destruct (selected_agreement c Hselected) as [Heval _].
      rewrite <- Heval; unfold patched; rewrite Htarget.
      exact (proj1 (small_post c Hselected)).
    + (* A nonselected target keeps its global value; selected rows stay wholly inside. *)
      destruct (FinSet.mem EC c (Local.selected r)) eqn:Hselected.
      * destruct Hclosed as [_ [_ Houtputs]].
        pose proof (Houtputs c Hselected (System.target S c) (or_introl eq_refl)) as Hbad.
        fold EX S E in Hbad; rewrite Htarget in Hbad; discriminate.
      * assert (Hsame : Query.eval (System.rhs S c) patched =
          Query.eval (System.rhs S c) global \/
          leb L (Query.eval (System.rhs S c) patched) (global (System.target S c)) = true).
        { right.
          destruct (HM c Hc) as [Hvalue _].
          eapply (leb_trans (Analysis.lattice_law HL)).
          - apply Hvalue; intro x; unfold patched; destruct (FinSet.mem EX x E).
            + apply small_below.
            + apply (leb_refl (Analysis.lattice_law HL)).
          - exact (proj1 (proj1 global_least c Hc)). }
        unfold patched at 2; rewrite Htarget.
        destruct Hsame as [->|Hsafe]; [exact (proj1 (proj1 global_least c Hc))|exact Hsafe].
  - intros x b Hside; destruct (FinSet.mem EX x E) eqn:Hx.
    + assert (Hselected : In c (Local.rows a r)).
      { apply (touching_selected c x Hc Hx); right.
        apply (System.sides_within (Analysis.static_law HL) c patched).
        apply in_map_iff; exists (x, b); split; [reflexivity|exact Hside]. }
      destruct (selected_agreement c Hselected) as [_ [_ Hsides]].
      rewrite <- Hsides in Hside; unfold patched; rewrite Hx.
      exact (proj2 (small_post c Hselected) x b Hside).
    + destruct (HM c Hc) as [_ Hsides].
      assert (Hbelow : fun_leb L patched global).
      { intro y; unfold patched; destruct (FinSet.mem EX y E).
        - apply small_below.
        - apply (leb_refl (Analysis.lattice_law HL)). }
      destruct (Hsides patched global Hbelow x b Hside) as [d [Hd Hbd]].
      unfold patched; rewrite Hx.
      eapply (leb_trans (Analysis.lattice_law HL)); [exact Hbd|].
      exact (proj2 (proj1 global_least c Hc) x d Hd).
Qed.

(** Closed restricted least values agree with global least values throughout the region. *)
Theorem region_least x :
  FinSet.mem EX x E = true -> leb L (small x) (global x) = true /\
    leb L (global x) (small x) = true.
Proof.
  intro Hx; split; [apply small_below|].
  pose proof (proj2 global_least patched patched_post x) as Hle.
  unfold patched in Hle; rewrite Hx in Hle; exact Hle.
Qed.

End Agreement.

(** Successful local solving agrees with the global least solution at every requested root. *)
Theorem local_least {X C A} (a : Analysis.t X C A) HT roots fuel result :
  Analysis.laws a -> lub_laws (Analysis.lat a) ->
  monotone_system (Analysis.lat a) (Analysis.system a) ->
  Local.run a HT roots fuel = Outcome.Solved result ->
  forall x, In x roots ->
    leb (Analysis.lat a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values result) x)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Total.run a HT) x) = true /\
    leb (Analysis.lat a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Total.run a HT) x)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values result) x) = true.
Proof.
  intros HL HJ HM Hrun x Hx.
  destruct (local_run_result a HT roots fuel result Hrun) as [r [Hdiscovered ->]].
  destruct (LocalProof.local_discover_closed a _ roots fuel r HL Hdiscovered)
    as [_ [_ Hclosed]].
  apply (region_least a HL HT HJ HM r roots Hclosed x).
  exact (proj1 Hclosed x Hx).
Qed.

End LocalLeast.
Import LocalLeast.
