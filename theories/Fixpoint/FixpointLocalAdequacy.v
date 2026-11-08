(** * Successful checked local outcomes

    Lawful completed discovery produces a closed partial solution that the partial checker accepts.
    For example, adequate discovery fuel yields a solved result even on a cyclic restricted system.
    Builds on: FixpointLocalLeast, FixpointLocalCost and FixpointPartial. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia Relations.Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointEval FixpointLeast
  FixpointIndex FixpointPartial FixpointAnalysis FixpointSolver FixpointTotal FixpointLocal
  FixpointLocalDiscover FixpointLocalProof FixpointLocalLeast FixpointLocalCost FixpointLocalCredit.
Import List.ListNotations.

Module LocalAdequacy.

(** Reconstructing a well-formed set from its canonical enumeration does not change the set. *)
Theorem normalize {X} EX (HE : encoding_laws EX) (E : FinSet.t X) :
  FinSet.wf EX E -> FinSet.of_list EX (FinSet.elements E) = E.
Proof.
  intro Hwf; apply (FinSet.ext EX HE); [apply FinSet.wf_of_list|exact Hwf|].
  intro x; apply Bool.eq_true_iff_eq.
  rewrite FinSet.mem_of_list, existsb_exists.
  split.
  - intros [y [Hy Hsame]]; apply (eqb_true_iff EX HE) in Hsame; subst y.
    apply (FinSet.elements_spec EX HE x E Hwf), Hy.
  - intro Hx; exists x; split; [apply (FinSet.elements_spec EX HE x E Hwf), Hx|apply eqb_refl].
Qed.

(** Successful local production gives a well-formed closed partial solution covering roots. *)
Theorem local_run_partial {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel candidate :
  Local.run a HT roots fuel = Outcome.Solved candidate ->
  FinSet.wf (Analysis.key_enc a) (Local.explored candidate) /\
  closed_partial (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (Analysis.static a) (Local.explored candidate)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values candidate)) /\
  forall x, In x roots -> FinSet.mem (Analysis.key_enc a) x (Local.explored candidate) = true.
Proof.
  intro Hrun; destruct (LocalLeast.local_run_result a HT roots fuel candidate Hrun)
    as [r [Hdiscovered ->]].
  destruct (LocalProof.local_discover_closed a _ roots fuel r HL Hdiscovered)
    as [Hwf [_ [Hroots [Hcontributors Hmetadata]]]].
  split; [exact Hwf|]; split; [|exact Hroots].
  intros c Hc [x [Hx Hout]].
  assert (Hselected : In c (Local.rows a r)).
  { apply Local.rows_spec; split; [exact Hc|].
    apply (Hcontributors x c Hx).
    apply (contributors_agree (index_system_laws _ (Analysis.key_laws HL) _ _)); now split. }
  set (small := Local.restrict a (Local.rows a r)).
  set (small_HT := Local.restriction_termination a HT (Local.rows a r) (Local.rows_incl a r)).
  pose proof (Total.total_post small (LocalLeast.restriction_laws a _ HL) small_HT) as Hpost.
  split.
  - intros y Hy; rewrite Eval.outputs_spec in Hy; cbn [snd] in Hy.
    apply (Hmetadata c (proj2 (proj1 (Local.rows_spec a r c) Hselected)) y).
    right; apply in_or_app; right.
    exact (System.reads_within (Analysis.static_law HL) c _ y Hy).
  - intros y v Hv _; rewrite Eval.outputs_spec in Hv; cbn [fst] in Hv.
    destruct (Hpost c Hselected) as [Hprimary Hsides].
    destruct Hv as [Heq|Hv].
    + injection Heq as <- <-; exact Hprimary.
    + exact (Hsides y v Hv).
Qed.

(** A lawful partial candidate covering roots is accepted without changing its fields. *)
Theorem check_accepts {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    ix roots candidate :
  sys_index_laws (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) ix ->
  FinSet.wf (Analysis.key_enc a) (Local.explored candidate) ->
  closed_partial (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (Analysis.static a) (Local.explored candidate)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values candidate)) ->
  (forall x, In x roots -> FinSet.mem (Analysis.key_enc a) x (Local.explored candidate) = true) ->
  Local.check a ix roots candidate = Outcome.Solved candidate.
Proof.
  intros HI Hwf Hpartial Hroots; rewrite Local.check_equation.
  rewrite (normalize _ (Analysis.key_laws HL) _ Hwf).
  assert (Hp : check_partial (Analysis.key_enc a) (Analysis.row_enc a) (Analysis.lat a)
    (Analysis.system a) (Analysis.static a) ix (Local.explored candidate)
    (Local.values candidate) = true).
  { apply (check_partial_correct _ _ (Analysis.key_laws HL) (Analysis.row_laws HL)
      _ _ _ _ _ _ HI Hwf), Hpartial. }
  assert (Hr : forallb (fun x => FinSet.mem (Analysis.key_enc a) x
    (Local.explored candidate)) roots = true) by (apply forallb_forall, Hroots).
  cbn zeta; rewrite Hp, Hr; destruct candidate; reflexivity.
Qed.

(** Every successful lawful local run passes the partial gate with the same candidate. *)
Theorem local_checked_matches {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel candidate :
  Local.run a HT roots fuel = Outcome.Solved candidate ->
  Local.checked a HT roots fuel = Outcome.Solved candidate.
Proof.
  intro Hrun; rewrite Local.checked_equation, Hrun.
  destruct (local_run_partial a HL HT roots fuel candidate Hrun) as [Hwf [Hpartial Hroots]].
  apply (check_accepts a HL); [apply index_system_laws, Analysis.key_laws, HL|
    exact Hwf|exact Hpartial|exact Hroots].
Qed.

(** A finite support-incidence threshold yields an actual checked solved outcome. *)
Theorem local_checked_adequate {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel :
  (N.of_nat (length roots) +
    LocalCredit.sum (LocalCredit.weight (LocalDiscover.adjacent_c a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a))))
      (LocalCost.support a roots) < N.pos fuel)%N ->
  exists candidate, Local.checked a HT roots fuel = Outcome.Solved candidate.
Proof.
  intro Hfuel.
  destruct (LocalCost.local_discover_adequate a HL roots fuel Hfuel) as [marked Hraw].
  assert (Hdiscovered : Cost.value (Local.discover_indexed_c a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel) =
    inr (Local.project (Analysis.key_enc a) (Analysis.row_enc a) marked)).
  { unfold Local.discover_indexed_c; rewrite Cost.value_bind.
    fold (LocalDiscover.run a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel).
    rewrite Hraw, Cost.value_map; reflexivity. }
  eexists; apply (local_checked_matches a HL).
  rewrite Local.run_equation, Local.run_indexed_equation, Hdiscovered; reflexivity.
Qed.

(** Restriction raises are original-system raises because filtering keeps the same callbacks. *)
Theorem restriction_reached {X C A} (a : Analysis.t X C A) cs s :
  incl cs (System.constraints (Analysis.system a)) ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system (Local.restrict a cs)) s ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a) s.
Proof.
  intros Hsub [m [Hpath Hagrees]]; exists m; split; [|exact Hagrees].
  clear Hagrees.
  induction Hpath as [m n Hraise|m|m n p Hmn IHmn Hnp IHnp].
  - apply rt_step; destruct Hraise as [Hwf [c [Hc Hnext]]].
    split; [exact Hwf|]; exists c; split; [apply Hsub, Hc|].
    rewrite raise_equation in Hnext |- *; rewrite Local.restrict_outputs in Hnext.
    exact Hnext.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

(** Every successful local assignment is reached by original-system joins from bottom. *)
Theorem local_reached {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel candidate :
  Local.run a HT roots fuel = Outcome.Solved candidate ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values candidate)).
Proof.
  intro Hrun; destruct (LocalLeast.local_run_result a HT roots fuel candidate Hrun)
    as [r [_ ->]].
  apply (restriction_reached a (Local.rows a r)); [apply Local.rows_incl|].
  exact (Total.total_reached (Local.restrict a (Local.rows a r))
    (LocalLeast.restriction_laws a _ HL)
    (Local.restriction_termination a HT (Local.rows a r) (Local.rows_incl a r))).
Qed.

(** A lawful checked result is exactly its successful local producer result. *)
Theorem checked_producer {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel candidate :
  Local.checked a HT roots fuel = Outcome.Solved candidate ->
  Local.run a HT roots fuel = Outcome.Solved candidate.
Proof.
  intro Hchecked; pose proof Hchecked as Hout; rewrite Local.checked_equation in Hout.
  destruct (Local.run a HT roots fuel) as [r|have|why] eqn:Hrun; try discriminate.
  pose proof (local_checked_matches a HL HT roots fuel r Hrun) as Hsame.
  rewrite Hchecked in Hsame; injection Hsame as <-; reflexivity.
Qed.

(** The checked local map keeps original-system joining reachability. *)
Theorem local_checked_reached {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel candidate :
  Local.checked a HT roots fuel = Outcome.Solved candidate ->
  reached (Analysis.key_enc a) (Analysis.lat a) (Analysis.system a)
    (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values candidate)).
Proof.
  intro Hchecked; apply (local_reached a HL HT roots fuel).
  apply (checked_producer a HL), Hchecked.
Qed.

(** Checked root values agree with the global least solution under the original semantic laws. *)
Theorem local_checked_least {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel candidate :
  lub_laws (Analysis.lat a) -> monotone_system (Analysis.lat a) (Analysis.system a) ->
  Local.checked a HT roots fuel = Outcome.Solved candidate ->
  forall x, In x roots ->
    leb (Analysis.lat a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values candidate) x)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Total.run a HT) x) = true /\
    leb (Analysis.lat a)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Total.run a HT) x)
      (lookup (Analysis.key_enc a) (Analysis.lat a) (Local.values candidate) x) = true.
Proof.
  intros HJ HM Hchecked; apply (LocalLeast.local_least a HT roots fuel candidate HL HJ HM).
  apply (checked_producer a HL), Hchecked.
Qed.

End LocalAdequacy.
Import LocalAdequacy.
