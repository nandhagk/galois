(** * Numeric composition of local solving

    Local solving retains global preparation and filtering plus numeric work on the selected system.
    For example, a small discovered region still pays for the original row-list filter.
    Builds on: FixpointLocalCost and FixpointTotalProof. *)

From Stdlib Require Import List Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeHeight.
From Galois.Fixpoint Require Import FixpointSystem FixpointEval FixpointIndex FixpointIndexCost
  FixpointAnalysis FixpointLocal FixpointLocalProof FixpointLocalLeast FixpointLocalDiscover
  FixpointLocalCredit FixpointLocalCost FixpointTotalKernel FixpointTotalCost FixpointTotalProof.
Import Cost.Notations.
Local Open Scope N_scope.

Module LocalRunCost.

(** Primitive total-engine duties restrict through the actual filtered source membership. *)
Theorem restriction_model {X C A} (a : Analysis.t X C A) tb cs :
  TotalCost.model a tb -> incl cs (System.constraints (Analysis.system a)) ->
  TotalCost.model (Local.restrict a cs) tb.
Proof.
  intros HB Hsub; constructor.
  - constructor.
    + intros c Hc; exact (SystemIndexCost.key_budget (TotalCost.metadata_model HB) c (Hsub c Hc)).
    + intros c Hc; exact (SystemIndexCost.callback_budget (TotalCost.metadata_model HB) c
        (Hsub c Hc)).
    + intros c Hc; exact (SystemIndexCost.count_budget (TotalCost.metadata_model HB) c
        (Hsub c Hc)).
  - intros c Hc; exact (TotalCost.row_keys HB c (Hsub c Hc)).
  - exact (TotalCost.lattice_calls HB).
  - intros c Hc; exact (TotalCost.rhs_calls HB c (Hsub c Hc)).
  - intros c s Hc; exact (TotalCost.query_paths HB c s (Hsub c Hc)).
  - intros c s Hc; rewrite Local.restrict_outputs.
    exact (TotalCost.output_sizes HB c s (Hsub c Hc)).
Qed.

(** The original filter pays for a row-encoding and membership probe at every source occurrence. *)
Theorem filter_cost {X C A} (a : Analysis.t X C A) roots lb
    (HB : LocalCost.model a roots lb) r :
  Cost.ticks (Local.rows_c a r) <=
    N.of_nat (length (System.constraints (Analysis.system a))) *
      (2 + LocalCost.Budget.row_encoder lb + LocalCost.Budget.row_digits lb).
Proof.
  unfold Local.rows_c; rewrite ticks_filter_c.
  assert (Hpred : forall c, In c (System.constraints (Analysis.system a)) ->
    Cost.ticks (FinSet.mem_c (Analysis.row_enc a) c (Local.selected r)) <=
      1 + LocalCost.Budget.row_encoder lb + LocalCost.Budget.row_digits lb).
  { intros c Hc; destruct (LocalCost.row_keys HB c Hc) as [He Hw].
    rewrite FinSet.mem_cost; fold (key_bits (Analysis.row_enc a) c); lia. }
  induction (System.constraints (Analysis.system a)) as [|c cs IH];
    cbn [fold_right length]; [lia|].
  specialize (IH (fun d Hd => Hpred d (or_intror Hd))).
  specialize (Hpred c (or_introl eq_refl)); rewrite Nat2N.inj_succ; nia.
Qed.

(** Total numerical work on a discovered restriction uses its own actual row and read counts. *)
Definition restricted_budget {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) tb r :=
  let small := Local.restrict a (Local.rows a r) in
  let small_HT := Local.restriction_termination a HT (Local.rows a r) (Local.rows_incl a r) in
  let C := length (System.constraints (Analysis.system small)) in
  let D := length (TotalKernel.read_keys small) in
  let H := bound (Terminates.hgt small_HT) in
  TotalProof.setup tb C D H + (TotalCost.Budget.step tb C + 2) *
    (N.of_nat (C + H * D) + 1) + 2 * N.pos (Pos.size (TotalKernel.fuel small small_HT)).

(** Local budgets expose preparation, complete-support discovery and actual selected-system work. *)
Definition run_budget {X C A} (a : Analysis.t X C A) (HT : Terminates.t a) roots fuel lb tb :=
  let ix := index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a) in
  let U := LocalCost.support a roots in
  let C := length (System.constraints (Analysis.system a)) in
  SystemIndexCost.Budget.preparation (TotalCost.Budget.metadata tb) C +
    (LocalCost.Budget.w lb + 4) * N.of_nat (length roots) +
    (4 * LocalCost.Budget.w lb + 10) *
      LocalCredit.sum (LocalCredit.weight (LocalDiscover.adjacent_c a ix)) U +
    N.pos (Pos.size fuel) + LocalCost.Budget.projection lb (length U) +
    N.of_nat C * (2 + LocalCost.Budget.row_encoder lb + LocalCost.Budget.row_digits lb) +
    match Cost.value (Local.discover_indexed_c a ix roots fuel) with
    | inl _ => 0
    | inr r => restricted_budget a HT tb r
    end.

(** Primitive finite-domain budgets imply a complete numeric local-run bound for every outcome. *)
Theorem local_run_cost {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel lb tb :
  LocalCost.model a roots lb -> TotalCost.model a tb ->
  Cost.ticks (Local.run_c a HT roots fuel) <= run_budget a HT roots fuel lb tb.
Proof.
  intros HB HTB.
  pose proof (LocalCost.public_discover_cost a HL roots lb HB fuel
    (TotalCost.Budget.metadata tb) (TotalCost.metadata_model HTB)) as Hdiscover.
  rewrite Local.run_cost; unfold run_budget.
  cbn zeta.
  destruct (Cost.value (Local.discover_indexed_c a
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots fuel))
    as [state|r] eqn:Hdiscovered; [nia|].
  pose proof (filter_cost a roots lb HB r) as Hfilter.
  pose proof (TotalProof.total_cost_separate (Local.restrict a (Local.rows a r))
    (LocalLeast.restriction_laws a _ HL)
    (Local.restriction_termination a HT (Local.rows a r) (Local.rows_incl a r)) tb
    (restriction_model a tb _ HTB (Local.rows_incl a r))) as Htotal.
  unfold restricted_budget; cbn zeta; nia.
Qed.

(** Numeric local-run families require primitive duties and no conditional whole-run premises. *)
Theorem local_run_bigO {T X C A} (a : T -> Analysis.t X C A)
    (HL : forall t, Analysis.laws (a t)) (HT : forall t, Terminates.t (a t))
    (roots : T -> list X) (fuel : T -> positive)
    (lb : T -> LocalCost.Budget.t) (tb : T -> TotalCost.Budget.t) :
  (forall t, LocalCost.model (a t) (roots t) (lb t)) ->
  (forall t, TotalCost.model (a t) (tb t)) ->
  bigO (fun t => run_budget (a t) (HT t) (roots t) (fuel t) (lb t) (tb t))
    (fun t => Cost.ticks (Local.run_c (a t) (HT t) (roots t) (fuel t))).
Proof.
  intros HB HTB; exists 1; intro t.
  pose proof (local_run_cost (a t) (HL t) (HT t) (roots t) (fuel t) (lb t) (tb t)
    (HB t) (HTB t)); nia.
Qed.

End LocalRunCost.
Import LocalRunCost.
