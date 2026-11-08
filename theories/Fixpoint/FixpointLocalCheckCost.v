(** * Cost composition at the partial certificate boundary

    The checked wrapper retains the public partial-checker budget and every normalization charge.
    For example, a rejected candidate still pays for enumerating and rebuilding its explored set.
    Builds on: FixpointLocalRunCost and the public FixpointPartial cost contract. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseMap BaseSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointCheck FixpointPartial
  FixpointAnalysis FixpointSolver FixpointLocal FixpointLocalCost FixpointTotalCost
  FixpointLocalRunCost.
Import Cost.Notations.
Local Open Scope N_scope.

Module LocalCheckCost.

(** Certificate budgets retain the public partial contract's preparation and per-row costs. *)
Definition certificate_budget {X C A} (a : Analysis.t X C A) ix roots candidate :=
  let EX := Analysis.key_enc a in
  let EC := Analysis.row_enc a in
  let L := Analysis.lat a in
  let S := Analysis.system a in
  let E := FinSet.of_list EX (FinSet.elements (Local.explored candidate)) in
  Cost.ticks (FinSet.elements_c (Local.explored candidate)) +
    Cost.ticks (FinSet.of_list_c EX (FinSet.elements (Local.explored candidate))) +
    Cost.ticks (partial_rows_c EX EC ix E) +
    fold_right (fun c n => 1 +
      Cost.ticks (partial_constraint_c EX L S E (lookup_c EX L (Local.values candidate)) c) + n)
      0 (partial_rows EX EC ix E) +
    fold_right (fun x n => 1 + Cost.ticks (FinSet.mem_c EX x E) + n) 0 roots.

(** The local gate composes the public partial cost bound without inspecting its implementation. *)
Theorem local_check_cost {X C A} (a : Analysis.t X C A) ix roots candidate :
  Cost.ticks (Local.check_c a ix roots candidate) <= certificate_budget a ix roots candidate.
Proof.
  set (EX := Analysis.key_enc a).
  set (EC := Analysis.row_enc a).
  set (L := Analysis.lat a).
  set (S := Analysis.system a).
  set (E := FinSet.of_list EX (FinSet.elements (Local.explored candidate))).
  pose proof (check_partial_cost EX EC L S (Analysis.static a) ix E (Local.values candidate))
    as Hpartial.
  pose proof (forallb_cost (fun x => FinSet.mem_c EX x E) roots) as Hroots.
  unfold Local.check_c; rewrite !Cost.ticks_bind.
  rewrite Cost.ticks_ret.
  change (Cost.ticks (FinSet.elements_c (Local.explored candidate)) +
    (Cost.ticks (FinSet.of_list_c EX (FinSet.elements (Local.explored candidate))) +
      (Cost.ticks (check_partial_c EX EC L S (Analysis.static a) ix E
        (Local.values candidate)) +
        (Cost.ticks (forallb_c (fun x => FinSet.mem_c EX x E) roots) + 0))) <=
    certificate_budget a ix roots candidate).
  unfold certificate_budget; cbn zeta.
  unfold E, EX, EC, L, S in *; nia.
Qed.

(** A complete checked-run budget combines numeric local solving and public certificate charges. *)
Definition checked_budget {X C A} (a : Analysis.t X C A) HT roots fuel lb tb :=
  LocalRunCost.run_budget a HT roots fuel lb tb +
    match Local.run a HT roots fuel with
    | Outcome.Solved candidate => certificate_budget a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots candidate
    | _ => 0
    end.

(** Checked local outcomes retain numeric engine work and the independent partial owner's budget. *)
Theorem local_checked_cost {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a)
    HT roots fuel lb tb :
  LocalCost.model a roots lb -> TotalCost.model a tb ->
  Cost.ticks (Local.checked_c a HT roots fuel) <= checked_budget a HT roots fuel lb tb.
Proof.
  intros HB HTB; pose proof (LocalRunCost.local_run_cost a HL HT roots fuel lb tb HB HTB)
    as Hrun.
  rewrite Local.checked_cost; unfold checked_budget.
  destruct (Local.run a HT roots fuel) as [candidate|have|why]; [|nia|nia].
  pose proof (local_check_cost a
    (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) roots candidate).
  nia.
Qed.

(** Checked families compose numeric engine bounds and the independent certificate contract. *)
Theorem local_checked_bigO {T X C A} (a : T -> Analysis.t X C A)
    (HL : forall t, Analysis.laws (a t)) (HT : forall t, Terminates.t (a t))
    (roots : T -> list X) (fuel : T -> positive)
    (lb : T -> LocalCost.Budget.t) (tb : T -> TotalCost.Budget.t) :
  (forall t, LocalCost.model (a t) (roots t) (lb t)) ->
  (forall t, TotalCost.model (a t) (tb t)) ->
  bigO (fun t => checked_budget (a t) (HT t) (roots t) (fuel t) (lb t) (tb t))
    (fun t => Cost.ticks (Local.checked_c (a t) (HT t) (roots t) (fuel t))).
Proof.
  intros HB HTB; exists 1; intro t.
  pose proof (local_checked_cost (a t) (HL t) (HT t) (roots t) (fuel t) (lb t) (tb t)
    (HB t) (HTB t)); nia.
Qed.

End LocalCheckCost.
Import LocalCheckCost.
