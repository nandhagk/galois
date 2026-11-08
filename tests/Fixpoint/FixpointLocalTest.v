(** * Actual demand-driven joining clients

    Local runs compute cyclic closures, smaller unrelated regions and checked partial outcomes.
    For example, deleting a required read from an external candidate makes the partial gate reject.
    Builds on: FixpointLocal, FixpointLocalProof and FixpointLocalLeast. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeProduct.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointAnalysis
  FixpointSolver FixpointPartial FixpointTotal FixpointTotalKernel FixpointLocal FixpointLocalProof
  FixpointLocalLeast FixpointLocalCost FixpointLocalCredit FixpointLocalDiscover
  FixpointLocalAdequacy FixpointLocalRunCost FixpointLocalCheckCost FixpointIndexCost
  FixpointTotalCost FixpointLeast.
Import List.ListNotations Cost.Notations.
Local Close Scope N_scope.

Module LocalTest.

Definition system : System.t nat nat bool :=
  System.Make [3; 0; 1; 2; 0]
    (fun c => Cost.ret (if Nat.eqb c 3 then 20 else c))
    (fun c => Cost.ret (match c with
      | O => Query.Ask 1 (fun b => Cost.ret (Query.Ret b))
      | S O => Query.Ask 0 (fun b => Cost.ret (Query.Ret b))
      | S (S O) => Query.Side 0 true (Query.Side 0 false (Query.Ret false))
      | _ => Query.Ret true
      end)).

Definition summaries : System.static system :=
  System.Static
    (fun c => Cost.ret (match c with O => [1] | S O => [0] | _ => [] end))
    (fun c => Cost.ret (match c with S (S O) => [0; 0] | _ => [] end)).

Definition analysis : Analysis.t nat nat bool :=
  Analysis.Make nat_encoding nat_encoding bool_lattice system summaries (Policy.flat nat).

Definition laws : Analysis.laws analysis.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact bool_laws.
  - constructor; intros c s x Hin; destruct c as [|[|[|c]]];
      vm_compute in *; exact Hin.
Qed.

Definition termination : Terminates.t analysis.
Proof.
  refine (@Terminates.Finite nat nat bool analysis (fun _ => True) bool_height _ _ _);
    intros; exact I.
Defined.

Definition ix := index_system nat_encoding system summaries.
Definition cyclic : Local.result nat bool :=
  Local.Result (FinSet.of_list nat_encoding [0; 1; 2])
    (Map.of_list nat_encoding [(0, true); (1, true)]).

Definition observation (outcome : Outcome.t nat bool (Local.result nat bool)) :=
  match outcome with
  | Outcome.Solved r =>
    (FinSet.elements (Local.explored r),
      map (lookup nat_encoding bool_lattice (Local.values r)) [0; 1; 2; 20; 99])
  | _ => ([], [])
  end.

Example cyclic_run : Local.run analysis termination [0] 64%positive = Outcome.Solved cyclic.
Proof.
  vm_compute; reflexivity.
Qed.

Example checked_cyclic :
  observation (Local.checked analysis termination [0] 64%positive) =
    ([1; 0; 2], [true; true; false; false; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example unrelated_region :
  observation (Local.checked analysis termination [20] 64%positive) =
    ([20], [false; false; false; true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_root :
  observation (Local.checked analysis termination [99] 4%positive) =
    ([99], [false; false; false; false; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_roots :
  observation (Local.checked analysis termination [] 1%positive) =
    ([], [false; false; false; false; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example exhausted_discovery :
  Local.checked analysis termination [0] 1%positive = Outcome.OutOfFuel Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example tampered_partial :
  Local.check analysis ix [0]
    (Local.Result (FinSet.of_list nat_encoding [0]) (Local.values cyclic)) =
    Outcome.Rejected Reason.Check_failed.
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_root_rejects :
  Local.check analysis ix [99] cyclic = Outcome.Rejected Reason.Check_failed.
Proof.
  vm_compute; reflexivity.
Qed.

(** The computed checked cyclic result discharges the importing partial-soundness client. *)
Theorem checked_sound_client :
  exists r, Local.checked analysis termination [0] 64%positive = Outcome.Solved r /\
    closed_partial nat_encoding bool_lattice system summaries
      (Local.explored r) (lookup nat_encoding bool_lattice (Local.values r)).
Proof.
  exists cyclic; assert (Hrun : Local.checked analysis termination [0] 64%positive =
    Outcome.Solved cyclic) by (vm_compute; reflexivity).
  split; [exact Hrun|].
  exact (proj1 (proj2 (LocalProof.local_checked_sound analysis termination [0] 64%positive
    cyclic laws Hrun))).
Qed.

Definition monotone : monotone_system bool_lattice system.
Proof.
  intros c Hc; destruct c as [|[|[|c]]]; split.
  - intros s t Hle; exact (Hle 1%nat).
  - intros s t Hle x v Hin; vm_compute in Hin; contradiction.
  - intros s t Hle; exact (Hle 0%nat).
  - intros s t Hle x v Hin; vm_compute in Hin; contradiction.
  - intros s t Hle; apply (leb_refl bool_laws).
  - intros s t Hle x v Hin; exists v; split; [exact Hin|apply (leb_refl bool_laws)].
  - intros s t Hle; apply (leb_refl bool_laws).
  - intros s t Hle x v Hin; vm_compute in Hin; contradiction.
Qed.

(** The actual local engine's root values agree with the actual global least solution. *)
Theorem least_client :
  leb bool_lattice (lookup nat_encoding bool_lattice (Local.values cyclic) 0)
    (lookup nat_encoding bool_lattice (Total.run analysis termination) 0) = true /\
  leb bool_lattice
    (lookup nat_encoding bool_lattice (Total.run analysis termination) 0)
    (lookup nat_encoding bool_lattice (Local.values cyclic) 0) = true.
Proof.
  apply (LocalLeast.local_least analysis termination [0%nat] 64%positive cyclic
    laws bool_lub monotone cyclic_run 0%nat); now left.
Qed.

Example local_is_charged :
  (0 < Cost.ticks (Local.checked_c analysis termination [0%nat] 64%positive))%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition budget : LocalCost.Budget.t :=
  LocalCost.Budget.Make 10000 10000 10000 10000 10000 10000 0 0 0.

(** Tagged and original key duties hold on the finite actual metadata support. *)
Theorem cost_model : LocalCost.model analysis [0] budget.
Proof.
  constructor.
  - intros [x|c] Hin; vm_compute in Hin;
      repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; try discriminate;
      repeat match goal with
      | H : inl _ = inl _ |- _ => injection H as H; subst
      | H : inr _ = inr _ |- _ => injection H as H; subst
      end; vm_compute; split; congruence.
  - intros x Hin; vm_compute in Hin;
      repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; try discriminate;
      repeat match goal with H : inl _ = inl _ |- _ => injection H as H; subst end;
      vm_compute; split; congruence.
  - intros c Hc; vm_compute in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|Hbad]]]]]; try contradiction;
      vm_compute; split; congruence.
  - intros c Hc; vm_compute; repeat split; congruence.
Qed.

(** The numeric importing client derives discovery work from primitive duties on finite keys. *)
Theorem discovery_cost_client :
  (Cost.ticks (LocalDiscover.run_c analysis ix [0%nat] 64%positive) <=
    (LocalCost.Budget.w budget + 4) * 1 +
    (4 * LocalCost.Budget.w budget + 10) *
      LocalCredit.sum (LocalCredit.weight (LocalDiscover.adjacent_c analysis ix))
        (LocalCost.support analysis [0%nat]) + N.pos (Pos.size 64%positive))%N.
Proof.
  exact (LocalCost.local_discover_full_cost analysis laws [0] budget cost_model 64%positive).
Qed.

(** The support threshold proves discovery completion independently of its result. *)
Theorem discovery_adequate_client :
  exists marked, LocalDiscover.run analysis ix [0] 64%positive = inr marked.
Proof.
  apply (LocalCost.local_discover_adequate analysis laws [0] 64%positive).
  vm_compute; congruence.
Qed.

(** Variable binary fuels instantiate the numeric discovery family without assuming success. *)
Theorem bigO_client :
  bigO (fun fuel : positive =>
    ((LocalCost.Budget.w budget + 4) * 1 +
      (4 * LocalCost.Budget.w budget + 10) *
        LocalCredit.sum (LocalCredit.weight (LocalDiscover.adjacent_c analysis ix))
          (LocalCost.support analysis [0%nat]) + N.pos (Pos.size fuel))%N)
    (fun fuel => Cost.ticks (LocalDiscover.run_c analysis ix [0] fuel)).
Proof.
  exact (LocalCost.local_bigO (fun _ : positive => analysis) (fun _ => laws)
    (fun _ => [0]) (fun _ => budget) (fun _ => cost_model) (fun p => p)).
Qed.

(** Adequate discovery produces a checked solution without an assumed successful run. *)
Theorem checked_adequate_client :
  exists r, Local.checked analysis termination [0] 64%positive = Outcome.Solved r.
Proof.
  apply (LocalAdequacy.local_checked_adequate analysis laws termination [0] 64%positive).
  vm_compute; congruence.
Qed.

Definition preparation_budget : SystemIndexCost.Budget.t :=
  SystemIndexCost.Budget.Make 10000 10000 0 0 0 1 3.
Definition total_budget : TotalCost.Budget.t :=
  TotalCost.Budget.Make preparation_budget 10000 10000 1 0 3 0 3.

(** Restricted total solving inherits this independently discharged primitive source model. *)
Theorem total_cost_model : TotalCost.model analysis total_budget.
Proof.
  constructor.
  - constructor.
    + intros c Hc x Hx; vm_compute in Hc.
      destruct Hc as [<-|[<-|[<-|[<-|[<-|Hbad]]]]]; try contradiction;
        vm_compute in Hx; intuition subst; vm_compute; congruence.
    + intros c Hc; vm_compute; repeat split; congruence.
    + intros c Hc; vm_compute in Hc.
      destruct Hc as [<-|[<-|[<-|[<-|[<-|Hbad]]]]]; try contradiction;
        vm_compute; split; lia.
  - intros c Hc; vm_compute in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|Hbad]]]]]; try contradiction;
      vm_compute; split; congruence.
  - intros [] []; vm_compute; split; congruence.
  - intros c Hc; vm_compute; congruence.
  - intros c s Hc; vm_compute in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|Hbad]]]]]; try contradiction.
    + exists 1%nat; split; [vm_compute; lia|vm_compute; apply Query.within_ret].
    + exists 2%nat; split; [vm_compute; lia|].
      vm_compute; apply Query.within_ask; [vm_compute; congruence|apply Query.within_ret].
    + exists 2%nat; split; [vm_compute; lia|].
      vm_compute; apply Query.within_ask; [vm_compute; congruence|apply Query.within_ret].
    + exists 3%nat; split; [vm_compute; lia|].
      vm_compute; apply Query.within_side, Query.within_side, Query.within_ret.
    + exists 2%nat; split; [vm_compute; lia|].
      vm_compute; apply Query.within_ask; [vm_compute; congruence|apply Query.within_ret].
  - intros c s Hc; vm_compute in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|Hbad]]]]]; try contradiction; vm_compute; lia.
Qed.

(** The local-run budget includes original setup, projection, filtering and selected solving. *)
Theorem numeric_run_client :
  (Cost.ticks (Local.run_c analysis termination [0%nat] 64%positive) <=
    LocalRunCost.run_budget analysis termination [0%nat] 64%positive budget total_budget)%N.
Proof.
  exact (LocalRunCost.local_run_cost analysis laws termination [0] 64%positive budget
    total_budget cost_model total_cost_model).
Qed.

(** Complete local runs instantiate the numeric family theorem at arbitrary binary fuels. *)
Theorem run_bigO_client :
  bigO (fun fuel => LocalRunCost.run_budget analysis termination [0] fuel budget total_budget)
    (fun fuel => Cost.ticks (Local.run_c analysis termination [0] fuel)).
Proof.
  exact (LocalRunCost.local_run_bigO (fun _ : positive => analysis) (fun _ => laws)
    (fun _ => termination) (fun _ => [0]) (fun p => p) (fun _ => budget)
    (fun _ => total_budget) (fun _ => cost_model) (fun _ => total_cost_model)).
Qed.

(** The checked cost client retains normalization and every public partial-certificate charge. *)
Theorem checked_cost_client :
  (Cost.ticks (Local.checked_c analysis termination [0%nat] 64%positive) <=
    LocalCheckCost.checked_budget analysis termination [0%nat] 64%positive budget total_budget)%N.
Proof.
  exact (LocalCheckCost.local_checked_cost analysis laws termination [0] 64%positive budget
    total_budget cost_model total_cost_model).
Qed.

(** Successful checked local production keeps original-system reachability. *)
Theorem reached_client :
  reached nat_encoding bool_lattice system
    (lookup nat_encoding bool_lattice (Local.values cyclic)).
Proof.
  apply (LocalAdequacy.local_checked_reached analysis laws termination [0] 64%positive cyclic).
  vm_compute; reflexivity.
Qed.

Definition direct_lat := product bool_lattice bool_lattice.
Definition direct_system : System.t nat nat (bool * bool) :=
  System.Make [3; 1; 2; 0; 1]
    (fun c => Cost.ret (if Nat.eqb c 2 then 10 else if Nat.eqb c 3 then 20 else c))
    (fun c => Cost.ret (match c with
      | O => Query.Ask 1 (fun b => Cost.ret (Query.Ret b))
      | S O => Query.Ask 0 (fun b => Cost.ret (Query.Ret b))
      | S (S O) => Query.Side 0 (true, false) (Query.Ret (false, false))
      | _ => Query.Ret (true, true)
      end)).
Definition direct_static : System.static direct_system :=
  System.Static
    (fun c => Cost.ret (match c with O => [1] | S O => [0] | _ => [] end))
    (fun c => Cost.ret (match c with S (S O) => [0; 42] | _ => [] end)).
Definition direct_analysis : Analysis.t nat nat (bool * bool) :=
  Analysis.Make nat_encoding nat_encoding direct_lat direct_system direct_static (Policy.flat nat).
Definition direct_termination : Terminates.t direct_analysis.
Proof.
  refine (@Terminates.Finite nat nat (bool * bool) direct_analysis _
    (product_height bool_lattice bool_lattice bool_laws bool_laws bool_closed bool_closed
      bool_height bool_height) _ _ _); intros; split; exact I.
Defined.

Example precise_non_top_local :
  match Local.checked direct_analysis direct_termination [0; 99] 128%positive with
  | Outcome.Solved r =>
    (map (fun x => FinSet.mem nat_encoding x (Local.explored r)) [0; 1; 10; 20; 42; 99],
      map (lookup nat_encoding direct_lat (Local.values r)) [0; 1; 10; 20; 42; 99])
  | _ => ([], [])
  end =
    ([true; true; true; false; true; true],
      [(true, false); (true, false); (false, false); (false, false);
        (false, false); (false, false)]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_bool : lattice bool :=
  {| leb_c := leb_c bool_lattice;
     join_c := fun x y => Cost.step ;; join_c bool_lattice x y;
     widen_c := widen_c bool_lattice;
     narrow_c := narrow_c bool_lattice;
     bot := false |}.
Definition charged_direct : Analysis.t nat nat (bool * bool) :=
  Analysis.Make nat_encoding nat_encoding (product charged_bool bool_lattice)
    direct_system direct_static (Policy.flat nat).
Definition direct_index := index_system nat_encoding direct_system direct_static.

Example nested_callbacks_keep_values :
  Cost.value (TotalKernel.loop_c direct_analysis direct_index 64%positive) =
    Cost.value (TotalKernel.loop_c charged_direct direct_index 64%positive).
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_callbacks_add_ticks :
  (Cost.ticks (TotalKernel.loop_c direct_analysis direct_index 64%positive) <
    Cost.ticks (TotalKernel.loop_c charged_direct direct_index 64%positive))%N.
Proof.
  vm_compute; reflexivity.
Qed.

End LocalTest.
Import LocalTest.
