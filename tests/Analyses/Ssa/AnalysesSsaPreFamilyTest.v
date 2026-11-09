(** * Discovery adequacy, duplicate arrivals and binary construction

    Computed fixtures separate memo hits from new translations and expose exhausted runs.
    For example, two parallel edge translations can return the same expression twice.
    Builds on: AnalysesSsaPreFamily and AnalysesSsaPreContextTest. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFamily.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest.
Import List.ListNotations.

Example binary_count : Cost.value (PreFamily.count_c [false; true; false]) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example binary_count_ticks : Cost.ticks (PreFamily.count_c [false; true; false]) = 3%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example charged_power :
  Cost.value (PreFamily.power_c 2%N [tt]) = 2%N /\
  Cost.ticks (PreFamily.power_c 2%N [tt]) = 3%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example nullary_family_bound :
  PreFamily.family_bound One.ctx = 1%N /\
  Cost.ticks (PreFamily.family_bound_c One.ctx) = 5%N.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example ordered_parallel_translations :
  PreFamily.translated Parallel.ctx [false; true; false] false = [false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_translations_preserved :
  PreFamily.translated Parallel.ctx [false; false] false = [false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_seed_discovery :
  PreFamily.discover Parallel.ctx = inr [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition arrivals :=
  PreFamily.Engine bool_encoding
    (Cost.lift (fun _ => 1%N) (fun x : bool => if x then [] else [true; true])).
Definition initial := ([false; false], @FinSet.empty bool).

Example exposed_exhaustion :
  match Cost.value (iterate (PreFamily.step_c arrivals) 4%positive initial) with
  | inl work => fst work = []
  | inr _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example adequate_stop :
  match Cost.value (iterate (PreFamily.step_c arrivals) 5%positive initial) with
  | inl _ => False
  | inr work => fst work = [] /\ FinSet.elements (snd work) = [true; false]
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example empty_worklist :
  Cost.value (iterate (PreFamily.step_c arrivals) 1%positive ([], FinSet.empty)) =
    inr ([], FinSet.empty).
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_discovery : PreFamily.discover One.ctx = inr [tt].
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_client : Pre.client unit unit bool unit unit unit unit nat unit :=
  Pre.Client One.points One.ssa One.expr
    (Pre.pure_c One.client) (Pre.recomputed_c One.client) [] []
    (Pre.shape_c One.client) (Pre.operands_c One.client) (Pre.eval One.client)
    (Pre.translate_c One.client) (Pre.initial_c One.client) (Pre.exit_point_c One.client).
Definition empty_ctx :=
  Pre.Context empty_client (Pre.keys One.ctx) One.blocks One.point_graph One.tree.

Example empty_seed_discovery : PreFamily.discover empty_ctx = inr [].
Proof.
  vm_compute; reflexivity.
Qed.

Definition duplicate_values_client : Pre.client unit unit bool unit unit unit unit nat unit :=
  Pre.Client One.points One.ssa One.expr
    (Pre.pure_c One.client) (Pre.recomputed_c One.client) [tt] [tt; tt]
    (Pre.shape_c One.client) (Pre.operands_c One.client) (Pre.eval One.client)
    (Pre.translate_c One.client) (Pre.initial_c One.client) (Pre.exit_point_c One.client).
Definition duplicate_values_ctx :=
  Pre.Context duplicate_values_client (Pre.keys One.ctx) One.blocks One.point_graph One.tree.

(** Duplicate client values satisfy the same finite-family laws without a uniqueness premise. *)
Example duplicate_values_laws : Pre.laws duplicate_values_ctx.
Proof.
  constructor.
  - constructor.
    + exact (Pre.params_nodup One.ctx One.shapes).
    + exact (Pre.occurrences_seeded One.ctx One.shapes).
    + exact (Pre.initials_in_family One.ctx One.shapes).
    + intros [] _ [] H; contradiction.
    + exact (Pre.shape_identity One.ctx One.shapes).
    + exact (Pre.shape_arity One.ctx One.shapes).
    + exact (Pre.closed_translation One.ctx One.shapes).
    + exact (Pre.translation_shape One.ctx One.shapes).
    + exact (Pre.translation_operands One.ctx One.shapes).
    + exact (Pre.translation_pure One.ctx One.shapes).
  - destruct One.graphs; constructor; assumption.
  - destruct One.kills; constructor; assumption.
  - destruct One.runtime; constructor; assumption.
Qed.

Example duplicate_value_construction_charged :
  Pre.values duplicate_values_client = [tt; tt] /\
  Cost.ticks (PreFamily.family_bound_c duplicate_values_ctx) = 7%N /\
  PreFamily.discover duplicate_values_ctx = inr [tt].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The exact-family theorem applies to an inhabited structural context. *)
Example singleton_family_client :
  NoDup (PreFamily.universe One.ctx) /\
  forall u, In u (PreFamily.universe One.ctx) <-> PreFamily.in_family One.ctx u.
Proof.
  exact (PreFamily.universe_exact One.ctx One.laws).
Qed.

(** Adequacy proves a stopping outcome for the same context used by the computed example. *)
Example singleton_adequacy_client :
  exists final, Cost.value (PreFamily.discover_state_c One.ctx) = inr final.
Proof.
  exact (PreFamily.discover_adequate One.ctx One.laws).
Qed.

Definition one_budgets := PreFamily.Budgets 3%N 1%N.

(** The numeric theorem accounts for actual bound construction and materialization on this model. *)
Example singleton_cost_client :
  (Cost.ticks (PreFamily.discover_c One.ctx) <=
    PreFamily.construction_work One.ctx + PreFamily.materialization_work One.ctx +
    PreFamily.discovered_count One.ctx *
      (3 + PreFamily.edge_count One.ctx * (2 + 1) + 1 +
        PreFamily.edge_count One.ctx * (3 + 3)) +
    PreFamily.seed_count One.ctx * (3 + 2) + 2 * PreFamily.fuel_width One.ctx)%N.
Proof.
  apply (PreFamily.discover_cost One.ctx one_budgets One.laws).
  - intros [] _; vm_compute; congruence.
  - intros [] [] Hbe; vm_compute in Hbe; contradiction.
Qed.
