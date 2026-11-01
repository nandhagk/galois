(** * Closed solver phase contract types

    These propositions quantify every parameter generalized by the original sections.
    For example, a local-solver erasure contract covers each actual scheduler and index.
    Builds on: the individual solver phase contract modules. *)

From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointNested
  FixpointAuditWorklist FixpointAuditRecorded FixpointAuditLocalPartial FixpointAuditLocalClosure
  FixpointAuditCut FixpointAuditLocal FixpointAuditNarrowCheck FixpointAuditNarrow
  FixpointAuditNestedMachine.

(** Declared worklist claims quantify the actual strategy and static-system index. *)

(** For every solver configuration, erasing declared-model traces recovers the original lookup,
    query, queue and worklist operations. *)
Definition fx_declared_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_declared_model_erasure_statement X C A EX EC L sch mode S SS ix.

(** For every solver configuration, the declared run returns the original result, its work splits
    into trace and primitive work, and its pop and right-hand-side counts are bounded by fuel. *)
Definition run_worklist_declared_model_cost_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @run_worklist_declared_model_cost_statement X C A EX EC L sch mode S SS ix.

(** For every solver configuration, each accessible engine state admits a declared run. *)
Definition fx_declared_total_engine_total_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_declared_total_engine_total_statement X C A EX EC L sch mode S SS ix.

(** For every solver configuration, a declared engine run matches terminating original steps and
    values, with one more pop than steps, one RHS call per step and the work equation. *)
Definition fx_declared_total_engine_erases_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_declared_total_engine_erases_statement X C A EX EC L sch mode S SS ix.

(** Recorded claims quantify the actual worklist parameters and source system. *)

(** For every solver configuration, erasing recorded-reader events recovers the worklist
    execution. *)
Definition fx_recorded_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A), @fx_recorded_model_erasure_statement X C A EX EC L sch mode S.

(** For every solver configuration, the recorded run returns the original result within its trace
    budget and bounds pop and RHS counts by fuel. *)
Definition fx_recorded_model_cost_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A), @fx_recorded_model_cost_statement X C A EX EC L sch mode S.

(** For every solver configuration, the recorded successor-event count equals the base
    right-hand-side call count. *)
Definition fx_recorded_successor_count_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A), @fx_recorded_successor_count_statement X C A EX EC L sch mode S.

(** Partial-check claims retain the actual explored set and assignment. *)

(** For every system and explored region, erasing partial-check traces recovers the original
    checks. *)
Definition fx_partial_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored values,
    @fx_partial_model_erasure_statement X C A EX L S SS ix explored values.

(** For every system and explored region, partial checking returns the original result within its
    work bound. *)
Definition fx_partial_model_cost_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored values,
    @fx_partial_model_cost_statement X C A EX EC L S SS ix explored values.

(** Closure and local-run claims retain the actual index and scheduler. *)

(** For every system and index, erasing a counted closure step recovers the original step. *)
Definition fx_local_step_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) ix, @fx_local_step_erasure_statement X C A EX EC S SS ix.

(** For every system and index, erasing a counted closure walk recovers the original walk. *)
Definition fx_local_walk_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (S : System.t X C A)
    (SS : System.static S) ix, @fx_local_walk_erasure_statement X C A EX EC S SS ix.

(** For every solver configuration, erasing local-solver events recovers the original local
    solve. *)
Definition fx_local_solve_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_local_solve_erasure_statement X C A EX EC L sch mode S SS ix.

(** For every solver configuration, erasing checked-local events recovers the original checked
    solve. *)
Definition fx_local_checked_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X) mode
    (S : System.t X C A) (SS : System.static S) ix,
    @fx_local_checked_erasure_statement X C A EX EC L sch mode S SS ix.

(** Cut, narrow and nested claims quantify their actual phase inputs. *)

(** For every system and index, erasing counted cut phases recovers the corresponding original
    phases. *)
Definition fx_cut_model_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix, @fx_cut_model_erasure_statement X C A EX L S SS ix.

(** For every system and index, erasing counted narrowing events recovers checked narrowing. *)
Definition fx_narrow_checked_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix, @fx_narrow_checked_erasure_statement X C A EX L S SS ix.

(** For every plan, erasing counted mark, raise, update, step and loop events recovers the
    original nested operations. *)
Definition fx_nested_machine_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (plan : NestedPlan.t X C) mode
    (S : System.t X C A), @fx_nested_machine_erasure_statement X C A EX L plan mode S.

(** For every assignment, erasing full-check events recovers the original checker result. *)
Definition fx_fullcheck_erasure_contract : Prop :=
  forall X C A (EX : encoding X) (L : lattice A) (S : System.t X C A) values,
    @fx_fullcheck_erasure_statement X C A EX L S values.
