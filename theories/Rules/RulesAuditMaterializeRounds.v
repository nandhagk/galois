(** * Complete seed, candidate, advancing and bounded-round bodies

    Prepared closures capture their cached universe once; bounded legacy rounds rebuild each
      variant's universe.
    For example, a completed bounded stratum returns its accumulated state when the next
    batch is empty.
    Builds on: RulesAuditMaterializeJobs, RulesAuditMaterializeDifference and delta state. *)

From Stdlib Require Import List NArith PArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditElements
  CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditDeltaRows RulesAuditMaterializePrelude
  RulesAuditMaterializeAdapters RulesAuditJoinSyntax RulesAuditMaterializePlans
  RulesAuditMaterializeDifference RulesAuditMaterializeJobs.
Import ListNotations.

(** * Seeding and bounded rounds *)

Definition mat_selected {P} strategy (prog : program P) (r : rule P) env :=
  ps <- mat_positive_atoms (body r);; snapshot <- mat_snapshot (penc prog) ps env;;
  plan <- mat_plan_rows strategy ps (mat_snapshot_rows (penc prog) snapshot);;
  mat_plan_bindings ps env plan.

Definition mat_seed_atoms {P} strategy (prog : program P) facts st k lower :=
  cached <- mat_setup_cached prog facts;;
  initial_facts <- mat_filter (fun f =>
    lev <- mat_level st (fst f);; same <- mat_nat_test 10 Nat.eqb lev k;;
    allowed <- mat_accept_cached prog cached (fst f) (snd f);; mat_return (same && allowed)) facts;;
  rs <- mat_filter (fun r =>
    lev <- mat_level st (pred (head r));; same <- mat_nat_test 11 Nat.eqb lev k;;
    recursive <- mat_recursive st k r;;
    no_recursive <- mat_return (
      match recursive with
      | [] => true
      | _ => false
      end);;
    mat_return (same && no_recursive)) (rules prog);;
  derived <- mat_flatmap (fun r =>
    bindings <- mat_selected strategy prog r (mat_current prog st k lower Map.empty);;
    good <- mat_filter (mat_negative r (mat_current prog st k lower Map.empty)) bindings;;
    rows <- mat_map (fun b => mat_instantiate b (args (head r))) good;;
    valid <- mat_filter (mat_accept_cached prog cached (pred (head r))) rows;;
    set <- mat_of_list (audit_list_encode audit_positive_encode)
      (audit_list_events_work audit_basic_encoding_work) valid;;
    elements <- mat_elements set;;
    mat_map (fun row => mat_return (pred (head r), row)) elements) rs;;
  mat_append initial_facts derived.

Definition mat_initial {P} strategy (prog : program P) facts st k lower :=
  atoms <- mat_seed_atoms strategy prog facts st k lower;; seeds <- mat_ground_set prog atoms;;
  index <- mat_index prog seeds;; jobs <- mat_prepare_jobs strategy prog st k lower index index;;
  mat_return (DeltaState seeds seeds index index jobs).

Definition mat_advance {P} (prog : program P) (s : delta_state P) batch :=
  index <- mat_index prog batch;;
  snapshot <- mat_lift 70 (fun m => audit_trie_nodes m)
    rules_delta_rows_snapshot_work (rules_delta_rows_snapshot_counted index);;
  accumulated <- mat_union (delta_accumulated s) batch;; atoms <- mat_elements batch;;
  accumulated_index <- mat_atom_fold prog atoms (delta_accumulated_index s);;
  jobs <- mat_update_jobs prog (mat_snapshot_rows (penc prog) snapshot) (delta_jobs s);;
  mat_return (DeltaState accumulated batch accumulated_index index jobs).

Definition mat_step {P} (prog : program P) facts st k lower (s : delta_state P) :=
  candidates <- mat_candidates prog facts st k lower (delta_accumulated_index s)
    (delta_frontier_index s) (delta_jobs s);;
  batch <- mat_diff candidates (delta_accumulated s);;
  mat_mark 71 (if FinSet.is_empty batch then mat_return None else
    next <- mat_advance prog s batch;; mat_return (Some next)).

Definition mat_prepared_step {P} (prog : program P) facts st k lower cached (s : delta_state P) :=
  candidates <- mat_candidates_prepared prog facts st k lower (delta_accumulated_index s)
    (delta_frontier_index s) (delta_jobs s) cached;;
  batch <- mat_diff candidates (delta_accumulated s);;
  mat_mark 72 (if FinSet.is_empty batch then mat_return None else
    next <- mat_advance prog s batch;; mat_return (Some next)).

Definition mat_one {P} (prog : program P) facts st k lower (s : delta_state P) :=
  next <- mat_step prog facts st k lower s;;
  mat_return (
    match next with
    | Some out => out
    | None => s
    end).

Fixpoint mat_observe {P} (prog : program P) facts st k lower (fuel : positive) (s : delta_state P) :
    mat_run (delta_state P) :=
  mat_mark 73 (
    match fuel with
    | xH => mat_one prog facts st k lower s
    | xO p => mid <- mat_observe prog facts st k lower p s;; mat_observe prog facts st k lower p mid
    | xI p =>
        mid1 <- mat_observe prog facts st k lower p s;;
        mid2 <- mat_observe prog facts st k lower p mid1;; mat_one prog facts st k lower mid2
    end).

Definition mat_bounded_stratum {P} strategy (prog : program P) facts st k lower fuel :=
  initial <- mat_initial strategy prog facts st k lower;;
  result <- mat_observe prog facts st k lower fuel initial;;
  final <- mat_step prog facts st k lower result;;
  mat_return (
    match final with
    | Some _ => None
    | None => Some result
    end).

Fixpoint mat_bounded_levels {P} strategy (prog : program P) facts st fuel (n : nat) :
    mat_run (option (database P)) :=
  mat_mark 74 (
    match n with
    | O => mat_return (Some Map.empty)
    | S k =>
        previous <- mat_bounded_levels strategy prog facts st fuel k;;
        match previous with
        | None => mat_return None
        | Some lower =>
            result <- mat_bounded_stratum strategy prog facts st k (mat_rel prog lower) fuel;;
            match result with
            | None => mat_return None
            | Some final =>
                atoms <- mat_elements (delta_accumulated final);;
                db <- mat_atom_fold prog atoms lower;;
                mat_return (Some db)
            end
        end
    end).

(** The proposed initialization erasure returns the native delta initial state. *)
Definition mat_initial_erases_statement : Prop :=
  forall P strategy (prog : program P) facts st k lower,
    fst (mat_initial strategy prog facts (MatExternalLevels st) k (fun p => mat_return (lower p))) =
      delta_initial strategy prog facts st k lower.

(** The proposed step erasure returns the native delta step outcome. *)
Definition mat_step_erases_statement : Prop :=
  forall P (prog : program P) facts st k lower s,
    fst (mat_step prog facts (MatExternalLevels st) k (fun p => mat_return (lower p)) s) =
      delta_step prog facts st k lower s.

(** The proposed prepared-step erasure uses the cache built from the same inputs. *)
Definition mat_prepared_step_erases_statement : Prop :=
  forall P (prog : program P) facts st k lower s,
    let cached := fst (mat_setup_cached prog facts) in
    fst (mat_prepared_step prog facts (MatExternalLevels st) k
      (fun p => mat_return (lower p)) cached s) =
      delta_prepared_step prog facts st k lower s.

(** The proposed bounded-level erasure preserves the native result for the same fuel. *)
Definition mat_bounded_levels_erases_statement : Prop :=
  forall P strategy (prog : program P) facts st fuel n,
    fst (mat_bounded_levels strategy prog facts (MatExternalLevels st) fuel n) =
      delta_bounded_levels strategy prog facts st fuel n.
