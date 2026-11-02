(** * Whole stratification source equations

    Done states still execute every remaining binary-fuel call; returned levels retain their map.
    For example, a negative edge requires the head level to exceed the dependency level.
    Builds on: RulesAuditMaterializePrelude and RulesStratify. *)

From Stdlib Require Import List NArith ZArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditEncoding.
From Galois.Rules Require Import RulesAuditRelations RulesAuditMaterializePrelude
  RulesAuditMaterializeAdapters RulesAuditJoinSyntax.
Import ListNotations.

(** * Counted stratification *)

Definition mat_rule_edges {P} (r : rule P) :=
  mat_map (fun lit => mat_return (pred (head r),
    (pred (lit_atom lit),
      match lit with
      | LPos _ => 0%nat
      | LNeg _ => 1%nat
      end))) (body r).

Definition mat_program_edges {P} (prog : program P) := mat_flatmap mat_rule_edges (rules prog).

Definition mat_rule_predicates {P} (r : rule P) :=
  tail <- mat_map (fun lit => mat_return (pred (lit_atom lit))) (body r);;
  mat_return (pred (head r) :: tail).

Definition mat_rule_nodes {P} (prog : program P) :=
  all <- mat_flatmap mat_rule_predicates (rules prog);;
  set <- mat_predicate_set_encoded (mat_encode (penc prog)) all;; mat_elements set.

Definition mat_level_at {P} E (m : Map.t P nat) p :=
  found <- mat_get E p m;;
  mat_return (
    match found with
    | Some n => n
    | None => 0%nat
    end).

Definition mat_edge_ok {P} E m (e : P * (P * nat)) :=
  source <- mat_level_at E m (fst (snd e));;
  required <- mat_nat 20 Nat.add source (snd (snd e));;
  target <- mat_level_at E m (fst e);; mat_nat_test 21 Nat.leb required target.

Definition mat_raise_edge {P} E m (e : P * (P * nat)) :=
  target <- mat_level_at E m (fst e);; source <- mat_level_at E m (fst (snd e));;
  required <- mat_nat 22 Nat.add source (snd (snd e));;
  maximum <- mat_nat 23 Nat.max target required;; mat_set E (fst e) maximum m.

Definition mat_stratify_tick {P} (prog : program P) (state : Map.t P nat * bool) :=
  mat_mark 80 (
    let '(levels, done) := state in
    if done then mat_return state else
    edges <- mat_program_edges prog;; ready <- mat_all (mat_edge_ok (penc prog) levels) edges;;
    if ready then mat_return (levels, true) else
    raising <- mat_program_edges prog;;
    next <- mat_foldl (mat_raise_edge (penc prog)) raising levels;;
    mat_return (next, false)).

Fixpoint mat_piter {A} (fuel : positive) (body : A -> mat_run A) (state : A) : mat_run A :=
  mat_mark 81 (
    match fuel with
    | xH => body state
    | xO p => mid <- mat_piter p body state;; mat_piter p body mid
    | xI p => mid1 <- mat_piter p body state;; mid2 <- mat_piter p body mid1;; body mid2
    end).

Definition mat_niter {A} (fuel : N) (body : A -> mat_run A) (state : A) :=
  mat_mark 82 (
    match fuel with
    | N0 => mat_return state
    | Npos p => mat_piter p body state
    end).

Definition mat_stratify {P} (prog : program P) : mat_run (option (mat_level_context P)) :=
  nodes <- mat_rule_nodes prog;; let count := length nodes in
  ignored <- mat_emit (MatNat 24 count 0);;
  let n := N.of_nat count in
  ignored <- mat_emit (MatChild 83 (audit_unary_conversion_weight count) (S count));;
  let square := (n * n)%N in
  ignored <- mat_emit (MatChild 84 (audit_multiply_weight (Z.of_N n) (Z.of_N n)) (S count));;
  let fuel := N.succ square in
  ignored <- mat_emit (MatChild 85 (audit_binary_weight (Z.of_N square) 0) (S count));;
  state <- mat_niter fuel (mat_stratify_tick prog) (Map.empty, false);;
  mat_mark 86 (
    let '(levels, done) := state in
    if done then
      nodes_again <- mat_rule_nodes prog;;
      values <- mat_map (mat_level_at (penc prog) levels) nodes_again;;
      maximum <- mat_foldr (fun n m => mat_nat 25 Nat.max n m) values 0%nat;;
      bound <- mat_nat 26 Nat.add maximum 1%nat;;
      mat_return (Some (MatCapturedLevels (penc prog) levels bound))
    else mat_return None).

(** The proposed erasure compares rejection and the levels returned on every predicate. *)
Definition mat_stratify_erases_statement : Prop :=
  forall P (prog : program P),
    match fst (mat_stratify prog), stratify prog with
    | None, None => True
    | Some context, Some native =>
        count (mat_native_levels context) = count native /\
        forall p, level (mat_native_levels context) p = level native p
    | _, _ => False
    end.

(** The size counts every original rule and body literal, including duplicates. *)
Definition mat_stratify_input_size {P} (prog : program P) : nat :=
  fold_right (fun r n => S (length (body r)) + n) 0 (rules prog).

(** The proposed work bound also counts original rules and body literals. *)
Definition mat_stratify_bound_statement : Prop :=
  forall P (prog : program P),
    let '(_, events) := mat_stratify prog in let width := S (mat_width events) in
    (mat_work events <= (N.to_nat 100000000%N) *
      S (mat_stratify_input_size prog) * Nat.pow width 12)%nat.

(** The proposed totality states that every program yields an output and trace. *)
Definition mat_stratify_total_statement : Prop :=
  forall P (prog : program P), exists out trace, mat_stratify prog = (out, trace).

(** The proposed uniqueness fixes both output and trace for a given program. *)
Definition mat_stratify_unique_statement : Prop :=
  forall P (prog : program P) r1 t1 r2 t2,
    mat_stratify prog = (r1, t1) -> mat_stratify prog = (r2, t2) -> r1 = r2 /\ t1 = t2.
