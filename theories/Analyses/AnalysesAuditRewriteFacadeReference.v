(** * AnalysesAuditRewriteFacadeReference

    Models facade tables, substitution, guard programs, and explanation checking traces.
    For example, looking up index 0 in an empty binding list returns variable 0.
    Builds on: AnalysesEgraph and
    RewriteSyntax. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Rewrite Require Import RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_facade_table_call (A : Type) : Type :=
  | RWFacadeTableSet : nat -> A -> Map.t nat A -> Map.t nat A -> positive -> list
      audit_nat_encoding_event -> audit_trace (audit_trie_call (nat * A)) -> rw_facade_table_call A
  | RWFacadeTableGet : nat -> Map.t nat A -> option A -> positive -> list audit_nat_encoding_event
      -> audit_trace (audit_trie_call (nat * A)) -> rw_facade_table_call A.
Arguments RWFacadeTableSet {A}.
Arguments RWFacadeTableGet {A}.

Fixpoint rw_facade_table_atomic {A} (xs : list A) (start : nat) : Map.t nat A * audit_trace
    (rw_facade_table_call A) :=
  match xs with
  | nil => (Map.empty, [AuditCase 550 []; AuditConstruct 551 []])
  | item :: rest =>
    let next := S start in
    let '(table, tail_trace) := rw_facade_table_atomic rest next in
    let '(code, enc_trace) := audit_nat_encode start in
    let '(out, trie_trace) := audit_trie_set code (start, item) table in
    (out, [AuditCase 552 []; AuditConstruct 553 []] ++ tail_trace ++
      [AuditCall (RWFacadeTableSet start item table out code enc_trace trie_trace)])
  end.

Definition rw_facade_lookup_atomic {A} (i : nat) (table : Map.t nat A) : option A * audit_trace
    (rw_facade_table_call A) :=
  let '(code, enc_trace) := audit_nat_encode i in
  let '(out, trie_trace) := audit_map_code_get code table in
  (out, [AuditCall (RWFacadeTableGet i table out code enc_trace trie_trace)]).

Fixpoint rw_facade_nth {A} (xs : list A) (n : nat) : option A * audit_trace unit :=
  match n with
  | 0 =>
    match xs with
    | nil => (None, [AuditCase 560 []; AuditCase 561 []; AuditConstruct 562 []])
    | x :: _ => (Some x, [AuditCase 560 []; AuditCase 563 []; AuditConstruct 564 []])
    end
  | S n' =>
    match xs with
    | nil => (None, [AuditCase 565 []; AuditCase 566 []; AuditConstruct 567 []])
    | _ :: rest =>
      let '(out, trace) := rw_facade_nth rest n' in
      (out, [AuditCase 565 []; AuditCase 568 []] ++ trace)
    end
  end.

Inductive rw_facade_subst_call (K : Type) : Type :=
  | RWFacadeNth : list (term K) -> nat -> option (term K) -> audit_trace unit ->
      rw_facade_subst_call K.
Arguments RWFacadeNth {K}.

Fixpoint rw_facade_subst_atomic {K} (bindings : list (term K)) (t : term K) : term K * audit_trace
    (rw_facade_subst_call K) :=
  match t with
  | TVar i =>
    let '(found, nth_trace) := rw_facade_nth bindings i in
    match found with
    | None => (TVar i, [AuditCase 569 []; AuditCall (RWFacadeNth bindings i None nth_trace);
      AuditCase 570 []; AuditConstruct 571 []])
    | Some out => (out, [AuditCase 569 []; AuditCall (RWFacadeNth bindings i (Some out) nth_trace);
      AuditCase 572 []])
    end
  | TApp op args =>
    let fix visit (xs : list (term K)) : list (term K) * audit_trace (rw_facade_subst_call K) :=
      match xs with
      | nil => (nil, [AuditCase 573 []; AuditConstruct 574 []])
      | head :: rest =>
        let '(out, first_trace) := rw_facade_subst_atomic bindings head in
        let '(tail, tail_trace) := visit rest in
        (out :: tail, [AuditCase 575 []] ++ first_trace ++ tail_trace ++ [AuditConstruct 576 []])
      end in
    let '(children, trace) := visit args in
    (TApp op children, [AuditCase 577 []] ++ trace ++ [AuditConstruct 578 []])
  end.

Definition rw_facade_binding_atomic {K} (bindings : list (term K)) (index : nat) : term K *
    audit_trace unit :=
  let '(found, trace) := rw_facade_nth bindings index in
  match found with
  | None => (TVar index, trace ++ [AuditCase 710 []; AuditConstruct 711 []])
  | Some t => (t, trace ++ [AuditCase 712 []])
  end.

Inductive rw_facade_guard_action (K : Type) : Type :=
  | RWGuardExternal : nat -> rw_facade_guard_action K
  | RWGuardSubstitution : nat -> term K -> audit_trace unit -> rw_facade_guard_action K.
Arguments RWGuardExternal {K}.
Arguments RWGuardSubstitution {K}.

Inductive rw_facade_guard_program (K : Type) : Type :=
  | RWFacadeGuardReturn : bool -> nat -> rw_facade_guard_program K
  | RWFacadeGuardLookup : nat -> nat -> (term K -> rw_facade_guard_program K) ->
      rw_facade_guard_program K.
Arguments RWFacadeGuardReturn {K}.
Arguments RWFacadeGuardLookup {K}.

Record rw_facade_guard_adapter (K : Type) := RWFacadeGuardAdapter {
  rw_facade_guard_program_of : rewrite_rule K -> rw_facade_guard_program K
}.
Arguments RWFacadeGuardAdapter {K}.
Arguments rw_facade_guard_program_of {K}.

Fixpoint rw_facade_guard_interpret {K} (provider : nat -> term K * audit_trace unit) (program :
    rw_facade_guard_program K) : bool * list (rw_facade_guard_action K) :=
  match program with
  | RWFacadeGuardReturn answer body => (answer, [RWGuardExternal body])
  | RWFacadeGuardLookup body index next =>
    let '(answer, trace) := provider index in
    let '(out, later) := rw_facade_guard_interpret provider (next answer) in
    (out, RWGuardExternal body :: RWGuardSubstitution index answer trace :: later)
  end.

Definition rw_facade_guard_run {K} (adapter : rw_facade_guard_adapter K) (rule : rewrite_rule K)
    (provider : nat -> term K * audit_trace unit) :=
  rw_facade_guard_interpret provider (rw_facade_guard_program_of adapter rule).

(** A substitution guard action records the actual binding lookup; external actions are
    unrestricted. *)
Definition rw_facade_guard_action_valid {K} (bindings : list (term K)) (action :
    rw_facade_guard_action K) : Prop :=
  match action with
  | RWGuardExternal _ => True
  | RWGuardSubstitution i out trace => rw_facade_binding_atomic bindings i = (out, trace)
  end.

(** The guard run has an external execution witness, returns the side condition, and
    records only valid substitution actions. *)
Definition rw_facade_guard_adapter_adequate {K} (adapter : rw_facade_guard_adapter K)
    (external_execution : ((nat -> term K) -> bool) -> (nat -> term K) -> bool ->
      list (rw_facade_guard_action K) -> Prop) (r : rewrite_rule K) (bindings : list (term K)) :
    Prop :=
  let '(answer, actions) := rw_facade_guard_run adapter r (rw_facade_binding_atomic bindings) in
  external_execution (rule_side r) (legacy_subst bindings) answer actions /\
  answer = rule_side r (legacy_subst bindings) /\
  Forall (rw_facade_guard_action_valid bindings) actions.

Fixpoint rw_facade_vars {K} (t : term K) : list nat * audit_trace unit :=
  match t with
  | TVar i => ([i], [AuditCase 500 []; AuditConstruct 501 []; AuditConstruct 502 []])
  | TApp _ args =>
    let fix visit (xs : list (term K)) : list nat * audit_trace unit :=
      match xs with
      | nil => (nil, [AuditCase 503 []; AuditConstruct 504 []])
      | first :: rest =>
        let '(head, head_trace) := rw_facade_vars first in
        let '(tail, tail_trace) := visit rest in
        let '(out, append_trace) := rw_queue_append_atomic head tail in
        (out, [AuditCase 505 []] ++ head_trace ++ tail_trace ++ append_trace)
      end in
    let '(out, trace) := visit args in (out, AuditCase 506 [] :: trace)
  end.

Fixpoint rw_facade_leb (n m : nat) : bool * audit_trace unit :=
  match n with
  | 0 => (true, [AuditCase 507 []; AuditConstruct 508 []])
  | S n' =>
    match m with
    | 0 => (false, [AuditCase 509 []; AuditCase 510 []; AuditConstruct 511 []])
    | S m' =>
      let '(out, trace) := rw_facade_leb n' m' in
      (out, [AuditCase 509 []; AuditCase 512 []] ++ trace)
    end
  end.

Fixpoint rw_facade_forallb (bound : nat) (vars : list nat) : bool * audit_trace unit :=
  match vars with
  | nil => (true, [AuditCase 513 []; AuditConstruct 514 []])
  | i :: rest =>
    let '(current, current_trace) := rw_facade_leb (S i) bound in
    let '(tail, tail_trace) := rw_facade_forallb bound rest in
    let '(answer, and_trace) := if current then (tail, [AuditCase 517 []])
      else (false, [AuditCase 517 []; AuditConstruct 518 []]) in
    (answer, [AuditCase 515 []; AuditConstruct 516 []] ++ current_trace ++ tail_trace ++ and_trace)
  end.

Inductive rw_facade_gate_call (K : Type) : Type :=
  | RWFacadeGuard : rewrite_rule K -> list (term K) -> bool -> list (rw_facade_guard_action K) ->
      rw_facade_gate_call K.
Arguments RWFacadeGuard {K}.

Definition rw_facade_lift_unit {K} (event : audit_event unit) :
    audit_event (rw_facade_gate_call K) :=
  match event with
  | AuditCase site xs => AuditCase site xs
  | AuditConstruct site xs => AuditConstruct site xs
  | AuditKeyBit bit => AuditKeyBit bit
  | AuditArithmetic site xs => AuditArithmetic site xs
  | AuditCall _ => AuditCase 519 []
  end.

Definition rw_facade_gate_atomic {K} (adapter : rw_facade_guard_adapter K) (r : rewrite_rule K)
    (bindings : list (term K)) : bool * audit_trace (rw_facade_gate_call K) :=
  let '(left_bound, lb_trace) := rw_fuel_length bindings in
  let '(left_vars, lv_trace) := rw_facade_vars (rule_lhs r) in
  let '(left_ok, lo_trace) := rw_facade_forallb left_bound left_vars in
  let '(right_bound, rb_trace) := rw_fuel_length bindings in
  let '(right_vars, rv_trace) := rw_facade_vars (rule_rhs r) in
  let '(right_ok, ro_trace) := rw_facade_forallb right_bound right_vars in
  let '(both, both_trace) := if left_ok then (right_ok, [AuditCase 520 []])
    else (false, [AuditCase 520 []; AuditConstruct 521 []]) in
  let '(guard, actions) := rw_facade_guard_run adapter r (rw_facade_binding_atomic bindings) in
  let '(answer, result_trace) := if both then (guard, [AuditCase 522 []])
    else (false, [AuditCase 522 []; AuditConstruct 523 []]) in
  (answer, map rw_facade_lift_unit
    (lb_trace ++ lv_trace ++ lo_trace ++ rb_trace ++ rv_trace ++ ro_trace) ++
    map rw_facade_lift_unit both_trace ++ [AuditCall (RWFacadeGuard r bindings guard actions)] ++
    map rw_facade_lift_unit result_trace).

Fixpoint rw_facade_embed_atomic {K} (t : term K) : rw_term K unit nat * audit_trace unit :=
  match t with
  | TVar i => (RWVar tt i, [AuditCase 580 []; AuditConstruct 581 []])
  | TApp op args =>
    let fix visit (xs : list (term K)) : list (rw_term K unit nat) * audit_trace unit :=
      match xs with
      | nil => (nil, [AuditCase 582 []; AuditConstruct 583 []])
      | x :: rest =>
        let '(a, first_trace) := rw_facade_embed_atomic x in
        let '(b, bt) := visit rest in
        (a :: b, [AuditCase 584 []] ++ first_trace ++ bt ++ [AuditConstruct 585 []])
      end in
    let '(children, trace) := visit args in
    (RWApp tt op children, [AuditCase 586 []] ++ trace ++ [AuditConstruct 587 []])
  end.

Fixpoint rw_facade_project_atomic {K} (t : rw_term K unit nat) : term K * audit_trace unit :=
  match t with
  | RWVar _ i => (TVar i, [AuditCase 588 []; AuditConstruct 589 []])
  | RWApp _ op args =>
    let fix visit (xs : list (rw_term K unit nat)) : list (term K) * audit_trace unit :=
      match xs with
      | nil => (nil, [AuditCase 590 []; AuditConstruct 591 []])
      | x :: rest =>
        let '(a, first_trace) := rw_facade_project_atomic x in
        let '(b, bt) := visit rest in
        (a :: b, [AuditCase 592 []] ++ first_trace ++ bt ++ [AuditConstruct 593 []])
      end in
    let '(children, trace) := visit args in
    (TApp op children, [AuditCase 594 []] ++ trace ++ [AuditConstruct 595 []])
  end.

Fixpoint rw_facade_at_core {K} (pos : list nat) (t : rw_term K unit nat) : option (rw_term K unit
    nat) * audit_trace unit :=
  match pos with
  | nil => (Some t, [AuditCase 596 []; AuditConstruct 597 []])
  | i :: rest =>
    match t with
    | RWVar _ _ => (None, [AuditCase 598 []; AuditCase 599 []; AuditConstruct 600 []])
    | RWApp _ _ args =>
      let '(found, nth_trace) := rw_facade_nth args i in
      match found with
      | None => (None, [AuditCase 598 []; AuditCase 601 []] ++ nth_trace ++
          [AuditCase 602 []; AuditConstruct 603 []])
      | Some child =>
        let '(out, trace) := rw_facade_at_core rest child in
        (out, [AuditCase 598 []; AuditCase 601 []] ++ nth_trace ++ [AuditCase 604 []] ++ trace)
      end
    end
  end.

Fixpoint rw_facade_set_nth {A} (i : nat) (xs : list A) (value : A) : option (list A) * audit_trace
    unit :=
  match i with
  | 0 =>
    match xs with
    | nil => (None, [AuditCase 605 []; AuditCase 606 []; AuditConstruct 607 []])
    | _ :: rest => (Some (value :: rest), [AuditCase 605 []; AuditCase 608 [];
        AuditConstruct 609 []; AuditConstruct 610 []])
    end
  | S j =>
    match xs with
    | nil => (None, [AuditCase 611 []; AuditCase 612 []; AuditConstruct 613 []])
    | x :: rest =>
      let '(out, trace) := rw_facade_set_nth j rest value in
      match out with
      | None => (None, [AuditCase 611 []; AuditCase 614 []] ++ trace ++
          [AuditCase 615 []; AuditConstruct 616 []])
      | Some tail => (Some (x :: tail), [AuditCase 611 []; AuditCase 614 []] ++ trace ++
          [AuditCase 617 []; AuditConstruct 618 []; AuditConstruct 619 []])
      end
    end
  end.

Fixpoint rw_facade_replace_core {K} (pos : list nat) (t u : rw_term K unit nat) : option (rw_term K
    unit nat) * audit_trace unit :=
  match pos with
  | nil => (Some u, [AuditCase 620 []; AuditConstruct 621 []])
  | i :: rest =>
    match t with
    | RWVar _ _ => (None, [AuditCase 622 []; AuditCase 623 []; AuditConstruct 624 []])
    | RWApp sort op args =>
      let '(found, nth_trace) := rw_facade_nth args i in
      match found with
      | None => (None, [AuditCase 622 []; AuditCase 625 []] ++ nth_trace ++
          [AuditCase 626 []; AuditConstruct 627 []])
      | Some child =>
        let '(replacement, child_trace) := rw_facade_replace_core rest child u in
        match replacement with
        | None => (None, [AuditCase 622 []; AuditCase 625 []] ++ nth_trace ++
            [AuditCase 628 []] ++ child_trace ++ [AuditCase 629 []; AuditConstruct 630 []])
        | Some value =>
          let '(updated, set_trace) := rw_facade_set_nth i args value in
          match updated with
          | None => (None, [AuditCase 622 []; AuditCase 625 []] ++ nth_trace ++
              [AuditCase 628 []] ++ child_trace ++ [AuditCase 631 []] ++ set_trace ++
              [AuditCase 632 []; AuditConstruct 633 []])
          | Some children => (Some (RWApp sort op children),
              [AuditCase 622 []; AuditCase 625 []] ++ nth_trace ++ [AuditCase 628 []] ++
              child_trace ++ [AuditCase 631 []] ++ set_trace ++
              [AuditCase 634 []; AuditConstruct 635 []; AuditConstruct 636 []])
          end
        end
      end
    end
  end.

Definition rw_facade_at_atomic {K} (pos : list nat) (t : term K) : option (term K) * audit_trace
    unit :=
  let '(embedded, embed_trace) := rw_facade_embed_atomic t in
  let '(out, at_trace) := rw_facade_at_core pos embedded in
  match out with
  | None => (None, embed_trace ++ at_trace ++ [AuditCase 637 []; AuditConstruct 638 []])
  | Some selected =>
    let '(result, trace) := rw_facade_project_atomic selected in
    (Some result, embed_trace ++ at_trace ++ [AuditCase 639 []] ++ trace ++ [AuditConstruct 640 []])
  end.

Definition rw_facade_replace_atomic {K} (pos : list nat) (t u : term K) : option (term K) *
    audit_trace unit :=
  let '(embedded, et) := rw_facade_embed_atomic t in
  let '(replacement, ut) := rw_facade_embed_atomic u in
  let '(out, rt) := rw_facade_replace_core pos embedded replacement in
  match out with
  | None => (None, et ++ ut ++ rt ++ [AuditCase 641 []; AuditConstruct 642 []])
  | Some selected =>
    let '(result, trace) := rw_facade_project_atomic selected in
    (Some result, et ++ ut ++ rt ++ [AuditCase 643 []] ++ trace ++ [AuditConstruct 644 []])
  end.

Inductive rw_facade_code_call (K : Type) : Type :=
  | RWCodeOp : K -> positive -> list nat -> rw_facade_code_call K
  | RWCodeNat : nat -> positive -> list audit_nat_encoding_event -> rw_facade_code_call K
  | RWCodeAppend : list positive -> list positive -> list positive -> audit_trace unit ->
      rw_facade_code_call K
  | RWCodeLength : nat -> audit_trace unit -> rw_facade_code_call K
  | RWCodeList : list positive -> positive -> list (audit_list_event positive
      (audit_basic_encoding_event positive)) -> rw_facade_code_call K
  | RWCodeEmbed : term K -> rw_term K unit nat -> audit_trace unit -> rw_facade_code_call K.
Arguments RWCodeOp {K}.
Arguments RWCodeNat {K}.
Arguments RWCodeAppend {K}.
Arguments RWCodeLength {K}.
Arguments RWCodeList {K}.
Arguments RWCodeEmbed {K}.

Fixpoint rw_facade_tree_code_atomic {K} (op_encode : K -> positive * list nat) (tree : rw_term K
    unit nat) : list positive * audit_trace (rw_facade_code_call K) :=
  match tree with
  | RWVar _ i =>
    let '(code, nat_trace) := audit_nat_encode i in
    ([1%positive; 1%positive; code; 1%positive],
      [AuditCase 650 []; AuditCase 651 []; AuditCall (RWCodeNat i code nat_trace);
        AuditConstruct 652 []; AuditConstruct 653 []; AuditConstruct 654 []; AuditConstruct 655 [];
        AuditConstruct 656 []])
  | RWApp _ op args =>
    let '(op_code, op_trace) := op_encode op in
    let '(arity, length_trace) := rw_fuel_length args in
    let '(arity_code, nat_trace) := audit_nat_encode arity in
    let fix visit (xs : list (rw_term K unit nat)) :
        list positive * audit_trace (rw_facade_code_call K) :=
      match xs with
      | nil => (nil, [AuditCase 657 []; AuditConstruct 658 []])
      | x :: rest =>
        let '(head, ht) := rw_facade_tree_code_atomic op_encode x in
        let '(tail, tail_trace) := visit rest in
        let '(out, append_trace) := rw_queue_append_atomic head tail in
        (out, [AuditCase 659 []] ++ ht ++ tail_trace ++
          [AuditCall (RWCodeAppend head tail out append_trace)])
      end in
    let '(children, child_trace) := visit args in
    (2%positive :: 1%positive :: op_code :: arity_code :: children,
      [AuditCase 660 []; AuditCase 661 []; AuditCall (RWCodeOp op op_code op_trace);
        AuditCall (RWCodeLength arity length_trace);
        AuditCall (RWCodeNat arity arity_code nat_trace)] ++
        child_trace ++ [AuditConstruct 662 []; AuditConstruct 663 []; AuditConstruct 664 [];
          AuditConstruct 665 []])
  end.

Definition rw_facade_code_atomic {K} (op_encode : K -> positive * list nat) (t : term K) : positive
    * audit_trace (rw_facade_code_call K) :=
  let '(embedded, embed_trace) := rw_facade_embed_atomic t in
  let '(tokens, token_trace) := rw_facade_tree_code_atomic op_encode embedded in
  let '(code, code_trace) := audit_list_encode audit_positive_encode tokens in
  (code, [AuditCall (RWCodeEmbed t embedded embed_trace)] ++ token_trace ++
    [AuditCall (RWCodeList tokens code code_trace)]).

Fixpoint rw_facade_positive_eqb (p q : positive) : bool * audit_trace unit :=
  match p, q with
  | xH, xH => (true, [AuditCase 666 []; AuditCase 667 []; AuditConstruct 668 []])
  | xO p', xO q' =>
    let '(out, trace) := rw_facade_positive_eqb p' q' in
    (out, [AuditCase 669 []; AuditCase 670 []] ++ trace)
  | xI p', xI q' =>
    let '(out, trace) := rw_facade_positive_eqb p' q' in
    (out, [AuditCase 671 []; AuditCase 672 []] ++ trace)
  | _, _ => (false, [AuditCase 673 []; AuditCase 674 []; AuditConstruct 675 []])
  end.

Inductive rw_facade_eq_call (K : Type) : Type :=
  | RWFacadeCode : term K -> positive -> audit_trace (rw_facade_code_call K) -> rw_facade_eq_call K
  | RWFacadeEqBits : positive -> positive -> bool -> audit_trace unit -> rw_facade_eq_call K.
Arguments RWFacadeCode {K}.
Arguments RWFacadeEqBits {K}.

Definition rw_facade_eq_atomic {K} (op_encode : K -> positive * list nat) (t u : term K) : bool *
    audit_trace (rw_facade_eq_call K) :=
  let '(first_code, first_trace) := rw_facade_code_atomic op_encode t in
  let '(second_code, second_trace) := rw_facade_code_atomic op_encode u in
  let '(result, comparison_trace) := rw_facade_positive_eqb first_code second_code in
  (result, [AuditCall (RWFacadeCode t first_code first_trace);
    AuditCall (RWFacadeCode u second_code second_trace);
    AuditCall (RWFacadeEqBits first_code second_code result comparison_trace)]).

Inductive rw_facade_step_call (K : Type) : Type :=
  | RWFacadeLookup : nat -> option (rewrite_rule K) -> audit_trace (rw_facade_table_call
      (rewrite_rule K)) -> rw_facade_step_call K
  | RWFacadeGate : rewrite_rule K -> list (term K) -> bool -> audit_trace (rw_facade_gate_call K) ->
      rw_facade_step_call K
  | RWFacadeSubst : term K -> term K -> audit_trace (rw_facade_subst_call K) -> rw_facade_step_call
      K
  | RWFacadePosition : list nat -> term K -> option (term K) -> audit_trace unit ->
      rw_facade_step_call K
  | RWFacadeEqual : term K -> term K -> bool -> audit_trace (rw_facade_eq_call K) ->
      rw_facade_step_call K
  | RWFacadeReplace : list nat -> term K -> term K -> option (term K) -> audit_trace unit ->
      rw_facade_step_call K.
Arguments RWFacadeLookup {K}.
Arguments RWFacadeGate {K}.
Arguments RWFacadeSubst {K}.
Arguments RWFacadePosition {K}.
Arguments RWFacadeEqual {K}.
Arguments RWFacadeReplace {K}.

Definition rw_facade_step_atomic {K} (op_encode : K -> positive * list nat) (guard_adapter :
    rw_facade_guard_adapter K) (table : Map.t nat (rewrite_rule K)) (input : term K) (step :
    rewrite_step K) : option (term K) * audit_trace (rw_facade_step_call K) :=
  let index := step_rule step in
  let '(found, lookup_trace) := rw_facade_lookup_atomic index table in
  let prefix := [AuditCase 680 []; AuditCall (RWFacadeLookup index found lookup_trace)] in
  match found with
  | None => (None, prefix ++ [AuditCase 681 []; AuditConstruct 682 []])
  | Some r =>
    let bindings := step_subst step in
    let '(accept, gate_trace) := rw_facade_gate_atomic guard_adapter r bindings in
    let prefix := prefix ++ [AuditCase 683 []; AuditConstruct 684 [];
      AuditCall (RWFacadeGate r bindings accept gate_trace)] in
    if accept then
      let source_pattern := if step_forward step then rule_lhs r else rule_rhs r in
      let '(source, source_trace) := rw_facade_subst_atomic bindings source_pattern in
      let target_pattern := if step_forward step then rule_rhs r else rule_lhs r in
      let '(target, target_trace) := rw_facade_subst_atomic bindings target_pattern in
      let pos := step_pos step in
      let '(selected, position_trace) := rw_facade_at_atomic pos input in
      let prefix := prefix ++ [AuditCase 685 []; AuditCase 686 [];
        AuditCall (RWFacadeSubst source_pattern source source_trace); AuditCase 687 [];
        AuditCall (RWFacadeSubst target_pattern target target_trace);
        AuditCall (RWFacadePosition pos input selected position_trace)] in
      match selected with
      | None => (None, prefix ++ [AuditCase 688 []; AuditConstruct 689 []])
      | Some actual =>
        let '(equal, equal_trace) := rw_facade_eq_atomic op_encode actual source in
        let prefix := prefix ++ [AuditCase 690 []; AuditCall (RWFacadeEqual actual source equal
          equal_trace)] in
        if equal then
          let '(out, replace_trace) := rw_facade_replace_atomic pos input target in
          (out, prefix ++ [AuditCase 691 [];
            AuditCall (RWFacadeReplace pos input target out replace_trace)])
        else (None, prefix ++ [AuditCase 692 []; AuditConstruct 693 []])
      end
    else (None, prefix ++ [AuditCase 694 []; AuditConstruct 695 []])
  end.

Inductive rw_facade_replay_call (K : Type) : Type :=
  | RWFacadeReplayStep : term K -> rewrite_step K -> option (term K) -> audit_trace
      (rw_facade_step_call K) -> rw_facade_replay_call K.
Arguments RWFacadeReplayStep {K}.

Fixpoint rw_facade_replay_atomic {K} (op_encode : K -> positive * list nat) (guard_adapter :
    rw_facade_guard_adapter K) (table : Map.t nat (rewrite_rule K)) (input : term K) (steps : list
    (rewrite_step K)) : option (term K) * audit_trace (rw_facade_replay_call K) :=
  match steps with
  | nil => (Some input, [AuditCase 696 []; AuditConstruct 697 []])
  | step :: rest =>
    let '(out, step_trace) := rw_facade_step_atomic op_encode guard_adapter table input step in
    match out with
    | None => (None, [AuditCase 698 []; AuditCall (RWFacadeReplayStep input step None step_trace);
        AuditCase 699 []; AuditConstruct 700 []])
    | Some next =>
      let '(result, tail_trace) := rw_facade_replay_atomic op_encode guard_adapter
        table next rest in
      (result, [AuditCase 698 []; AuditCall (RWFacadeReplayStep input step (Some next) step_trace);
        AuditCase 701 []] ++ tail_trace)
    end
  end.

Inductive rw_facade_checker_call (K : Type) : Type :=
  | RWFacadeCheckerTable : Map.t nat (rewrite_rule K) -> audit_trace (rw_facade_table_call
      (rewrite_rule K)) -> rw_facade_checker_call K
  | RWFacadeCheckerReplay : term K -> list (rewrite_step K) -> option (term K) -> audit_trace
      (rw_facade_replay_call K) -> rw_facade_checker_call K
  | RWFacadeCheckerEqual : term K -> term K -> bool -> audit_trace (rw_facade_eq_call K) ->
      rw_facade_checker_call K.
Arguments RWFacadeCheckerTable {K}.
Arguments RWFacadeCheckerReplay {K}.
Arguments RWFacadeCheckerEqual {K}.

Definition rw_facade_checker_atomic {K} (op_encode : K -> positive * list nat) (guard_adapter :
    rw_facade_guard_adapter K) (rules : list (rewrite_rule K)) (input target : term K) (steps : list
    (rewrite_step K)) : bool * audit_trace (rw_facade_checker_call K) :=
  let '(table, table_trace) := rw_facade_table_atomic rules 0 in
  let '(out, replay_trace) := rw_facade_replay_atomic op_encode guard_adapter table input steps in
  let prefix := [AuditCall (RWFacadeCheckerTable table table_trace);
    AuditCall (RWFacadeCheckerReplay input steps out replay_trace)] in
  match out with
  | None => (false, prefix ++ [AuditCase 702 []; AuditConstruct 703 []])
  | Some actual =>
    let '(answer, eq_trace) := rw_facade_eq_atomic op_encode actual target in
    (answer, prefix ++ [AuditCase 704 [];
      AuditCall (RWFacadeCheckerEqual actual target answer eq_trace)])
  end.

(** When operator encoding agrees and the guard adapter is adequate for every rule and
    binding list, erasing the checker trace yields the original explanation checker result. *)
Definition rw_facade_checker_erases_statement : Prop :=
  forall K (EK : encoding K) op_encode guard_adapter guard_execution rules input target steps,
    (forall op, fst (op_encode op) = encode EK op) ->
    (forall r bindings,
      rw_facade_guard_adapter_adequate guard_adapter guard_execution r bindings) ->
    fst (rw_facade_checker_atomic op_encode guard_adapter rules input target steps) =
      check_explanation EK rules input target steps.

(** The checker erasure contract requires agreement of operator encoding and guard
    adapters before identifying the observed and original checker results. *)
Definition rw_facade_checker_erases_contract : Prop :=
  rw_facade_checker_erases_statement.
