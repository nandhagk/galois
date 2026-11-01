(** * Materialization source-accounting foundation

    These mathematical writers retain fixed source frames and actual collection subruns.
    For example, a counted map lookup retains its key, encoded key and trie trace.
    Builds on: RulesSyntax, RulesStratify and the shared collection audit models. *)

From Stdlib Require Import List NArith PArith ZArith Bool Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsTable CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditUnion.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesDelta.
Import List.ListNotations.

Inductive mat_frame : Type :=
  | MatBlock (site : nat)
  | MatNat (site lhs rhs : nat)
  | MatEncode : forall Q, encoding Q -> Q -> positive -> mat_frame
  | MatLevel : forall P, stratification P -> P -> nat -> mat_frame
  | MatArity : forall P, program P -> P -> nat -> mat_frame
  | MatOperand (size : nat)
  | MatChild (site work operand_size : nat)
  | MatImported : forall T, nat -> T -> nat -> nat -> mat_frame.

Definition mat_frame_work (e : mat_frame) : nat :=
  match e with
  | MatBlock _ => 100
  | MatNat _ a b => 1 + a + b
  | MatEncode _ _ _ _
  | MatLevel _ _ _ _
  | MatArity _ _ _ _ => 1
  | MatOperand _ => 0
  | MatChild _ work _
  | MatImported _ _ _ work _ => work
  end.

Definition mat_work (trace : list mat_frame) : nat :=
  fold_right (fun e n => mat_frame_work e + n) 0 trace.

Definition mat_width (trace : list mat_frame) : nat :=
  fold_right (fun e n => Nat.max n (match e with
    | MatNat _ a b => 1 + a + b
    | MatEncode _ _ _ code => Pos.size_nat code
    | MatLevel _ _ _ value
    | MatArity _ _ _ value => S value
    | MatOperand size
    | MatChild _ _ size
    | MatImported _ _ _ _ size => size
    | _ => 1
    end)) 1 trace.

Definition mat_run (A : Type) : Type := A * list mat_frame.

Definition mat_return {A} (a : A) : mat_run A := (a, [MatBlock 0]).

Definition mat_bind {A B} (r : mat_run A) (f : A -> mat_run B) : mat_run B :=
  let '(a, first) := r in
  let '(b, second) := f a in
  (b, first ++ second).

Notation "x <- r ;; body" := (mat_bind r (fun x => body))
  (at level 100, r at next level, right associativity).

Definition mat_mark {A} (site : nat) (r : mat_run A) : mat_run A :=
  (fst r, MatBlock site :: snd r).

Definition mat_lift {A E} (site : nat) (size : A -> nat) (work : list E -> nat)
    (r : A * list E) : mat_run A :=
  let '(a, events) := r in
  (a, [MatImported (A * list E) site (a, events) (work events) (size a)]).

Definition mat_emit (e : mat_frame) : mat_run unit := (tt, [e]).

Fixpoint mat_map {A B} (f : A -> mat_run B) (xs : list A) : mat_run (list B) :=
  mat_mark 1 (match xs with
    | [] => mat_return []
    | x :: rest => y <- f x;; ys <- mat_map f rest;; mat_return (y :: ys)
    end).

Fixpoint mat_append {A} (xs ys : list A) : mat_run (list A) :=
  mat_mark 2 (match xs with
    | [] => mat_return ys
    | x :: rest => tail <- mat_append rest ys;; mat_return (x :: tail)
    end).

Fixpoint mat_flatmap {A B} (f : A -> mat_run (list B)) (xs : list A) : mat_run (list B) :=
  mat_mark 3 (match xs with
    | [] => mat_return []
    | x :: rest => first <- f x;; later <- mat_flatmap f rest;; mat_append first later
    end).

Fixpoint mat_filter {A} (f : A -> mat_run bool) (xs : list A) : mat_run (list A) :=
  mat_mark 4 (match xs with
    | [] => mat_return []
    | x :: rest => keep <- f x;; tail <- mat_filter f rest;;
        mat_return (if keep then x :: tail else tail)
    end).

Fixpoint mat_foldr {A B} (f : A -> B -> mat_run B) (xs : list A) (initial : B) : mat_run B :=
  mat_mark 5 (match xs with
    | [] => mat_return initial
    | x :: rest => before <- mat_foldr f rest initial;; f x before
    end).

Fixpoint mat_foldl {A B} (f : B -> A -> mat_run B) (xs : list A) (initial : B) : mat_run B :=
  mat_mark 6 (match xs with
    | [] => mat_return initial
    | x :: rest => next <- f initial x;; mat_foldl f rest next
    end).

Fixpoint mat_all {A} (f : A -> mat_run bool) (xs : list A) : mat_run bool :=
  mat_mark 7 (match xs with
    | [] => mat_return true
    | x :: rest => first <- f x;; later <- mat_all f rest;; mat_return (first && later)
    end).

Definition mat_encode {Q} (E : encoding Q) (q : Q) : mat_run positive :=
  let code := encode E q in (code, [MatEncode Q E q code]).

Inductive mat_level_context (P : Type) : Type :=
  | MatExternalLevels (st : stratification P)
  | MatCapturedLevels (E : encoding P) (levels : Map.t P nat) (bound : nat).
Arguments MatExternalLevels {P} _.
Arguments MatCapturedLevels {P} _ _ _.

Definition mat_native_levels {P} (st : mat_level_context P) : stratification P :=
  match st with
  | MatExternalLevels native => native
  | MatCapturedLevels E levels bound => Stratification (level_at E levels) bound
  end.

Definition mat_arity {P} (prog : program P) (p : P) : mat_run nat :=
  let n := arity prog p in (n, [MatArity P prog p n]).

Definition mat_nat (site : nat) (f : nat -> nat -> nat) (a b : nat) : mat_run nat :=
  (f a b, [MatNat site a b]).

Definition mat_nat_test (site : nat) (f : nat -> nat -> bool) (a b : nat) : mat_run bool :=
  (f a b, [MatNat site a b]).

Definition mat_tuple_size (row : tuple) : nat :=
  fold_right (fun p n => 1 + Pos.size_nat p + n) 1 row.

Definition mat_set_size {Q} (s : FinSet.t Q) : nat := audit_trie_nodes s.

Definition mat_db_size {P} (db : database P) : nat :=
  1 + audit_trie_nodes db +
  fold_right (fun entry n => audit_trie_nodes (snd entry) + n) 0 (Map.elements db).

Definition mat_get {Q A} (E : encoding Q) (key : Q) (input : Map.t Q A) : mat_run (option A) :=
  code <- mat_encode E key;;
  let '(out, events) := audit_map_code_get code input in
  (out, [MatImported _ 10 (key, code, input, out, events)
    (audit_trie_get_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes input)]).

Definition mat_level {P} (st : mat_level_context P) (p : P) : mat_run nat :=
  match st with
  | MatExternalLevels native => let n := level native p in (n, [MatLevel P native p n])
  | MatCapturedLevels E levels _ =>
      found <- mat_get E p levels;;
      mat_return (match found with
      | Some n => n
      | None => 0
      end)
  end.

Definition mat_set {Q A} (E : encoding Q) (key : Q) (value : A) (input : Map.t Q A) :
    mat_run (Map.t Q A) :=
  code <- mat_encode E key;;
  let '(out, events) := audit_trie_set code (key, value) input in
  (out, [MatImported _ 11 (key, code, value, input, out, events)
    (audit_trie_update_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes out)]).

Definition mat_rel {P} (prog : program P) (db : database P) (p : P) : mat_run (FinSet.t tuple) :=
  found <- mat_get (penc prog) p db;;
  mat_return (match found with
  | Some s => s
  | None => FinSet.empty
  end).

Definition mat_elements {Q} (s : FinSet.t Q) : mat_run (list Q) :=
  mat_lift 12 (fun xs => 1 + length xs + audit_trie_nodes s)
    audit_set_elements_work (audit_finset_elements s).

Definition mat_of_list {Q E} (enc : Q -> positive * list E) (ew : list E -> nat) (xs : list Q) :=
  mat_lift 13 (fun s => 1 + length xs + audit_trie_nodes s)
    (audit_finset_source_work ew) (audit_finset_of_list enc xs).

Definition mat_tuple_mem (row : tuple) (s : FinSet.t tuple) :=
  mat_lift 14 (fun _ => 1 + mat_tuple_size row + audit_trie_nodes s)
    (audit_finset_source_work (audit_list_events_work audit_basic_encoding_work))
    (audit_finset_mem (audit_list_encode audit_positive_encode) row s).

Definition mat_union {Q} (a b : FinSet.t Q) :=
  mat_lift 15 (fun s => 1 + audit_trie_nodes a + audit_trie_nodes b + audit_trie_nodes s)
    audit_finset_union_source_work (audit_finset_union a b).

Definition mat_nat_add (v : nat) (s : FinSet.t nat) :=
  mat_lift 16 (fun out => 1 + v + audit_trie_nodes s + audit_trie_nodes out)
    (audit_finset_source_work audit_nat_events_work) (audit_finset_add audit_nat_encode v s).

Definition mat_get_encoded {Q A} (enc : Q -> mat_run positive) (key : Q) (input : Map.t Q A) :=
  code <- enc key;;
  let '(out, events) := audit_map_code_get code input in
  (out, [MatImported _ 10 (key, code, input, out, events)
    (audit_trie_get_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes input)]).

Definition mat_set_encoded {Q A} (enc : Q -> mat_run positive) (key : Q) (value : A)
    (input : Map.t Q A) :=
  code <- enc key;;
  let '(out, events) := audit_trie_set code (key, value) input in
  (out, [MatImported _ 11 (key, code, value, input, out, events)
    (audit_trie_update_trace_source_work events) (1 + Pos.size_nat code + audit_trie_nodes out)]).

Definition mat_predicate_set_encoded {Q} (enc : Q -> mat_run positive) (keys : list Q) :=
  mat_foldl (fun set key => mat_set_encoded enc key tt set) keys Map.empty.
