(** * RewriteAuditPlainCore2

    This module computes plain proof keys, evidence closure, and provenance connections.
    For example, a variable whose sort and value both encode as 1 emits [1; 1; 1; 1].
    Builds on: RewriteAuditPlainCore1 and
    RewriteAuditProofCarrier. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditPlainCore1 RewriteAuditPlainPrimitives
  RewriteAuditProofCarrier RewriteAuditProofClosure RewriteAuditSharedReference.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_rw_shared_unfold_atomic :=
  @rw_shared_unfold.

Arguments rw_plain_rw_shared_unfold_atomic {K Sort V} _.

Fixpoint rw_plain_rw_rp_term_tokens {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (term : rw_term K Sort V) : list positive :=
  match term with
  | RWVar ty v =>
    let s := rw_plain_rw_queue_encoder_run sort ty in
    let x := rw_plain_rw_queue_encoder_run value v in
    [1%positive; s; x; 1%positive]
  | RWApp ty k children =>
    let s := rw_plain_rw_queue_encoder_run sort ty in
    let x := rw_plain_rw_queue_encoder_run op k in
    let arity := rw_plain_rw_fuel_length children in
    let arity_code := rw_plain_audit_nat_encode arity in
    let fix visit (ts : list (rw_term K Sort V)) : list positive :=
      match ts with
      | nil => nil
      | t :: rest =>
        let head := rw_plain_rw_rp_term_tokens op sort value t in
        let tail := visit rest in
        let out := rw_plain_rw_rp_append head tail in
        out
      end in
    let tokens := visit children in
    2%positive :: s :: x :: arity_code :: tokens
  end.

Definition rw_plain_rw_rp_term_key {K Sort V} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (term : rw_term K Sort V) : positive :=
  let tokens := rw_plain_rw_rp_term_tokens op sort value term in
  let code := rw_plain_audit_list_encode rw_plain_audit_positive_encode tokens in
  code.

Fixpoint rw_plain_rw_rp_fresh_loop (ids : list positive) (largest : positive) : positive :=
  match ids with
  | nil =>
    let fresh := rw_plain_rw_fuel_pos_succ largest in
    fresh
  | id :: rest =>
    let order := rw_plain_rw_rd_positive_compare_cont Eq id largest in
    let next :=
      match order with
      | Gt => id
      | _ => largest
      end in
    let fresh := rw_plain_rw_rp_fresh_loop rest next in
    fresh
  end.

Definition rw_plain_rw_rp_proof_get (lhs rhs : positive) (index : rw_rp_proof_index) :
    option positive :=
  let answer := rw_plain_audit_map_get rw_plain_rw_rd_pair_encode (lhs, rhs) index in
  answer.

Definition rw_plain_rw_rp_proof_put (lhs rhs id : positive) (index : rw_rp_proof_index) :
    rw_rp_proof_index :=
  let answer := rw_plain_audit_map_set rw_plain_rw_rd_pair_encode (lhs, rhs) id index in
  answer.

Definition rw_plain_rw_rp_add_evidence {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (lhs rhs : rw_term K Sort V)
    (reason : rw_evidence_reason K Sort V H) (state : rw_rp_connection_state K Sort V H) :
    (positive * rw_rp_connection_state K Sort V H) :=
  let proof := rw_rp_proof state in
  let id := rw_plain_rw_rp_fresh_loop (rw_provenance_ids proof) 1%positive in
  let node := RWEvidenceNode lhs rhs reason stamp in
  let nodes :=
    rw_plain_audit_map_set rw_plain_audit_positive_encode id node (rw_provenance_nodes proof) in
  let lk := rw_plain_rw_rp_term_key op sort value lhs in
  let rk := rw_plain_rw_rp_term_key op sort value rhs in
  let index := rw_plain_rw_rp_proof_put lk rk id (rw_rp_index state) in
  (id, RwRpConnectionState (RWProvenance (id :: rw_provenance_ids proof) nodes) index).

Fixpoint rw_plain_rw_rp_index_existing {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (ids : list positive) (proof : rw_provenance K Sort V H)
    (index : rw_rp_proof_index) : rw_rp_proof_index :=
  match ids with
  | nil => index
  | id :: rest =>
    let found :=
      rw_plain_audit_map_get rw_plain_audit_positive_encode id (rw_provenance_nodes proof) in
    match found with
    | None =>
      let out := rw_plain_rw_rp_index_existing op sort value rest proof index in out
    | Some node =>
      let lk := rw_plain_rw_rp_term_key op sort value (rw_evidence_left node) in
      let rk :=
        rw_plain_rw_rp_term_key op sort value (rw_evidence_right node) in
      let next :=
        rw_plain_rw_rp_proof_put lk rk id index in
      let out := rw_plain_rw_rp_index_existing op sort value rest proof next in out
    end
  end.

Definition rw_plain_rw_rp_try_symmetry {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (lhs rhs : rw_term K Sort V)
    (state : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort V H) :=
  let lk := rw_plain_rw_rp_term_key op sort value lhs in
  let rk := rw_plain_rw_rp_term_key op sort value rhs in
  let reverse := rw_plain_rw_rp_proof_get rk lk (rw_rp_index state) in
  match reverse with
  | None => (None, state)
  | Some id =>
    let '(new, next) :=
      rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceSym id) state in
    (Some new, next)
  end.

Fixpoint rw_plain_rw_rp_try_transitivity {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (lhs rhs : rw_term K Sort V)
    (middles : list (rw_term K Sort V)) (state : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort V H) :=
  match middles with
  | nil => (None, state)
  | middle :: rest =>
    let lk := rw_plain_rw_rp_term_key op sort value lhs in
    let mk := rw_plain_rw_rp_term_key op sort value middle in
    let rk := rw_plain_rw_rp_term_key op sort value rhs in
    let first := rw_plain_rw_rp_proof_get lk mk (rw_rp_index state) in
    match first with
    | None =>
      let answer := rw_plain_rw_rp_try_transitivity op sort value stamp lhs rhs rest state in
      answer
    | Some a =>
      let second := rw_plain_rw_rp_proof_get mk rk (rw_rp_index state) in
      match second with
      | None =>
        let answer := rw_plain_rw_rp_try_transitivity op sort value stamp lhs rhs rest state in
        answer
      | Some b =>
        let '(id, next) :=
          rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceTrans a b) state in
        (Some id, next)
      end
    end
  end.

Fixpoint rw_plain_rw_rp_children_evidence {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (lhs rhs : list (rw_term K Sort V))
    (state : rw_rp_connection_state K Sort V H) : option (list positive) :=
  match lhs, rhs with
  | nil, nil => Some nil
  | a :: xs, b :: ys =>
    let lk := rw_plain_rw_rp_term_key op sort value a in
    let rk := rw_plain_rw_rp_term_key op sort value b in
    let found := rw_plain_rw_rp_proof_get lk rk (rw_rp_index state) in
    match found with
    | None => None
    | Some id =>
      let tail := rw_plain_rw_rp_children_evidence op sort value xs ys state in
      option_map (fun ids => id :: ids) tail
    end
  | _, _ => None
  end.

Definition rw_plain_rw_rp_try_congruence {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (lhs rhs : rw_term K Sort V)
    (state : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort V H) :=
  match lhs, rhs with
  | RWApp s k xs, RWApp t l ys =>
    let sc := rw_plain_rw_queue_encoder_run sort s in
    let tc := rw_plain_rw_queue_encoder_run sort t in
    let same_sort := rw_plain_audit_positive_eqb sc tc in
    if same_sort then
      let kc := rw_plain_rw_queue_encoder_run op k in
      let lc := rw_plain_rw_queue_encoder_run op l in
      let same_op := rw_plain_audit_positive_eqb kc lc in
      if same_op then
        let children := rw_plain_rw_rp_children_evidence op sort value xs ys state in
        match children with
        | None => (None, state)
        | Some ids =>
          let '(id, next) :=
            rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs
              (RWEvidenceCongruence ids) state in
          (Some id, next)
        end
      else (None, state)
    else (None, state)
  | _, _ => (None, state)
  end.

Definition rw_plain_rw_rp_close_pair {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (terms : list (rw_term K Sort V))
    (lhs rhs : rw_term K Sort V) (state : rw_rp_connection_state K Sort V H) :
    rw_rp_connection_state K Sort V H :=
  let lk := rw_plain_rw_rp_term_key op sort value lhs in
  let rk := rw_plain_rw_rp_term_key op sort value rhs in
  let present := rw_plain_rw_rp_proof_get lk rk (rw_rp_index state) in
  match present with
  | Some _ => state
  | None =>
    let same := rw_plain_audit_positive_eqb lk rk in
    if same then
      let '(_, next) :=
        rw_plain_rw_rp_add_evidence op sort value stamp lhs rhs RWEvidenceRefl state in
      next
    else
      let '(symmetric, first) := rw_plain_rw_rp_try_symmetry op sort value stamp lhs rhs state in
      match symmetric with
      | Some _ => first
      | None =>
        let '(transitive, second) :=
          rw_plain_rw_rp_try_transitivity op sort value stamp lhs rhs terms first in
        match transitive with
        | Some _ => second
        | None =>
          let '(_, final) :=
            rw_plain_rw_rp_try_congruence op sort value stamp lhs rhs second in
          final
        end
      end
  end.

Fixpoint rw_plain_rw_rp_close_row {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (terms : list (rw_term K Sort V))
    (lhs : rw_term K Sort V) (rights : list (rw_term K Sort V))
    (state : rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort V H :=
  match rights with
  | nil => state
  | rhs :: rest =>
    let next := rw_plain_rw_rp_close_pair op sort value stamp terms lhs rhs state in
    let out := rw_plain_rw_rp_close_row op sort value stamp terms lhs rest next in
    out
  end.

Fixpoint rw_plain_rw_rp_close_pass {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (terms lefts : list (rw_term K Sort V))
    (state : rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort V H :=
  match lefts with
  | nil => state
  | lhs :: rest =>
    let next := rw_plain_rw_rp_close_row op sort value stamp terms lhs terms state in
    let out := rw_plain_rw_rp_close_pass op sort value stamp terms rest next in
    out
  end.

Fixpoint rw_plain_rw_rp_close_rounds {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (stamp : nat * nat) (terms : list (rw_term K Sort V)) (fuel : positive)
    (state : rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort V H :=
  match fuel with
  | xH =>
    let out := rw_plain_rw_rp_close_pass op sort value stamp terms terms state in
    out
  | xO rest =>
    let middle := rw_plain_rw_rp_close_rounds op sort value stamp terms rest state in
    let out := rw_plain_rw_rp_close_rounds op sort value stamp terms rest middle in
    out
  | xI rest =>
    let first := rw_plain_rw_rp_close_pass op sort value stamp terms terms state in
    let middle := rw_plain_rw_rp_close_rounds op sort value stamp terms rest first in
    let out := rw_plain_rw_rp_close_rounds op sort value stamp terms rest middle in
    out
  end.

Fixpoint rw_plain_rw_rp_subterms {K Sort V} (term : rw_term K Sort V) : list (rw_term K Sort V) :=
  match term with
  | RWVar _ _ => [term]
  | RWApp _ _ children =>
    let fix visit (ts : list (rw_term K Sort V)) : list (rw_term K Sort V) :=
      match ts with
      | nil => nil
      | t :: rest =>
        let head := rw_plain_rw_rp_subterms t in
        let tail := visit rest in
        let out := rw_plain_rw_rp_append head tail in
        out
      end in
    let others := visit children in
    term :: others
  end.

Fixpoint rw_plain_rw_rp_nat_compare (a b : nat) : comparison :=
  match a, b with
  | 0, 0 => Eq
  | 0, S _ => Lt
  | S _, 0 => Gt
  | S x, S y =>
    let answer := rw_plain_rw_rp_nat_compare x y in
    answer
  end.

Fixpoint rw_plain_rw_rp_evidence_terms {K Sort V H}
    (entries : list (positive * rw_evidence_node K Sort V H)) (largest_group : nat) :
    (list (rw_term K Sort V) * nat) :=
  match entries with
  | nil => (nil, largest_group)
  | (_, node) :: rest =>
    let group := fst (rw_evidence_time node) in
    let order := rw_plain_rw_rp_nat_compare group largest_group in
    let next :=
      match order with
      | Gt => group
      | _ => largest_group
      end in
    let lhs := rw_plain_rw_rp_subterms (rw_evidence_left node) in
    let rhs := rw_plain_rw_rp_subterms (rw_evidence_right node) in
    let '(tail, maximum) := rw_plain_rw_rp_evidence_terms rest next in
    let both := rw_plain_rw_rp_append lhs rhs in
    let out := rw_plain_rw_rp_append both tail in
    (out, maximum)
  end.

Definition rw_plain_rw_rp_connect_atomic {K Sort V H} (op : encoding K) (sort : encoding Sort)
    (value : encoding V) (proof : rw_provenance K Sort V H) (lhs rhs : rw_term K Sort V) :
    option (rw_provenance K Sort V H * positive) :=
  let entries := rw_plain_audit_map_elements (rw_provenance_nodes proof) in
  let '(known, largest) := rw_plain_rw_rp_evidence_terms entries 0 in
  let lefts := rw_plain_rw_rp_subterms lhs in
  let rights := rw_plain_rw_rp_subterms rhs in
  let both := rw_plain_rw_rp_append lefts rights in
  let terms := rw_plain_rw_rp_append both known in
  let index :=
    rw_plain_rw_rp_index_existing op sort value (rw_provenance_ids proof) proof Map.empty in
  let count := rw_plain_rw_fuel_length terms in
  let square := rw_plain_rw_fuel_mul count count in
  let fuel := rw_plain_rw_fuel_to_positive square in
  let final :=
    rw_plain_rw_rp_close_rounds op sort value (S largest, 0) terms fuel
      (RwRpConnectionState proof index) in
  let lk := rw_plain_rw_rp_term_key op sort value lhs in
  let rk := rw_plain_rw_rp_term_key op sort value rhs in
  let answer := rw_plain_rw_rp_proof_get lk rk (rw_rp_index final) in
  option_map (fun id => (rw_rp_proof final, id)) answer.

Definition rw_plain_rw_rp_stamp_put (stamp : nat * nat) (id : positive)
    (table : Map.t (nat * nat) positive) : Map.t (nat * nat) positive :=
  let out := rw_plain_audit_map_set rw_plain_rw_rp_stamp_encode stamp id table in
  out.
