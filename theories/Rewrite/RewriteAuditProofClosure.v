(** * RewriteAuditProofClosure

    This module constructs evidence connections and states their soundness and completeness.
    For example, closing natural variable 0 against itself adds reflexivity evidence when
    its encoded pair is absent from the proof index.
    Builds on: ProofCarrier, SharedCompare and QueueReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditProofCarrier RewriteAuditQueueReference
  RewriteAuditSharedCompare.
Import List.ListNotations.

Fixpoint rw_rp_append {A} (xs ys : list A) : list A * nat :=
  match xs with
  | nil => (ys, 64)
  | x :: rest =>
    let '(tail, work) := rw_rp_append rest ys in
    (x :: tail, 128 + work)
  end.

Fixpoint rw_rp_term_tokens {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (term : rw_term K Sort V) : list positive * nat :=
  match term with
  | RWVar ty v =>
    let '(s, sw) := rw_queue_encoder_run sort ty in
    let '(x, xw) := rw_queue_encoder_run value v in
    ([1%positive; s; x; 1%positive], 64 + sw + xw)
  | RWApp ty k children =>
    let '(s, sw) := rw_queue_encoder_run sort ty in
    let '(x, xw) := rw_queue_encoder_run op k in
    let '(arity, lt) := rw_fuel_length children in
    let '(arity_code, et) := audit_nat_encode arity in
    let fix visit (ts : list (rw_term K Sort V)) : list positive * nat :=
      match ts with
      | nil => (nil, 64)
      | t :: rest =>
        let '(head, hw) := rw_rp_term_tokens op sort value t in
        let '(tail, tw) := visit rest in
        let '(out, aw) := rw_rp_append head tail in
        (out, 64 + hw + tw + aw)
      end in
    let '(tokens, work) := visit children in
    (2%positive :: s :: x :: arity_code :: tokens,
      64 + sw + xw + audit_work lt + audit_nat_events_work et + work)
  end.

Definition rw_rp_term_key {K Sort V} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (term : rw_term K Sort V) : positive * nat :=
  let '(tokens, work) := rw_rp_term_tokens op sort value term in
  let '(code, trace) := audit_list_encode audit_positive_encode tokens in
  (code, 64 + work + audit_list_events_work audit_basic_encoding_work trace).

Fixpoint rw_rp_fresh_loop (ids : list positive) (largest : positive) : positive * nat :=
  match ids with
  | nil =>
    let '(fresh, trace) := rw_fuel_pos_succ largest in
    (fresh, 64 + audit_work trace)
  | id :: rest =>
    let '(order, comparison_work) := rw_rd_positive_compare_cont Eq id largest in
    let next :=
      match order with
      | Gt => id
      | _ => largest
      end in
    let '(fresh, tail_work) := rw_rp_fresh_loop rest next in
    (fresh, 64 + comparison_work + tail_work)
  end.

Definition rw_rp_proof_index :=
  Map.t (positive * positive) positive.

Definition rw_rp_proof_get (lhs rhs : positive) (index : rw_rp_proof_index) :
    option positive * nat :=
  let '(answer, trace) := audit_map_get rw_rd_pair_encode (lhs, rhs) index in
  (answer, 64 + audit_map_source_work rw_rd_pair_encoding_work trace).

Definition rw_rp_proof_put (lhs rhs id : positive) (index : rw_rp_proof_index) :
    rw_rp_proof_index * nat :=
  let '(answer, trace) := audit_map_set rw_rd_pair_encode (lhs, rhs) id index in
  (answer, 64 + audit_map_source_work rw_rd_pair_encoding_work trace).

Record rw_rp_connection_state (K Sort V H : Type) := RwRpConnectionState {
  rw_rp_proof : rw_provenance K Sort V H;
  rw_rp_index : rw_rp_proof_index
}.
Arguments RwRpConnectionState {K Sort V H}.
Arguments rw_rp_proof {K Sort V H}.
Arguments rw_rp_index {K Sort V H}.

Definition rw_rp_add_evidence {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (lhs rhs : rw_term K Sort V) (reason : rw_evidence_reason K Sort V H)
    (state : rw_rp_connection_state K Sort V H) :
    (positive * rw_rp_connection_state K Sort V H) * nat :=
  let proof := rw_rp_proof state in
  let '(id, fresh_work) := rw_rp_fresh_loop (rw_provenance_ids proof) 1%positive in
  let node := RWEvidenceNode lhs rhs reason stamp in
  let '(nodes, nt) := audit_map_set audit_positive_encode id node (rw_provenance_nodes proof) in
  let '(lk, lw) := rw_rp_term_key op sort value lhs in
  let '(rk, rw) := rw_rp_term_key op sort value rhs in
  let '(index, iw) := rw_rp_proof_put lk rk id (rw_rp_index state) in
  ((id, RwRpConnectionState (RWProvenance (id :: rw_provenance_ids proof) nodes) index),
    64 + fresh_work + audit_map_source_work audit_basic_encoding_work nt + lw + rw + iw).

Fixpoint rw_rp_index_existing {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (ids : list positive)
    (proof : rw_provenance K Sort V H) (index : rw_rp_proof_index) : rw_rp_proof_index * nat :=
  match ids with
  | nil => (index, 64)
  | id :: rest =>
    let '(found, nt) := audit_map_get audit_positive_encode id (rw_provenance_nodes proof) in
    let nw := audit_map_source_work audit_basic_encoding_work nt in
    match found with
    | None =>
      let '(out, tw) := rw_rp_index_existing op sort value rest proof index in
      (out, 64 + nw + tw)
    | Some node =>
      let '(lk, lw) := rw_rp_term_key op sort value (rw_evidence_left node) in
      let '(rk, rw) := rw_rp_term_key op sort value (rw_evidence_right node) in
      let '(next, iw) := rw_rp_proof_put lk rk id index in
      let '(out, tw) := rw_rp_index_existing op sort value rest proof next in
      (out, 64 + nw + lw + rw + iw + tw)
    end
  end.

Definition rw_rp_try_symmetry {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (lhs rhs : rw_term K Sort V) (state : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort V H) * nat :=
  let '(lk, lw) := rw_rp_term_key op sort value lhs in
  let '(rk, rw) := rw_rp_term_key op sort value rhs in
  let '(reverse, lookup_work) := rw_rp_proof_get rk lk (rw_rp_index state) in
  match reverse with
  | None => ((None, state), 64 + lw + rw + lookup_work)
  | Some id =>
    let '((new, next), work) :=
      rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceSym id) state in
    ((Some new, next), 64 + lw + rw + lookup_work + work)
  end.

Fixpoint rw_rp_try_transitivity {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat) (lhs rhs : rw_term K Sort V) (middles : list (rw_term K Sort V))
    (state : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort V H) * nat :=
  match middles with
  | nil => ((None, state), 64)
  | middle :: rest =>
    let '(lk, lw) := rw_rp_term_key op sort value lhs in
    let '(mk, mw) := rw_rp_term_key op sort value middle in
    let '(rk, rw) := rw_rp_term_key op sort value rhs in
    let '(first, fw) := rw_rp_proof_get lk mk (rw_rp_index state) in
    match first with
    | None =>
      let '(answer, work) := rw_rp_try_transitivity op sort value stamp lhs rhs rest state in
      (answer, 64 + lw + mw + rw + fw + work)
    | Some a =>
      let '(second, sw) := rw_rp_proof_get mk rk (rw_rp_index state) in
      match second with
      | None =>
        let '(answer, work) := rw_rp_try_transitivity op sort value stamp lhs rhs rest state in
        (answer, 64 + lw + mw + rw + fw + sw + work)
      | Some b =>
        let '((id, next), work) :=
          rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceTrans a b) state in
        ((Some id, next), 64 + lw + mw + rw + fw + sw + work)
      end
    end
  end.

(** When operator, sort, and value adapters agree, erasing term-key work yields the
    encoding of the given term's tree-code list. *)
Definition rw_rp_term_key_agrees_statement : Prop :=
  forall K Sort V (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) term,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    fst (rw_rp_term_key op sort value term) =
      encode (list_encoding positive_encoding) (rw_tree_code EK ES EV term).

Fixpoint rw_rp_children_evidence {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (lhs rhs : list (rw_term K Sort V)) (state : rw_rp_connection_state K Sort V H) :
    option (list positive) * nat :=
  match lhs, rhs with
  | nil, nil => (Some nil, 64)
  | a :: xs, b :: ys =>
    let '(lk, lw) := rw_rp_term_key op sort value a in
    let '(rk, rw) := rw_rp_term_key op sort value b in
    let '(found, fw) := rw_rp_proof_get lk rk (rw_rp_index state) in
    match found with
    | None => (None, 64 + lw + rw + fw)
    | Some id =>
      let '(tail, tw) := rw_rp_children_evidence op sort value xs ys state in
      (option_map (fun ids => id :: ids) tail, 64 + lw + rw + fw + tw)
    end
  | _, _ => (None, 64)
  end.

Definition rw_rp_try_congruence {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (stamp : nat * nat) (lhs rhs : rw_term K Sort V) (state : rw_rp_connection_state K Sort V H) :
    (option positive * rw_rp_connection_state K Sort V H) * nat :=
  match lhs, rhs with
  | RWApp s k xs, RWApp t l ys =>
    let '(sc, sw) := rw_queue_encoder_run sort s in
    let '(tc, tw) := rw_queue_encoder_run sort t in
    let '(same_sort, st) := audit_positive_eqb sc tc in
    if same_sort then
      let '(kc, kw) := rw_queue_encoder_run op k in
      let '(lc, lw) := rw_queue_encoder_run op l in
      let '(same_op, kt) := audit_positive_eqb kc lc in
      if same_op then
        let '(children, cw) := rw_rp_children_evidence op sort value xs ys state in
        match children with
        | None =>
          ((None, state), 64 + sw + tw + audit_positive_eqb_source_work st +
            kw + lw + audit_positive_eqb_source_work kt + cw)
        | Some ids =>
          let '((id, next), work) :=
            rw_rp_add_evidence op sort value stamp lhs rhs (RWEvidenceCongruence ids) state in
          ((Some id, next), 64 + sw + tw + audit_positive_eqb_source_work st +
            kw + lw + audit_positive_eqb_source_work kt + cw + work)
        end
      else
        ((None, state), 64 + sw + tw + audit_positive_eqb_source_work st +
          kw + lw + audit_positive_eqb_source_work kt)
    else ((None, state), 64 + sw + tw + audit_positive_eqb_source_work st)
  | _, _ => ((None, state), 64)
  end.

Definition rw_rp_close_pair {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (terms : list (rw_term K Sort V)) (lhs rhs : rw_term K Sort V)
    (state : rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort V H * nat :=
  let '(lk, lw) := rw_rp_term_key op sort value lhs in
  let '(rk, rw) := rw_rp_term_key op sort value rhs in
  let '(present, pw) := rw_rp_proof_get lk rk (rw_rp_index state) in
  match present with
  | Some _ => (state, 64 + lw + rw + pw)
  | None =>
    let '(same, st) := audit_positive_eqb lk rk in
    let prefix := 64 + lw + rw + pw + audit_positive_eqb_source_work st in
    if same then
      let '((_, next), work) :=
        rw_rp_add_evidence op sort value stamp lhs rhs RWEvidenceRefl state in
      (next, prefix + work)
    else
      let '((symmetric, first), fw) :=
        rw_rp_try_symmetry op sort value stamp lhs rhs state in
      match symmetric with
      | Some _ => (first, prefix + fw)
      | None =>
        let '((transitive, second), sw) :=
          rw_rp_try_transitivity op sort value stamp lhs rhs terms first in
        match transitive with
        | Some _ => (second, prefix + fw + sw)
        | None =>
          let '((_, final), cw) :=
            rw_rp_try_congruence op sort value stamp lhs rhs second in
          (final, prefix + fw + sw + cw)
        end
      end
  end.

Fixpoint rw_rp_close_row {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (terms : list (rw_term K Sort V)) (lhs : rw_term K Sort V) (rights : list (rw_term K Sort V))
    (state : rw_rp_connection_state K Sort V H) : rw_rp_connection_state K Sort V H * nat :=
  match rights with
  | nil => (state, 64)
  | rhs :: rest =>
    let '(next, nw) :=
      rw_rp_close_pair op sort value stamp terms lhs rhs state in
    let '(out, tw) :=
      rw_rp_close_row op sort value stamp terms lhs rest next in
    (out, 64 + nw + tw)
  end.

Fixpoint rw_rp_close_pass {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (terms lefts : list (rw_term K Sort V)) (state : rw_rp_connection_state K Sort V H) :
    rw_rp_connection_state K Sort V H * nat :=
  match lefts with
  | nil => (state, 64)
  | lhs :: rest =>
    let '(next, nw) := rw_rp_close_row op sort value stamp terms lhs terms state in
    let '(out, tw) := rw_rp_close_pass op sort value stamp terms rest next in
    (out, 64 + nw + tw)
  end.

Fixpoint rw_rp_close_rounds {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V) (stamp : nat * nat)
    (terms : list (rw_term K Sort V)) (fuel : positive)
    (state : rw_rp_connection_state K Sort V H) :
    rw_rp_connection_state K Sort V H * nat :=
  match fuel with
  | xH =>
    let '(out, work) := rw_rp_close_pass op sort value stamp terms terms state in
    (out, 64 + work)
  | xO rest =>
    let '(middle, mw) :=
      rw_rp_close_rounds op sort value stamp terms rest state in
    let '(out, tw) :=
      rw_rp_close_rounds op sort value stamp terms rest middle in
    (out, 64 + mw + tw)
  | xI rest =>
    let '(first, fw) := rw_rp_close_pass op sort value stamp terms terms state in
    let '(middle, mw) := rw_rp_close_rounds op sort value stamp terms rest first in
    let '(out, tw) := rw_rp_close_rounds op sort value stamp terms rest middle in
    (out, 64 + fw + mw + tw)
  end.

Fixpoint rw_rp_subterms {K Sort V} (term : rw_term K Sort V) : list (rw_term K Sort V) * nat :=
  match term with
  | RWVar _ _ => ([term], 64)
  | RWApp _ _ children =>
    let fix visit (ts : list (rw_term K Sort V)) : list (rw_term K Sort V) * nat :=
      match ts with
      | nil => (nil, 64)
      | t :: rest =>
        let '(head, hw) := rw_rp_subterms t in
        let '(tail, tw) := visit rest in
        let '(out, aw) := rw_rp_append head tail in (out, 64 + hw + tw + aw)
      end in
    let '(others, work) := visit children in (term :: others, 64 + work)
  end.

Fixpoint rw_rp_nat_compare (a b : nat) : comparison * nat :=
  match a, b with
  | 0, 0 => (Eq, 64)
  | 0, S _ => (Lt, 64)
  | S _, 0 => (Gt, 64)
  | S x, S y =>
    let '(answer, work) := rw_rp_nat_compare x y in (answer, 64 + work)
  end.

Fixpoint rw_rp_evidence_terms {K Sort V H} (entries : list (positive * rw_evidence_node K Sort V H))
    (largest_group : nat) : (list (rw_term K Sort V) * nat) * nat :=
  match entries with
  | nil => ((nil, largest_group), 64)
  | (_, node) :: rest =>
    let group := fst (rw_evidence_time node) in
    let '(order, cw) := rw_rp_nat_compare group largest_group in
    let next :=
      match order with
      | Gt => group
      | _ => largest_group
      end in
    let '(lhs, lw) := rw_rp_subterms (rw_evidence_left node) in
    let '(rhs, rw) := rw_rp_subterms (rw_evidence_right node) in
    let '((tail, maximum), tw) := rw_rp_evidence_terms rest next in
    let '(both, bw) := rw_rp_append lhs rhs in
    let '(out, aw) := rw_rp_append both tail in
    ((out, maximum), 64 + cw + lw + rw + tw + bw + aw)
  end.

Definition rw_rp_connect_atomic {K Sort V H} (op : rw_queue_encoder_adapter K)
    (sort : rw_queue_encoder_adapter Sort) (value : rw_queue_encoder_adapter V)
    (proof : rw_provenance K Sort V H) (lhs rhs : rw_term K Sort V) :
    option (rw_provenance K Sort V H * positive) * nat :=
  let '(entries, et) := audit_map_elements (rw_provenance_nodes proof) in
  let '((known, largest), kw) := rw_rp_evidence_terms entries 0 in
  let '(lefts, lw) := rw_rp_subterms lhs in
  let '(rights, rw) := rw_rp_subterms rhs in
  let '(both, bw) := rw_rp_append lefts rights in
  let '(terms, aw) := rw_rp_append both known in
  let '(index, iw) :=
    rw_rp_index_existing op sort value (rw_provenance_ids proof) proof Map.empty in
  let '(count, lt) := rw_fuel_length terms in
  let '(square, mt) := rw_fuel_mul count count in
  let '(fuel, ft) := rw_fuel_to_positive square in
  let '(final, work) :=
    rw_rp_close_rounds op sort value (S largest, 0) terms fuel
      (RwRpConnectionState proof index) in
  let '(lk, lkw) := rw_rp_term_key op sort value lhs in
  let '(rk, rkw) := rw_rp_term_key op sort value rhs in
  let '(answer, qw) := rw_rp_proof_get lk rk (rw_rp_index final) in
  (option_map (fun id => (rw_rp_proof final, id)) answer,
    64 + audit_elements_work et + kw + lw + rw + bw + aw + iw +
      audit_work lt + audit_work mt + audit_work ft + work + lkw + rkw + qw).

(** Generated equality closes provenance-node endpoints under reflexivity, symmetry,
    transitivity, and application congruence. *)
Inductive rw_rp_generated {K Sort V H} (proof : rw_provenance K Sort V H) :
    rw_term K Sort V -> rw_term K Sort V -> Prop :=
  | RPGeneratedLeaf : forall id node, Map.get positive_encoding id (rw_provenance_nodes proof) =
      Some node -> rw_rp_generated proof (rw_evidence_left node) (rw_evidence_right node)
  | RPGeneratedRefl : forall t, rw_rp_generated proof t t
  | RPGeneratedSym : forall t u, rw_rp_generated proof t u -> rw_rp_generated proof u t
  | RPGeneratedTrans : forall t u v, rw_rp_generated proof t u -> rw_rp_generated proof u v ->
      rw_rp_generated proof t v
  | RPGeneratedCongruence : forall s k xs ys, Forall2 (rw_rp_generated proof) xs ys ->
      rw_rp_generated proof (RWApp s k xs) (RWApp s k ys).

(** With agreeing encoders, a well-formed provenance map whose IDs enumerate its nodes,
    and a generated equality, the connection procedure succeeds. *)
Definition rw_rp_connect_complete_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (proof : rw_provenance K Sort V H) lhs rhs,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    Map.wf positive_encoding (rw_provenance_nodes proof) ->
    (forall id, In id (rw_provenance_ids proof) <->
      exists node, Map.get positive_encoding id (rw_provenance_nodes proof) = Some node) ->
    rw_rp_generated proof lhs rhs ->
    exists extended id,
      fst (rw_rp_connect_atomic op sort value proof lhs rhs) = Some (extended, id).

(** With agreeing encoders and valid provenance, a successful connection preserves
    all existing nodes and valid provenance and records the requested endpoints. *)
Definition rw_rp_connect_sound_statement : Prop :=
  forall K Sort V H (EK : encoding K) (ES : encoding Sort) (EV : encoding V) (EH : encoding H)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (sig : rw_signature K Sort V) rules proof lhs rhs
    extended id,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    (forall ty, fst (rw_queue_encoder_run sort ty) = encode ES ty) ->
    (forall v, fst (rw_queue_encoder_run value v) = encode EV v) ->
    rw_provenance_valid EH sig rules proof ->
    fst (rw_rp_connect_atomic op sort value proof lhs rhs) = Some (extended, id) ->
    rw_provenance_valid EH sig rules extended /\
    (forall key node, Map.get positive_encoding key (rw_provenance_nodes proof) = Some node ->
      Map.get positive_encoding key (rw_provenance_nodes extended) = Some node) /\
    exists node, Map.get positive_encoding id (rw_provenance_nodes extended) = Some node /\
      rw_evidence_left node = lhs /\
      rw_evidence_right node = rhs.
