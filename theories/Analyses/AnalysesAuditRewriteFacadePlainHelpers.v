(** * AnalysesAuditRewriteFacadePlainHelpers

    This file evaluates fixed legacy preparation, provenance, and application stages.
    For example, the hole-occurrence list [0; 0] produces the single hole [0].
    Builds on: the fixed Rewrite plain builders and legacy facade source equations. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia Wellfounded.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadePrepare.
From Galois.Rewrite Require Import RewriteAuditIndexReference RewriteAuditPlainCore1
  RewriteAuditPlainCore2 RewriteAuditPlainCore3 RewriteAuditPlainPrimitives
  RewriteAuditProofCarrier RewriteAuditProofRun RewriteAuditProofTick.
Import List.ListNotations.
Local Coercion encode : encoding >-> Funclass.

Definition rw_plain_audit_finset_mem :=
  @FinSet.mem.

Definition rw_plain_audit_finset_add :=
  @FinSet.add.

Definition rw_plain_audit_trie_elements :=
  @Trie.elements.

Definition rw_plain_rw_facade_vars :=
  @term_vars.

Definition rw_plain_rw_queue_append_atomic :=
  @app.

Definition rw_plain_rw_facade_unit_adapter :=
  unit_encoding.

Definition rw_plain_rw_facade_nat_adapter :=
  nat_encoding.
Arguments rw_plain_audit_finset_mem {K} _ _ _.
Arguments rw_plain_audit_finset_add {K} _ _ _.
Arguments rw_plain_audit_trie_elements {A} _.
Arguments rw_plain_rw_facade_vars {K} _.
Arguments rw_plain_rw_queue_append_atomic {A} _ _.

Fixpoint rw_plain_rw_facade_pattern_atomic {K} (source : term K) : rw_pattern K unit nat nat :=
  match source with
  | TVar index => RWHole tt index
  | TApp op children =>
    let fix visit (terms : list (term K)) : list (rw_pattern K unit nat nat) :=
      match terms with
      | nil => nil
      | t :: rest =>
        let head := rw_plain_rw_facade_pattern_atomic t in
        let tail := visit rest in head :: tail
      end in
    let patterns := visit children in RWPApp tt op patterns
  end.

Fixpoint rw_plain_rw_facade_holes_atomic (occurrences : list nat) : (list nat * FinSet.t nat) :=
  match occurrences with
  | nil => (nil, FinSet.empty)
  | index :: rest =>
    let '(holes, present) := rw_plain_rw_facade_holes_atomic rest in
    let seen := rw_plain_audit_finset_mem rw_plain_audit_nat_encode index present in
    if seen then (holes, present)
    else
      let next := rw_plain_audit_finset_add rw_plain_audit_nat_encode index present in
      (index :: holes, next)
  end.

Definition rw_plain_rw_facade_prepare_rule_atomic {K} (rule : rewrite_rule K) :
    rw_facade_prepared_rule K :=
  let left_vars := rw_plain_rw_facade_vars (rule_lhs rule) in
  let right_vars := rw_plain_rw_facade_vars (rule_rhs rule) in
  let occurrences := rw_plain_rw_queue_append_atomic left_vars right_vars in
  let '(holes, present) := rw_plain_rw_facade_holes_atomic occurrences in
  let lhs := rw_plain_rw_facade_pattern_atomic (rule_lhs rule) in
  let rhs := rw_plain_rw_facade_pattern_atomic (rule_rhs rule) in
  let core := RwRule K unit nat nat holes
    (fun index => if existsb (Nat.eqb index) holes then Some tt else None)
    lhs rhs (fun sub => rule_side rule (legacy_total_sub sub)) in
  RwFacadePreparedRule rule core present.

Fixpoint rw_plain_rw_facade_prepare_atomic {K} (rules : list (rewrite_rule K)) (index : nat) :
    rw_facade_prepared K :=
  match rules with
  | nil => RwFacadePrepared nil Map.empty Map.empty nil
  | rule :: rest =>
    let tail := rw_plain_rw_facade_prepare_atomic rest (S index) in
    let prepared := rw_plain_rw_facade_prepare_rule_atomic rule in
    let table := rw_plain_audit_map_set rw_plain_audit_nat_encode index prepared
      (rw_facade_rule_table tail) in
    let original := rw_plain_audit_map_set rw_plain_audit_nat_encode index rule
      (rw_facade_original_table tail) in
    RwFacadePrepared ((index, prepared) :: rw_facade_rule_entries tail) table original
      (rw_facade_core_rule prepared :: rw_facade_core_rules tail)
  end.

Fixpoint rw_plain_rw_facade_materialize_project_atomic {K} (source : rw_term K unit nat) : term K :=
  match source with
  | RWVar _ v => TVar v
  | RWApp _ op children =>
    let fix visit (ts : list (rw_term K unit nat)) : list (term K) :=
      match ts with
      | nil => nil
      | t :: rest =>
        let head := rw_plain_rw_facade_materialize_project_atomic t in
        let tail := visit rest in head :: tail
      end in
    let args := visit children in TApp op args
  end.

Fixpoint rw_plain_rw_facade_binding_max {K} (entries : list (nat * rw_term K unit nat)) :
    option nat :=
  match entries with
  | nil => None
  | (index, _) :: rest =>
    let tail := rw_plain_rw_facade_binding_max rest in
    match tail with
    | None => Some index
    | Some largest =>
      let order := rw_plain_rw_rp_nat_compare index largest in
      Some (
        match order with
        | Gt => index
        | _ => largest
        end)
    end
  end.

Fixpoint rw_plain_rw_facade_binding_range {K} (bindings : Map.t nat (rw_term K unit nat))
    (remaining index : nat) : list (term K) :=
  match remaining with
  | 0 => nil
  | S rest =>
    let found := rw_plain_audit_map_get rw_plain_audit_nat_encode index bindings in
    let head :=
      match found with
      | None => TVar index
      | Some term => rw_plain_rw_facade_materialize_project_atomic term
      end in
    let tail := rw_plain_rw_facade_binding_range bindings rest (S index) in
    head :: tail
  end.

Definition rw_plain_rw_facade_bindings_atomic {K} (bindings : Map.t nat (rw_term K unit nat)) :
    list (term K) :=
  let entries := rw_plain_audit_map_elements bindings in
  let largest := rw_plain_rw_facade_binding_max entries in
  match largest with
  | None => nil
  | Some n =>
    let out := rw_plain_rw_facade_binding_range bindings (S n) 0 in
    out
  end.

Fixpoint rw_plain_rw_facade_invert_onto {K} (steps acc : list (rewrite_step K)) :
    list (rewrite_step K) :=
  match steps with
  | nil => acc
  | step :: rest =>
    let flipped :=
      RewriteStep (step_pos step) (step_rule step) (negb (step_forward step)) (step_subst step) in
    let out := rw_plain_rw_facade_invert_onto rest (flipped :: acc) in
    out
  end.

Fixpoint rw_plain_rw_facade_prefix_atomic {K} (position : nat) (steps : list (rewrite_step K)) :
    list (rewrite_step K) :=
  match steps with
  | nil => nil
  | step :: rest =>
    let head :=
      RewriteStep (position :: step_pos step) (step_rule step) (step_forward step)
        (step_subst step) in
    let tail := rw_plain_rw_facade_prefix_atomic position rest in
    head :: tail
  end.

Fixpoint rw_plain_rw_facade_capture_entries {K}
    (entries : list (positive * rw_evidence_node K unit nat nat))
    (leaves : Map.t positive (rewrite_step K)) : Map.t positive (rewrite_step K) :=
  match entries with
  | nil => leaves
  | (id, node) :: rest =>
    let next :=
      match rw_evidence_reason_of node with
      | RWEvidenceRule index bindings =>
        let sub := rw_plain_rw_facade_bindings_atomic bindings in
        let out :=
          rw_plain_audit_map_set rw_plain_audit_positive_encode id
            (RewriteStep nil index true sub) leaves in
        out
      | _ => leaves
      end in
    let out := rw_plain_rw_facade_capture_entries rest next in
    out
  end.

Definition rw_plain_rw_facade_capture_atomic {K} (output : rw_tracked_output K unit nat nat) :
    Map.t positive (rewrite_step K) :=
  let entries :=
    rw_plain_audit_map_elements (rw_provenance_nodes (rw_tracked_provenance
      (rw_tracked_final output))) in
  let leaves := rw_plain_rw_facade_capture_entries entries Map.empty in
  leaves.

Fixpoint rw_plain_rw_facade_references_valid {K} (proof : rw_provenance K unit nat nat)
    (parent : positive) (references : list positive) : bool :=
  match references with
  | nil => true
  | child :: rest =>
    let order := rw_plain_rw_rd_positive_compare_cont Eq child parent in
    let found :=
      rw_plain_audit_map_get rw_plain_audit_positive_encode child (rw_provenance_nodes proof) in
    let tail := rw_plain_rw_facade_references_valid proof parent rest in
    let earlier :=
      match order with
      | Lt => true
      | _ => false
      end in
    let present :=
      match found with
      | Some _ => true
      | None => false
      end in
    earlier && present && tail
  end.

Fixpoint rw_plain_rw_facade_provenance_entries_valid {K} (proof : rw_provenance K unit nat nat)
    (entries : list (positive * (positive * rw_evidence_node K unit nat nat))) : bool :=
  match entries with
  | nil => true
  | (position, (stored, node)) :: rest =>
    let same_key := rw_plain_audit_positive_eqb position stored in
    let references :=
      rw_plain_rw_facade_references_valid proof position
        (rw_reason_references (rw_evidence_reason_of node)) in
    let tail := rw_plain_rw_facade_provenance_entries_valid proof rest in
    same_key && references && tail
  end.

Definition rw_plain_rw_facade_materialize_shape_atomic {K} (proof : rw_provenance K unit nat nat)
    (root : positive) : bool :=
  let found :=
    rw_plain_audit_map_get rw_plain_audit_positive_encode root (rw_provenance_nodes proof) in
  let entries := rw_plain_audit_trie_elements (rw_provenance_nodes proof) in
  let valid := rw_plain_rw_facade_provenance_entries_valid proof entries in
  let present :=
    match found with
    | Some _ => true
    | None => false
    end in
  present && valid.

Definition rw_plain_rw_facade_local_callbacks {K} (_ : unit)
    (prepared : rw_facade_prepared_rule K) :
    rw_plain_callbacks K unit nat nat :=
  RwPlainCallbacks (fun _ => Some tt) (fun _ _ _ => true)
    (fun _ index =>
      if FinSet.mem nat_encoding index (rw_facade_hole_set prepared) then Some tt else None)
    (fun _ sub => rule_side (rw_facade_original_rule prepared)
      (fun index =>
        match sub index with
        | None => TVar index
        | Some term => rw_plain_rw_facade_materialize_project_atomic term
        end)).

Definition rw_plain_rw_facade_apply_atomic {K} (EK : encoding K) (op : encoding K)
    (guard : (fun _ : Type => unit) K) (prepared : rw_facade_prepared K) (position : nat)
    (state : rw_tracked_state K unit nat nat) (attempt : rw_attempt K unit nat nat) :
    option (rw_tracked_state K unit nat nat * list rw_index_event) :=
  let found :=
    rw_plain_audit_map_get rw_plain_audit_nat_encode (rw_attempt_rule attempt)
      (rw_facade_rule_table prepared) in
  match found with
  | None => None
  | Some entry =>
    let gate :=
      rw_plain_rw_rp_rule_body_gate_atomic rw_plain_rw_facade_unit_adapter
        rw_plain_rw_facade_nat_adapter (rw_plain_rw_facade_local_callbacks guard entry)
        (rw_facade_core_rule entry) attempt in
    match gate with
    | None => None
    | Some (lhs, rhs) =>
      let represented :=
        rw_plain_rw_ri_member_atomic op rw_plain_rw_facade_unit_adapter
          rw_plain_rw_facade_nat_adapter
          (rw_tracked_machine state) lhs (rw_attempt_root attempt) in
      if represented then
        let accepted :=
          rw_plain_rw_rp_accept_atomic EK unit_encoding nat_encoding op
            rw_plain_rw_facade_unit_adapter
            rw_plain_rw_facade_nat_adapter (S position, 0) state attempt lhs rhs in
        match accepted with
        | None => None
        | Some next =>
          let out :=
            rw_plain_rw_rp_rebuild_atomic op rw_plain_rw_facade_unit_adapter
              rw_plain_rw_facade_nat_adapter (S position) next in
          Some out
        end
      else None
    end
  end.
