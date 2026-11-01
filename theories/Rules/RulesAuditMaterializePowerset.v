(** * Literal finite-powerset callback bodies

    Inclusion follows only left paths and preserves every native conditional short circuit.
    For example, an empty left trie is included without traversing the right trie.
    Builds on: the native finite relation lattice and the materialization union model. *)

From Stdlib Require Import List Bool NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesAuditMaterializePrelude
  RulesAuditMaterializeAdapters RulesAuditJoinSyntax.
From Galois.Collections Require Import CollectionsAuditElements.

(** * Inclusion and lattice callback models *)

Definition mat_subset_root {K} (right : Trie.t (K * unit)) :=
  mat_mark 140 (mat_return (
    match Trie.value right with
    | Some _ => true
    | None => false
    end)).

Fixpoint mat_subset_ne {K} (left : Trie.ne (K * unit)) (right : Trie.t (K * unit)) : mat_run bool :=
  mat_mark 141 (
    match left with
    | Trie.N001 r => mat_subset_ne r (Trie.right right)
    | Trie.N010 _ => mat_subset_root right
    | Trie.N011 _ r =>
        root <- mat_subset_root right;;
        if root then mat_subset_ne r (Trie.right right) else mat_return false
    | Trie.N100 l => mat_subset_ne l (Trie.left right)
    | Trie.N101 l r =>
        first <- mat_subset_ne l (Trie.left right);;
        if first then mat_subset_ne r (Trie.right right) else mat_return false
    | Trie.N110 l _ =>
        first <- mat_subset_ne l (Trie.left right);;
        if first then mat_subset_root right else mat_return false
    | Trie.N111 l _ r =>
        first <- mat_subset_ne l (Trie.left right);;
        if first then
          root <- mat_subset_root right;;
          if root then mat_subset_ne r (Trie.right right) else mat_return false
        else mat_return false
    end).

Definition mat_subset {K} (a b : FinSet.t K) :=
  mat_mark 142 (
    match a with
    | Trie.Empty => mat_return true
    | Trie.Nodes n => mat_subset_ne n b
    end).

(** The proposed erasure identifies the result with native finite-set inclusion. *)
Definition mat_subset_erases_statement : Prop :=
  forall K E (a b : FinSet.t K), fst (mat_subset a b) = FinSet.subset E a b.

(** The proposed work bound is linear in the nodes of the left trie. *)
Definition mat_subset_bound_statement : Prop :=
  forall K (a b : FinSet.t K),
    (mat_work (snd (mat_subset a b)) <= (N.to_nat 10000%N) * (1 + audit_trie_nodes a))%nat.

Definition mat_relation_leb {P} (prog : program P) facts (a b : relation prog facts) :=
  ignored <- mat_emit (MatOperand (1 + audit_trie_nodes (proj1_sig a) +
    audit_trie_nodes (proj1_sig b)));;
  mat_subset (proj1_sig a) (proj1_sig b).

Definition mat_relation_bot {P} (prog : program P) facts :=
  mat_return (bot (relation_lattice prog facts)).

Definition mat_relation_join {P} (prog : program P) facts (a b : relation prog facts) :=
  source <- mat_union (proj1_sig a) (proj1_sig b);;
  mat_return (join (relation_lattice prog facts) a b).

Definition mat_relation_widen {P} (prog : program P) facts (a b : relation prog facts) :=
  source <- mat_union (proj1_sig a) (proj1_sig b);;
  mat_return (widen (relation_lattice prog facts) a b).

Definition mat_relation_narrow {P} (prog : program P) facts (a b : relation prog facts) :=
  mat_return a.

(** The proposed erasure relates inclusion, join and widening to the native relation lattice. *)
Definition mat_relation_callbacks_erases_statement : Prop :=
  forall P (prog : program P) facts,
    (forall a b, fst (mat_relation_leb prog facts a b) = leb (relation_lattice prog facts) a b) /\
    (forall a b, fst (mat_relation_join prog facts a b) = join (relation_lattice prog facts) a b) /\
    (forall a b, fst (mat_relation_widen prog facts a b) = widen (relation_lattice prog facts) a b).

(** The three callback bounds use the combined node counts of the two input relations. *)
Definition mat_relation_callbacks_bound_statement : Prop :=
  forall P (prog : program P) facts (a b : relation prog facts),
    let nodes := (1 + audit_trie_nodes (proj1_sig a) + audit_trie_nodes (proj1_sig b))%nat in
    (mat_work (snd (mat_relation_leb prog facts a b)) <= (N.to_nat 10000%N) * nodes /\
    mat_work (snd (mat_relation_join prog facts a b)) <= (N.to_nat 10000%N) * nodes /\
    mat_work (snd (mat_relation_widen prog facts a b)) <= (N.to_nat 10000%N) * nodes)%nat.
