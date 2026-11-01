(** * Literal FinSet difference trie combine

    Both one-sided filters traverse every stored node; empty output does not skip their work.
    For example, subtracting a singleton from a two-element set retains the other element.
    Builds on: RulesAuditMaterializePrelude and the seven native nonempty trie constructors. *)

From Stdlib Require Import List NArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesAuditMaterializePrelude RulesAuditMaterializeAdapters
  RulesAuditJoinSyntax.
From Galois.Collections Require Import CollectionsAuditElements.

(** * Trie difference and its source bounds *)

Definition mat_node {A} (l : Trie.t A) o r := mat_mark 40 (mat_return (Trie.node l o r)).

Fixpoint mat_filter_ne {A B} (f : A -> mat_run (option B)) (n : Trie.ne A) :
    mat_run (Trie.t B) :=
  mat_mark 41 (
    match n with
    | Trie.N001 r => right <- mat_filter_ne f r;; mat_node Trie.Empty None right
    | Trie.N010 v => value <- f v;; mat_node Trie.Empty value Trie.Empty
    | Trie.N011 v r =>
        value <- f v;; right <- mat_filter_ne f r;; mat_node Trie.Empty value right
    | Trie.N100 l => left <- mat_filter_ne f l;; mat_node left None Trie.Empty
    | Trie.N101 l r =>
        left <- mat_filter_ne f l;; right <- mat_filter_ne f r;; mat_node left None right
    | Trie.N110 l v =>
        left <- mat_filter_ne f l;; value <- f v;; mat_node left value Trie.Empty
    | Trie.N111 l v r =>
        left <- mat_filter_ne f l;; value <- f v;; right <- mat_filter_ne f r;;
        mat_node left value right
    end).

Definition mat_filter_trie {A B} (f : A -> mat_run (option B)) (input : Trie.t A) :=
  mat_mark 42 (
    match input with
    | Trie.Empty => mat_return Trie.Empty
    | Trie.Nodes n => mat_filter_ne f n
    end).

Definition mat_diff_value {K} (a b : option (K * unit)) :=
  mat_mark 43 (mat_return (
    match a, b with
    | Some (k, _), None => Some (k, tt)
    | _, _ => None
    end)).

Definition mat_diff_left {K} :=
  @mat_filter_trie (K * unit) (K * unit) (fun a => mat_diff_value (Some a) None).

Definition mat_diff_right {K} :=
  @mat_filter_trie (K * unit) (K * unit) (fun b => mat_diff_value None (Some b)).

Fixpoint mat_diff_ne {K} (n : Trie.ne (K * unit)) (b : Trie.t (K * unit)) :
    mat_run (Trie.t (K * unit)) :=
  mat_mark 44 (
    match b with
    | Trie.Empty => mat_diff_left (Trie.Nodes n)
    | Trie.Nodes _ =>
        match n with
        | Trie.N001 r =>
            left <- mat_diff_right (Trie.left b);; value <- mat_diff_value None (Trie.value b);;
            right <- mat_diff_ne r (Trie.right b);; mat_node left value right
        | Trie.N010 v =>
            left <- mat_diff_right (Trie.left b);; value <- mat_diff_value (Some v) (Trie.value b);;
            right <- mat_diff_right (Trie.right b);; mat_node left value right
        | Trie.N011 v r =>
            left <- mat_diff_right (Trie.left b);; value <- mat_diff_value (Some v) (Trie.value b);;
            right <- mat_diff_ne r (Trie.right b);; mat_node left value right
        | Trie.N100 l =>
            left <- mat_diff_ne l (Trie.left b);; value <- mat_diff_value None (Trie.value b);;
            right <- mat_diff_right (Trie.right b);; mat_node left value right
        | Trie.N101 l r =>
            left <- mat_diff_ne l (Trie.left b);; value <- mat_diff_value None (Trie.value b);;
            right <- mat_diff_ne r (Trie.right b);; mat_node left value right
        | Trie.N110 l v =>
            left <- mat_diff_ne l (Trie.left b);; value <- mat_diff_value (Some v) (Trie.value b);;
            right <- mat_diff_right (Trie.right b);; mat_node left value right
        | Trie.N111 l v r =>
            left <- mat_diff_ne l (Trie.left b);; value <- mat_diff_value (Some v) (Trie.value b);;
            right <- mat_diff_ne r (Trie.right b);; mat_node left value right
        end
    end).

Definition mat_diff {K} (a b : FinSet.t K) :=
  mat_mark 45 (
    match a with
    | Trie.Empty => mat_diff_right b
    | Trie.Nodes n => mat_diff_ne n b
    end).

(** The proposed erasure gives the native finite-set difference. *)
Definition mat_diff_erases_statement : Prop :=
  forall K E (a b : FinSet.t K), fst (mat_diff a b) = FinSet.diff E a b.

(** The proposed difference bound is linear in the two trie sizes. *)
Definition mat_diff_bound_statement : Prop :=
  forall K (a b : FinSet.t K),
    (mat_work (snd (mat_diff a b)) <=
      (N.to_nat 10000%N) * (1 + audit_trie_nodes a + audit_trie_nodes b))%nat.
