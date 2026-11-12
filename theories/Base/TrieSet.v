(** * Trie sets

    Unit-valued maps represent finite sets.
    For example, adding one key twice leaves a singleton.
    Builds on: SetSig and MapSig. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig TrieSig MapSig SetSig.
From Galois.Base Require Import Trie.

Module TrieSetCode (K : KEY_OPS) <: SET_OPS K.
  Definition t := PTrieCode.t K.t.
  Definition empty : t := PTrieCode.empty.
  Definition has (p : positive) (s : t) :=
    match PTrieCode.get p s with Some _ => true | None => false end.
  Definition mem (k : K.t) (s : t) :=
    match PTrieCode.get (K.encode k) s with Some _ => true | None => false end.
  Definition add (k : K.t) (s : t) := PTrieCode.set (K.encode k) k s.
  Definition remove (k : K.t) (s : t) := PTrieCode.remove (K.encode k) s.
  Definition union (s u : t) :=
    PTrieCode.merge (fun a b => match a with Some _ => a | None => b end) s u.
  Definition inter (s u : t) :=
    PTrieCode.merge (fun a b => match b with Some _ => a | None => None end) s u.
  Definition diff (s u : t) :=
    PTrieCode.merge (fun a b => match b with Some _ => None | None => a end) s u.
  Definition subset (s u : t) :=
    PTrieCode.forall2 (fun _ b => match b with Some _ => true | None => false end) s u.
  Definition equal (s u : t) := andb (subset s u) (subset u s).
  Definition fold {A} (f : A -> K.t -> A) (s : t) (a : A) :=
    PTrieCode.fold_values f s a.
  Definition elements (s : t) := List.rev_append (fold (fun acc k => k :: acc) s nil) nil.
End TrieSetCode.

Module TrieSet (K : KEY) <: SET K.
  Include TrieSetCode K.
  Include SET_SPEC K.
  Definition wf (s : t) : Prop :=
    forall p k, PTrieCode.get p s = Some k -> K.encode k = p.
  Definition nodes (s : t) : nat := PTrie.nodes s.
  Lemma wf_empty : wf empty.
  Proof. Admitted.
  Lemma wf_add : forall k s, wf s -> wf (add k s).
  Proof. Admitted.
  Lemma wf_remove : forall k s, wf s -> wf (remove k s).
  Proof. Admitted.
  Lemma wf_union : forall s u, wf s -> wf u -> wf (union s u).
  Proof. Admitted.
  Lemma wf_inter : forall s u, wf s -> wf u -> wf (inter s u).
  Proof. Admitted.
  Lemma wf_diff : forall s u, wf s -> wf u -> wf (diff s u).
  Proof. Admitted.
  Lemma mem_empty : forall k, mem k empty = false.
  Proof. Admitted.
  Lemma mem_add_same : forall k s, mem k (add k s) = true.
  Proof. Admitted.
  Lemma mem_add_other : forall k q s, k <> q -> mem k (add q s) = mem k s.
  Proof. Admitted.
  Lemma mem_remove_same : forall k s, mem k (remove k s) = false.
  Proof. Admitted.
  Lemma mem_remove_other : forall k q s, k <> q -> mem k (remove q s) = mem k s.
  Proof. Admitted.
  Lemma mem_union : forall k s u, mem k (union s u) = (mem k s || mem k u).
  Proof. Admitted.
  Lemma mem_inter : forall k s u, mem k (inter s u) = (mem k s && mem k u).
  Proof. Admitted.
  Lemma mem_diff : forall k s u, mem k (diff s u) = (mem k s && negb (mem k u)).
  Proof. Admitted.
  Lemma elements_spec : forall s k, wf s -> (In k (elements s) <-> mem k s = true).
  Proof. Admitted.
  Lemma elements_nodup : forall s, wf s -> NoDup (elements s).
  Proof. Admitted.
  Lemma fold_spec : forall A (f : A -> K.t -> A) s a,
    fold f s a = fold_left f (elements s) a.
  Proof. Admitted.
  Lemma ext : forall s u, wf s -> wf u -> (forall k, mem k s = mem k u) -> s = u.
  Proof. Admitted.
  Lemma mem_has : forall k s, mem k s = has (K.encode k) s.
  Proof. Admitted.
  Lemma has_empty : forall p, has p empty = false.
  Proof. Admitted.
  Lemma has_add : forall p k s, has p (add k s) = Pos.eqb p (K.encode k) || has p s.
  Proof. Admitted.
  Lemma has_remove : forall p k s,
  has p (remove k s) = negb (Pos.eqb p (K.encode k)) && has p s.
  Proof. Admitted.
  Lemma has_union : forall p s u, has p (union s u) = has p s || has p u.
  Proof. Admitted.
  Lemma has_inter : forall p s u, has p (inter s u) = has p s && has p u.
  Proof. Admitted.
  Lemma has_diff : forall p s u, has p (diff s u) = has p s && negb (has p u).
  Proof. Admitted.
  Lemma subset_spec : forall s u,
  subset s u = true <-> forall p, has p s = true -> has p u = true.
  Proof. Admitted.
  Lemma equal_spec : forall s u, equal s u = true <-> forall p, has p s = has p u.
  Proof. Admitted.
  Lemma wf_has : forall s p, wf s -> has p s = true -> exists k, K.encode k = p.
  Proof. Admitted.
  Lemma nodes_empty : nodes empty = 0.
  Proof. Admitted.
  Lemma nodes_add : forall k s, nodes (add k s) <= nodes s + K.bits k.
  Proof. Admitted.
  Lemma nodes_remove : forall k s, nodes (remove k s) <= nodes s.
  Proof. Admitted.
  Lemma nodes_union : forall s u, nodes (union s u) <= nodes s + nodes u.
  Proof. Admitted.
  Lemma nodes_inter : forall s u, nodes (inter s u) <= nodes s.
  Proof. Admitted.
  Lemma nodes_diff : forall s u, nodes (diff s u) <= nodes s.
  Proof. Admitted.
  Lemma nodes_le_weight : forall s, wf s -> nodes s <= weight s.
  Proof. Admitted.
End TrieSet.

Module TrieSetT (K : KEY_T) <: SET_T K.
  Include TrieSet K.
  TimeFun has.
  TimeFun mem.
  TimeFun add.
  TimeFun remove.
  TimeFun union.
  TimeFun inter.
  TimeFun diff.
  TimeFun subset.
  TimeFun equal.
  TimeFun fold.
  TimeFun elements.
  Definition c_set : N := 1. (* STUB *)
  Lemma T_mem_le : forall k s, (T_mem k s <= c_set * N.of_nat (K.bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_add_le : forall k s, (T_add k s <= c_set * N.of_nat (K.bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_remove_le : forall k s, (T_remove k s <= c_set * N.of_nat (K.bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_union_le : forall s u, (T_union s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_inter_le : forall s u, (T_inter s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_diff_le : forall s u, (T_diff s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_subset_le : forall s u, (T_subset s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_equal_le : forall s u, (T_equal s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_elements_le : forall s, (wf s -> T_elements s <= c_set * N.of_nat (weight s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fold_le : forall A (f : A -> K.t -> A) T_f s a c,
    ((forall acc k, T_f acc k <= c) ->
    T_fold f T_f s a <= c_set * (c + 1) * N.of_nat (nodes s + 1))%N.
  Proof. Admitted. (* STUB *)
End TrieSetT.
