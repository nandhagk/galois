(** * Placeholder tuple indexes

    Indexes store tuples and navigate prefixes.
    For example, an empty index has a root node.
    Builds on: IndexSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Egglog Require Import ValueSig Syntax IndexSig.

Import List.ListNotations.

Module IndexCode (V : VALUE_OPS) <: INDEX_OPS V.
  Definition t := list (list (cell V.t)).
  (* STUB-CODE *)
  Definition empty : t := [].
  (* STUB-CODE *)
  Definition insert (_ : list (cell V.t)) (ix : t) : t := ix.
  (* STUB-CODE *)
  Definition remove (_ : list (cell V.t)) (ix : t) : t := ix.
  (* STUB-CODE *)
  Definition root (_ : t) : positive := 1%positive.
  (* STUB-CODE *)
  Definition child (_ : t) (_ : positive) (_ : cell V.t) : option positive := None.
  (* STUB-CODE *)
  Definition children (_ : t) (_ : positive) : list (cell V.t) := [].
  (* STUB-CODE *)
  Definition degree (_ : t) (_ : positive) : N := 0%N.
End IndexCode.

Module Index (V : VALUE) <: INDEX V.
  Include IndexCode V.
  Include INDEX_SPEC V.
  Definition wf (_ : nat) (_ : t) : Prop := True.
  Definition mem (_ : t) (_ : list (cell V.t)) : Prop := False.
  Definition node (_ : t) (_ : positive) (_ : list (cell V.t)) : Prop := False.
  Lemma wf_empty : forall a, wf a empty.
  Proof. Admitted.

  Lemma wf_insert : forall a r ix, wf a ix -> length r = a -> wf a (insert r ix).
  Proof. Admitted.

  Lemma wf_remove : forall a r ix, wf a ix -> wf a (remove r ix).
  Proof. Admitted.

  Lemma mem_insert : forall a r ix u, wf a ix -> length r = a ->
    (mem (insert r ix) u <-> u = r \/ mem ix u).
  Proof. Admitted.

  Lemma mem_remove : forall a r ix u, wf a ix ->
    (mem (remove r ix) u <-> u <> r /\ mem ix u).
  Proof. Admitted.

  Lemma mem_arity : forall a ix u, wf a ix -> mem ix u -> length u = a.
  Proof. Admitted.

  Lemma node_root : forall a ix, wf a ix -> node ix (root ix) [].
  Proof. Admitted.

  Lemma node_live : forall a ix n pre, wf a ix -> node ix n pre -> pre <> [] ->
    exists suf, mem ix (pre ++ suf).
  Proof. Admitted.

  Lemma node_fun : forall a ix n m pre, wf a ix ->
    node ix n pre -> node ix m pre -> n = m.
  Proof. Admitted.

  Lemma child_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (forall m, child ix n c = Some m <-> node ix m (pre ++ [c])) /\
    (child ix n c = None <-> ~ exists suf, mem ix (pre ++ c :: suf)).
  Proof. Admitted.

  Lemma children_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (In c (children ix n) <-> exists m, child ix n c = Some m) /\
    NoDup (children ix n).
  Proof. Admitted.

  Lemma degree_spec : forall a ix n pre, wf a ix -> node ix n pre ->
    N.to_nat (degree ix n) = length (children ix n).
  Proof. Admitted.

End Index.

Module IndexT (V : VALUE_T) <: INDEX_ALL V.
  Include Index V.
  TimeFun empty.
  TimeFun insert.
  TimeFun remove.
  TimeFun root.
  TimeFun child.
  TimeFun children.
  TimeFun degree.
  Definition width (_ : t) (_ : list (cell V.t)) : nat := 0.
  Definition c_ix : N := 1. (* STUB *)
  Lemma T_insert_le : forall r ix,
    (T_insert r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_remove_le : forall r ix,
    (T_remove r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_child_le : forall ix n c,
    (T_child ix n c <= c_ix * N.of_nat (width ix [c] + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_children_le : forall ix n,
    (T_children ix n <= c_ix * N.of_nat (N.to_nat (degree ix n) + 1) *
      N.of_nat (width ix [] + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_degree_le : forall ix n,
    (T_degree ix n <= c_ix * N.of_nat (width ix [] + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition inv (_ : t) : Prop := True.
  (* STUB-CODE *)
  Definition insert_step (ix : t) (_ : positive) (_ : cell V.t) : t := ix.
  TimeFun insert_step.
  Definition c_map : N := 1. (* STUB *)
  Lemma inv_wf : forall a ix,
    wf a ix <-> inv ix /\ (forall u, mem ix u -> length u = a).
  Proof. Admitted. (* STUB *)

  Lemma insert_path : forall ix r, inv ix -> inv (insert r ix).
  Proof. Admitted. (* STUB *)

  Lemma remove_path : forall ix r, inv ix -> inv (remove r ix).
  Proof. Admitted. (* STUB *)

  Lemma T_insert_step_le : forall ix n c,
    (T_insert_step ix n c <= 4 * c_map * N.of_nat (width ix [c] + 1) + 4)%N.
  Proof. Admitted. (* STUB *)

End IndexT.
