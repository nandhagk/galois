(** * Interning and indexes

    Interners assign dense identifiers and indexes group values by key.
    For example, interning [a; b; a] allocates only two identifiers.
    Builds on: InternSig, MapSig and KeySig. *)

From Stdlib Require Import List Bool NArith PArith Lia Sorting.Sorted.
From Argent Require Import Time Std.
From Galois.Base Require Import InternSig KeySig MapSig.
From Galois.Base Require Import Trie.

Record intern_table (K : Type) (M : Type -> Type) := InternTable {
  intern_forward : M positive;
  intern_inverse : PTrieCode.t K;
  intern_next : positive
}.
Arguments InternTable {K M} _ _ _.
Arguments intern_forward {K M} _.
Arguments intern_inverse {K M} _.
Arguments intern_next {K M} _.

TimeFun intern_forward.
TimeFun intern_inverse.
TimeFun intern_next.

Module InternCode (K : KEY_OPS) (M : MAP_OPS K) <: INTERN_OPS K.
  Definition t := intern_table K.t M.t.
  Definition empty : t := InternTable M.empty PTrieCode.empty 1%positive.
  Definition find (k : K.t) (s : t) := M.get k (intern_forward s).
  Definition name (i : positive) (s : t) := PTrieCode.get i (intern_inverse s).
  Definition size (s : t) := M.fold (fun n _ _ => N.succ n) (intern_forward s) 0%N.
  Definition intern (k : K.t) (s : t) : positive * t :=
    match find k s with
    | Some i => (i, s)
    | None =>
      let i := intern_next s in
      (i, InternTable (M.set k i (intern_forward s))
            (PTrieCode.set i k (intern_inverse s)) (Pos.succ i))
    end.
End InternCode.

Module Intern (K : KEY) (M : MAP K) <: INTERN K.
  Include InternCode K M.
  Definition wf (s : t) : Prop :=
    M.wf (intern_forward s) /\
    (forall k i, find k s = Some i -> (i < intern_next s)%positive) /\
    (forall k i, find k s = Some i <-> name i s = Some k) /\
    (forall i, (i < intern_next s)%positive -> exists k, find k s = Some i).
  Lemma find_empty : forall k, find k empty = None.
  Proof. intro k; apply M.get_empty. Qed.
  Lemma name_empty : forall i, name i empty = None.
  Proof. intro i; apply PTrie.get_empty. Qed.
  Lemma wf_empty : wf empty.
  Proof.
    split; [apply M.wf_empty|]. split.
    - intros k i H; rewrite find_empty in H; discriminate.
    - split.
      + intros k i; rewrite find_empty, name_empty; split; discriminate.
      + intros i Hi; change (i < 1)%positive in Hi; lia.
  Qed.
  Lemma wf_intern : forall k s, wf s -> wf (snd (intern k s)).
  Proof. Admitted. (* CONVERT: intern_wf: The variable fresh_bound was not found in the current environment. *)
  Lemma size_empty : size empty = 0%N.
  Proof. Admitted.
  Lemma find_name : forall k i s, wf s -> (find k s = Some i <-> name i s = Some k).
  Proof. intros k i s [_ [_ [Hlink _]]]; apply Hlink. Qed.
  Lemma find_inj : forall k l i s, wf s ->
    find k s = Some i -> find l s = Some i -> k = l.
  Proof.
    intros k l i s Hwf Hk Hl.
    apply (proj1 (find_name k i s Hwf)) in Hk.
    apply (proj1 (find_name l i s Hwf)) in Hl; congruence.
  Qed.
  Lemma find_range : forall k i s, wf s -> find k s = Some i ->
    (N.pos i <= size s)%N.
  Proof. Admitted. (* CONVERT: ids_size: The variable ids_size was not found in the current environment. *)
  Lemma dense : forall i s, wf s -> (N.pos i <= size s)%N -> exists k, name i s = Some k.
  Proof. Admitted. (* CONVERT: ids_size: The variable ids_size was not found in the current environment. *)
  Lemma intern_found : forall k s i, find k s = Some i -> intern k s = (i, s).
  Proof. intros k s i H; unfold intern; rewrite H; reflexivity. Qed.
  Lemma intern_new : forall k s, wf s -> find k s = None ->
    N.pos (fst (intern k s)) = N.succ (size s).
  Proof. Admitted. (* CONVERT: next_size: The variable next_size was not found in the current environment. *)
  Lemma find_intern_same : forall k s, wf s ->
    find k (snd (intern k s)) = Some (fst (intern k s)).
  Proof.
    intros k s Hwf; unfold intern; destruct (find k s) eqn:H; cbn; [exact H|].
    apply M.get_set_same.
  Qed.
  Lemma find_intern_other : forall k l s, wf s -> k <> l ->
    find l (snd (intern k s)) = find l s.
  Proof.
    intros k l s Hwf Hneq; unfold intern; destruct (find k s) eqn:H; cbn; [reflexivity|].
    unfold find; cbn; apply M.get_set_other; congruence.
  Qed.
  Lemma name_intern : forall k s, wf s ->
    name (fst (intern k s)) (snd (intern k s)) = Some k.
  Proof.
    intros k s Hwf; apply (proj1 (find_name k (fst (intern k s)) (snd (intern k s)) (wf_intern k s Hwf))).
    apply find_intern_same; exact Hwf.
  Qed.
  Lemma name_stable : forall k s i l, wf s -> name i s = Some l ->
    name i (snd (intern k s)) = Some l.
  Proof. Admitted.
  Lemma size_intern : forall k s, wf s ->
    size (snd (intern k s)) =
      match find k s with Some _ => size s | None => N.succ (size s) end.
  Proof. Admitted.
End Intern.

Module InternT (K : KEY_T) (M : MAP_T K) <: INTERN_T K.
  Include Intern K M.

  TimeFun find.
  TimeFun name.
  TimeFun size.
  TimeFun intern.

  Definition c_intern : nat := 1. (* STUB *)

  Lemma T_intern_le : forall k s, wf s ->
    T_intern k s <= c_intern * (K.bits k + N.size_nat (size s) + 1).
  Proof. Admitted. (* STUB *)
  Lemma T_find_le : forall k s,
    T_find k s <= c_intern * (K.bits k + N.size_nat (size s) + 1).
  Proof. Admitted. (* STUB *)
  Lemma T_name_le : forall i s,
    T_name i s <= c_intern * (Pos.size_nat i + N.size_nat (size s) + 1).
  Proof. Admitted. (* STUB *)
End InternT.
