(** * Placeholder tuple indexes

    Indexes store tuples and navigate prefixes.
    For example, an empty index has a root node.
    Builds on: IndexSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
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
  Definition next (_ : t) : positive := 1%positive.
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
  (** The initial node counter starts at one. *)
  Lemma next_empty : next empty = 1%positive.
  Proof. Admitted. (* STUB *)

  (** Insertion allocates at most one node per tuple cell. *)
  Lemma next_insert : forall a r ix, wf a ix ->
    (next (insert r ix) <= next ix + Pos.of_nat (length r))%positive.
  Proof. Admitted. (* STUB *)

  (** Removal keeps the fresh node counter. *)
  Lemma next_remove : forall a r ix, wf a ix -> next (remove r ix) = next ix.
  Proof. Admitted. (* STUB *)

  Lemma mem_empty : forall u, ~ mem empty u.
  Proof. Admitted. (* STUB *)

  Lemma wf_empty : forall a, wf a empty.
  Proof. Admitted. (* STUB *)

  Lemma wf_insert : forall a r ix, wf a ix -> length r = a -> wf a (insert r ix).
  Proof. Admitted. (* STUB *)

  Lemma wf_remove : forall a r ix, wf a ix -> wf a (remove r ix).
  Proof. Admitted. (* STUB *)

  Lemma mem_insert : forall a r ix u, wf a ix -> length r = a ->
    (mem (insert r ix) u <-> u = r \/ mem ix u).
  Proof. Admitted. (* STUB *)

  Lemma mem_remove : forall a r ix u, wf a ix ->
    (mem (remove r ix) u <-> u <> r /\ mem ix u).
  Proof. Admitted. (* STUB *)

  Lemma mem_arity : forall a ix u, wf a ix -> mem ix u -> length u = a.
  Proof. Admitted. (* STUB *)

  Lemma node_root : forall a ix, wf a ix -> node ix (root ix) [].
  Proof. Admitted. (* STUB *)

  Lemma node_live : forall a ix n pre, wf a ix -> node ix n pre -> pre <> [] ->
    exists suf, mem ix (pre ++ suf).
  Proof. Admitted. (* STUB *)

  Lemma node_fun : forall a ix n m pre, wf a ix ->
    node ix n pre -> node ix m pre -> n = m.
  Proof. Admitted. (* STUB *)

  Lemma child_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (forall m, child ix n c = Some m <-> node ix m (pre ++ [c])) /\
    (child ix n c = None <-> ~ exists suf, mem ix (pre ++ c :: suf)).
  Proof. Admitted. (* STUB *)

  Lemma children_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (In c (children ix n) <-> exists m, child ix n c = Some m) /\
    NoDup (children ix n).
  Proof. Admitted. (* STUB *)

  Lemma degree_spec : forall a ix n pre, wf a ix -> node ix n pre ->
    N.to_nat (degree ix n) = length (children ix n).
  Proof. Admitted. (* STUB *)

End Index.

Module IndexT (V : VALUE_T) <: INDEX_ALL V.
  Include Index V.
  TimeFun empty.
  TimeFun insert.
  TimeFun remove.
  TimeFun next.
  TimeFun root.
  TimeFun child.
  TimeFun children.
  TimeFun degree.
  Definition max_cell_bits (ix : t) : nat :=
    fold_right (fun r n => fold_right
      (fun c m => Nat.max (cell_bits V.encode c) m) n r) 0 ix.
  Definition width (_ : t) (_ : list (cell V.t)) : nat := 0.
  (** Empty indexes have no encoded cells. *)
  Lemma max_cell_bits_empty : max_cell_bits empty = 0.
  Proof. Admitted. (* STUB *)

  (** Insertion adds at most the encoded width of its tuple. *)
  Lemma max_cell_bits_insert : forall r ix,
    max_cell_bits (insert r ix) <=
      Nat.max (max_cell_bits ix)
        (fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r).
  Proof. Admitted. (* STUB *)

  (** Removal never increases the stored cell width. *)
  Lemma max_cell_bits_remove : forall r ix,
    max_cell_bits (remove r ix) <= max_cell_bits ix.
  Proof. Admitted. (* STUB *)

  (** Every stored cell fits the recorded cell width. *)
  Lemma max_cell_bits_mem : forall a ix u c, wf a ix -> mem ix u -> In c u ->
    cell_bits V.encode c <= max_cell_bits ix.
  Proof. Admitted. (* STUB *)

  Lemma width_le : forall ix r,
    width ix r <= Pos.size_nat (next ix + Pos.of_nat (length r)) +
      fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r + max_cell_bits ix.
  Proof. Admitted. (* STUB *)

  Definition c_ix : N := 1. (* STUB *)
  (** The fresh node counter is stored. *)
  Lemma T_next_le : forall ix, (T_next ix <= c_ix)%N.
  Proof. Admitted. (* STUB *)

  (** The empty index is a constant. *)
  Lemma T_empty_le : (T_empty <= c_ix)%N.
  Proof. Admitted. (* STUB *)

  (** The root is stored. *)
  Lemma T_root_le : forall ix, (T_root ix <= c_ix)%N.
  Proof. Admitted. (* STUB *)

  Lemma T_insert_le : forall a r ix, wf a ix ->
    (T_insert r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_remove_le : forall a r ix, wf a ix ->
    (T_remove r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_child_le : forall ix n c,
    (T_child ix n c <= c_ix * N.of_nat (width ix [c] + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_children_le : forall a ix n, wf a ix ->
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

  Definition walk_state := (t * positive)%type.
  (* STUB-CODE *)
  Definition start (ix : t) : walk_state := (ix, root ix).
  (* STUB-CODE *)
  Definition insert_step_st (st : walk_state) (_ : cell V.t) := st.
  (* STUB-CODE *)
  Definition remove_step_st (st : walk_state) (_ : cell V.t) := st.
  (* STUB-CODE *)
  Definition insert_finish (_ : list (cell V.t)) (ix : t) (_ : walk_state) := ix.
  (* STUB-CODE *)
  Definition remove_finish (_ : list (cell V.t)) (ix : t) (_ : walk_state) := ix.
  TimeFun start.
  TimeFun insert_step_st.
  TimeFun remove_step_st.
  TimeFun insert_finish.
  TimeFun remove_finish.

  (** Edge maps use the shared binary trie contracts. *)
  Lemma c_map_source : c_map = PTrieT.c_trie.
  Proof. Admitted. (* STUB *)
  Definition k_walk : N := 1. (* STUB *)
  (** The public constant absorbs the aggregate path and wrapper charges. *)
  Lemma c_ix_walk : (4 * c_map + 4 + k_walk <= c_ix)%N.
  Proof. Admitted. (* STUB *)
  (** Each insertion step uses the width of the complete original walk. *)
  Lemma T_insert_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_insert_step_st (fold_left insert_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  Proof. Admitted. (* STUB *)

  (** Each removal step uses the width of the complete original walk. *)
  Lemma T_remove_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_remove_step_st (fold_left remove_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  Proof. Admitted. (* STUB *)

  (** Initialization and both finishing passes fit the original walk budget. *)
  Lemma T_walk_ends : forall r ix, inv ix ->
    (T_start ix +
     T_insert_finish r ix (fold_left insert_step_st r (start ix)) +
     T_remove_finish r ix (fold_left remove_step_st r (start ix)) <=
      k_walk * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Insertion follows its named state walk. *)
  Lemma F_insert_steps : forall r ix, inv ix ->
    insert r ix = insert_finish r ix (fold_left insert_step_st r (start ix)).
  Proof. Admitted. (* STUB *)

  (** Removal follows its named state walk. *)
  Lemma F_remove_steps : forall r ix, inv ix ->
    remove r ix = remove_finish r ix (fold_left remove_step_st r (start ix)).
  Proof. Admitted. (* STUB *)

  (** Insertion aggregates the path-step charges. *)
  Lemma T_insert_steps : forall r ix, inv ix ->
    (T_insert r ix <= N.of_nat (length r + 1) *
      ((4 * c_map + k_walk) * N.of_nat (width ix r + 1) + 4))%N.
  Proof. Admitted. (* STUB *)

  (** Removal aggregates the path-step charges. *)
  Lemma T_remove_steps : forall r ix, inv ix ->
    (T_remove r ix <= N.of_nat (length r + 1) *
      ((4 * c_map + k_walk) * N.of_nat (width ix r + 1) + 4))%N.
  Proof. Admitted. (* STUB *)

End IndexT.
