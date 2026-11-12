(** * Trie indexes for tuples

    Indexes expose tuple membership and navigation through live prefixes.
    For example, following two children from the root selects a two-cell prefix.
    Builds on: ValueSig and Syntax. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig Syntax.

Import List.ListNotations.

Definition cell_bits {V : Type} (encode : V -> positive) (c : cell V) : nat :=
  match c with
  | Id i => Pos.size_nat (xO i)
  | Val v => Pos.size_nat (xI (encode v))
  end.
TimeFun cell_bits.

Module Type INDEX_OPS (V : VALUE_OPS).
  Parameter t : Type.
  Parameter empty : t.
  Parameter insert : list (cell V.t) -> t -> t.
  Parameter remove : list (cell V.t) -> t -> t.
  Parameter next : t -> positive.
  Parameter root : t -> positive.
  Parameter child : t -> positive -> cell V.t -> option positive.
  Parameter children : t -> positive -> list (cell V.t).
  Parameter degree : t -> positive -> N.
End INDEX_OPS.

Module Type INDEX_SPEC (V : VALUE_OPS) (Import X : INDEX_OPS V).
End INDEX_SPEC.

Module Type INDEX_LAWS (V : VALUE) (Import X : INDEX_OPS V).
  (* spec: wf mem node *)
  Parameter wf : nat -> t -> Prop.
  Parameter mem : t -> list (cell V.t) -> Prop.
  Parameter node : t -> positive -> list (cell V.t) -> Prop.
  (** The initial node counter starts at one. *)
  Parameter next_empty : next empty = 1%positive.
  (** Insertion allocates at most one node per tuple cell. *)
  Parameter next_insert : forall a r ix, wf a ix ->
    (next (insert r ix) <= next ix + Pos.of_nat (length r))%positive.
  (** Removal keeps the fresh node counter. *)
  Parameter next_remove : forall a r ix, wf a ix -> next (remove r ix) = next ix.
  (** Empty indexes accept every arity. *)
  (** Empty indexes contain no tuple. *)
  Parameter mem_empty : forall u, ~ mem empty u.
  Parameter wf_empty : forall a, wf a empty.
  (** Insertion keeps the declared arity. *)
  Parameter wf_insert : forall a r ix, wf a ix -> length r = a -> wf a (insert r ix).
  (** Removal keeps the declared arity. *)
  Parameter wf_remove : forall a r ix, wf a ix -> wf a (remove r ix).
  (** Insertion adds precisely the supplied tuple. *)
  Parameter mem_insert : forall a r ix u, wf a ix -> length r = a ->
    (mem (insert r ix) u <-> u = r \/ mem ix u).
  (** Removal deletes precisely the supplied tuple. *)
  Parameter mem_remove : forall a r ix u, wf a ix ->
    (mem (remove r ix) u <-> u <> r /\ mem ix u).
  (** Members have the declared arity. *)
  Parameter mem_arity : forall a ix u, wf a ix -> mem ix u -> length u = a.
  (** The root represents the empty prefix. *)
  Parameter node_root : forall a ix, wf a ix -> node ix (root ix) [].
  (** Every nonempty node prefix extends to a member. *)
  Parameter node_live : forall a ix n pre, wf a ix -> node ix n pre -> pre <> [] ->
    exists suf, mem ix (pre ++ suf).
  (** A prefix identifies at most one node. *)
  Parameter node_fun : forall a ix n m pre, wf a ix ->
    node ix n pre -> node ix m pre -> n = m.
  (** Child lookup agrees with prefix extension and detects missing members. *)
  Parameter child_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (forall m, child ix n c = Some m <-> node ix m (pre ++ [c])) /\
    (child ix n c = None <-> ~ exists suf, mem ix (pre ++ c :: suf)).
  (** Child enumeration is exact and duplicate free. *)
  Parameter children_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (In c (children ix n) <-> exists m, child ix n c = Some m) /\
    NoDup (children ix n).
  (** Stored degrees count enumerated children. *)
  Parameter degree_spec : forall a ix n pre, wf a ix -> node ix n pre ->
    N.to_nat (degree ix n) = length (children ix n).
End INDEX_LAWS.

Module Type INDEX (V : VALUE) := INDEX_OPS V <+ INDEX_SPEC V <+ INDEX_LAWS V.

Module Type INDEX_TIME (V : VALUE_T) (Import X : INDEX V).
  (* spec: width *)
  (** The largest encoded cell width stored on an index edge. *)
  Parameter max_cell_bits : t -> nat.
  Parameter width : t -> list (cell V.t) -> nat.
  (** Empty indexes have no encoded cells. *)
  Parameter max_cell_bits_empty : max_cell_bits empty = 0.
  (** Insertion adds at most the encoded width of its tuple. *)
  Parameter max_cell_bits_insert : forall r ix,
    max_cell_bits (insert r ix) <=
      Nat.max (max_cell_bits ix)
        (fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r).
  (** Removal never increases the stored cell width. *)
  Parameter max_cell_bits_remove : forall r ix,
    max_cell_bits (remove r ix) <= max_cell_bits ix.
  (** Width charges the fresh node counter and the largest query and stored cells. *)
  Parameter width_le : forall ix r,
    width ix r <= Pos.size_nat (next ix + Pos.of_nat (length r)) +
      fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r + max_cell_bits ix.
  Parameter T_empty : N.
  Parameter T_insert T_remove : list (cell V.t) -> t -> N.
  Parameter T_next : t -> N.
  Parameter T_root : t -> N.
  Parameter T_child : t -> positive -> cell V.t -> N.
  Parameter T_children T_degree : t -> positive -> N.
  Parameter c_ix : N.
  (** The fresh node counter is stored. *)
  Parameter T_next_le : forall ix, (T_next ix <= c_ix)%N.
  (** Insertion pays for one path through the tuple. *)
  Parameter T_insert_le : forall r ix,
    (T_insert r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  (** Removal pays for one path through the tuple. *)
  Parameter T_remove_le : forall r ix,
    (T_remove r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  (** Child lookup pays for the encoded edge. *)
  Parameter T_child_le : forall ix n c,
    (T_child ix n c <= c_ix * N.of_nat (width ix [c] + 1))%N.
  (** Child enumeration pays for each child. *)
  Parameter T_children_le : forall ix n,
    (T_children ix n <= c_ix * N.of_nat (N.to_nat (degree ix n) + 1) *
      N.of_nat (width ix [] + 1))%N.
  (** Degree lookup pays for the encoded node. *)
  Parameter T_degree_le : forall ix n,
    (T_degree ix n <= c_ix * N.of_nat (width ix [] + 1))%N.
End INDEX_TIME.

Module Type INDEX_T (V : VALUE_T) := INDEX V <+ INDEX_TIME V.

Module Type INDEX_PLAN (V : VALUE_T) (Import X : INDEX_T V).
  Parameter inv : t -> Prop.
  (** The representation invariant and member arities characterize well-formed indexes. *)
  Parameter inv_wf : forall a ix,
    wf a ix <-> inv ix /\ (forall u, mem ix u -> length u = a).
  (** Walking and allocating an insertion path keeps edge and count consistency. *)
  Parameter insert_path : forall ix r, inv ix -> inv (insert r ix).
  (** Unlinking zero-count nodes keeps edge and count consistency. *)
  Parameter remove_path : forall ix r, inv ix -> inv (remove r ix).
  Parameter insert_step : t -> positive -> cell V.t -> t.
  Parameter T_insert_step : t -> positive -> cell V.t -> N.
  Parameter c_map : N.
  (** A path step uses at most four map operations and constant bookkeeping. *)
  Parameter T_insert_step_le : forall ix n c,
    (T_insert_step ix n c <= 4 * c_map * N.of_nat (width ix [c] + 1) + 4)%N.
  Definition walk_state := (t * positive)%type.
  Parameter start : t -> walk_state.
  Parameter insert_step_st remove_step_st : walk_state -> cell V.t -> walk_state.
  Parameter insert_finish remove_finish : list (cell V.t) -> t -> walk_state -> t.
  Parameter T_start : t -> N.
  Parameter T_insert_step_st T_remove_step_st : walk_state -> cell V.t -> N.
  Parameter T_insert_finish T_remove_finish : list (cell V.t) -> t -> walk_state -> N.
  (** Edge maps use the shared binary trie contracts. *)
  Parameter c_map_source : c_map = PTrieT.c_trie.
  Parameter k_walk : N.
  (** The public constant absorbs the aggregate path and wrapper charges. *)
  Parameter c_ix_walk : (4 * c_map + 4 + k_walk <= c_ix)%N.
  (** Each insertion step uses the width of the complete original walk. *)
  Parameter T_insert_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_insert_step_st (fold_left insert_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  (** Each removal step uses the width of the complete original walk. *)
  Parameter T_remove_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_remove_step_st (fold_left remove_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  (** Initialization and both finishing passes fit the original walk budget. *)
  Parameter T_walk_ends : forall r ix st, inv ix ->
    (T_start ix + T_insert_finish r ix st + T_remove_finish r ix st <=
      k_walk * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.

  (** Insertion follows its named state walk. *)
  Parameter F_insert_steps : forall r ix, inv ix ->
    insert r ix = insert_finish r ix (fold_left insert_step_st r (start ix)).
  (** Removal follows its named state walk. *)
  Parameter F_remove_steps : forall r ix, inv ix ->
    remove r ix = remove_finish r ix (fold_left remove_step_st r (start ix)).
  (** Insertion aggregates the path-step charges. *)
  Parameter T_insert_steps : forall r ix, inv ix ->
    (T_insert r ix <= N.of_nat (length r + 1) *
      ((4 * c_map + k_walk) * N.of_nat (width ix r + 1) + 4))%N.
  (** Removal aggregates the path-step charges. *)
  Parameter T_remove_steps : forall r ix, inv ix ->
    (T_remove r ix <= N.of_nat (length r + 1) *
      ((4 * c_map + k_walk) * N.of_nat (width ix r + 1) + 4))%N.

End INDEX_PLAN.

Module Type INDEX_ALL (V : VALUE_T) := INDEX_T V <+ INDEX_PLAN V.
