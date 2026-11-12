(** * Trie indexes for tuples

    Indexes expose tuple membership and navigation through live prefixes.
    For example, following two children from the root selects a two-cell prefix.
    Builds on: ValueSig and Syntax. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time.
From Galois.Egglog Require Import ValueSig Syntax.

Import List.ListNotations.

Module Type INDEX_OPS (V : VALUE_OPS).
  Parameter t : Type.
  Parameter empty : t.
  Parameter insert : list (cell V.t) -> t -> t.
  Parameter remove : list (cell V.t) -> t -> t.
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
  (** Empty indexes accept every arity. *)
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
  Parameter width : t -> list (cell V.t) -> nat.
  Parameter T_empty : nat.
  Parameter T_insert T_remove : list (cell V.t) -> t -> nat.
  Parameter T_root : t -> nat.
  Parameter T_child : t -> positive -> cell V.t -> nat.
  Parameter T_children T_degree : t -> positive -> nat.
  Parameter c_ix : nat.
  (** Insertion pays for one path through the tuple. *)
  Parameter T_insert_le : forall r ix,
    T_insert r ix <= c_ix * (length r + 1) * (width ix r + 1).
  (** Removal pays for one path through the tuple. *)
  Parameter T_remove_le : forall r ix,
    T_remove r ix <= c_ix * (length r + 1) * (width ix r + 1).
  (** Child lookup pays for the encoded edge. *)
  Parameter T_child_le : forall ix n c, T_child ix n c <= c_ix * (width ix [c] + 1).
  (** Child enumeration pays for each child. *)
  Parameter T_children_le : forall ix n,
    T_children ix n <= c_ix * (N.to_nat (degree ix n) + 1) * (width ix [] + 1).
  (** Degree lookup pays for the encoded node. *)
  Parameter T_degree_le : forall ix n, T_degree ix n <= c_ix * (width ix [] + 1).
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
  Parameter T_insert_step : t -> positive -> cell V.t -> nat.
  Parameter c_map : nat.
  (** A path step uses at most four map operations and constant bookkeeping. *)
  Parameter T_insert_step_le : forall ix n c,
    T_insert_step ix n c <= 4 * c_map * (width ix [c] + 1) + 4.
End INDEX_PLAN.

Module Type INDEX_ALL (V : VALUE_T) := INDEX_T V <+ INDEX_PLAN V.
