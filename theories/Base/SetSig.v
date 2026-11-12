(** * Keyed set signatures

    Keyed sets provide membership and finite set operations over client keys.
    For example, union contains each key present in either operand.
    Builds on: KeySig, Stdlib lists and Argent time interfaces. *)

From Stdlib Require Import NArith PArith List Bool.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.

Module Type SET_OPS (K : KEY_OPS).
  Parameter t : Type.
  Parameter empty : t.
  Parameter has : positive -> t -> bool.
  Parameter mem : K.t -> t -> bool.
  Parameter add : K.t -> t -> t.
  Parameter remove : K.t -> t -> t.
  Parameter union : t -> t -> t.
  Parameter inter : t -> t -> t.
  Parameter diff : t -> t -> t.
  Parameter subset : t -> t -> bool.
  Parameter equal : t -> t -> bool.
  Parameter elements : t -> list K.t.
  Parameter fold : forall {A}, (A -> K.t -> A) -> t -> A -> A.
End SET_OPS.

Module Type SET_SPEC (K : KEY_OPS) (Import S : SET_OPS K).
  (** Weight counts encoded member bits and one unit per member. *)
  Definition weight (s : t) : nat :=
    fold_right Nat.add 0 (List.map (fun k => Pos.size_nat (K.encode k) + 1) (elements s)).
End SET_SPEC.

Module Type SET_LAWS (K : KEY) (Import S : SET_OPS K) (Import W : SET_SPEC K S).
  (* spec: wf nodes *)
  Parameter wf : t -> Prop.
  Parameter nodes : t -> nat.
  (** The empty set has consistent stored keys. *)
  Parameter wf_empty : wf empty.
  (** Adding a key retains consistency. *)
  Parameter wf_add : forall k s, wf s -> wf (add k s).
  (** Removing a key retains consistency. *)
  Parameter wf_remove : forall k s, wf s -> wf (remove k s).
  (** Union retains consistency of its operands. *)
  Parameter wf_union : forall s u, wf s -> wf u -> wf (union s u).
  (** Intersection retains consistency of its operands. *)
  Parameter wf_inter : forall s u, wf s -> wf u -> wf (inter s u).
  (** Difference retains consistency of its operands. *)
  Parameter wf_diff : forall s u, wf s -> wf u -> wf (diff s u).
  (** The empty set has no member. *)
  Parameter mem_empty : forall k, mem k empty = false.
  (** Adding a key makes it a member. *)
  Parameter mem_add_same : forall k s, mem k (add k s) = true.
  (** Adding another key leaves membership unchanged. *)
  Parameter mem_add_other : forall k q s, k <> q -> mem k (add q s) = mem k s.
  (** Removing a key makes it absent. *)
  Parameter mem_remove_same : forall k s, mem k (remove k s) = false.
  (** Removing another key leaves membership unchanged. *)
  Parameter mem_remove_other : forall k q s, k <> q -> mem k (remove q s) = mem k s.
  (** Union contains members of either operand. *)
  Parameter mem_union : forall k s u, mem k (union s u) = (mem k s || mem k u).
  (** Intersection contains shared members. *)
  Parameter mem_inter : forall k s u, mem k (inter s u) = (mem k s && mem k u).
  (** Difference removes the right operand's members from the left. *)
  Parameter mem_diff : forall k s u, mem k (diff s u) = (mem k s && negb (mem k u)).
  (** Consistent sets enumerate precisely their members. *)
  Parameter elements_spec : forall s k, wf s -> (In k (elements s) <-> mem k s = true).
  (** Consistent sets enumerate each member once. *)
  Parameter elements_nodup : forall s, wf s -> NoDup (elements s).
  (** Folding follows enumeration order. *)
  Parameter fold_spec : forall A (f : A -> K.t -> A) s a,
    fold f s a = fold_left f (elements s) a.
  (** Membership determines a consistent set. *)
  Parameter ext : forall s u, wf s -> wf u -> (forall k, mem k s = mem k u) -> s = u.
  Parameter mem_has : forall k s, mem k s = has (K.encode k) s.
  Parameter has_empty : forall p, has p empty = false.
  Parameter has_add : forall p k s, has p (add k s) = Pos.eqb p (K.encode k) || has p s.
  Parameter has_remove : forall p k s,
  has p (remove k s) = negb (Pos.eqb p (K.encode k)) && has p s.
  Parameter has_union : forall p s u, has p (union s u) = has p s || has p u.
  Parameter has_inter : forall p s u, has p (inter s u) = has p s && has p u.
  Parameter has_diff : forall p s u, has p (diff s u) = has p s && negb (has p u).
  Parameter subset_spec : forall s u,
  subset s u = true <-> forall p, has p s = true -> has p u = true.
  Parameter equal_spec : forall s u, equal s u = true <-> forall p, has p s = has p u.
  Parameter wf_has : forall s p, wf s -> has p s = true -> exists k, K.encode k = p.

  Parameter nodes_empty : nodes empty = 0.
  Parameter nodes_add : forall k s, nodes (add k s) <= nodes s + K.bits k.
  Parameter nodes_remove : forall k s, nodes (remove k s) <= nodes s.
  Parameter nodes_union : forall s u, nodes (union s u) <= nodes s + nodes u.
  Parameter nodes_inter : forall s u, nodes (inter s u) <= nodes s.
  Parameter nodes_diff : forall s u, nodes (diff s u) <= nodes s.
  Parameter nodes_le_weight : forall s, wf s -> nodes s <= weight s.
End SET_LAWS.

Module Type SET (K : KEY) := SET_OPS K <+ SET_SPEC K <+ SET_LAWS K.

Module Type SET_TIME (K : KEY_T) (Import S : SET K).
  Parameter T_mem : K.t -> t -> N.
  Parameter T_add : K.t -> t -> N.
  Parameter T_remove : K.t -> t -> N.
  Parameter T_union : t -> t -> N.
  Parameter T_inter : t -> t -> N.
  Parameter T_diff : t -> t -> N.
  Parameter T_subset : t -> t -> N.
  Parameter T_equal : t -> t -> N.
  Parameter T_elements : t -> N.
  Parameter T_fold : forall {A}, (A -> K.t -> A) -> (A -> K.t -> N) -> t -> A -> N.
  Parameter c_set : N.
  (** Membership takes time bounded by the encoded key length. *)
  Parameter T_mem_le : forall k s, (T_mem k s <= c_set * N.of_nat (K.bits k + 1))%N.
  (** Adding a member takes time bounded by the encoded key length. *)
  Parameter T_add_le : forall k s, (T_add k s <= c_set * N.of_nat (K.bits k + 1))%N.
  (** Removing a member takes time bounded by the encoded key length. *)
  Parameter T_remove_le : forall k s, (T_remove k s <= c_set * N.of_nat (K.bits k + 1))%N.
  (** Union visits at most the combined skeletons. *)
  Parameter T_union_le : forall s u, (T_union s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  (** Intersection visits at most the combined skeletons. *)
  Parameter T_inter_le : forall s u, (T_inter s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  (** Difference visits at most the combined skeletons. *)
  Parameter T_diff_le : forall s u, (T_diff s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  (** Inclusion checking visits at most the combined skeletons. *)
  Parameter T_subset_le : forall s u, (T_subset s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  (** Equality checking visits at most the combined skeletons. *)
  Parameter T_equal_le : forall s u, (T_equal s u <= c_set * N.of_nat (nodes s + nodes u + 1))%N.
  (** Enumeration charges the encoded members of a consistent set. *)
  Parameter T_elements_le : forall s, (wf s -> T_elements s <= c_set * N.of_nat (weight s + 1))%N.
  (** Folding charges bounded callbacks over one skeleton. *)
  Parameter T_fold_le : forall A (f : A -> K.t -> A) T_f s a c,
    ((forall acc k, T_f acc k <= c) ->
    T_fold f T_f s a <= c_set * (c + 1) * N.of_nat (nodes s + 1))%N.
End SET_TIME.

Module Type SET_T (K : KEY_T) := SET K <+ SET_TIME K.
