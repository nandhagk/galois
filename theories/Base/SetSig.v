(** * Keyed set signatures

    Keyed sets provide membership and finite set operations over client keys.
    For example, union contains each key present in either operand.
    Builds on: KeySig, Stdlib lists and Argent time interfaces. *)

From Stdlib Require Import PArith List Bool.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.

Module Type SET_OPS (K : KEY_OPS).
  Parameter t : Type.
  Parameter empty : t.
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

Module Type SET_LAWS (K : KEY) (Import S : SET_OPS K).
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
  (** Inclusion checks membership implication for every key. *)
  Parameter subset_spec : forall s u,
    subset s u = true <-> forall k, mem k s = true -> mem k u = true.
  (** Equality checks agreement of all membership observations. *)
  Parameter equal_spec : forall s u,
    equal s u = true <-> forall k, mem k s = mem k u.
  (** Consistent sets enumerate precisely their members. *)
  Parameter elements_spec : forall s k, wf s -> (In k (elements s) <-> mem k s = true).
  (** Consistent sets enumerate each member once. *)
  Parameter elements_nodup : forall s, wf s -> NoDup (elements s).
  (** Folding follows enumeration order. *)
  Parameter fold_spec : forall A (f : A -> K.t -> A) s a,
    fold f s a = fold_left f (elements s) a.
  (** Membership determines a consistent set. *)
  Parameter ext : forall s u, wf s -> wf u -> (forall k, mem k s = mem k u) -> s = u.
End SET_LAWS.

Module Type SET (K : KEY) := SET_OPS K <+ SET_SPEC K <+ SET_LAWS K.

Module Type SET_TIME (K : KEY_T) (Import S : SET K).
  Parameter T_mem : K.t -> t -> nat.
  Parameter T_add : K.t -> t -> nat.
  Parameter T_remove : K.t -> t -> nat.
  Parameter T_union : t -> t -> nat.
  Parameter T_inter : t -> t -> nat.
  Parameter T_diff : t -> t -> nat.
  Parameter T_subset : t -> t -> nat.
  Parameter T_equal : t -> t -> nat.
  Parameter T_elements : t -> nat.
  Parameter T_fold : forall {A}, (A -> K.t -> A) -> (A -> K.t -> nat) -> t -> A -> nat.
  Parameter c_set : nat.
  (** Membership takes time bounded by the encoded key length. *)
  Parameter T_mem_le : forall k s, T_mem k s <= c_set * (K.bits k + 1).
  (** Adding a member takes time bounded by the encoded key length. *)
  Parameter T_add_le : forall k s, T_add k s <= c_set * (K.bits k + 1).
  (** Removing a member takes time bounded by the encoded key length. *)
  Parameter T_remove_le : forall k s, T_remove k s <= c_set * (K.bits k + 1).
  (** Union visits at most the combined skeletons. *)
  Parameter T_union_le : forall s u, T_union s u <= c_set * (nodes s + nodes u + 1).
  (** Intersection visits at most the combined skeletons. *)
  Parameter T_inter_le : forall s u, T_inter s u <= c_set * (nodes s + nodes u + 1).
  (** Difference visits at most the combined skeletons. *)
  Parameter T_diff_le : forall s u, T_diff s u <= c_set * (nodes s + nodes u + 1).
  (** Inclusion checking visits at most the combined skeletons. *)
  Parameter T_subset_le : forall s u, T_subset s u <= c_set * (nodes s + nodes u + 1).
  (** Equality checking visits at most the combined skeletons. *)
  Parameter T_equal_le : forall s u, T_equal s u <= c_set * (nodes s + nodes u + 1).
  (** Enumeration charges the encoded members of a consistent set. *)
  Parameter T_elements_le : forall s, wf s -> T_elements s <= c_set * (weight s + 1).
  (** Folding charges bounded callbacks over one skeleton. *)
  Parameter T_fold_le : forall A (f : A -> K.t -> A) T_f s a c,
    (forall acc k, T_f acc k <= c) ->
    T_fold f T_f s a <= c_set * (c + 1) * (nodes s + 1).
End SET_TIME.

Module Type SET_T (K : KEY_T) := SET K <+ SET_TIME K.
