(** * Interning signatures

    Interning assigns stable dense positive identifiers to client keys.
    For example, interning the same key twice returns the same identifier.
    Builds on: KeySig, Stdlib binary arithmetic, and Argent time interfaces. *)

From Stdlib Require Import PArith NArith.
From Argent Require Import Time.
From Galois.Base Require Import KeySig.

Module Type INTERN_OPS (K : KEY_OPS).
  Parameter t : Type.
  Parameter empty : t.
  Parameter intern : K.t -> t -> positive * t.
  Parameter find : K.t -> t -> option positive.
  Parameter name : positive -> t -> option K.t.
  Parameter size : t -> N.
End INTERN_OPS.

Module Type INTERN_LAWS (K : KEY) (Import I : INTERN_OPS K).
  (* spec: wf *)
  Parameter wf : t -> Prop.
  (** Empty tables have consistent forward and inverse maps. *)
  Parameter wf_empty : wf empty.
  (** Interning retains consistency of both maps. *)
  Parameter wf_intern : forall k s, wf s -> wf (snd (intern k s)).
  (** Empty tables contain no key. *)
  Parameter find_empty : forall k, find k empty = None.
  (** Empty tables contain no identifier. *)
  Parameter name_empty : forall i, name i empty = None.
  (** Empty tables have zero size. *)
  Parameter size_empty : size empty = 0%N.
  (** A key's identifier names exactly that key in a consistent table. *)
  Parameter find_name : forall k i s, wf s -> (find k s = Some i <-> name i s = Some k).
  (** Distinct keys have distinct identifiers. *)
  Parameter find_inj : forall k l i s, wf s ->
    find k s = Some i -> find l s = Some i -> k = l.
  (** Every allocated identifier is within the dense interval. *)
  Parameter find_range : forall k i s, wf s -> find k s = Some i ->
    (N.pos i <= size s)%N.
  (** Every identifier up to the table size names a key. *)
  Parameter dense : forall i s, wf s -> (N.pos i <= size s)%N ->
    exists k, name i s = Some k.
  (** Interning an existing key leaves the table unchanged. *)
  Parameter intern_found : forall k s i, find k s = Some i -> intern k s = (i, s).
  (** A new key receives the next dense identifier. *)
  Parameter intern_new : forall k s, wf s -> find k s = None ->
    N.pos (fst (intern k s)) = N.succ (size s).
  (** Interning installs the returned identifier in the forward map. *)
  Parameter find_intern_same : forall k s, wf s ->
    find k (snd (intern k s)) = Some (fst (intern k s)).
  (** Interning leaves other keys' identifiers unchanged. *)
  Parameter find_intern_other : forall k l s, wf s -> k <> l ->
    find l (snd (intern k s)) = find l s.
  (** The inverse map names the key just interned. *)
  Parameter name_intern : forall k s, wf s ->
    name (fst (intern k s)) (snd (intern k s)) = Some k.
  (** Previously allocated identifiers retain their names. *)
  Parameter name_stable : forall k s i l, wf s -> name i s = Some l ->
    name i (snd (intern k s)) = Some l.
  (** Interning increases size exactly when a key is absent. *)
  Parameter size_intern : forall k s, wf s ->
    size (snd (intern k s)) =
      match find k s with Some _ => size s | None => N.succ (size s) end.
End INTERN_LAWS.

Module Type INTERN (K : KEY) := INTERN_OPS K <+ INTERN_LAWS K.

Module Type INTERN_TIME (K : KEY_T) (Import I : INTERN K).
  Parameter T_intern : K.t -> t -> N.
  Parameter T_find : K.t -> t -> N.
  Parameter T_name : positive -> t -> N.
  Parameter T_size : t -> N.
  Parameter c_intern : N.
  (** Interning charges key bits and the allocation frontier's width. *)
  Parameter T_intern_le : forall k s, (wf s ->
    T_intern k s <= c_intern * N.of_nat (K.bits k + N.size_nat (size s) + 1))%N.
  (** Forward lookup charges the queried key's bits. *)
  Parameter T_find_le : forall k s,
    (T_find k s <= c_intern * N.of_nat (K.bits k + N.size_nat (size s) + 1))%N.
  (** Inverse lookup charges the queried identifier's bits, including absent identifiers. *)
  Parameter T_name_le : forall i s,
    (T_name i s <= c_intern * N.of_nat (Pos.size_nat i + N.size_nat (size s) + 1))%N.
End INTERN_TIME.

Module Type INTERN_T (K : KEY_T) := INTERN K <+ INTERN_TIME K.
