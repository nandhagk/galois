(** * Interning and indexes

    Interners assign dense identifiers and indexes group values by key.
    For example, interning [a; b; a] allocates only two identifiers.
    Builds on: InternSig, MapSig and KeySig. *)

From Stdlib Require Import List Bool NArith PArith Lia Sorting.Sorted.
From Argent Require Import Time.
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
