(** * Trie sets

    Unit-valued maps represent finite sets.
    For example, adding one key twice leaves a singleton.
    Builds on: SetSig and MapSig. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Argent Require Import Time.
From Galois.Base Require Import KeySig TrieSig MapSig SetSig.
From Galois.Base Require Import Trie.

Module TrieSetCode (K : KEY_OPS) <: SET_OPS K.
  Definition t := PTrieCode.t K.t.
  Definition empty : t := PTrieCode.empty.
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
  Definition elements (s : t) := List.rev (fold (fun acc k => k :: acc) s nil).
End TrieSetCode.
