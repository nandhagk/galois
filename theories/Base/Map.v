(** * Trie maps

    Maps store client keys and values in a canonical trie.
    For example, enumeration returns the client key stored by insertion.
    Builds on: KeySig, TrieSig and Argent time interfaces. *)

From Stdlib Require Import List Bool NArith Lia Sorting.Sorted.
From Argent Require Import Time.
From Galois.Base Require Import KeySig TrieSig MapSig.
From Galois.Base Require Import Trie.

Module TrieMapCode (K : KEY_OPS) <: MAP_OPS K.
  Definition t := kmap K.t.
  Definition empty {A} : t A := PTrieCode.empty.
  Definition get {A} (k : K.t) (m : t A) := option_map snd (PTrieCode.get (K.encode k) m).
  Definition set {A} (k : K.t) (a : A) (m : t A) := PTrieCode.set (K.encode k) (k, a) m.
  Definition remove {A} (k : K.t) (m : t A) := PTrieCode.remove (K.encode k) m.
  Definition merge {A B C} (f : option A -> option B -> option C) (x : t A) (y : t B) : t C :=
    PTrieCode.merge (fun a b =>
      match a, b with
      | Some (k, v), Some (_, w) => option_map (pair k) (f (Some v) (Some w))
      | Some (k, v), None => option_map (pair k) (f (Some v) None)
      | None, Some (k, w) => option_map (pair k) (f None (Some w))
      | None, None => None
      end) x y.
  Definition forall2b {A B} (f : option A -> option B -> bool) (x : t A) (y : t B) :=
    PTrieCode.forall2b (fun a b => f (option_map snd a) (option_map snd b)) x y.
  Definition existsb {A} (f : A -> bool) (x : t A) := PTrieCode.existsb (fun kv => f (snd kv)) x.
  Definition fold {A B} (f : B -> K.t -> A -> B) (x : t A) (b : B) :=
    PTrieCode.fold_values (fun acc kv => f acc (fst kv) (snd kv)) x b.
  Definition elements {A} (x : t A) : list (K.t * A) :=
    List.rev (fold (fun acc k a => (k, a) :: acc) x nil).
End TrieMapCode.
