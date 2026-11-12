(** * Priority queues

    A binomial forest indexes a live map and retains obsolete entries after decreases.
    For example, pushing priorities five and two for one key leaves priority two live.
    Builds on: HeapSig, MapSig and Argent time interfaces. *)

From Stdlib Require Import List Bool NArith PArith PeanoNat Lia.
From Argent Require Import Time.
From Galois.Base Require Import HeapSig KeySig MapSig.
From Stdlib Require Import List NArith PArith.
From Galois.Base Require Import Trie Loop.
Import List.ListNotations.

Definition heap_entry := (N * positive)%type.
Scheme All for list.

Inductive heap_tree := HeapTree (root_entry : heap_entry) (children : list heap_tree).
Definition heap_forest := list (option heap_tree).
Record priority_queue := Queue {
  pending : heap_forest;
  live : PTrieCode.t N;
  live_count : N;
  pending_count : N
}.

Definition heap_root (t : heap_tree) := match t with HeapTree e _ => e end.
Definition heap_before (a b : heap_entry) :=
  if N.ltb (fst a) (fst b) then true
  else if N.eqb (fst a) (fst b) then Pos.leb (snd a) (snd b) else false.
Definition heap_link (a b : heap_tree) :=
  match a, b with
  | HeapTree e cs, HeapTree e' cs' =>
    if heap_before e e' then HeapTree e (b :: cs) else HeapTree e' (a :: cs')
  end.
Definition heap_digit (s : option heap_tree) (hs : heap_forest) :=
  match s, hs with None, [] => [] | _, _ => s :: hs end.
Fixpoint heap_insert (t : heap_tree) (h : heap_forest) : heap_forest :=
  match h with
  | [] => [Some t]
  | None :: hs => Some t :: hs
  | Some u :: hs => None :: heap_insert (heap_link t u) hs
  end.
Fixpoint heap_meld (a b : heap_forest) (carry : option heap_tree) {struct a} : heap_forest :=
  match a with
  | [] => match carry with None => b | Some t => heap_insert t b end
  | x :: xs =>
    match b with
    | [] => match carry with None => a | Some t => heap_insert t a end
    | y :: ys =>
      match x, y, carry with
      | None, None, c => heap_digit c (heap_meld xs ys None)
      | Some t, None, None | None, Some t, None => heap_digit (Some t) (heap_meld xs ys None)
      | Some t, Some u, None | Some t, None, Some u | None, Some t, Some u =>
        heap_digit None (heap_meld xs ys (Some (heap_link t u)))
      | Some t, Some u, Some c => heap_digit (Some c) (heap_meld xs ys (Some (heap_link t u)))
      end
    end
  end.
Fixpoint heap_select (h : heap_forest) : option (heap_tree * heap_forest) :=
  match h with
  | [] => None
  | x :: xs =>
    match heap_select xs with
    | None => match x with None => None | Some t => Some (t, []) end
    | Some (t, rest) =>
      match x with
      | None => Some (t, heap_digit None rest)
      | Some u => if heap_before (heap_root u) (heap_root t)
                  then Some (u, heap_digit None xs) else Some (t, heap_digit (Some u) rest)
      end
    end
  end.
Definition heap_remove_min (h : heap_forest) : option (heap_entry * heap_forest) :=
  match heap_select h with
  | None => None
  | Some (HeapTree e cs, rest) => Some (e, heap_meld (map (@Some heap_tree) (rev cs)) rest None)
  end.
Fixpoint heap_fuel (h : heap_forest) : positive :=
  match h with [] => xH | _ :: rest => xO (heap_fuel rest) end.

Module HeapCode <: PQ_OPS.
  Definition t := priority_queue.
  Definition empty : t := Queue [] PTrieCode.empty 0%N 0%N.
  Definition size (q : t) := live_count q.
  Definition enqueue (p : N) (k : positive) (q : t) (n : N) : t :=
    Queue (heap_insert (HeapTree (p, k) []) (pending q))
      (PTrieCode.set k p (live q)) n (N.succ (pending_count q)).
  Definition push (p : N) (k : positive) (q : t) : t :=
    match PTrieCode.get k (live q) with
    | None => enqueue p k q (N.succ (live_count q))
    | Some old => if N.ltb p old then enqueue p k q (live_count q) else q
    end.
  Definition pop_step (m : PTrieCode.t N) (n : N) (s : heap_forest * N) :
      heap_forest * N + option (N * positive * t) :=
    let '(h, total) := s in
    match heap_remove_min h with
    | None => inr None
    | Some ((p, k), rest) =>
      match PTrieCode.get k m with
      | Some current =>
        if N.eqb p current then
          inr (Some (p, k, Queue rest (PTrieCode.remove k m) (N.pred n) (N.pred total)))
        else inl (rest, N.pred total)
      | None => inl (rest, N.pred total)
      end
    end.
  Definition pop (q : t) : option (N * positive * t) :=
    match loopN (pop_step (live q) (live_count q)) (N.pos (heap_fuel (pending q)))
      (pending q, pending_count q) with
    | inl _ => None
    | inr result => result
    end.
End HeapCode.
