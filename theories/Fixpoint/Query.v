(** * Queries with explicit frames

    Queries return a value, read a key through a frame, or emit a side contribution.
    For example, [Side x a (Ret b)] returns [b] and the contribution [(x, a)].
    Builds on: Argent.Loop, Base.Trie and Base.MapSig. *)

From Stdlib Require Import List Bool PArith.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import MapSig Trie.

Inductive query (K A F : Type) : Type :=
  | Ret (a : A)
  | Ask (x : K) (f : F)
  | Side (x : K) (a : A) (q : query K A F).

Arguments Ret {K A F} a.
Arguments Ask {K A F} x f.
Arguments Side {K A F} x a q.

Fixpoint peel {K A F} (q : query K A F) (acc : list (K * A))
    : (A + K * F) * list (K * A) :=
  match q with
  | Ret a => (inl a, acc)
  | Ask x f => (inr (x, f), acc)
  | Side x a rest => peel rest ((x, a) :: acc)
  end.
TimeFun peel.

Definition eval_step {K A F} (resume : F -> A -> query K A F) (look : K -> A)
    (s : query K A F * list (K * A))
    : query K A F * list (K * A) + A * list (K * A) :=
  match peel (fst s) (snd s) with
  | (inl a, acc) => inr (a, rev_append acc nil)
  | (inr (x, f), acc) => inl (resume f (look x), acc)
  end.
TimeFun eval_step.

Definition eval_query {K A F} (resume : F -> A -> query K A F) (look : K -> A)
    (fuel : nat) (q : query K A F) : option (A * list (K * A)) :=
  match loop_fuel (eval_step resume look) fuel (q, nil) with
  | inr out => Some out
  | inl _ => None
  end.
TimeFun eval_query.

(** A row is accepted when its primary value and every side contribution fit the lookup. *)
Definition row_ok {K A} (leb : A -> A -> bool) (look : K -> A) (x : K)
    (out : option (A * list (K * A))) : bool :=
  match out with
  | None => false
  | Some (a, ss) =>
    leb a (look x) && forallb (fun xa => leb (snd xa) (look (fst xa))) ss
  end.
TimeFun row_ok.

Definition look_or {K A} (code : K -> positive) (d : A) (m : kmap K A) (x : K) : A :=
  match trie_get (code x) m with
  | Some (_, a) => a
  | None => d
  end.
TimeFun look_or.

(** Output comparison retains the keys and occurrence order of side contributions. *)
Definition out_leb {K A} (leb : A -> A -> bool)
    (left right : option (A * list (K * A))) : Prop :=
  match left, right with
  | Some (a, ss), Some (b, ts) =>
    leb a b = true /\
    Forall2 (fun xa yb => fst xa = fst yb /\ leb (snd xa) (snd yb) = true) ss ts
  | _, _ => False
  end.
