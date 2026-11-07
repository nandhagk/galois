(** * Trie VM gate

    Pure and costed tries run identical insertion and lookup workloads.
    For example, setting key thirteen makes its lookup return the stored value.
    Builds on: CostMonad and CostList. *)

From Stdlib Require Import NArith PArith List.
From Galois.Cost Require Import CostMonad CostList.
Import Cost.Notations List.ListNotations.

Inductive trie (A : Type) : Type :=
  | Empty
  | Node (left : trie A) (entry : option A) (right : trie A).

Arguments Empty {A}.
Arguments Node {A} left entry right.

Definition left {A} (t : trie A) : trie A :=
  match t with Empty => Empty | Node l _ _ => l end.

Definition entry {A} (t : trie A) : option A :=
  match t with Empty => None | Node _ v _ => v end.

Definition right {A} (t : trie A) : trie A :=
  match t with Empty => Empty | Node _ _ r => r end.

Fixpoint get_pure {A} (p : positive) (t : trie A) : option A :=
  match p with
  | xH => entry t
  | xO q => get_pure q (left t)
  | xI q => get_pure q (right t)
  end.

Fixpoint set_pure {A} (p : positive) (v : A) (t : trie A) : trie A :=
  match p with
  | xH => Node (left t) (Some v) (right t)
  | xO q => Node (set_pure q v (left t)) (entry t) (right t)
  | xI q => Node (left t) (entry t) (set_pure q v (right t))
  end.

Fixpoint get_c {A} (p : positive) (t : trie A) : Cost.t (option A) :=
  Cost.step ;;
  match p with
  | xH => Cost.ret (entry t)
  | xO q => get_c q (left t)
  | xI q => get_c q (right t)
  end.

Fixpoint set_c {A} (p : positive) (v : A) (t : trie A) : Cost.t (trie A) :=
  Cost.step ;;
  match p with
  | xH => Cost.ret (Node (left t) (Some v) (right t))
  | xO q => Cost.map (fun l => Node l (entry t) (right t)) (set_c q v (left t))
  | xI q => Cost.map (fun r => Node (left t) (entry t) r) (set_c q v (right t))
  end.

(** Costed lookup returns the pure lookup's optional value at every key. *)
Theorem value_get_c {A} p (t : trie A) : Cost.value (get_c p t) = get_pure p t.
Proof.
  revert t. induction p as [p IH |p IH |]; intro t; cbn [get_c get_pure];
    autorewrite with galois_cost; apply IH || reflexivity.
Qed.

(** Costed insertion returns the same trie as pure insertion at every key. *)
Theorem value_set_c {A} p (v : A) (t : trie A) :
  Cost.value (set_c p v t) = set_pure p v t.
Proof.
  revert t. induction p as [p IH |p IH |]; intro t; cbn [set_c set_pure];
    autorewrite with galois_cost; rewrite ?IH; reflexivity.
Qed.

(** Lookup charges one tick per key bit, even on an empty trie. *)
Theorem ticks_get_c {A} p (t : trie A) :
  Cost.ticks (get_c p t) = N.pos (Pos.size p).
Proof.
  revert t. induction p as [p IH |p IH |]; intro t; cbn [get_c];
    autorewrite with galois_cost; rewrite ?IH; rewrite ?N.add_1_l; reflexivity.
Qed.

(** Insertion charges one tick per key bit, including a new leaf. *)
Theorem ticks_set_c {A} p (v : A) (t : trie A) :
  Cost.ticks (set_c p v t) = N.pos (Pos.size p).
Proof.
  revert t. induction p as [p IH |p IH |]; intro t; cbn [set_c];
    autorewrite with galois_cost; rewrite ?IH; rewrite ?N.add_1_l; reflexivity.
Qed.

(** Binary successor avoids rebuilding each key from a unary index in the measurement harness. *)
Fixpoint keys_from (n : nat) (p : positive) : list positive :=
  match n with
  | O => []
  | S n' => p :: keys_from n' (Pos.succ p)
  end.

Definition keys (n : nat) : list positive := keys_from n 1.

Definition build_pure (n : nat) : trie bool :=
  fold_left (fun t p => set_pure p true t) (keys n) Empty.

Definition build_c (n : nat) : Cost.t (trie bool) :=
  fold_left_c (fun t p => set_c p true t) (keys n) Empty.

Definition workload_pure (n : nat) : list (option bool) :=
  let t := build_pure n in List.map (fun p => get_pure p t) (keys n).

Definition workload_c (n : nat) : Cost.t (list (option bool)) :=
  let* t := build_c n in map_c (fun p => get_c p t) (keys n).

(** The costed builder agrees with the independent pure builder. *)
Theorem value_build_c n : Cost.value (build_c n) = build_pure n.
Proof.
  unfold build_c, build_pure. rewrite value_fold_left_c.
  assert (Hfold : forall l t,
    fold_left (fun t p => Cost.value (set_c p true t)) l t =
    fold_left (fun t p => set_pure p true t) l t).
  { intro l. induction l as [|p ps IH]; intro t; cbn [fold_left].
    - reflexivity.
    - rewrite value_set_c. apply IH. }
  apply Hfold.
Qed.

(** Both workloads return the same ordered lookup observations for every size. *)
Theorem value_workload_c n : Cost.value (workload_c n) = workload_pure n.
Proof.
  unfold workload_c, workload_pure.
  rewrite Cost.value_bind, value_build_c, value_map_c.
  apply List.map_ext. intro p. apply value_get_c.
Qed.

Example empty_trie :
  (Cost.value (get_c 1 (Empty : trie bool)), Cost.ticks (get_c 1 (Empty : trie bool))) =
    (None, 1%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example singleton_trie :
  (Cost.value (get_c 13 (Cost.value (set_c 13 true Empty))),
   Cost.ticks (set_c 13 true Empty), Cost.ticks (get_c 13 (Empty : trie bool))) =
    (Some true, 4%N, 4%N).
Proof.
  vm_compute. reflexivity.
Qed.

Example absent_key :
  Cost.value (get_c 2 (Cost.value (set_c 1 true Empty))) = None.
Proof.
  vm_compute. reflexivity.
Qed.

(** The gate uses this size in both fully checked examples and every repeated scratch run. *)
Definition gate_size : nat := 10 * 4000.

Example pure_workload :
  workload_pure gate_size = repeat (Some true) gate_size.
Proof.
  vm_compute. reflexivity.
Qed.

Example costed_workload :
  Cost.value (workload_c gate_size) = repeat (Some true) gate_size.
Proof.
  vm_compute. reflexivity.
Qed.
