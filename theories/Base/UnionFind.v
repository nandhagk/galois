(** * Union-find implementation

    Union by size maintains a forest and compresses paths during lookup.
    For example, union links the smaller class under the larger root.
    Builds on: trie code and Argent fuelled loops. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Argent Require Import Time Loop Std BigO.
From Galois.Base Require Import Trie UnionFindSig.
Import ListNotations.

Record uf : Type := UF { parents : PTrieCode.t positive; sizes : PTrieCode.t N; count : N }.

TimeFun parents.
TimeFun sizes.
TimeFun count.

Module UnionFindCode <: UNION_FIND_OPS.
  Definition t := uf.
  Definition empty : t := UF PTrieCode.empty PTrieCode.empty 0.
  Definition parent_of (x : positive) (u : t) : positive :=
    match PTrieCode.get x (parents u) with Some p => p | None => x end.
  TimeFun parent_of.
  Definition size_at (r : positive) (u : t) : N :=
    match PTrieCode.get r (sizes u) with Some n => n | None => 1%N end.
  Definition add (x : positive) (u : t) : t :=
    match PTrieCode.get x (parents u) with
    | Some _ => u
    | None => UF (PTrieCode.set x x (parents u)) (PTrieCode.set x 1%N (sizes u)) (N.succ (count u))
    end.
  Definition walk_step (u : t) (s : positive * list positive)
      : positive * list positive + positive * list positive :=
    let p := parent_of (fst s) u in
    if Pos.eqb p (fst s) then inr s else inl (p, fst s :: snd s).
  TimeFun walk_step.
  Definition walk (x : positive) (u : t) : positive * list positive :=
    match loop_fuel (walk_step u) (S (N.size_nat (count u))) (x, []) with inl s => s | inr s => s end.
  TimeFun walk.
  Definition compress (root : positive) (path : list positive) (u : t) : t :=
    UF (fold_left (fun m y => PTrieCode.set y root m) path (parents u)) (sizes u) (count u).
  TimeFun compress.
  Definition find (x : positive) (u : t) : positive * t :=
    let r := walk x u in (fst r, compress (fst r) (snd r) u).
  TimeFun find.
  Definition link (w l : positive) (u : t) : t :=
    UF (PTrieCode.set l w (parents u)) (PTrieCode.set w (size_at w u + size_at l u)%N (sizes u)) (count u).
  Definition union (x y : positive) (u : t) : option (positive * positive) * t :=
    let fx := find x (add y (add x u)) in
    let fy := find y (snd fx) in
    let rx := fst fx in
    let ry := fst fy in
    let u2 := snd fy in
    if Pos.eqb rx ry then (None, u2)
    else if N.leb (size_at ry u2) (size_at rx u2) then (Some (rx, ry), link rx ry u2)
    else (Some (ry, rx), link ry rx u2).
End UnionFindCode.
Module UnionFind <: UNION_FIND.
  Include UnionFindCode.
  Definition support (u : t) : list positive := map fst (PTrieCode.elements (parents u)).
  Definition mem (u : t) (x : positive) : Prop := PTrieCode.get x (parents u) <> None.
  Definition card (u : t) : nat := N.to_nat (count u).
  Definition repr (u : t) (x : positive) : positive := Nat.iter (card u) (fun y => parent_of y u) x.
  Definition size_of (u : t) (x : positive) : nat :=
    length (filter (fun y => Pos.eqb (repr u y) (repr u x)) (support u)).
  Definition width (u : t) : nat := fold_right (fun y w => Nat.max (Pos.size_nat y) w) 0 (support u).
  Definition is_root (u : t) (x : positive) : Prop := parent_of x u = x.
  Definition ranked (u : t) (rk : positive -> nat) : Prop :=
    (forall x, mem u x -> ~ is_root u x -> rk x < rk (parent_of x u)) /\
    (forall r, mem u r -> is_root u r -> 2 ^ rk r <= size_of u r).
  Definition wf (u : t) : Prop :=
    card u = length (support u) /\
    (forall x p, PTrieCode.get x (parents u) = Some p -> mem u p) /\
    (forall r, mem u r -> is_root u r -> N.to_nat (size_at r u) = size_of u r) /\
    exists rk, ranked u rk.
  Lemma wf_empty : wf empty. Proof. Admitted.
  Lemma wf_add   : forall x u, wf u -> wf (add x u). Proof. Admitted.
  Lemma wf_find  : forall x u, wf u -> wf (snd (find x u)). Proof. Admitted.
  Lemma wf_union : forall x y u, wf u -> wf (snd (union x y u)). Proof. Admitted.
  Lemma mem_add   : forall x u y, wf u -> (mem (add x u) y <-> mem u y \/ y = x). Proof. Admitted.
  Lemma mem_find  : forall x u y, wf u -> (mem (snd (find x u)) y <-> mem u y). Proof. Admitted.
  Lemma mem_union : forall x y u z, wf u -> (mem (snd (union x y u)) z <-> mem u z \/ z = x \/ z = y).
  Proof. Admitted.
  Lemma repr_empty : forall x, repr empty x = x. Proof. reflexivity. Qed.
  Lemma repr_idem  : forall u x, wf u -> repr u (repr u x) = repr u x. Proof. Admitted.
  Lemma repr_add   : forall x u y, wf u -> repr (add x u) y = repr u y. Proof. Admitted.
  Lemma find_repr  : forall x u, wf u -> fst (find x u) = repr u x. Proof. Admitted.
  Lemma find_same  : forall x u y, wf u -> repr (snd (find x u)) y = repr u y. Proof. Admitted.
  Lemma union_none : forall x y u u1, wf u -> union x y u = (None, u1) ->
    repr u x = repr u y /\ forall z, repr u1 z = repr u z. Proof. Admitted.
  Lemma union_some : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    repr u x <> repr u y /\
    ((w = repr u x /\ l = repr u y) \/ (w = repr u y /\ l = repr u x)) /\
    forall z, repr u1 z = if Pos.eqb (repr u z) l then w else repr u z. Proof. Admitted.
  Lemma union_by_size : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u l <= size_of u w. Proof. Admitted.
  Lemma size_of_union : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u1 w = size_of u w + size_of u l. Proof. Admitted.
  Lemma size_of_le_card : forall u x, wf u -> mem u x -> size_of u x <= card u. Proof. Admitted.
  Lemma card_empty : card empty = 0. Proof. reflexivity. Qed.
  Lemma card_add   : forall x u, wf u -> card (add x u) <= card u + 1. Proof. Admitted.
  Lemma card_find  : forall x u, wf u -> card (snd (find x u)) = card u. Proof. reflexivity. Qed.
  Lemma card_union : forall x y u, wf u -> card (snd (union x y u)) <= card u + 2. Proof. Admitted.
  Lemma width_mem  : forall u x, wf u -> mem u x -> Pos.size_nat x <= width u. Proof. Admitted.
End UnionFind.

Module UnionFindT <: UNION_FIND_ALL.
  Include UnionFind.

  TimeFun add.
  TimeFun size_at.
  TimeFun link.
  TimeFun union.

  Definition c_uf : N := 1. (* STUB *)

  Definition k_get : N := 1. (* STUB *)
  Definition k_step : N := 1. (* STUB *)
  Definition k_walk : N := 1. (* STUB *)
  Definition k_comp : N := 1. (* STUB *)
  Definition k_link : N := 1. (* STUB *)

  Lemma T_add_le : forall x u, (wf u ->
    T_add x u <= c_uf * N.of_nat (Pos.size_nat x + Nat.log2 (card u) + 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_find_le : forall x u, (wf u ->
    T_find x u <= c_uf * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_union_le : forall x y u, (wf u ->
    T_union x y u <= c_uf * N.of_nat (Nat.log2 (card u + 2) + 1) *
      N.of_nat (Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma find_bigO : bigO (fun xu : positive * t => wf (snd xu))
    (fun xu => N.of_nat ((Nat.log2 (card (snd xu)) + 1) *
      (Nat.max (width (snd xu)) (Pos.size_nat (fst xu)) + 1)))
    (fun xu => T_find (fst xu) (snd xu)).
  Proof. Admitted. (* STUB *)

  Lemma F1_ranked : forall u, wf u -> exists rk, ranked u rk.
  Proof. Admitted. (* STUB *)
  Lemma F2_rank_log : forall u rk x, wf u -> ranked u rk -> mem u x ->
    rk x <= Nat.log2 (card u).
  Proof. Admitted. (* STUB *)
  Lemma F3_walk_root : forall x u, wf u -> fst (walk x u) = repr u x.
  Proof. Admitted. (* STUB *)
  Lemma F4_walk_path : forall x u, wf u -> mem u x ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x.
  Proof. Admitted. (* STUB *)
  Lemma F5_compress : forall u rk r path, wf u -> ranked u rk -> is_root u r ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) ->
    ranked (compress r path u) rk.
  Proof. Admitted. (* STUB *)
  Lemma F6_link : forall u rk w l, wf u -> ranked u rk ->
    is_root u w -> is_root u l -> w <> l -> size_of u l <= size_of u w ->
    ranked (link w l u)
      (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  Proof. Admitted. (* STUB *)

  Lemma T1_parent_of : forall x u,
    (T_parent_of x u <= k_get * N.of_nat (Pos.size_nat x + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_walk_step : forall u s, (wf u -> mem u (fst s) ->
    T_walk_step u s <= k_step * N.of_nat (width u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_walk : forall x u, (wf u ->
    T_walk x u <= k_walk * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_compress : forall r path u, (wf u -> (forall y, In y path -> mem u y) ->
    T_compress r path u <= k_comp * N.of_nat (length path + 1) *
      N.of_nat (width u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T5_link : forall w l u, (wf u -> mem u w -> mem u l ->
    T_link w l u <= k_link * N.of_nat (width u + Nat.log2 (card u) + 2))%N.
  Proof. Admitted. (* STUB *)
End UnionFindT.
