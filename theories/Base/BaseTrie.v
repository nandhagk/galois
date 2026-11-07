(** * Canonical costed binary tries

    Seven nonempty node shapes give every finite positive-key map one representation.
    For example, setting key thirteen descends four bits, even in an empty trie.
    Builds on: CostMonad and Stdlib binary integers. *)

From Stdlib Require Import NArith List Bool Lia.
From Galois.Cost Require Import CostMonad.
Import List.ListNotations Cost.Notations.

Module Trie.

(** A nonempty node records which of its three components are present. *)
Inductive ne (A : Type) : Type :=
  | N001 (r : ne A)
  | N010 (v : A)
  | N011 (v : A) (r : ne A)
  | N100 (l : ne A)
  | N101 (l r : ne A)
  | N110 (l : ne A) (v : A)
  | N111 (l : ne A) (v : A) (r : ne A).

Arguments N001 {A}.
Arguments N010 {A}.
Arguments N011 {A}.
Arguments N100 {A}.
Arguments N101 {A}.
Arguments N110 {A}.
Arguments N111 {A}.

(** The empty trie has a unique constructor and cannot contain empty internal nodes. *)
Inductive t (A : Type) : Type :=
  | Empty
  | Nodes (n : ne A).

Arguments Empty {A}.
Arguments Nodes {A}.

Definition empty {A} : t A := Empty.

Definition is_empty {A} (tr : t A) : bool :=
  match tr with
  | Empty => true
  | Nodes _ => false
  end.

Definition left {A} (tr : t A) : t A :=
  match tr with
  | Nodes (N100 l) | Nodes (N101 l _) | Nodes (N110 l _) | Nodes (N111 l _ _) =>
    Nodes l
  | _ => Empty
  end.

Definition value {A} (tr : t A) : option A :=
  match tr with
  | Nodes (N010 v) | Nodes (N011 v _) | Nodes (N110 _ v) | Nodes (N111 _ v _) =>
    Some v
  | _ => None
  end.

Definition right {A} (tr : t A) : t A :=
  match tr with
  | Nodes (N001 r) | Nodes (N011 _ r) | Nodes (N101 _ r) | Nodes (N111 _ _ r) =>
    Nodes r
  | _ => Empty
  end.

(** Smart construction collapses the all-absent case to the unique empty trie. *)
Definition node {A} (l : t A) (o : option A) (r : t A) : t A :=
  match l, o, r with
  | Empty, None, Empty => Empty
  | Empty, None, Nodes r => Nodes (N001 r)
  | Empty, Some v, Empty => Nodes (N010 v)
  | Empty, Some v, Nodes r => Nodes (N011 v r)
  | Nodes l, None, Empty => Nodes (N100 l)
  | Nodes l, None, Nodes r => Nodes (N101 l r)
  | Nodes l, Some v, Empty => Nodes (N110 l v)
  | Nodes l, Some v, Nodes r => Nodes (N111 l v r)
  end.

(** Smart construction retains its left component. *)
Theorem left_node {A} (l r : t A) o : left (node l o r) = l.
Proof.
  destruct l, o, r; reflexivity.
Qed.

(** Smart construction retains its optional binding. *)
Theorem value_node {A} (l r : t A) o : value (node l o r) = o.
Proof.
  destruct l, o, r; reflexivity.
Qed.

(** Smart construction retains its right component. *)
Theorem right_node {A} (l r : t A) o : right (node l o r) = r.
Proof.
  destruct l, o, r; reflexivity.
Qed.

(** Rebuilding a trie from its components returns the same canonical value. *)
Theorem node_eta {A} (tr : t A) : node (left tr) (value tr) (right tr) = tr.
Proof.
  destruct tr as [|n]; [reflexivity|destruct n; reflexivity].
Qed.

(** Node induction hides the seven concrete shapes from semantic proofs. *)
Theorem node_ind {A} (P : t A -> Prop) :
  P Empty -> (forall l o r, P l -> P r -> P (node l o r)) -> forall tr, P tr.
Proof.
  intros Hempty Hnode [|n]; [exact Hempty|].
  induction n as [r IHr|v|v r IHr|l IHl|l IHl r IHr|l IHl v|l IHl v r IHr].
  - exact (Hnode Empty None (Nodes r) Hempty IHr).
  - exact (Hnode Empty (Some v) Empty Hempty Hempty).
  - exact (Hnode Empty (Some v) (Nodes r) Hempty IHr).
  - exact (Hnode (Nodes l) None Empty IHl Hempty).
  - exact (Hnode (Nodes l) None (Nodes r) IHl IHr).
  - exact (Hnode (Nodes l) (Some v) Empty IHl Hempty).
  - exact (Hnode (Nodes l) (Some v) (Nodes r) IHl IHr).
Qed.

(** Lookup charges every key bit, including bits below an absent subtree. *)
Fixpoint get_c {A} (p : positive) (tr : t A) : Cost.t (option A) :=
  Cost.step ;;
  match p with
  | xH => Cost.ret (value tr)
  | xO q => get_c q (left tr)
  | xI q => get_c q (right tr)
  end.

Definition get {A} p (tr : t A) := Cost.value (get_c p tr).

(** Lookup exposes one digit of its least-significant-bit-first descent. *)
Theorem get_equation {A} p (tr : t A) :
  get p tr =
  match p with
  | xH => value tr
  | xO q => get q (left tr)
  | xI q => get q (right tr)
  end.
Proof.
  destruct p; reflexivity.
Qed.

(** Empty tries bind no key. *)
Theorem get_empty {A} (p : positive) : get p (@empty A) = None.
Proof.
  induction p; rewrite get_equation; cbn [left right value empty];
    assumption || reflexivity.
Qed.

(** Lookup through smart construction selects the corresponding component. *)
Theorem get_node {A} (p : positive) (l r : t A) o :
  get p (node l o r) =
  match p with
  | xH => o
  | xO q => get q l
  | xI q => get q r
  end.
Proof.
  destruct p; rewrite get_equation, ?left_node, ?right_node, ?value_node; reflexivity.
Qed.

(** A trie is empty precisely when its outer emptiness test succeeds. *)
Theorem is_empty_spec {A} (tr : t A) : is_empty tr = true <-> tr = empty.
Proof.
  destruct tr; split; intro H; try reflexivity; discriminate H.
Qed.

Local Lemma all_absent_empty {A} (tr : t A) :
  (forall p, get p tr = None) -> tr = Empty.
Proof.
  induction tr as [|l o r IHl IHr] using node_ind; intro Hnone.
  - reflexivity.
  - assert (Hl : l = Empty).
    { apply IHl. intro p. specialize (Hnone (xO p)). now rewrite get_node in Hnone. }
    assert (Hr : r = Empty).
    { apply IHr. intro p. specialize (Hnone (xI p)). now rewrite get_node in Hnone. }
    specialize (Hnone xH). rewrite get_node in Hnone.
    rewrite Hl, Hr, Hnone. reflexivity.
Qed.

(** Equal lookup observations identify equal canonical tries. *)
Theorem extensionality {A} (t1 t2 : t A) :
  (forall p, get p t1 = get p t2) -> t1 = t2.
Proof.
  revert t2.
  induction t1 as [|l o r IHl IHr] using node_ind; intros t2 Hagree.
  - symmetry. apply all_absent_empty. intro p. rewrite <- Hagree. apply get_empty.
  - assert (Hl : l = left t2).
    { apply IHl. intro p. specialize (Hagree (xO p)).
      rewrite get_node, (get_equation (xO p) t2) in Hagree. exact Hagree. }
    assert (Hr : r = right t2).
    { apply IHr. intro p. specialize (Hagree (xI p)).
      rewrite get_node, (get_equation (xI p) t2) in Hagree. exact Hagree. }
    specialize (Hagree xH). rewrite get_node, get_equation in Hagree.
    rewrite Hl, Hr, Hagree. apply node_eta.
Qed.

(** Replacement charges one recursive step per key bit and collapses empty paths. *)
Fixpoint replace_c {A} (p : positive) (o : option A) (tr : t A) : Cost.t (t A) :=
  Cost.step ;;
  match p with
  | xH => Cost.ret (node (left tr) o (right tr))
  | xO q =>
    Cost.map (fun l => node l (value tr) (right tr)) (replace_c q o (left tr))
  | xI q =>
    Cost.map (fun r => node (left tr) (value tr) r) (replace_c q o (right tr))
  end.

Definition replace {A} p o (tr : t A) := Cost.value (replace_c p o tr).
Definition set_c {A} p (v : A) tr := replace_c p (Some v) tr.
Definition set {A} p (v : A) tr := Cost.value (set_c p v tr).
Definition remove_c {A} p (tr : t A) := replace_c p None tr.
Definition remove {A} p (tr : t A) := Cost.value (remove_c p tr).

(** Replacement exposes its one-path recursion. *)
Theorem replace_equation {A} p o (tr : t A) :
  replace p o tr =
  match p with
  | xH => node (left tr) o (right tr)
  | xO q => node (replace q o (left tr)) (value tr) (right tr)
  | xI q => node (left tr) (value tr) (replace q o (right tr))
  end.
Proof.
  destruct p; reflexivity.
Qed.

(** Insertion follows the selected path and retains both other components. *)
Theorem set_equation {A} p (v : A) tr :
  set p v tr =
  match p with
  | xH => node (left tr) (Some v) (right tr)
  | xO q => node (set q v (left tr)) (value tr) (right tr)
  | xI q => node (left tr) (value tr) (set q v (right tr))
  end.
Proof.
  apply replace_equation.
Qed.

(** Removal follows the selected path and smart construction collapses it. *)
Theorem remove_equation {A} p (tr : t A) :
  remove p tr =
  match p with
  | xH => node (left tr) None (right tr)
  | xO q => node (remove q (left tr)) (value tr) (right tr)
  | xI q => node (left tr) (value tr) (remove q (right tr))
  end.
Proof.
  apply replace_equation.
Qed.

(** Replacement writes the selected optional binding. *)
Theorem get_replace_same {A} (tr : t A) p o : get p (replace p o tr) = o.
Proof.
  revert tr. induction p; intro tr; rewrite replace_equation, get_node; auto.
Qed.

(** Replacement leaves lookup at every other key unchanged. *)
Theorem get_replace_other {A} (tr : t A) p q o :
  p <> q -> get q (replace p o tr) = get q tr.
Proof.
  revert tr q. induction p; intros tr q Hneq; destruct q;
    rewrite replace_equation, get_node, (get_equation _ tr);
    try reflexivity; try congruence; apply IHp; congruence.
Qed.

(** Lookup at the updated key returns its new value. *)
Theorem get_set_same {A} (tr : t A) p v : get p (set p v tr) = Some v.
Proof.
  apply get_replace_same.
Qed.

(** Updating a distinct key preserves lookup. *)
Theorem get_set_other {A} (tr : t A) p q v :
  p <> q -> get q (set p v tr) = get q tr.
Proof.
  apply get_replace_other.
Qed.

(** Lookup at the removed key returns no value. *)
Theorem get_remove_same {A} (tr : t A) p : get p (remove p tr) = None.
Proof.
  apply get_replace_same.
Qed.

(** Removing a distinct key preserves lookup. *)
Theorem get_remove_other {A} (tr : t A) p q :
  p <> q -> get q (remove p tr) = get q tr.
Proof.
  apply get_replace_other.
Qed.

(** Update retains the callback's entire charge and one invocation-overhead tick. *)
Definition update_c {A} p (f_c : option A -> Cost.t (option A)) (tr : t A) :=
  let* old := get_c p tr in
  Cost.step ;;
  let* new := f_c old in replace_c p new tr.

Definition update {A} p (f : option A -> option A) tr :=
  Cost.value (update_c p (Cost.lift (fun _ => 1%N) f) tr).

(** Updating applies the callback to the old lookup before replacing that binding. *)
Theorem update_equation {A} p (f : option A -> option A) tr :
  update p f tr = replace p (f (get p tr)) tr.
Proof.
  reflexivity.
Qed.

(** Lookup charges the complete binary key width on every input trie. *)
Theorem get_cost {A} p (tr : t A) :
  Cost.ticks (get_c p tr) = N.pos (Pos.size p).
Proof.
  revert tr. induction p; intro tr; cbn [get_c];
    autorewrite with galois_cost; rewrite ?IHp, ?N.add_1_l; reflexivity.
Qed.

(** Replacement charges the complete binary key width even on empty paths. *)
Theorem replace_cost {A} p o (tr : t A) :
  Cost.ticks (replace_c p o tr) = N.pos (Pos.size p).
Proof.
  revert tr. induction p; intro tr; cbn [replace_c];
    autorewrite with galois_cost; rewrite ?IHp, ?N.add_1_l; reflexivity.
Qed.

(** Insertion charges one tick per key bit. *)
Theorem set_cost {A} p (v : A) tr :
  Cost.ticks (set_c p v tr) = N.pos (Pos.size p).
Proof.
  apply replace_cost.
Qed.

(** Removal charges one tick per key bit without an inequality relaxation. *)
Theorem remove_cost {A} p (tr : t A) :
  Cost.ticks (remove_c p tr) = N.pos (Pos.size p).
Proof.
  apply replace_cost.
Qed.

(** Update charges two key traversals, invocation overhead and the reached callback. *)
Theorem update_cost {A} p (f_c : option A -> Cost.t (option A)) tr :
  Cost.ticks (update_c p f_c tr) =
    (2 * N.pos (Pos.size p) + 1 + Cost.ticks (f_c (get p tr)))%N.
Proof.
  unfold update_c. autorewrite with galois_cost.
  rewrite get_cost, replace_cost. fold (get p tr). lia.
Qed.

Arguments get_c {A} p tr : simpl never.
Arguments get {A} p tr : simpl never.
Arguments replace_c {A} p o tr : simpl never.
Arguments replace {A} p o tr : simpl never.
Arguments set_c {A} p v tr : simpl never.
Arguments set {A} p v tr : simpl never.
Arguments remove_c {A} p tr : simpl never.
Arguments remove {A} p tr : simpl never.
Arguments update_c {A} p f_c tr : simpl never.
Arguments update {A} p f tr : simpl never.

End Trie.
