(** * Costed binomial forests

    A forest has one optional tree at each rank and omits trailing empty positions.
    For example, inserting two singleton trees creates one tree at rank one.
    Builds on: CostMonad, CostList and the standard positive order. *)

From Stdlib Require Import List Bool NArith PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostList.
Import List.ListNotations Cost.Notations.

Local Open Scope nat_scope.

Module HeapBinomial.

(** Entries cache their priority, encoded key and original key. *)
Definition entry (K : Type) := (positive * positive * K)%type.

(** Priorities use numeric codes to break ties. *)
Definition precedes {K} (a b : entry K) : Prop :=
  (fst (fst a) < fst (fst b))%positive \/
  (fst (fst a) = fst (fst b) /\ (snd (fst a) <= snd (fst b))%positive).

(** Comparing cached codes charges their digit traversals on a priority tie. *)
Definition precedesb_c {K} (a b : entry K) : Cost.t bool :=
  Cost.step ;;
  if Pos.ltb (fst (fst a)) (fst (fst b)) then Cost.ret true
  else if Pos.eqb (fst (fst a)) (fst (fst b)) then
    Cost.tick_bits (snd (fst a)) ;;
    Cost.tick_bits (snd (fst b)) ;;
    Cost.ret (Pos.leb (snd (fst a)) (snd (fst b)))
  else Cost.ret false.

Definition precedesb {K} (a b : entry K) := Cost.value (precedesb_c a b).

(** The costed comparator reflects the lexicographic priority order. *)
Theorem precedesb_spec {K} (a b : entry K) :
  precedesb a b = true <-> precedes a b.
Proof.
  unfold precedesb, precedesb_c, precedes.
  autorewrite with galois_cost.
  destruct (Pos.ltb (fst (fst a)) (fst (fst b))) eqn:Hlt.
  - apply Pos.ltb_lt in Hlt. intuition.
  - apply Pos.ltb_ge in Hlt.
    destruct (Pos.eqb (fst (fst a)) (fst (fst b))) eqn:Heq.
    + apply Pos.eqb_eq in Heq. autorewrite with galois_cost.
      rewrite Pos.leb_le. intuition lia.
    + apply Pos.eqb_neq in Heq. cbn. intuition lia.
Qed.

Lemma precedes_refl {K} (a : entry K) : precedes a a.
Proof.
  right. split; [reflexivity|apply Pos.le_refl].
Qed.

Lemma precedes_trans {K} (a b c : entry K) :
  precedes a b -> precedes b c -> precedes a c.
Proof.
  unfold precedes. intros [Hab|[Hab Hcab]] [Hbc|[Hbc Hcbc]];
    try (left; lia); right; split; lia.
Qed.

Lemma precedesb_false {K} (a b : entry K) :
  precedesb a b = false -> precedes b a.
Proof.
  intro Hfalse.
  assert (Hnot : ~ precedes a b) by (intro H; apply precedesb_spec in H; congruence).
  unfold precedes in *. destruct (Pos.eq_dec (fst (fst a)) (fst (fst b))); intuition lia.
Qed.

Scheme All for list.

(** A tree stores its children in decreasing rank order. *)
Inductive tree (K : Type) : Type :=
  | Tree (top : entry K) (children : list (tree K)).

Arguments Tree {K}.

Definition root {K} (t : tree K) : entry K :=
  match t with
  | Tree e _ => e
  end.

Fixpoint tree_entries {K} (t : tree K) : list (entry K) :=
  match t with
  | Tree e cs => e :: flat_map tree_entries cs
  end.

Definition tree_all {K} (P : entry K -> Prop) (t : tree K) : Prop :=
  forall e, In e (tree_entries t) -> P e.

(** Linking uses one comparison and shares both child lists. *)
Definition link_c {K} (a b : tree K) : Cost.t (tree K) :=
  match a, b with
  | Tree e cs, Tree e' cs' =>
    let* yes := precedesb_c e e' in
    Cost.ret (if yes then Tree e (b :: cs) else Tree e' (a :: cs'))
  end.

Definition link {K} (a b : tree K) := Cost.value (link_c a b).

(** Linking retains the smaller root. *)
Theorem link_equation {K} (e e' : entry K) cs cs' :
  link (Tree e cs) (Tree e' cs') =
    if precedesb e e' then Tree e (Tree e' cs' :: cs) else Tree e' (Tree e cs :: cs').
Proof.
  reflexivity.
Qed.

(** Valid trees have a proof-indexed rank, ordered roots and entry property [P]. *)
Inductive valid {K} (P : entry K -> Prop) : nat -> tree K -> Prop :=
  | Valid_zero e : P e -> valid P 0 (Tree e [])
  | Valid_link r e cs b :
      valid P r (Tree e cs) ->
      valid P r b ->
      tree_all (precedes e) b ->
      valid P (S r) (Tree e (b :: cs)).

Definition heap (K : Type) := list (option (tree K)).

Definition slot_entries {K} (s : option (tree K)) : list (entry K) :=
  match s with
  | None => []
  | Some t => tree_entries t
  end.

Fixpoint entries {K} (h : heap K) : list (entry K) :=
  match h with
  | [] => []
  | s :: hs => slot_entries s ++ entries hs
  end.

Definition heap_count {K} (h : heap K) := length (entries h).

(** Position [r] contains a rank-[r] tree and the last position is occupied. *)
Fixpoint forest_valid {K} (P : entry K -> Prop) r (h : heap K) : Prop :=
  match h with
  | [] => True
  | s :: hs =>
    (match s with None => True | Some t => valid P r t end) /\
    forest_valid P (S r) hs /\ (s <> None \/ hs <> [])
  end.

Definition digit {K} (s : option (tree K)) (hs : heap K) : heap K :=
  match s, hs with
  | None, [] => []
  | _, _ => s :: hs
  end.

(** Insertion propagates a carry through occupied rank positions. *)
Fixpoint insert_c {K} (t : tree K) (h : heap K) : Cost.t (heap K) :=
  Cost.step ;;
  match h with
  | [] => Cost.ret [Some t]
  | None :: hs => Cost.ret (Some t :: hs)
  | Some u :: hs =>
    let* carry := link_c t u in
    let* rest := insert_c carry hs in Cost.ret (None :: rest)
  end.

Definition insert {K} (t : tree K) h := Cost.value (insert_c t h).

(** Insertion performs binary carrying without inspecting tree contents. *)
Theorem insert_equation {K} (t : tree K) h :
  insert t h =
  match h with
  | [] => [Some t]
  | None :: hs => Some t :: hs
  | Some u :: hs => None :: insert (link t u) hs
  end.
Proof.
  destruct h as [|[u|] hs]; unfold insert at 1; cbn [insert_c];
    autorewrite with galois_cost; reflexivity.
Qed.

(** Full-adder melding processes each rank position once. *)
Fixpoint meld_c {K} (a : heap K) : heap K -> option (tree K) -> Cost.t (heap K) :=
  match a with
  | [] => fun b carry =>
    Cost.step ;;
    match carry with
    | None => Cost.ret b
    | Some t => insert_c t b
    end
  | x :: xs => fun b carry =>
    Cost.step ;;
    match b with
    | [] =>
      match carry with
      | None => Cost.ret a
      | Some t => insert_c t a
      end
    | y :: ys =>
      match x, y, carry with
      | None, None, c =>
        let* rest := meld_c xs ys None in Cost.ret (digit c rest)
      | Some t, None, None | None, Some t, None =>
        let* rest := meld_c xs ys None in Cost.ret (digit (Some t) rest)
      | Some t, Some u, None
      | Some t, None, Some u
      | None, Some t, Some u =>
        let* carry' := link_c t u in
        let* rest := meld_c xs ys (Some carry') in Cost.ret (digit None rest)
      | Some t, Some u, Some c =>
        let* carry' := link_c t u in
        let* rest := meld_c xs ys (Some carry') in Cost.ret (digit (Some c) rest)
      end
    end
  end.

Definition meld {K} (a b : heap K) c := Cost.value (meld_c a b c).
Definition merge {K} (a b : heap K) := meld a b None.

(** Melding follows a binary full adder and trims trailing empty positions. *)
Theorem meld_equation {K} (a b : heap K) carry :
  meld a b carry =
  match a, b with
  | [], _ => match carry with None => b | Some t => insert t b end
  | _, [] => match carry with None => a | Some t => insert t a end
  | x :: xs, y :: ys =>
    match x, y, carry with
    | None, None, c => digit c (meld xs ys None)
    | Some t, None, None | None, Some t, None => digit (Some t) (meld xs ys None)
    | Some t, Some u, None
    | Some t, None, Some u
    | None, Some t, Some u => digit None (meld xs ys (Some (link t u)))
    | Some t, Some u, Some c => digit (Some c) (meld xs ys (Some (link t u)))
    end
  end.
Proof.
  destruct a as [|[x|] xs], b as [|[y|] ys], carry as [c|];
    unfold meld at 1; cbn [meld_c]; autorewrite with galois_cost; reflexivity.
Qed.

(** Selection scans the roots and retains the winning tree and remaining forest. *)
Fixpoint select_c {K} (h : heap K) : Cost.t (option (tree K * heap K)) :=
  match h with
  | [] => Cost.ret None
  | x :: xs =>
    Cost.step ;;
    let* tail := select_c xs in
    match tail with
    | None =>
      Cost.ret (match x with None => None | Some t => Some (t, []) end)
    | Some (t, rest) =>
      match x with
      | None => Cost.ret (Some (t, digit None rest))
      | Some u =>
        let* yes := precedesb_c (root u) (root t) in
        Cost.ret (if yes then Some (u, digit None xs) else Some (t, digit (Some u) rest))
      end
    end
  end.

Definition select {K} (h : heap K) := Cost.value (select_c h).

(** Selection compares each occupied root with the selected suffix root. *)
Theorem select_equation {K} (h : heap K) :
  select h =
  match h with
  | [] => None
  | x :: xs =>
    match select xs with
    | None => match x with None => None | Some t => Some (t, []) end
    | Some (t, rest) =>
      match x with
      | None => Some (t, digit None rest)
      | Some u =>
        if precedesb (root u) (root t) then Some (u, digit None xs)
        else Some (t, digit (Some u) rest)
      end
    end
  end.
Proof.
  destruct h as [|x xs]; [reflexivity|].
  unfold select at 1. cbn [select_c]. autorewrite with galois_cost.
  fold (select xs). destruct (select xs) as [[t rest]|], x;
    autorewrite with galois_cost; reflexivity.
Qed.

(** Reversing the children places each child at its ascending rank position. *)
Definition children_heap_c {K} (t : tree K) : Cost.t (heap K) :=
  match t with
  | Tree _ cs =>
    let* ascending := rev_c cs in map_c (fun t => Cost.ret (Some t)) ascending
  end.

Definition children_heap {K} (t : tree K) := Cost.value (children_heap_c t).

(** Child enumeration reverses the descending child list. *)
Theorem children_heap_equation {K} (e : entry K) cs :
  children_heap (Tree e cs) = List.map (@Some (tree K)) (rev cs).
Proof.
  unfold children_heap, children_heap_c. rewrite Cost.value_bind, value_map_c, value_rev_c.
  reflexivity.
Qed.

(** Removing the selected root melds its children with the unselected trees. *)
Definition remove_min_c {K} (h : heap K) : Cost.t (option (entry K * heap K)) :=
  let* selected := select_c h in
  match selected with
  | None => Cost.ret None
  | Some (t, rest) =>
    let* children := children_heap_c t in
    let* result := meld_c children rest None in Cost.ret (Some (root t, result))
  end.

Definition remove_min {K} (h : heap K) := Cost.value (remove_min_c h).

(** Minimum removal shares unvisited trees and returns the selected cached entry. *)
Theorem remove_min_equation {K} (h : heap K) :
  remove_min h =
  match select h with
  | None => None
  | Some (t, rest) => Some (root t, merge (children_heap t) rest)
  end.
Proof.
  unfold remove_min, remove_min_c. rewrite Cost.value_bind. fold (select h).
  destruct (select h) as [[t rest]|]; autorewrite with galois_cost; reflexivity.
Qed.

Lemma entries_digit {K} s (h : heap K) :
  entries (digit s h) = slot_entries s ++ entries h.
Proof.
  destruct s, h; reflexivity.
Qed.

Lemma valid_digit {K} P r s (h : heap K) :
  (match s with None => True | Some t => valid P r t end) ->
  forest_valid P (S r) h -> forest_valid P r (digit s h).
Proof.
  destruct s as [t|], h as [|x xs]; cbn; intros Hs Hh.
  - split; [exact Hs|]; split; [exact I|left; discriminate].
  - split; [exact Hs|]; split; [exact Hh|left; discriminate].
  - exact I.
  - split; [exact I|]; split; [exact Hh|right; discriminate].
Qed.

Lemma entries_link {K} (a b : tree K) e :
  In e (tree_entries (link a b)) <-> In e (tree_entries a) \/ In e (tree_entries b).
Proof.
  destruct a as [x xs], b as [y ys]. rewrite link_equation.
  destruct (precedesb x y); cbn; rewrite in_app_iff; intuition congruence.
Qed.

Lemma count_link {K} (a b : tree K) :
  length (tree_entries (link a b)) = length (tree_entries a) + length (tree_entries b).
Proof.
  destruct a as [x xs], b as [y ys]. rewrite link_equation.
  destruct (precedesb x y); cbn; rewrite length_app; cbn; lia.
Qed.

Lemma valid_root {K} P r (t : tree K) :
  valid P r t -> tree_all (precedes (root t)) t.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore];
    intros a Hin; cbn in *.
  - destruct Hin as [Heq|Hfalse]; [subst; apply precedes_refl|contradiction].
  - destruct Hin as [Heq|Hin]; [subst; apply precedes_refl|].
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + apply Hbefore; exact Hin.
    + apply IH; right; exact Hin.
Qed.

Lemma valid_all {K} P r (t : tree K) : valid P r t -> tree_all P t.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore];
    intros a Hin; cbn in Hin.
  - destruct Hin as [Heq|Hfalse]; [subst; exact He|contradiction].
  - destruct Hin as [Heq|Hin].
    + apply IH; left; exact Heq.
    + apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      * apply IHchild; exact Hin.
      * apply IH; right; exact Hin.
Qed.

(** Every forest entry satisfies the property carried by its ranked-tree certificates. *)
Theorem forest_all {K} P r (h : heap K) :
  forest_valid P r h -> forall e, In e (entries h) -> P e.
Proof.
  revert r. induction h as [|[t|] hs IH]; intros r Hvalid e Hin.
  - contradiction.
  - destruct Hvalid as [Ht [Hhs Hlast]]. cbn [entries slot_entries] in Hin.
    apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + exact (valid_all P r t Ht e Hin).
    + exact (IH (S r) Hhs e Hin).
  - destruct Hvalid as [_ [Hhs Hlast]]. exact (IH (S r) Hhs e Hin).
Qed.

Lemma valid_link {K} P r (a b : tree K) :
  valid P r a -> valid P r b -> valid P (S r) (link a b).
Proof.
  intros Ha Hb. destruct a as [e cs], b as [e' cs']. rewrite link_equation.
  destruct (precedesb e e') eqn:Hcmp; apply Valid_link; try assumption.
  - intros x Hin. eapply precedes_trans.
    + apply precedesb_spec; exact Hcmp.
    + apply (valid_root P r (Tree e' cs') Hb); exact Hin.
  - intros x Hin. eapply precedes_trans.
    + apply precedesb_false; exact Hcmp.
    + apply (valid_root P r (Tree e cs) Ha); exact Hin.
Qed.

Lemma entries_insert {K} (t : tree K) h e :
  In e (entries (insert t h)) <-> In e (tree_entries t) \/ In e (entries h).
Proof.
  revert t. induction h as [|[u|] hs IH]; intro t; rewrite insert_equation;
    cbn [entries slot_entries flat_map app length].
  - rewrite app_nil_r. cbn. tauto.
  - rewrite IH, entries_link. cbn [entries slot_entries]. rewrite in_app_iff. tauto.
  - rewrite in_app_iff. cbn. tauto.
Qed.

Lemma count_insert {K} (t : tree K) h :
  heap_count (insert t h) = length (tree_entries t) + heap_count h.
Proof.
  revert t. induction h as [|[u|] hs IH]; intro t; rewrite insert_equation.
  - unfold heap_count. cbn [entries slot_entries]. rewrite app_nil_r. cbn. lia.
  - change (heap_count (insert (link t u) hs) =
      length (tree_entries t) + length (tree_entries u ++ entries hs)).
    rewrite IH, count_link, length_app. unfold heap_count. lia.
  - unfold heap_count. cbn [entries slot_entries app]. rewrite length_app. reflexivity.
Qed.

Lemma valid_insert {K} P r (t : tree K) h :
  valid P r t -> forest_valid P r h -> forest_valid P r (insert t h).
Proof.
  revert r t. induction h as [|[u|] hs IH]; intros r t Ht Hh;
    rewrite insert_equation; cbn [forest_valid] in *.
  - split; [exact Ht|]; split; [exact I|left; discriminate].
  - destruct Hh as [Hu [Hhs Hlast]]. split; [exact I|]; split.
    + apply IH; [apply valid_link; assumption|exact Hhs].
    + right. destruct hs as [|[v|] hs]; rewrite insert_equation; discriminate.
  - destruct Hh as [_ [Hhs Hlast]].
    split; [exact Ht|]; split; [exact Hhs|left; discriminate].
Qed.

Lemma entries_meld {K} (a b : heap K) c e :
  In e (entries (meld a b c)) <->
    In e (entries a) \/ In e (entries b) \/ In e (slot_entries c).
Proof.
  revert b c. induction a as [|[x|] xs IH]; intros b c; rewrite meld_equation.
  - destruct c; cbn [slot_entries entries]; [rewrite entries_insert|]; cbn; tauto.
  - destruct b as [|[y|] ys].
    + destruct c; try rewrite entries_insert; cbn [slot_entries entries];
        rewrite ?in_app_iff; cbn; tauto.
    + destruct c; rewrite entries_digit; cbn [entries slot_entries];
        rewrite ?in_app_iff, IH; cbn [slot_entries]; rewrite ?entries_link; cbn; tauto.
    + destruct c; rewrite entries_digit; cbn [entries slot_entries];
        rewrite ?in_app_iff, IH; cbn [slot_entries]; rewrite ?entries_link; cbn; tauto.
  - destruct b as [|[y|] ys].
    + destruct c; try rewrite entries_insert; cbn [slot_entries entries]; cbn; tauto.
    + destruct c; rewrite entries_digit; cbn [entries slot_entries];
        rewrite ?in_app_iff, IH; cbn [slot_entries]; rewrite ?entries_link; cbn; tauto.
    + destruct c; rewrite entries_digit; cbn [entries slot_entries];
        rewrite ?in_app_iff, IH; cbn [slot_entries]; cbn; tauto.
Qed.

Lemma count_digit {K} s (h : heap K) :
  heap_count (digit s h) = length (slot_entries s) + heap_count h.
Proof.
  unfold heap_count. rewrite entries_digit, length_app. reflexivity.
Qed.

Lemma count_meld {K} (a b : heap K) c :
  heap_count (meld a b c) = heap_count a + heap_count b + length (slot_entries c).
Proof.
  revert b c. induction a as [|[x|] xs IH]; intros b c; rewrite meld_equation.
  - destruct c; cbn [slot_entries]; [rewrite count_insert|];
      unfold heap_count; cbn [entries length]; lia.
  - destruct b as [|[y|] ys].
    + destruct c; try rewrite count_insert;
        unfold heap_count; cbn [entries slot_entries length]; lia.
    + destruct c; rewrite count_digit, IH; cbn [slot_entries]; rewrite count_link;
        unfold heap_count; cbn [entries slot_entries]; rewrite !length_app; lia.
    + destruct c; rewrite count_digit, IH; cbn [slot_entries]; rewrite ?count_link;
        unfold heap_count; cbn [entries slot_entries app length]; rewrite !length_app; lia.
  - destruct b as [|[y|] ys].
    + destruct c; try rewrite count_insert;
        unfold heap_count; cbn [entries slot_entries app length]; lia.
    + destruct c; rewrite count_digit, IH; cbn [slot_entries]; rewrite ?count_link;
        unfold heap_count; cbn [entries slot_entries app length]; rewrite !length_app; lia.
    + destruct c; rewrite count_digit, IH;
        unfold heap_count; cbn [entries slot_entries app length]; lia.
Qed.

Lemma valid_meld {K} P (a b : heap K) c r :
  forest_valid P r a -> forest_valid P r b ->
  (match c with None => True | Some t => valid P r t end) ->
  forest_valid P r (meld a b c).
Proof.
  revert b c r. induction a as [|[x|] xs IH]; intros b c r Ha Hb Hc;
    rewrite meld_equation.
  - destruct c; [apply valid_insert|]; assumption.
  - destruct Ha as [Hx [Hxs Hlast]]. destruct b as [|[y|] ys].
    + destruct c; [apply valid_insert|]; cbn; auto.
    + destruct Hb as [Hy [Hys Hlast']].
      destruct c; apply valid_digit; auto; apply IH; auto; apply valid_link; assumption.
    + destruct Hb as [_ [Hys Hlast']].
      destruct c; apply valid_digit; auto; apply IH; auto; apply valid_link; assumption.
  - destruct Ha as [_ [Hxs Hlast]]. destruct b as [|[y|] ys].
    + destruct c; [apply valid_insert|]; cbn; auto.
    + destruct Hb as [Hy [Hys Hlast']].
      destruct c; apply valid_digit; auto; apply IH; auto; apply valid_link; assumption.
    + destruct Hb as [_ [Hys Hlast']].
      destruct c; apply valid_digit; auto; apply IH; auto.
Qed.

Lemma select_entries {K} (h : heap K) :
  match select h with
  | None => entries h = []
  | Some (t, rest) =>
    (forall e, In e (entries h) <-> In e (tree_entries t) \/ In e (entries rest)) /\
    heap_count h = length (tree_entries t) + heap_count rest
  end.
Proof.
  induction h as [|[u|] xs IH]; rewrite select_equation.
  - reflexivity.
  - destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Hin Hcount]. destruct (precedesb (root u) (root t)); split.
      * intro e. rewrite entries_digit. cbn [entries slot_entries app].
        rewrite in_app_iff. cbn. tauto.
      * unfold heap_count at 1. cbn [entries slot_entries]. rewrite length_app.
        unfold heap_count. rewrite entries_digit. cbn [slot_entries app]. reflexivity.
      * intro e. rewrite entries_digit. cbn [entries slot_entries].
        rewrite !in_app_iff, Hin. cbn. tauto.
      * rewrite count_digit. unfold heap_count in *.
        cbn [entries slot_entries]. rewrite !length_app. lia.
    + split.
      * intro e. cbn [entries slot_entries]. rewrite IH, app_nil_r. cbn. tauto.
      * unfold heap_count. cbn [entries slot_entries]. rewrite IH, app_nil_r. cbn. lia.
  - destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Hin Hcount]. split.
      * intro e. rewrite entries_digit. cbn [entries slot_entries app]. apply Hin.
      * change (heap_count xs = length (tree_entries t) + heap_count (digit None rest)).
        rewrite count_digit. cbn [slot_entries length]. lia.
    + exact IH.
Qed.

Lemma select_valid {K} P r (h : heap K) :
  forest_valid P r h ->
  match select h with
  | None => h = []
  | Some (t, rest) => (exists rank, valid P rank t) /\ forest_valid P r rest
  end.
Proof.
  revert r. induction h as [|[u|] xs IH]; intros r Hh; rewrite select_equation.
  - reflexivity.
  - destruct Hh as [Hu [Hxs Hlast]].
    specialize (IH (S r) Hxs). destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Ht Hrest]. destruct (precedesb (root u) (root t)); split.
      * exists r; exact Hu.
      * apply valid_digit; [exact I|exact Hxs].
      * exact Ht.
      * apply valid_digit; assumption.
    + split; [exists r; exact Hu|exact I].
  - destruct Hh as [_ [Hxs Hlast]].
    specialize (IH (S r) Hxs). destruct (select xs) as [[t rest]|] eqn:Hselect.
    + destruct IH as [Ht Hrest]. split; [exact Ht|].
      apply valid_digit; [exact I|exact Hrest].
    + subst xs. destruct Hlast; contradiction.
Qed.

Lemma select_min {K} P r (h : heap K) t rest :
  forest_valid P r h -> select h = Some (t, rest) ->
  forall e, In e (entries h) -> precedes (root t) e.
Proof.
  revert r t rest. induction h as [|[u|] xs IH]; intros r t rest Hh Hselect e Hin;
    rewrite select_equation in Hselect.
  - discriminate.
  - destruct Hh as [Hu [Hxs Hlast]].
    destruct (select xs) as [[v tail]|] eqn:Htail.
    + destruct (precedesb (root u) (root v)) eqn:Hcmp; inversion Hselect; subst t rest.
      * cbn [entries slot_entries] in Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        -- apply (valid_root P r u Hu); exact Hin.
        -- eapply precedes_trans; [apply precedesb_spec; exact Hcmp|].
           apply (IH (S r) v tail Hxs eq_refl); exact Hin.
      * cbn [entries slot_entries] in Hin. apply in_app_iff in Hin.
        destruct Hin as [Hin|Hin].
        -- eapply precedes_trans; [apply precedesb_false; exact Hcmp|].
           apply (valid_root P r u Hu); exact Hin.
        -- apply (IH (S r) v tail Hxs eq_refl); exact Hin.
    + inversion Hselect; subst t rest.
      pose proof (select_entries xs) as Hempty. rewrite Htail in Hempty.
      cbn [entries slot_entries] in Hin. rewrite Hempty, app_nil_r in Hin.
      apply (valid_root P r u Hu); exact Hin.
  - destruct Hh as [_ [Hxs Hlast]].
    destruct (select xs) as [[v tail]|] eqn:Htail; [|discriminate].
    inversion Hselect; subst t rest. cbn [entries slot_entries app] in Hin.
    apply (IH (S r) v tail Hxs eq_refl); exact Hin.
Qed.

Lemma forest_append {K} P r (a b : heap K) :
  forest_valid P r a -> forest_valid P (r + length a) b ->
  forest_valid P r (a ++ b).
Proof.
  revert r. induction a as [|s xs IH]; intros r Ha Hb; cbn in *.
  - replace (r + 0) with r in Hb by lia. exact Hb.
  - destruct Ha as [Hs [Hxs Hlast]]. split; [exact Hs|]; split.
    + apply IH; [exact Hxs|].
      replace (S r + length xs) with (r + S (length xs)) by lia. exact Hb.
    + destruct Hlast as [Hsome|Htail]; [left; exact Hsome|].
      right. intro Heq. apply app_eq_nil in Heq. cbn. tauto.
Qed.

Lemma valid_children {K} P r (t : tree K) :
  valid P r t -> forest_valid P 0 (children_heap t) /\ length (children_heap t) = r.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore].
  - rewrite children_heap_equation. split; [exact I|reflexivity].
  - destruct IH as [Hcs Hlength].
    rewrite children_heap_equation in *. cbn [rev]. rewrite map_app. cbn [map].
    split.
    + apply forest_append; [exact Hcs|]. cbn.
      rewrite Hlength. split; [exact Hchild|]; split; [exact I|left; discriminate].
    + rewrite length_app. cbn. lia.
Qed.

Lemma entries_some {K} (ts : list (tree K)) :
  entries (List.map (@Some (tree K)) ts) = flat_map tree_entries ts.
Proof.
  induction ts as [|u us IH]; cbn [entries map slot_entries flat_map]; auto.
  rewrite IH. reflexivity.
Qed.

Lemma entries_children {K} (t : tree K) e :
  In e (tree_entries t) <-> e = root t \/ In e (entries (children_heap t)).
Proof.
  destruct t as [top cs]. rewrite children_heap_equation.
  cbn [tree_entries root In]. rewrite entries_some, !in_flat_map.
  split.
  - intros [Heq|[u [Hu Hin]]]; [left; congruence|right].
    exists u. split; [apply (proj1 (in_rev cs u)); exact Hu|exact Hin].
  - intros [Heq|[u [Hu Hin]]]; [left; congruence|right].
    exists u. split; [apply (proj2 (in_rev cs u)); exact Hu|exact Hin].
Qed.

Lemma count_children {K} (t : tree K) :
  length (tree_entries t) = S (heap_count (children_heap t)).
Proof.
  destruct t as [e cs]. rewrite children_heap_equation.
  cbn [tree_entries length]. f_equal. unfold heap_count. rewrite entries_some.
  induction cs as [|u us IH]; cbn [flat_map rev]; [reflexivity|].
  rewrite flat_map_app, !length_app. cbn [flat_map]. rewrite app_nil_r. lia.
Qed.

(** Minimum removal preserves ranks and entry properties and removes one entry. *)
Theorem remove_min_correct {K} P (h : heap K) :
  forest_valid P 0 h ->
  match remove_min h with
  | None => entries h = []
  | Some (e, rest) =>
    P e /\ forest_valid P 0 rest /\
    (forall a, In a (entries h) <-> a = e \/ In a (entries rest)) /\
    heap_count h = S (heap_count rest) /\
    (forall a, In a (entries h) -> precedes e a)
  end.
Proof.
  intro Hvalid. rewrite remove_min_equation.
  pose proof (select_entries h) as Hentries.
  pose proof (select_valid P 0 h Hvalid) as Hshape.
  destruct (select h) as [[t rest]|] eqn:Hselect; [|exact Hentries].
  destruct Hentries as [Hin Hcount], Hshape as [[rank Htree] Hrest].
  split.
  - apply (valid_all P rank t Htree). destruct t; cbn; auto.
  - split.
    + unfold merge. apply valid_meld.
      * apply (proj1 (valid_children P rank t Htree)).
      * exact Hrest.
      * exact I.
    + split.
      * intro a. rewrite Hin, entries_children.
        unfold merge. rewrite entries_meld. cbn [slot_entries In]. tauto.
      * split.
        -- unfold merge. rewrite count_meld. cbn [slot_entries length].
           rewrite count_children in Hcount. lia.
        -- apply (select_min P 0 h t rest Hvalid Hselect).
Qed.

(** A rank-[r] tree contains two to the power [r] entries. *)
Theorem valid_size {K} P r (t : tree K) :
  valid P r t -> length (tree_entries t) = 2 ^ r.
Proof.
  intro Hvalid; induction Hvalid as [e He|r e cs b Hbase IH Hchild IHchild Hbefore].
  - reflexivity.
  - cbn [tree_entries flat_map length] in *. rewrite length_app.
    rewrite Nat.pow_succ_r by lia. lia.
Qed.

(** A nonempty canonical forest's highest position bounds its width. *)
Theorem forest_height_bound {K} P r (h : heap K) :
  forest_valid P r h -> h <> [] -> 2 ^ (r + length h) <= 2 * heap_count h.
Proof.
  revert r. induction h as [|[t|] hs IH]; intros r Hforest Hnonempty.
  - contradiction.
  - destruct Hforest as [Ht [Hhs Hlast]]. destruct hs as [|s ss].
    + cbn [length]. rewrite Nat.add_1_r, Nat.pow_succ_r by lia.
      unfold heap_count. cbn [entries slot_entries]. rewrite app_nil_r.
      rewrite (valid_size P r t Ht). lia.
    + specialize (IH (S r) Hhs ltac:(discriminate)).
      replace (S r + length (s :: ss)) with (r + length (Some t :: s :: ss)) in IH
        by (cbn; lia).
      unfold heap_count in *. cbn [entries slot_entries] in IH |- *.
      rewrite !length_app in *. lia.
  - destruct Hforest as [_ [Hhs Hlast]]. destruct hs as [|s ss].
    + destruct Hlast; contradiction.
    + specialize (IH (S r) Hhs ltac:(discriminate)).
      replace (S r + length (s :: ss)) with (r + length (None :: s :: ss)) in IH
        by (cbn; lia).
      exact IH.
Qed.

(** A selected tree's rank is an occupied position inside the input forest. *)
Theorem select_rank_bounds {K} P r (h : heap K) t rest :
  forest_valid P r h -> select h = Some (t, rest) ->
  r <= length (children_heap t) /\ length (children_heap t) < r + length h.
Proof.
  revert r t rest. induction h as [|[u|] xs IH]; intros r t rest Hh Hselect;
    rewrite select_equation in Hselect.
  - discriminate.
  - destruct Hh as [Hu [Hxs Hlast]].
    pose proof (proj2 (valid_children P r u Hu)) as Hrank.
    destruct (select xs) as [[v tail]|] eqn:Htail.
    + destruct (precedesb (root u) (root v)); inversion Hselect; subst t rest.
      * rewrite Hrank. cbn [length]. lia.
      * specialize (IH (S r) v tail Hxs eq_refl). cbn [length]. lia.
    + inversion Hselect; subst t rest. rewrite Hrank. cbn [length]. lia.
  - destruct Hh as [_ [Hxs Hlast]].
    destruct (select xs) as [[v tail]|] eqn:Htail; [|discriminate].
    inversion Hselect; subst t rest.
    specialize (IH (S r) v tail Hxs eq_refl). cbn [length]. lia.
Qed.

(** Canonical forests use at most one plus the base-two logarithm of their entry count. *)
Theorem forest_width {K} P (h : heap K) :
  forest_valid P 0 h -> length h <= S (Nat.log2 (heap_count h)).
Proof.
  intro Hvalid. destruct h as [|s hs]; [cbn; lia|].
  pose proof (forest_height_bound P 0 (s :: hs) Hvalid ltac:(discriminate)) as Hheight.
  cbn [length Nat.add] in Hheight.
  rewrite Nat.pow_succ_r in Hheight by lia.
  assert (Hcount : 0 < heap_count (s :: hs)).
  { pose proof (Nat.pow_nonzero 2 (length hs) ltac:(lia)). nia. }
  assert (Hpow : 2 ^ length hs <= heap_count (s :: hs)) by nia.
  apply (proj1 (Nat.log2_le_pow2 (heap_count (s :: hs)) (length hs) Hcount)) in Hpow.
  cbn [length]. lia.
Qed.

(** Every selected tree has rank at most the logarithm of the input entry count. *)
Theorem selected_rank_log {K} P (h : heap K) t rest :
  forest_valid P 0 h -> select h = Some (t, rest) ->
  length (children_heap t) <= Nat.log2 (heap_count h).
Proof.
  intros Hvalid Hselect.
  pose proof (forest_width P h Hvalid).
  pose proof (select_rank_bounds P 0 h t rest Hvalid Hselect). lia.
Qed.

Local Lemma forest_member_rank {K} P start (h : heap K) t :
  forest_valid P start h -> In (Some t) h ->
  exists rank, valid P rank t /\ rank < start + length h.
Proof.
  revert start. induction h as [|[u|] hs IH]; intros start Hvalid Hin; [contradiction| |].
  - destruct Hvalid as [Hu [Hhs Hlast]]. destruct Hin as [Hequal|Hin].
    + inversion Hequal; subst u. exists start. split; [exact Hu|cbn; lia].
    + destruct (IH (S start) Hhs Hin) as [rank [Ht Hrank]].
      exists rank. split; [exact Ht|cbn; lia].
  - destruct Hvalid as [_ [Hhs Hlast]]. destruct Hin as [Hequal|Hin]; [discriminate|].
    destruct (IH (S start) Hhs Hin) as [rank [Ht Hrank]].
    exists rank. split; [exact Ht|cbn; lia].
Qed.

(** Every occupied tree has rank at most the logarithm of the forest's entry count. *)
Theorem forest_rank_log {K} P (h : heap K) t :
  forest_valid P 0 h -> In (Some t) h ->
  length (children_heap t) <= Nat.log2 (heap_count h).
Proof.
  intros Hvalid Hin.
  destruct (forest_member_rank P 0 h t Hvalid Hin) as [rank [Ht Hrank]].
  pose proof (forest_width P h Hvalid).
  rewrite (proj2 (valid_children P rank t Ht)). lia.
Qed.

(** Entry comparison charges one priority test and both cached widths on a tie. *)
Theorem precedesb_cost {K} (a b : entry K) :
  (Cost.ticks (precedesb_c a b) <=
    1 + N.pos (Pos.size (snd (fst a))) + N.pos (Pos.size (snd (fst b))))%N.
Proof.
  unfold precedesb_c. autorewrite with galois_cost.
  destruct (Pos.ltb (fst (fst a)) (fst (fst b))); autorewrite with galois_cost; [lia|].
  destruct (Pos.eqb (fst (fst a)) (fst (fst b)));
    autorewrite with galois_cost; lia.
Qed.

(** A link has the cost of its sole root comparison. *)
Theorem link_cost {K} (a b : tree K) :
  Cost.ticks (link_c a b) = Cost.ticks (precedesb_c (root a) (root b)).
Proof.
  destruct a as [a ac], b as [b bc]. unfold link_c. rewrite Cost.ticks_bind.
  destruct (Cost.value (precedesb_c a b)); rewrite Cost.ticks_ret; cbn [root]; lia.
Qed.

End HeapBinomial.
